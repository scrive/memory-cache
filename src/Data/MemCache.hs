-- | In-memory LRU cache for storing results of monadic actions.
module Data.MemCache
  ( MemCache

    -- * Operations
  , new
  , fetch
  , fetch_
  , invalidate
  ) where

import Control.Concurrent.MVar.Strict
import Control.DeepSeq
import Control.Exception
import Control.Monad
import Control.Monad.Base
import Control.Monad.Trans.Control
import Data.Function
import Data.HashMap.Strict qualified as HM
import Data.HashPSQ qualified as Q
import Data.Hashable
import Data.Word

data MemCache_ k v = MemCache_
  { mcSizeFun :: v -> Int
  , mcSizeLimit :: Int
  , mcCurrentSize :: Int
  , mcTick :: Word64
  , mcInProgress :: HM.HashMap k (MVar' (Maybe v))
  , mcCache :: Q.HashPSQ k Word64 v
  }

-- | In-memory LRU cache for storing results of monadic actions.
newtype MemCache k v = MemCache (MVar' (MemCache_ k v))

-- | Create a new 'MemCache'.
new
  :: MonadBase IO m
  => (v -> Int)
  -- ^ The sizing function.
  -> Int
  -- ^ Cache size (in bytes).
  -> m (MemCache k v)
new sizeFun sizeLimit =
  liftBase $
    MemCache
      <$> newMVar'
        MemCache_
          { mcSizeFun = sizeFun
          , mcSizeLimit = sizeLimit
          , mcCurrentSize = 0
          , mcTick = 0
          , mcInProgress = HM.empty
          , mcCache = Q.empty
          }
{-# INLINEABLE new #-}

-- | Fetch an object from 'MemCache' or construct it if it's not there. If
-- multiple threads try to access a key that doesn't exist in parallel, the
-- constructing action will be run only once.
--
-- /Note:/ returned 'Bool' signifies whether the object was constructed.
--
-- __Warning:__ for a given key, the constructing action needs to always return
-- the same result.
fetch
  :: (Ord k, Hashable k, NFData v, MonadBaseControl IO m)
  => MemCache k v
  -> k
  -> m v
  -- ^ The constructing action.
  -> m (v, Bool)
fetch (MemCache mv) key construct = do
  control $ \unlift -> fix $ \loop -> mask $ \release -> do
    -- Note: asynchronous exceptions need to be masked in the following places:
    --
    -- (1) When eel is Left and mvAlreadyThere is False: if asynchronous
    -- exception arrives between first modifyMVar returns and onException
    -- handler is estabilished, we'll be left with an orphan MVar in
    -- mcInProgress that never gets filled.
    --
    -- (2) When constructing action throws, then, if the exception arrives
    --   between second modifyMVar returns and onException block is exited, it
    --   may happen that another thread already inserted a different MVar under
    --   the same key, which would've been then removed by the onException
    --   handler.
    --
    -- Attempt to get a value corresponding to the key from cache. If it's
    -- there, bump its priority and return it. Otherwise either check whether
    -- the value is already being computed and return associated MVar or create
    -- a new one.
    eel <- modifyMVar' mv $ \mc -> release $ do
      case Q.alter (lookupAndIncreasePriorityTo $ mcTick mc) key $ mcCache mc of
        (Just el, updatedCache) -> do
          pure
            ( mc {mcTick = mcTick mc + 1, mcCache = updatedCache}
            , Right el
            )
        (Nothing, _) -> case key `HM.lookup` mcInProgress mc of
          Just mvEl -> pure (mc, Left (mvEl, True))
          Nothing -> do
            mvEl <- newEmptyMVar'
            pure
              ( mc {mcInProgress = HM.insert key mvEl $ mcInProgress mc}
              , Left (mvEl, False)
              )

    case eel of
      Right el -> unlift $ pure (el, False)
      Left (mvEl, mvAlreadyThere) -> do
        -- If we got an existing MVar, wait for its result. Otherwise run
        -- constructing action and update cache accordingly.
        if mvAlreadyThere
          then
            release $
              readMVar' mvEl >>= \case
                Nothing -> do
                  -- If the thread that was supposed to construct the value
                  -- failed for some reason, let's try ourselves.
                  loop
                Just value -> unlift $ pure (value, False)
          else do
            evalue <- (`onException` removeInProgress mvEl) $ do
              -- Construct the value and update cache accordingly.
              --
              -- If at any point during construction the exception is thrown,
              -- use mvEl to propagate the failure to any other caller that
              -- waits for its result. If at any point in time the current
              -- thread throws (or receives asynchronous exception), remove mvEl
              -- from mcInProgress as at this point it's a dangling MVar.
              evalue <- try @SomeException . release . unlift $ do
                v <- liftBase . evaluate . force =<< construct
                liftBase $ do
                  putMVar' mvEl $ Just v
                  pure (v, True)
              modifyMVar'_ mv $ \mc ->
                tryReadMVar' mvEl >>= \case
                  Nothing -> do
                    putMVar' mvEl Nothing
                    pure $ mc {mcInProgress = HM.delete key $ mcInProgress mc}
                  Just (Just value) -> do
                    pure $
                      tidyCache
                        mc
                          { mcCurrentSize = mcCurrentSize mc + mcSizeFun mc value
                          , mcTick = mcTick mc + 1
                          , mcInProgress = HM.delete key $ mcInProgress mc
                          , mcCache = Q.insert key (mcTick mc) value $ mcCache mc
                          }
                  Just Nothing -> error "fetch: impossible"
              pure evalue
            either throwIO pure evalue
  where
    lookupAndIncreasePriorityTo prio = \case
      Nothing -> (Nothing, Nothing)
      Just (_, mvEl) -> (Just mvEl, Just (prio, mvEl))

    removeInProgress mvEl = uninterruptibleMask_ $ do
      -- Signal other threads waiting for the MVar and remove it from cache.
      -- UninterruptibleMask is there since modifyMVar_ might block.
      void $ tryPutMVar' mvEl Nothing
      modifyMVar'_ mv $ \mc -> do
        pure mc {mcInProgress = HM.delete key $ mcInProgress mc}

    tidyCache mc = go (mcCache mc) (mcCurrentSize mc)
      where
        go cache size
          | size <= mcSizeLimit mc = mc {mcCurrentSize = size, mcCache = cache}
          | otherwise = case Q.minView cache of
              Nothing ->
                error "tidyCache: size limit exceeded even though cache is empty"
              Just (_, _, minEl, tidiedCache) -> go tidiedCache $ size - mcSizeFun mc minEl
{-# INLINEABLE fetch #-}

-- | Fetch an object from cache or construct it if it's not there.
fetch_
  :: (Ord k, Hashable k, NFData v, MonadBaseControl IO m)
  => MemCache k v
  -> k
  -> m v
  -- ^ The constructing action.
  -> m v
fetch_ mc key = fmap fst . fetch mc key
{-# INLINEABLE fetch_ #-}

-- | Invalidate a key in cache.
invalidate
  :: (Ord k, Hashable k, MonadBase IO m)
  => MemCache k v
  -> k
  -- ^ The key to invalidate.
  -> m ()
invalidate (MemCache mv) key = liftBase . modifyMVar'_ mv $ \mc ->
  case Q.deleteView key $ mcCache mc of
    Nothing -> pure mc
    Just (_, value, newCache) -> do
      pure $
        mc
          { mcCurrentSize = mcCurrentSize mc - mcSizeFun mc value
          , mcCache = newCache
          }
{-# INLINEABLE invalidate #-}

----------------------------------------
-- Specializations for IO

{-# SPECIALIZE new ::
  (v -> Int)
  -> Int
  -> IO (MemCache k v)
  #-}

{-# SPECIALIZE fetch ::
  (Ord k, Hashable k, NFData v)
  => MemCache k v
  -> k
  -> IO v
  -> IO (v, Bool)
  #-}

{-# SPECIALIZE fetch_ ::
  (Ord k, Hashable k, NFData v)
  => MemCache k v
  -> k
  -> IO v
  -> IO v
  #-}

{-# SPECIALIZE invalidate ::
  (Ord k, Hashable k)
  => MemCache k v
  -> k
  -> IO ()
  #-}
