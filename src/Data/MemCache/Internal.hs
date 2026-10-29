-- | Internals of "Data.MemCache", e.g. for implementing an instance of
-- 'Data.MemCache.MonadMemCache'.
--
-- This module is not part of the stable API.
module Data.MemCache.Internal
  ( MemCache (..)
  , MemCacheState (..)
  , new

    -- * Operations
  , LookupResult (..)
  , Reservation (..)
  , withLookupResult
  , fulfillReservation
  , invalidate
  ) where

import Control.Concurrent.MVar.Strict qualified as S
import Control.DeepSeq
import Control.Exception
import Control.Monad
import Control.Monad.Base
import Data.HashMap.Strict qualified as HM
import Data.HashPSQ qualified as Q
import Data.Hashable
import Data.Word

-- | The state of a 'MemCache'.
data MemCacheState k v = MemCacheState
  { mcSizeFun :: !(v -> Int)
  , mcSizeLimit :: !Int
  , mcCurrentSize :: !Int
  , mcTick :: !Word64
  , mcInProgress :: !(HM.HashMap k (S.MVar (Maybe v)))
  , mcCache :: !(Q.HashPSQ k Word64 v)
  }

-- | In-memory LRU cache for storing results of monadic actions.
newtype MemCache k v = MemCache (S.MVar (MemCacheState k v))

-- | Create a new 'MemCache'.
new
  :: MonadBase IO m
  => (v -> Int)
  -- ^ The sizing function. It must not throw. If it throws for a value, the
  -- value isn't cached, and the fetches that wait for it construct it again.
  -> Int
  -- ^ Cache size (in bytes).
  -> m (MemCache k v)
new sizeFun sizeLimit =
  liftBase $
    MemCache
      <$> S.newMVar
        MemCacheState
          { mcSizeFun = sizeFun
          , mcSizeLimit = sizeLimit
          , mcCurrentSize = 0
          , mcTick = 0
          , mcInProgress = HM.empty
          , mcCache = Q.empty
          }
{-# INLINEABLE new #-}
{-# SPECIALIZE new ::
  (v -> Int)
  -> Int
  -> IO (MemCache k v)
  #-}

----------------------------------------
-- Operations

-- | Result of a lookup in the cache.
data LookupResult k v
  = -- | The value is in the cache, or another thread constructed it.
    Hit v
  | -- | The key is reserved for the caller, who needs to construct the value
    -- and pass it to 'Data.MemCache.fulfillReservation'.
    Reserved (Reservation k v)
  | -- | The cache is unavailable, e.g. because an instance of
    -- 'Data.MemCache.MonadMemCache' disables caching. The caller needs to
    -- construct the value without storing it. 'withLookupResult' never passes
    -- this.
    Unavailable

-- | A key reserved for construction of its value.
data Reservation k v = Reservation
  { rvCache :: !(S.MVar (MemCacheState k v))
  , rvKey :: !k
  , rvValue :: !(S.MVar (Maybe v))
  }

-- | Look up a key and pass the result to the callback.
--
-- If another thread constructs the value, wait for it. If the value is neither
-- in the cache nor under construction, reserve the key for the callback. If the
-- callback exits without a call to 'fulfillReservation', the threads that wait
-- for the value try to construct it themselves.
withLookupResult
  :: forall k v a
   . (Ord k, Hashable k)
  => MemCache k v
  -> k
  -> (LookupResult k v -> IO a)
  -> IO a
withLookupResult cache@(MemCache mv) key f =
  mask
    ( \release ->
        reserve >>= \case
          Left mvValue -> release (S.readMVar mvValue) >>= traverse (release . f . Hit)
          -- The callback might short-circuit without an exception, e.g. in
          -- ExceptT, so the reservation needs to be aborted unconditionally.
          Right result@(Reserved reservation) -> Just <$> release (f result) `finally` abort reservation
          Right result -> Just <$> release (f result)
    )
    >>= maybe (withLookupResult cache key f) pure
  where
    -- Returns the MVar of the value if another thread constructs it.
    reserve :: IO (Either (S.MVar (Maybe v)) (LookupResult k v))
    reserve = S.modifyMVar mv $ \mc ->
      case Q.alter (lookupAndIncreasePriorityTo $ mcTick mc) key $ mcCache mc of
        (Just value, updatedCache) -> do
          pure
            ( mc {mcTick = mcTick mc + 1, mcCache = updatedCache}
            , Right $ Hit value
            )
        (Nothing, _) -> case key `HM.lookup` mcInProgress mc of
          Just mvValue -> pure (mc, Left mvValue)
          Nothing -> do
            mvValue <- S.newEmptyMVar
            pure
              ( mc {mcInProgress = HM.insert key mvValue $ mcInProgress mc}
              , Right $
                  Reserved
                    Reservation
                      { rvCache = mv
                      , rvKey = key
                      , rvValue = mvValue
                      }
              )
      where
        lookupAndIncreasePriorityTo
          :: Word64
          -> Maybe (Word64, v)
          -> (Maybe v, Maybe (Word64, v))
        lookupAndIncreasePriorityTo prio = \case
          Nothing -> (Nothing, Nothing)
          Just (_, value) -> (Just value, Just (prio, value))

    abort :: Reservation k v -> IO ()
    abort reservation = do
      S.tryReadMVar (rvValue reservation) >>= \case
        Just _ -> pure ()
        -- If modifyMVar_ blocks and gets interrupted, the key stays reserved.
        Nothing -> uninterruptibleMask_ . S.modifyMVar_ mv $ \mc -> do
          void $ S.tryPutMVar (rvValue reservation) Nothing
          pure $
            if holdsReservation mc reservation
              then mc {mcInProgress = HM.delete key $ mcInProgress mc}
              else mc
{-# INLINEABLE withLookupResult #-}

-- | Fully evaluate a constructed value, put it in the cache and pass it to the
-- threads that wait for it. Return the evaluated value.
--
-- If the key was invalidated after the reservation, the value isn't cached, but
-- the waiting threads still get it. If the reservation is already fulfilled,
-- or the callback of 'withLookupResult' has exited, the cache and the waiting
-- threads stay unchanged.
fulfillReservation
  :: (Ord k, Hashable k, NFData v)
  => Reservation k v
  -> v
  -> IO v
fulfillReservation reservation@(Reservation mv key mvValue) value = do
  forcedValue <- evaluate $ force value
  -- An exception after the waiting threads get the value would roll back the
  -- cache state, so the key would stay reserved with a value. Hence the mask,
  -- and the evaluation of the new state before the waiting threads get it, in
  -- case the sizing function throws.
  S.modifyMVarMasked_ mv $ \mc ->
    if holdsReservation mc reservation
      then do
        newMc <-
          evaluate $
            tidyCache
              mc
                { mcCurrentSize = mcCurrentSize mc + mcSizeFun mc forcedValue
                , mcTick = mcTick mc + 1
                , mcInProgress = HM.delete key $ mcInProgress mc
                , mcCache = Q.insert key (mcTick mc) forcedValue $ mcCache mc
                }
        S.tryPutMVar mvValue (Just forcedValue) >>= \case
          False -> pure mc
          True -> pure newMc
      else mc <$ S.tryPutMVar mvValue (Just forcedValue)
  pure forcedValue
  where
    tidyCache :: (Ord k, Hashable k) => MemCacheState k v -> MemCacheState k v
    tidyCache mc
      | mcCurrentSize mc <= mcSizeLimit mc = mc
      | otherwise = case Q.minView $ mcCache mc of
          Nothing ->
            error "tidyCache: size limit exceeded even though cache is empty"
          Just (_, _, minValue, tidiedCache) ->
            tidyCache
              mc
                { mcCurrentSize = mcCurrentSize mc - mcSizeFun mc minValue
                , mcCache = tidiedCache
                }
{-# INLINEABLE fulfillReservation #-}

-- | Invalidate a key in cache.
--
-- If a value for the key is under construction, it won't be cached. The
-- constructing fetch and the fetches that already wait for it still get it. If
-- the construction fails, the waiting fetches try again. Later fetches
-- construct the value again.
invalidate
  :: (Ord k, Hashable k)
  => MemCache k v
  -> k
  -- ^ The key to invalidate.
  -> IO ()
invalidate (MemCache mv) key = S.modifyMVar_ mv $ \mc -> do
  let unreserved = mc {mcInProgress = HM.delete key $ mcInProgress mc}
  pure $ case Q.deleteView key $ mcCache mc of
    Nothing -> unreserved
    Just (_, value, newCache) ->
      unreserved
        { mcCurrentSize = mcCurrentSize mc - mcSizeFun mc value
        , mcCache = newCache
        }
{-# INLINEABLE invalidate #-}

-- | Whether the key of the reservation is still reserved by it. It isn't once
-- the reservation is finished or the key is invalidated.
holdsReservation :: (Eq k, Hashable k) => MemCacheState k v -> Reservation k v -> Bool
holdsReservation mc reservation =
  HM.lookup (rvKey reservation) (mcInProgress mc) == Just (rvValue reservation)
