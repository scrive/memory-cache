-- | In-memory LRU cache for storing results of monadic actions.
--
-- The operations work in every monad with an instance of 'MonadMemCache'. The
-- class has an instance for 'IO' and lifts through all monad transformers
-- with an instance of 'MonadTransControl'. An instance for another monad, e.g.
-- an effect monad, can run the methods of the 'IO' instance.
module Data.MemCache
  ( I.MemCache
  , I.new

    -- * Operations
  , fetch
  , fetch_
  , MonadMemCache (..)

    -- * Low-level operations
  , I.LookupResult (..)
  , I.Reservation
  ) where

import Control.DeepSeq
import Control.Monad.Trans.Class
import Control.Monad.Trans.Control
import Data.Hashable

import Data.MemCache.Internal qualified as I

-- | Fetch an object from 'I.MemCache' or construct it if it's not there. If
-- multiple threads try to access a key that doesn't exist in parallel, the
-- constructing action will be run only once. This doesn't hold if the instance
-- disables caching.
--
-- /Note:/ returned 'Bool' signifies whether the object was in cache.
--
-- /Note:/ the returned object is fully evaluated, unless the instance disables
-- caching.
--
-- __Warning:__ for a given key, the constructing action needs to always return
-- the same result.
fetch
  :: (Ord k, Hashable k, NFData v, MonadMemCache m)
  => I.MemCache k v
  -> k
  -> m v
  -- ^ The constructing action.
  -> m (v, Bool)
fetch cache key construct = withLookupResult cache key $ \case
  I.Hit value -> pure (value, True)
  I.Reserved reservation -> (,False) <$> (fulfillReservation reservation =<< construct)
  I.Unavailable -> (,False) <$> construct
{-# INLINEABLE fetch #-}

-- | Variant of 'fetch' that doesn't return a 'Bool'.
fetch_
  :: (Ord k, Hashable k, NFData v, MonadMemCache m)
  => I.MemCache k v
  -> k
  -> m v
  -- ^ The constructing action.
  -> m v
fetch_ cache key = fmap fst . fetch cache key
{-# INLINEABLE fetch_ #-}

-- | Monads that can operate on a 'I.MemCache'.
--
-- The first two methods are low-level operations. Use 'fetch' instead of them.
class Monad m => MonadMemCache m where
  -- | See 'I.withLookupResult'.
  withLookupResult
    :: (Ord k, Hashable k)
    => I.MemCache k v
    -> k
    -> (I.LookupResult k v -> m a)
    -> m a

  -- | See 'I.fulfillReservation'.
  fulfillReservation :: (Ord k, Hashable k, NFData v) => I.Reservation k v -> v -> m v

  -- | Invalidate a key in cache.
  invalidate :: (Ord k, Hashable k) => I.MemCache k v -> k -> m ()

instance MonadMemCache IO where
  withLookupResult = I.withLookupResult
  fulfillReservation = I.fulfillReservation
  invalidate = I.invalidate

instance
  {-# OVERLAPPABLE #-}
  ( Monad (t m)
  , MonadTransControl t
  , MonadMemCache m
  )
  => MonadMemCache (t m)
  where
  withLookupResult cache key f = controlT $ \run -> withLookupResult cache key (run . f)
  fulfillReservation reservation = lift . fulfillReservation reservation
  invalidate cache = lift . invalidate cache

----------------------------------------
-- Specializations for IO

{-# SPECIALIZE fetch ::
  (Ord k, Hashable k, NFData v)
  => I.MemCache k v
  -> k
  -> IO v
  -> IO (v, Bool)
  #-}

{-# SPECIALIZE fetch_ ::
  (Ord k, Hashable k, NFData v)
  => I.MemCache k v
  -> k
  -> IO v
  -> IO v
  #-}
