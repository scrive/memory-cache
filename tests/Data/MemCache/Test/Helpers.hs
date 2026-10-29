-- | The helpers that several test modules use.
module Data.MemCache.Test.Helpers
  ( newCache
  , waitUntilBlocked
  ) where

import Control.Concurrent.Async
import GHC.Conc
import Test.Tasty.HUnit

import Data.MemCache

newCache :: (Int -> Int) -> Int -> IO (MemCache Int Int)
newCache = new

-- | Wait until the fetch blocks on an MVar.
--
-- In the tests, a fetch blocks either on the value that another thread
-- constructs, or on the lock of the cache while other fetches start. In the
-- second case, the fetch finds the key reserved or the value cached once it
-- gets the lock.
waitUntilBlocked :: Async a -> IO ()
waitUntilBlocked thread = do
  threadStatus (asyncThreadId thread) >>= \case
    ThreadBlocked BlockedOnMVar -> pure ()
    ThreadFinished -> assertFailure "The fetch finished without waiting"
    ThreadDied -> assertFailure "The fetch died without waiting"
    _ -> yield >> waitUntilBlocked thread
