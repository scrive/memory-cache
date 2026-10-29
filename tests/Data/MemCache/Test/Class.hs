module Data.MemCache.Test.Class (classTests) where

import Control.Monad
import Control.Monad.IO.Class
import Data.IORef
import Test.Tasty
import Test.Tasty.HUnit

import Data.MemCache
import Data.MemCache.Test.Helpers

classTests :: TestTree
classTests =
  testGroup
    "class"
    [ testCase "instance without a cache" test_noCache
    , testCase "fulfillment after the callback exits" test_lateFulfillment
    , testCase "second fulfillment" test_secondFulfillment
    ]

newtype NoCache a = NoCache (IO a)
  deriving newtype (Functor, Applicative, Monad, MonadIO)

instance MonadMemCache NoCache where
  withLookupResult _ _ f = f Unavailable
  fulfillReservation _ _ = error "No reservation exists"
  invalidate _ _ = pure ()

test_noCache :: Assertion
test_noCache = do
  cache <- newCache (const 1) 10
  runs <- newIORef @Int 0
  results <- runNoCache . replicateM 3 . fetch cache 1 $ do
    liftIO $ modifyIORef' runs (+ 1)
    pure 2
  readIORef runs >>= assertEqual "Number of constructions" 3
  assertEqual "Results" (replicate 3 (2, False)) results
  where
    runNoCache :: NoCache a -> IO a
    runNoCache (NoCache action) = action

test_lateFulfillment :: Assertion
test_lateFulfillment = do
  cache <- newCache (const 1) 10
  withLookupResult cache 1 pure >>= \case
    Reserved reservation ->
      fulfillReservation reservation 2 >>= assertEqual "Returned value" 2
    _ -> assertFailure "The key wasn't reserved"
  fetch cache 1 (pure 3) >>= assertEqual "Later fetch" (3, False)

test_secondFulfillment :: Assertion
test_secondFulfillment = do
  cache <- newCache (const 1) 10
  withLookupResult cache 1 $ \case
    Reserved reservation -> do
      void $ fulfillReservation reservation 2
      fulfillReservation reservation 3 >>= assertEqual "Returned value" 3
    _ -> assertFailure "The key wasn't reserved"
  fetch cache 1 (pure 4) >>= assertEqual "Later fetch" (2, True)
