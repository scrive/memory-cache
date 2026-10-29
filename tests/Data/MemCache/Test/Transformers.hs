module Data.MemCache.Test.Transformers (transformerTests) where

import Control.Concurrent
import Control.Concurrent.Async
import Control.Exception
import Control.Monad
import Control.Monad.Trans.State.Strict
import Test.Tasty
import Test.Tasty.HUnit

import Data.MemCache
import Data.MemCache.Test.Helpers

transformerTests :: TestTree
transformerTests =
  testGroup
    "transformers"
    [ testCase "state on a miss" test_stateOnMiss
    , testCase "state on a hit" test_stateOnHit
    , testCase "state of a waiting fetch" test_stateOfWaitingFetch
    , testCase "state of a waiting fetch that retries" test_stateOfRetryingFetch
    , testCase "invalidation in a transformer" test_invalidation
    ]

test_stateOnMiss :: Assertion
test_stateOnMiss = do
  cache <- newCache (const 1) 10
  runStateT @Int (fetch cache 1 $ modify (+ 1) >> pure 2) 10
    >>= assertEqual "Result and state" ((2, False), 11)

test_stateOnHit :: Assertion
test_stateOnHit = do
  cache <- newCache (const 1) 10
  void $ fetch cache 1 (pure 2)
  runStateT @Int (fetch cache 1 $ modify (+ 1) >> pure 3) 10
    >>= assertEqual "Result and state" ((2, True), 10)

test_stateOfWaitingFetch :: Assertion
test_stateOfWaitingFetch = do
  cache <- newCache (const 1) 10
  started <- newEmptyMVar
  gate <- newEmptyMVar
  constructing <- async . fetch cache 1 $ do
    putMVar started ()
    takeMVar gate
    pure 2
  takeMVar started
  waiting <- async $ runStateT @Int (fetch cache 1 $ modify (+ 1) >> pure 3) 10
  waitUntilBlocked waiting
  putMVar gate ()
  void $ wait constructing
  wait waiting >>= assertEqual "Result and state" ((2, True), 10)

-- | The waiting fetch constructs the value itself after the other
-- construction fails, so its state changes once.
test_stateOfRetryingFetch :: Assertion
test_stateOfRetryingFetch = do
  cache <- newCache (const 1) 10
  started <- newEmptyMVar
  gate <- newEmptyMVar
  constructing <- async . fetch cache 1 $ do
    putMVar started ()
    takeMVar gate
    throwIO $ ErrorCall "Construction failed"
  takeMVar started
  waiting <- async $ runStateT @Int (fetch cache 1 $ modify (+ 1) >> pure 3) 10
  waitUntilBlocked waiting
  putMVar gate ()
  void $ waitCatch constructing
  wait waiting >>= assertEqual "Result and state" ((3, False), 11)

test_invalidation :: Assertion
test_invalidation = do
  cache <- newCache (const 1) 10
  void $ fetch cache 1 (pure 2)
  evalStateT @IO @Int (invalidate cache 1) 0
  fetch cache 1 (pure 3) >>= assertEqual "Fetch after invalidation" (3, False)
