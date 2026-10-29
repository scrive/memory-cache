module Data.MemCache.Test.Concurrency (concurrencyTests) where

import Control.Concurrent
import Control.Concurrent.Async
import Control.Exception
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Except
import Data.IORef
import Test.Tasty
import Test.Tasty.HUnit

import Data.MemCache
import Data.MemCache.Test.Helpers

concurrencyTests :: TestTree
concurrencyTests =
  testGroup
    "concurrency"
    [ testCase "construction runs once" test_constructionRunsOnce
    , testCase "construction throws" test_constructionThrows
    , testCase "construction short-circuits" test_constructionShortCircuits
    , testCase "constructing thread is killed" test_constructingThreadKilled
    , testCase "cancelled fetches" test_cancelledFetches
    ]

test_constructionRunsOnce :: Assertion
test_constructionRunsOnce = do
  cache <- newCache (const 1) 10
  runs <- newIORef @Int 0
  started <- newEmptyMVar
  gate <- newEmptyMVar
  constructing <- async . fetch cache 1 $ do
    atomicModifyIORef' runs $ \n -> (n + 1, ())
    putMVar started ()
    takeMVar gate
    pure 2
  takeMVar started
  waiting <- replicateM 19 . async . fetch cache 1 $ do
    atomicModifyIORef' runs $ \n -> (n + 1, ())
    pure 3
  mapM_ waitUntilBlocked waiting
  putMVar gate ()
  wait constructing >>= assertEqual "Constructing fetch" (2, False)
  mapM wait waiting >>= assertEqual "Waiting fetches" (replicate 19 (2, True))
  readIORef runs >>= assertEqual "Number of constructions" 1

test_constructionThrows :: Assertion
test_constructionThrows = do
  cache <- newCache (const 1) 10
  started <- newEmptyMVar
  gate <- newEmptyMVar
  constructing <- async . fetch cache 1 $ do
    putMVar started ()
    takeMVar gate
    throwIO $ ErrorCall "Construction failed"
  takeMVar started
  waiting <- async $ fetch cache 1 (pure 2)
  waitUntilBlocked waiting
  putMVar gate ()
  waitCatch constructing >>= \case
    Left e ->
      assertEqual
        "Exception of the constructing fetch"
        (Just $ ErrorCall "Construction failed")
        (fromException e)
    Right _ -> assertFailure "The constructing fetch didn't throw"
  wait waiting >>= assertEqual "Waiting fetch" (2, False)
  fetch cache 1 (pure 3) >>= assertEqual "Later fetch" (2, True)

test_constructionShortCircuits :: Assertion
test_constructionShortCircuits = do
  cache <- newCache (const 1) 10
  started <- newEmptyMVar
  gate <- newEmptyMVar
  constructing <- async . runExceptT . fetch cache 1 $ do
    liftIO $ putMVar started ()
    liftIO $ takeMVar gate
    throwE "Construction failed"
  takeMVar started
  waiting <- async $ fetch cache 1 (pure 2)
  waitUntilBlocked waiting
  putMVar gate ()
  wait constructing
    >>= assertEqual "Constructing fetch" (Left "Construction failed")
  wait waiting >>= assertEqual "Waiting fetch" (2, False)
  fetch cache 1 (pure 3) >>= assertEqual "Later fetch" (2, True)

test_constructingThreadKilled :: Assertion
test_constructingThreadKilled = do
  cache <- newCache (const 1) 10
  started <- newEmptyMVar
  gate <- newEmptyMVar @()
  constructing <- async . fetch cache 1 $ do
    putMVar started ()
    takeMVar gate
    pure 2
  takeMVar started
  waiting <- async $ fetch cache 1 (pure 3)
  waitUntilBlocked waiting
  cancel constructing
  wait waiting >>= assertEqual "Waiting fetch" (3, False)

-- | Cancel fetches after a varying number of yields, so that some
-- cancellations arrive while the key gets reserved. Every key must stay usable.
test_cancelledFetches :: Assertion
test_cancelledFetches = do
  cache <- newCache (const 1) 10
  -- A broken copy of the cache had an unmasked point between the reservation
  -- and the installation of the finalizer. With it, about 1 in 135 iterations
  -- left its key reserved on several cores. On a single core, none did.
  forM_ [1 .. 5000] $ \key -> do
    thread <- async $ fetch cache key (pure key)
    replicateM_ (key `mod` 50) yield
    cancel thread
    -- Blocks if the key stays reserved.
    void $ fetch cache key (pure 0)
