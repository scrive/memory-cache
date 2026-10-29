module Data.MemCache.Test.Storage (storageTests) where

import Control.Exception
import Control.Monad
import Test.Tasty
import Test.Tasty.HUnit

import Data.MemCache
import Data.MemCache.Test.Helpers

storageTests :: TestTree
storageTests =
  testGroup
    "storage"
    [ testCase "cached value" test_cachedValue
    , testCase "full evaluation" test_fullEvaluation
    , testCase "sizing function throws" test_sizingFunctionThrows
    , testCase "eviction" test_eviction
    , testCase "eviction by size" test_evictionBySize
    , testCase "value larger than the limit" test_valueLargerThanLimit
    , testCase "invalidation" test_invalidation
    , testCase "invalidation frees the size" test_invalidationFreesSize
    ]

test_cachedValue :: Assertion
test_cachedValue = do
  cache <- newCache (const 1) 10
  fetch cache 1 (pure 2) >>= assertEqual "First fetch" (2, False)
  fetch cache 1 (pure 3) >>= assertEqual "Second fetch" (2, True)

-- | The sizing function doesn't evaluate the elements of the list.
test_fullEvaluation :: Assertion
test_fullEvaluation = do
  cache <- new @IO @[Int] @Int length 10
  try @ErrorCall (fetch cache 1 (pure [1, error "Unevaluated element"])) >>= \case
    Left _ -> pure ()
    Right _ -> assertFailure "The first fetch didn't evaluate the value fully"
  fetch cache 1 (pure [2]) >>= assertEqual "Second fetch" ([2], False)

test_sizingFunctionThrows :: Assertion
test_sizingFunctionThrows = do
  cache <- newCache (\value -> if value == 1 then error "Sizing failed" else 1) 10
  try @ErrorCall (fetch cache 1 (pure 1)) >>= \case
    Left _ -> pure ()
    Right _ -> assertFailure "The first fetch didn't throw"
  fetch cache 1 (pure 2) >>= assertEqual "Second fetch" (2, False)

test_eviction :: Assertion
test_eviction = do
  cache <- newCache (const 1) 2
  forM_ [1, 2] $ \key -> fetch cache key (pure key)
  void $ fetch cache 1 (pure 0)
  void $ fetch cache 3 (pure 3)
  fetch cache 1 (pure 0) >>= assertEqual "Recently used value" (1, True)
  fetch cache 2 (pure 0) >>= assertEqual "Evicted value" (0, False)

test_evictionBySize :: Assertion
test_evictionBySize = do
  cache <- newCache id 10
  void $ fetch cache 1 (pure 6)
  void $ fetch cache 2 (pure 5)
  fetch cache 2 (pure 0) >>= assertEqual "Newer value" (5, True)
  fetch cache 1 (pure 0) >>= assertEqual "Evicted value" (0, False)

test_valueLargerThanLimit :: Assertion
test_valueLargerThanLimit = do
  cache <- newCache id 10
  fetch cache 1 (pure 20) >>= assertEqual "Large value" (20, False)
  fetch cache 1 (pure 0) >>= assertEqual "Large value again" (0, False)
  void $ fetch cache 2 (pure 5)
  fetch cache 2 (pure 0) >>= assertEqual "Value that fits" (5, True)

test_invalidation :: Assertion
test_invalidation = do
  cache <- newCache (const 1) 10
  void $ fetch cache 1 (pure 2)
  invalidate cache 1
  fetch cache 1 (pure 3) >>= assertEqual "Fetch after invalidation" (3, False)

-- | If the size of an invalidated value stayed counted, the next value would
-- exceed the limit and be evicted right away.
test_invalidationFreesSize :: Assertion
test_invalidationFreesSize = do
  cache <- newCache id 10
  void $ fetch cache 1 (pure 6)
  invalidate cache 1
  void $ fetch cache 2 (pure 5)
  fetch cache 2 (pure 0) >>= assertEqual "Value after invalidation" (5, True)
