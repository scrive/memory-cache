module Main (main) where

import Test.Tasty

import Data.MemCache.Test.Class
import Data.MemCache.Test.Concurrency
import Data.MemCache.Test.Storage
import Data.MemCache.Test.Transformers

main :: IO ()
main =
  defaultMain . localOption (mkTimeout timeLimit) $
    testGroup
      "memory-cache"
      [ concurrencyTests
      , storageTests
      , transformerTests
      , classTests
      ]
  where
    -- A bug in the cache usually makes a fetch block forever, and the time
    -- limit of a test turns that into a failure. No measurement gave the
    -- limit. The slowest test takes about 0.03 seconds on a fast local
    -- machine. The limit is far above that, so that a slow CI machine stays
    -- below it.
    timeLimit :: Integer
    timeLimit = 10_000_000
