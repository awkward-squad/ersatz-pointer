{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE TypeApplications #-}

import Control.Concurrent (threadDelay)
import Data.Function ((&))
import Data.IORef (newIORef, readIORef)
import ErsatzPointer qualified as Ersatz (Pointer (Pointer))
import ErsatzPointer qualified as ErsatzPointer
import System.Mem (performGC)

main :: IO ()
main = do
  source <- newIORef ()
  let target = 17 :: Int

  -- Construct an ersatz pointer made of straw from source to target.
  strawPointerReference <-
    ErsatzPointer.construct @'ErsatzPointer.Straw $
      Ersatz.Pointer source target
        & ErsatzPointer.onDemolish (putStrLn "Goodbye, straw world!")

  let queryStrawPointer =
        ErsatzPointer.dereference strawPointerReference >>= \case
          Nothing -> putStrLn "Straw pointer is no longer constructed."
          Just (Ersatz.Pointer _source _target) -> putStrLn "Straw pointer is still constructed."

  -- Construct an ersatz pointer made of brick from source to target.
  brickPointerReference <-
    ErsatzPointer.construct @'ErsatzPointer.Brick $
      Ersatz.Pointer source target
        & ErsatzPointer.onDemolish (putStrLn "Goodbye, brick world!")

  let queryBrickPointer =
        ErsatzPointer.dereference brickPointerReference >>= \case
          Nothing -> putStrLn "Brick pointer is no longer constructed."
          Just (Ersatz.Pointer _source _target) -> putStrLn "Brick pointer is still constructed."

  -- Query whether the straw pointer is still constructed.
  queryStrawPointer

  -- Query whether the brick pointer is still constructed.
  queryBrickPointer

  -- Demolish the straw pointer before the source is garbage-collected, and observe that its finalizer runs.
  ErsatzPointer.demolish strawPointerReference

  -- Query whether the straw pointer is still constructed.
  queryStrawPointer

  -- Observe that a second demolish is a no-op: its finalizer does not run again.
  ErsatzPointer.demolish strawPointerReference

  -- Keep the source alive until here.
  readIORef source

  -- Run a major GC and observe that the brick pointer finalizer runs.
  putStrLn "Running performGC"
  performGC

  -- Sleep for 100ms just to allow finalizer to run.
  threadDelay 100_000

  -- Query whether the brick pointer is still constructed.
  queryBrickPointer
