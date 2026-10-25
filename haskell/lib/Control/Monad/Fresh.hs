{-# LANGUAGE DerivingStrategies #-}

-- | A supply of fresh tags.
module Control.Monad.Fresh
  ( Fresh,
    fresh,
    runFresh,
    runFreshFrom,
    countFresh,
  )
where

import Control.Monad.Trans.State.Strict (State, evalState, runState, state)
import Numeric.Natural (Natural)

-- | A computation that may draw fresh tags.
newtype Fresh a = Fresh (State Natural a)
  deriving newtype (Functor, Applicative, Monad)

-- | A tag never drawn before in this run.
fresh :: Fresh Natural
fresh = Fresh $ state (\s -> (s, s + 1))

-- | Run a computation, with tags starting at the given number.
runFreshFrom :: Natural -> Fresh a -> a
runFreshFrom s (Fresh m) = evalState m s

-- | Run a computation, with tags starting at zero.
runFresh :: Fresh a -> a
runFresh = runFreshFrom 0

-- | Run a computation and report how many tags it drew.
countFresh :: Fresh a -> (a, Natural)
countFresh (Fresh m) = runState m 0
