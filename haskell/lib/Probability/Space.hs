-- | Finite probability spaces and random variables on them.
--
-- A 'Space' is a finite list of weighted sample points, with the value of every
-- named variable at every point. It is either a Monte Carlo sample
-- ('monteCarlo', equal weights) or the exact product of finite laws ('exact',
-- over any ring, for example 'Rational'). A random variable ('RV') is a
-- constant or its list of values on the points.
module Probability.Space
  ( Space,
    points,
    column,
    RV (..),
    mean,
    monteCarlo,
    exact,
  )
where

import Algebra.Ring
import Data.List (genericLength, transpose, unfoldr)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Word (Word64)
import Numeric.Natural (Natural)
import Probability.Random

-- | A finite probability space: the weights of the points, which sum to one,
-- and for each named variable its values on the points.
data Space name c = Space [c] (Map name [c])

-- | The number of sample points.
points :: Space name c -> Natural
points (Space ws _) = genericLength ws

-- | The named variable, as a random variable.
column :: (Ord name) => Space name c -> name -> Maybe (RV c)
column (Space _ cols) n = Values <$> Map.lookup n cols

-- | A random variable: a constant, or its values on the points of a space.
data RV c = Const c | Values [c]

-- | Equality of functions on the points; a constant equals the variable that
-- takes its value everywhere.
instance (Eq c) => Eq (RV c) where
  Const a == Const b = a == b
  Const a == Values ys = all (== a) ys
  Values xs == Const b = all (== b) xs
  Values xs == Values ys = xs == ys

lift2 :: (c -> c -> c) -> RV c -> RV c -> RV c
lift2 f (Const a) (Const b) = Const (f a b)
lift2 f (Const a) (Values ys) = Values (map (f a) ys)
lift2 f (Values xs) (Const b) = Values (map (`f` b) xs)
lift2 f (Values xs) (Values ys) = Values (zipWith f xs ys)

-- | Random variables on one space form a ring under the pointwise operations.
instance (Ring c) => Ring (RV c) where
  zero = Const zero
  one = Const one
  (.+.) = lift2 (.+.)
  (.*.) = lift2 (.*.)
  neg (Const a) = Const (neg a)
  neg (Values xs) = Values (map neg xs)

-- | The expectation of a random variable on a space.
mean :: (Ring c) => Space name c -> RV c -> c
mean _ (Const c) = c
mean (Space ws _) (Values xs) = sumR (zipWith (.*.) ws xs)

-- | A Monte Carlo sample: @n@ independent draws of each named law, from a seed.
-- Different names get independent streams.
monteCarlo :: (Ord name) => Natural -> Word64 -> [(name, Law)] -> Space name Double
monteCarlo n seed laws =
  Space name mp
  where
    name = replicate (fromIntegral n) (1 / fromIntegral n)
    mp = Map.fromList $ zip (fst <$> laws) columns
    gens = unfoldr (Just . splitGen) (mkGen seed)
    columns = [draws n law g | ((_, law), g) <- zip laws gens]

-- | The exact product of finite laws, each given by values and probabilities.
-- Over 'Rational' every expectation is exact.
exact :: (Ord name, Ring c) => [(name, [(c, c)])] -> Space name c
exact laws =
  Space name mp
  where
    name = map (productR . map snd) pts
    mp = Map.fromList $ zip (fst <$> laws) columns
    pts = mapM snd laws
    columns = transpose $ map (fst <$>) pts
