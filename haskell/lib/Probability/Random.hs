-- | A small pseudo-random generator and some probability laws.
--
-- The generator is SplitMix64 (Steele, Lea and Flood, OOPSLA 2014), written out
-- to avoid a dependency. It is deterministic: the same seed gives the same
-- draws.
module Probability.Random
  ( Gen,
    mkGen,
    splitGen,
    uniform01,
    Law (..),
    draws,
    uniform,
    normal,
    exponential,
    bernoulli,
    rademacher,
    poissonLaw,
    discrete,
  )
where

import Data.Bits (shiftR, xor)
import Data.List.NonEmpty (NonEmpty (..))
import Data.Word (Word64)
import Numeric.Natural (Natural)

-- | The state of the generator.
newtype Gen = Gen Word64

-- | A generator from a seed.
mkGen :: Word64 -> Gen
mkGen = Gen

golden :: Word64
golden = 0x9e3779b97f4a7c15

mix :: Word64 -> Word64
mix z0 =
  let z1 = (z0 `xor` (z0 `shiftR` 30)) * 0xbf58476d1ce4e5b9
      z2 = (z1 `xor` (z1 `shiftR` 27)) * 0x94d049bb133111eb
   in z2 `xor` (z2 `shiftR` 31)

next64 :: Gen -> (Word64, Gen)
next64 (Gen s) = let s' = s + golden in (mix s', Gen s')

-- | Two independent generators.
splitGen :: Gen -> (Gen, Gen)
splitGen g = let (a, g1) = next64 g; (b, _) = next64 g1 in (Gen (mix a), Gen (mix (b `xor` golden)))

-- | A uniform draw from @[0, 1)@, with 53 random bits.
uniform01 :: Gen -> (Double, Gen)
uniform01 g = let (w, g') = next64 g in (fromIntegral (w `shiftR` 11) / 9007199254740992, g')

-- | A probability law on the real line: a way to draw from it.
newtype Law = Law (Gen -> (Double, Gen))

-- | @n@ independent draws.
draws :: Natural -> Law -> Gen -> [Double]
draws n (Law f) = go n
  where
    go 0 _ = []
    go i g = let (x, g') = f g in x : go (i - 1) g'

-- | The uniform law on @[a, b)@.
uniform :: Double -> Double -> Law
uniform a b = Law (\g -> let (u, g') = uniform01 g in (a + (b - a) * u, g'))

-- | The normal law with mean @μ@ and standard deviation @σ@ (Box–Muller).
normal :: Double -> Double -> Law
normal mu sigma = Law $ \g ->
  let (u1, g1) = uniform01 g
      (u2, g2) = uniform01 g1
      r = sqrt (-(2 * log (1 - u1)))
   in (mu + sigma * r * cos (2 * pi * u2), g2)

-- | The exponential law with rate @λ@.
exponential :: Double -> Law
exponential lam = Law (\g -> let (u, g') = uniform01 g in (negate (log (1 - u)) / lam, g'))

-- | The Bernoulli law: 1 with probability @p@, else 0.
bernoulli :: Double -> Law
bernoulli p = Law (\g -> let (u, g') = uniform01 g in (if u < p then 1 else 0, g'))

-- | The Rademacher law: ±1 with probability one half each.
rademacher :: Law
rademacher = Law (\g -> let (u, g') = uniform01 g in (if u < 0.5 then -1 else 1, g'))

-- | The Poisson law with mean @λ@ (Knuth's product of uniforms; for small @λ@).
poissonLaw :: Double -> Law
poissonLaw lam = Law (go 0 1)
  where
    limit = exp (negate lam)
    go k p g =
      let (u, g') = uniform01 g
          p' = p * u
       in if p' < limit then (k, g') else go (k + 1) p' g'

-- | A finite law, given by values and probabilities summing to one.
discrete :: NonEmpty (Double, Double) -> Law
discrete vps = Law (\g -> let (u, g') = uniform01 g in (pick u vps, g'))
  where
    pick u ((x, p) :| rest) = case rest of
      [] -> x
      next : more -> if u < p then x else pick (u - p) (next :| more)
