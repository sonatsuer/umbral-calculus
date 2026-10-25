-- | The language as a tool on sequences.
--
-- Each function takes and returns moment sequences as streams indexed from 0,
-- with entry 0 equal to 1 (the zeroth moment, never read). Each runs one of the
-- terms of "Umbral.Auxiliary" in the moment model, so the result depends only
-- on the moments put in. The exception is 'cumulants', which uses the
-- recursive moment-cumulant formula for speed; 'cumulantsByComposition' is the
-- term, and the tests check that the two agree.
--
-- Only the entries needed are read.
module Umbral.Sequences
  ( -- * Running terms on sequences
    MomentDict,
    momentDict,
    transform,
    transformA,
    closedMoments,

    -- * Moments and cumulants
    cumulants,
    cumulantsByComposition,
    fromCumulants,
    factorialMoments,
    sumOfIid,
    compoundPoisson,

    -- * Counting labelled structures
    connected,
    fromConnected,
    partitionsWithBlocks,
    bellSeq,
    stirling2,
    stirling1,

    -- * Lagrange inversion
    compositionalInverse,

    -- * Bernoulli numbers
    bernoulliSeq,
  )
where

import Algebra.Binomial
import Algebra.Polynomial
import Control.Monad.Fresh
import Data.Memo (memoSeq)
import Data.Stream (Stream)
import Data.Stream qualified as S
import Umbral.Auxiliary
import Umbral.Language
import Umbral.Moment
import Umbral.Name

-- | The moment dictionary with scalars @k@ and one old umbra, named @()@.
type MomentDict k = Umbral Fresh k (Name () k) (Poly (Name () k) k)

-- | The moment dictionary whose old umbra has the given moments.
momentDict :: (Ring k) => Stream k -> MomentDict k
momentDict xs = momentModel (\() i -> S.index xs i)

-- | The moments of the umbra a term builds from an umbra with the given
-- moments.
transform :: (Ring k) => (MomentDict k -> Name () k -> Fresh (Name () k)) -> Stream k -> Stream k
transform t = transformA (\d u -> inj d <$> t d u)

-- | The moments @E[pⁱ]@ of the polynomial a term builds from an umbra with the
-- given moments.
transformA :: (Ring k) => (MomentDict k -> Name () k -> Fresh (Poly (Name () k) k)) -> Stream k -> Stream k
transformA t xs = runFresh $ do
  p <- t d (Old ())
  return (S.generate (\i -> eval d (p .^ i)))
  where
    d = momentDict xs

-- | The moments of the umbra a closed term builds. The old umbra is not used,
-- so its moments are immaterial.
closedMoments :: (Ring k) => (MomentDict k -> Fresh (Name () k)) -> Stream k
closedMoments t = transform (\d _ -> t d) (S.repeat zero)

-- | The cumulants @κ₁, κ₂, …@ (from entry 1 on), by the recursive
-- moment-cumulant formula @κₙ = aₙ - Σ_{k<n} C(n-1, k-1) κₖ aₙ₋ₖ@. It counts a
-- structure on @n@ points by the component of the first point, and takes
-- @O(n)@ products per entry. The result is that of 'cumulantsByComposition'.
-- For example the cumulants of the Poisson law are all equal to its mean.
cumulants :: (Ring k) => Stream k -> Stream k
cumulants xs = S.generate kappa
  where
    a = memoSeq (S.index xs)
    kappa = memoSeq go
    go 0 = one
    go n = a n .-. sumR [binomial (n - 1) (j - 1) *. (kappa j .*. a (n - j)) | j <- [1 .. n - 1]]

-- | The cumulants as the moments of the cumulant umbra @χ.α@: the term of
-- "Umbral.Auxiliary", run in the moment model. It takes @O(n²)@ products per
-- entry, since it builds the partial Bell polynomials.
cumulantsByComposition :: (Ring k) => Stream k -> Stream k
cumulantsByComposition = transform cumulant

-- | The moments with the given cumulants: the moments of @β.κ@, with @β@ the
-- Bell umbra. Inverse to 'cumulants'.
fromCumulants :: (Ring k) => Stream k -> Stream k
fromCumulants = transform $ \d u -> do
  b <- bellUmbra d
  compose d b u

-- | The factorial moments @E[(α)ⱼ] = E[α(α-1)⋯(α-j+1)]@.
factorialMoments :: (Ring k) => Stream k -> Stream k
factorialMoments xs = S.generate (eval d . fallingFactorial (inj d (Old ())))
  where
    d = momentDict xs

-- | The moments of the sum of @n@ independent copies: @n.α@.
sumOfIid :: (Ring k) => Natural -> Stream k -> Stream k
sumOfIid n = transformA (`dotSymbolic` n)

-- | The moments of a random sum @X₁ + ⋯ + X_N@ with @N@ Poisson of mean @λ@:
-- the composition with the Poisson umbra.
compoundPoisson :: (Ring k) => k -> Stream k -> Stream k
compoundPoisson lam = transform $ \d u -> do
  p <- poisson d lam
  compose d p u

-- | Connected structures from all structures, by the exponential formula: if
-- @aₙ@ counts the structures on @n@ labelled points that split uniquely into
-- connected components, the connected ones are counted by the cumulants. For
-- example @connected (S.generate (\n -> 2 ^ ((n * n - n) `div` 2)))@ counts the
-- connected labeled graphs (OEIS A001187).
connected :: (Ring k) => Stream k -> Stream k
connected = cumulants

-- | All structures from the connected ones: the inverse of 'connected'.
fromConnected :: (Ring k) => Stream k -> Stream k
fromConnected = fromCumulants

-- | The number of partitions of an @n@-set into blocks whose sizes satisfy the
-- predicate: @β.α@, with @α@ the indicator of the allowed sizes. Blocks of size
-- 1 or 2 give the involutions (OEIS A000085).
partitionsWithBlocks :: (Natural -> Bool) -> Stream Integer
partitionsWithBlocks ok = closedMoments $ \d -> do
  b <- bellUmbra d
  a <- mk d (\n -> if ok n then one else zero)
  compose d b a

-- | The Bell numbers @1, 1, 2, 5, 15, …@ (OEIS A000110), the moments of the Bell
-- umbra.
bellSeq :: (Ring k) => Stream k
bellSeq = closedMoments bellUmbra

-- | The Stirling numbers of the second kind, @S(n,k) = B_{n,k}(1, 1, …)@.
stirling2 :: Natural -> Natural -> Integer
stirling2 = flip table
  where
    table = bell (const 1)

-- | The unsigned Stirling numbers of the first kind,
-- @c(n,k) = B_{n,k}(0!, 1!, 2!, …)@.
stirling1 :: Natural -> Natural -> Integer
stirling1 = flip table
  where
    table = bell (\i -> product [1 .. toInteger i - 1])

-- | **Lagrange inversion.** For moments with @a₁ = 1@, the moments of the
-- compositional inverse umbra: if @F(t) = Σ_{n ≥ 1} aₙ tⁿ/n!@ then the result
-- @g@ has @G(F(t)) = t@ with @G(t) = Σ_{n ≥ 1} gₙ tⁿ/n!@. For example the
-- inverse of @t e⁻ᵗ@ counts the rooted labelled trees, @nⁿ⁻¹@.
compositionalInverse :: (Ring k) => Stream k -> Stream k
compositionalInverse = transform inverse

-- | The Bernoulli numbers with @B₁ = -1/2@, as the moments of @-1.U@, with @U@
-- uniform on @[0, 1]@ (moments @1/(n+1)@). The dot product with @-1@ is the
-- composition with the constant umbra @-1@.
bernoulliSeq :: Stream Rational
bernoulliSeq = transform term (S.generate (\n -> 1 / fromIntegral (n + 1)))
  where
    term d u = do
      c <- constantUmbra d $ fromInt (-1)
      compose d c u
