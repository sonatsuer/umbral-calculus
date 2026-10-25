{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Checks of the umbral language, without test libraries.
--
-- * The substitution principle for every example expression: at an assignment
--   where two umbrae have the same moments, the expression takes the same value
--   at both; with allocation as well.
-- * The auxiliary umbrae: what each term allocates and the moments it gives.
-- * Representation independence: contexts cannot tell apart two
--   implementations of an interface, although the implementations allocate
--   different numbers of umbrae.
-- * The library: the compositional inverse, memoisation, the modular and
--   probability models, "Umbral.Sequences", and the worked computations of
--   "Umbral.Showcase".
module Main (main) where

import Algebra.Modular
import Algebra.Polynomial
import Control.Monad (unless)
import Control.Monad.Fresh
import Data.List (genericIndex, genericLength)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy (..))
import Data.Stream (Stream)
import Data.Stream qualified as S
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as T
import GHC.TypeNats (KnownNat)
import Probability.Random (exponential, normal)
import Probability.Space
import System.Exit (exitFailure)
import Umbral.Auxiliary
import Umbral.Examples
import Umbral.Language
import Umbral.Moment
import Umbral.Name
import Umbral.Probability
import Umbral.Sequences
import Umbral.Showcase
import Umbral.Symbolic

data Check = Check Text Bool

tshow :: (Show s) => s -> Text
tshow = T.pack . show

-- * Models

-- | The moment model over 'Integer', over 'Rational', and the symbolic one.
type ModelZ = Umbral Fresh Integer (Name Char Integer) (Poly (Name Char Integer) Integer)

type ModelQ = Umbral Fresh Rational (Name Char Rational) (Poly (Name Char Rational) Rational)

type ModelS = Umbral Fresh Formula (Name Char Formula) (Poly (Name Char Formula) Formula)

-- | Moments taken from a stream; the umbra @'c'@ gets other moments, so that it
-- is not similar to @'a'@ and @'b'@.
similarAB :: Stream Integer -> Stream Integer -> Assign Char Integer
similarAB xs ys n i = if n == 'c' then S.index ys i else S.index xs i

sequences :: [(Text, Stream Integer)]
sequences =
  [ ("Bell", bellNumbers),
    ("Gaussian", gaussianMoments),
    ("1,2,3,...", S.generate toInteger),
    ("squares", S.generate (\n -> toInteger n ^ (2 :: Natural)))
  ]

-- | The models most checks run in: @a@ and @b@ similar, @c@ not.
models :: [(Text, ModelZ)]
models = [(label, momentModel (similarAB xs (fmap (* 3) xs))) | (label, xs) <- sequences]

-- | Moments as a function, with the zeroth entry 1, from a finite list padded
-- with zeros.
listMoments :: (Num c) => [c] -> Natural -> c
listMoments xs = streamMoments (S.prepend xs (S.repeat 0))

-- | Moments as a function, with the zeroth entry 1.
streamMoments :: (Num c) => Stream c -> Natural -> c
streamMoments xs i = if i == 0 then 1 else S.index xs i

-- | The moments @1..n@ of a fresh umbra, and how many umbrae the computation
-- allocated.
momentsAlloc :: (Ring a) => Umbral Fresh k u a -> Natural -> Fresh u -> ([k], Natural)
momentsAlloc d n c = countFresh (c >>= \g -> return [moment d i g | i <- [1 .. n]])

-- | The partial Bell polynomials by the other recurrence,
-- @B_{n,j} = Σ_{i=1}^{n-j+1} C(n-1,i-1) aᵢ B_{n-i,j-1}@: a reference for 'bell'.
partialBellRef :: (Ring k) => (Natural -> k) -> Natural -> Natural -> k
partialBellRef a = go
  where
    go 0 0 = one
    go 0 _ = zero
    go _ 0 = zero
    go n j = sumR [binomN (n - 1) (i - 1) *. a i .*. go (n - i) (j - 1) | i <- [1 .. n], i + j <= n + 1]

-- | Newton's forward differences of @q@ at 0: @Δᵏq(0)@, so that
-- @q(t) = Σₖ Δᵏq(0) C(t,k)@ for a polynomial @q@ of degree at most @m@.
forwardDiffs :: Natural -> (Natural -> Rational) -> [Rational]
forwardDiffs m q = [sum [fromInteger ((-1) ^ (k - i) * binomN k i) * q i | i <- [0 .. k]] | k <- [0 .. m]]

binomN :: Natural -> Natural -> Integer
binomN n k
  | k > n = 0
  | otherwise = toInteger (product [n - k + 1 .. n] `div` product [1 .. k])

-- * Expressions that do not allocate

substitution :: [Check]
substitution =
  concat [oneUmbra, twoUmbrae, symbolicOne]
  where
    oneUmbra =
      [ Check ("substitution, " <> name <> ", " <> label) (e d (Old 'a') == e d (Old 'b'))
      | (label, d) <- models,
        Named1 name e <- oneUmbraExamples
      ]
    twoUmbrae =
      [ Check ("substitution, " <> name <> ", " <> label) (e d (Old 'a') (Old 'c') == e d (Old 'b') (Old 'c'))
      | (label, d) <- models,
        Named2 name e <- twoUmbraExamples
      ]
    symbolicOne =
      [ Check ("substitution, symbolic, " <> name) (e symbolicSimilar (Old 'a') == e symbolicSimilar (Old 'b'))
      | Named1 name e <- oneUmbraExamples
      ]

-- | Similar umbrae are exchangeable: @t a b == t b a@ when @a@ and @b@ are
-- similar. With a non-similar umbra the asymmetric examples are not symmetric,
-- so the check is not vacuous.
exchangeability :: [Check]
exchangeability =
  concat [numeric, symbolicTwo, notVacuous]
  where
    numeric =
      [ Check ("exchangeable, " <> name <> ", " <> label) (e d (Old 'a') (Old 'b') == e d (Old 'b') (Old 'a'))
      | (label, d) <- models,
        Named2 name e <- twoUmbraExamples
      ]
    symbolicTwo =
      [ Check ("exchangeable, symbolic, " <> name) (e symbolicSimilar (Old 'a') (Old 'b') == e symbolicSimilar (Old 'b') (Old 'a'))
      | Named2 name e <- twoUmbraExamples
      ]
    notVacuous =
      [Check "not exchangeable without similarity: E[α²β]" (mixedMoment 2 1 symbolic (Old 'a') (Old 'b') /= mixedMoment 2 1 symbolic (Old 'b') (Old 'a'))]

-- | @E[(α+β)ⁿ] = Σ C(n,i) aᵢ b_{n-i}@ for uncorrelated umbrae.
binomialConvolution :: [Check]
binomialConvolution =
  [ Check ("binomial convolution, n = " <> tshow n) (sumMoment n d (Old 'a') (Old 'c') == expected n)
  | n <- [0 .. 6]
  ]
  where
    xs = bellNumbers
    ys = fmap (* 3) bellNumbers
    d = momentModel (similarAB xs ys)
    expected n = sum [binomN n i * streamMoments xs i * streamMoments ys (n - i) | i <- [0 .. n]]

bernoulli :: [Check]
bernoulli =
  [ Check ("Bernoulli relation, n = " <> tshow n) (bernoulliDefect n d (Old 'a') == 0)
  | n <- [2 .. 10]
  ]
  where
    d = momentModel (uniform (S.index bernoulliNumbers) :: Assign Char Rational)

cumulantFormulas :: [Check]
cumulantFormulas =
  [ Check "Bell cumulants are 1" (map ($ Old 'a') [variance bellD, cumulant3 bellD, cumulant4 bellD] == [1, 1, 1]),
    Check "Gaussian cumulants are 1, 0, 0" (map ($ Old 'a') [variance gauss, cumulant3 gauss, cumulant4 gauss] == [1, 0, 0]),
    Check "two Bell umbrae sum to Touchard T_n(2)" ([sumMoment n bellD (Old 'a') (Old 'b') | n <- [1 .. 8]] == map touchard2 [1 .. 8])
  ]
  where
    bellD = momentModel (uniform (S.index bellNumbers))
    gauss = momentModel (uniform (S.index gaussianMoments))

uncorrelation :: [Check]
uncorrelation =
  [ Check "E[ab] = a1*b1" $ showFormula (productMoment symbolic (Old 'a') (Old 'b')) == "a1*b1",
    Check "E[aa] = a2" $ showFormula (productMoment symbolic (Old 'a') (Old 'a')) == "a2",
    Check "variance = a2 - a1^2" $ showFormula (variance symbolic (Old 'a')) == "a2 - a1^2"
  ]

-- * Expressions that allocate

-- | The substitution principle with allocation, numerically and symbolically;
-- and the fresh tags used do not matter.
substitutionWithAllocation :: [Check]
substitutionWithAllocation =
  concat [numeric, symbolicOne, freshTags]
  where
    numeric =
      [ Check ("substitution with allocation, " <> name <> ", " <> label) (runFresh (e d (Old 'a')) == runFresh (e d (Old 'b')))
      | (label, d) <- models,
        NamedM1 name e <- allocatingExamples
      ]
    symbolicOne =
      [ Check ("substitution with allocation, symbolic, " <> name) (runFresh (e symbolicSimilar (Old 'a')) == runFresh (e symbolicSimilar (Old 'b')))
      | NamedM1 name e <- allocatingExamples
      ]
    freshTags =
      [ Check ("fresh tags do not matter, " <> name <> ", " <> label) (runFreshFrom 0 (e d (Old 'a')) == runFreshFrom 1000 (e d (Old 'a')))
      | (label, d) <- models,
        NamedM1 name e <- allocatingExamples
      ]

-- ** The auxiliary umbrae

-- | @new u@ allocates one umbra, with the moments of @u@.
freshCopy :: [Check]
freshCopy =
  [ Check ("new: one fresh umbra with the moments of its argument, " <> label) (momentsAlloc d 6 (new d (Old 'c')) == ([moment d i (Old 'c') | i <- [1 .. 6]], 1))
  | (label, d) <- models
  ]

-- | The constructed dot product allocates @n@ umbrae, each similar to @u@, and
-- returns a polynomial with the moments of @n.α@.
dotConstructedChecks :: [Check]
dotConstructedChecks =
  [Check ("constructed dot product: n similar copies, moments of n.α, n = " <> tshow n) (ok n) | n <- [0 .. 4]]
  where
    d = symbolic
    a i = moment d i (Old 'a')
    ok n =
      let ((vals, similar), count) = countFresh $ do
            p <- dotConstructed d n (Old 'a')
            return
              ( [eval d (p .^ j) | j <- [0 .. 5]],
                and [f i == a i | (m, _) <- terms p, (New _ f, _) <- Map.toList m, i <- [1 .. 5]]
              )
       in vals == [dotMoments a n j | j <- [0 .. 5]] && similar && count == n

-- | The symbolic dot product allocates one umbra, with the moments of @n.α@.
dotSymbolicChecks :: [Check]
dotSymbolicChecks =
  [ Check ("symbolic dot product: one fresh umbra with the moments of n.α, n = " <> tshow n) (countFresh (dotSymbolic d n (Old 'a') >>= \p -> return [eval d (p .^ j) | j <- [0 .. 5]]) == ([dotMoments a n j | j <- [0 .. 5]], 1))
  | n <- [0 .. 4]
  ]
  where
    d = symbolic
    a i = moment d i (Old 'a')

-- | The moments of @n@ uncorrelated copies are the @n@-fold convolution.
dotMomentsCopies :: [Check]
dotMomentsCopies =
  [ Check ("moments of n.α are those of n uncorrelated copies, n = " <> tshow n <> ", " <> label) (and [eval d (sumOf n .^ j) == dotMoments a n j | j <- [0 .. 6]])
  | (label, xs) <- sequences,
    let d = momentModel (uniform (streamMoments xs)) :: ModelZ,
    let a = streamMoments xs,
    n <- [0 .. 4]
  ]
  where
    sumOf :: Natural -> Poly (Name Char Integer) Integer
    sumOf n = sumR [var (Old c) | c <- take (fromIntegral n) "abcd"]

-- | @Σⱼ (n)ⱼ B_{m,j}(a) = E[(n.α)ᵐ]@; and the partial Bell polynomials satisfy
-- the other recurrence.
dotMomentsBell :: [Check]
dotMomentsBell =
  concat [identity, otherRecurrence]
  where
    identity =
      [ Check ("dot-moment identity, " <> label) (and [sum [falling n j * bell a j m | j <- [0 .. m]] == dotMoments a n m | n <- [0 .. 5], m <- [0 .. 7]])
      | (label, xs) <- sequences,
        let a = streamMoments xs
      ]
    otherRecurrence =
      [Check "partial Bell polynomials by the other recurrence" (and [bell sa j m == partialBellRef sa m j | m <- [0 .. 6], j <- [0 .. 6]])]
    falling :: Natural -> Natural -> Integer
    falling n j = product [toInteger n - i | i <- [0 .. toInteger j - 1]]
    sa i = var (Sym 'a' i) :: Formula

-- | @β.α@ allocates one umbra, with moments @Σⱼ E[(β)ⱼ] B_{m,j}(a)@ (with the
-- reference Bell polynomials).
composition :: [Check]
composition =
  [ Check "composition: one fresh umbra with Σⱼ E[(β)ⱼ] B_{m,j}(a), symbolically" (momentsAlloc d 5 (compose d (Old 'b') (Old 'a')) == (map expected [1 .. 5], 1)),
    Check "composition: Bell.unity is Bell" (runFresh unityMoments == S.take 8 (S.drop 1 bellNumbers))
  ]
  where
    d = symbolic
    a i = moment d i (Old 'a')
    expected m = sumR [factorialMoment j d (Old 'b') .*. partialBellRef a m j | j <- [0 .. m]]
    bu :: ModelZ
    bu = momentModel (\n i -> if n == 'u' then 1 else streamMoments bellNumbers i)
    unityMoments = do
      g <- compose bu (Old 'b') (Old 'u')
      return [moment bu k g | k <- [1 .. 8]]

-- | The moments of @β.α@ are @E[q_m(β)]@, where @q_m(n) = E[(n.α)ᵐ]@ at every
-- natural number @n@. Over ℚ, @q_m@ is interpolated by Newton's forward
-- differences.
compositionMoments :: [Check]
compositionMoments =
  [ Check ("composition is Rota and Taylor's, E[q_m(β)], m = " <> tshow m) (composeMoments d (Old 'b') (Old 'a') m == expected m)
  | m <- [1 .. 6]
  ]
  where
    d = momentModel (\n i -> if n == 'a' then listMoments [1, 1, 3, -2, 5, 0, 7] i else listMoments [1, 2, 2, 5, -1, 4, 3] i) :: ModelQ
    a i = moment d i (Old 'a')
    q m n = dotMoments a n m
    expected m =
      sum [c * factorialMoment k d (Old 'b') / fromInteger (product [1 .. toInteger k]) | (k, c) <- zip [0 :: Natural ..] (forwardDiffs m (q m))]

-- | @n̄.α ≡ n.α@.
compositionConstant :: [Check]
compositionConstant =
  [Check "composition with the constant n is the dot product n.α" (and [constantVsDot n | n <- [0 .. 3]])]
  where
    dz :: ModelZ
    dz = momentModel (uniform (streamMoments bellNumbers))
    constantVsDot n = runFresh $ do
      c <- constantUmbra dz (fromInt (toInteger n))
      g <- compose dz c (Old 'a')
      p <- dotConstructed dz n (Old 'a')
      return ([moment dz k g | k <- [1 .. 6]] == [eval dz (p .^ k) | k <- [1 .. 6]])

-- | @χ.α@ allocates two umbrae, and its moments are the linear coefficients of
-- @n ↦ E[(n.α)ᵐ]@, the cumulants.
cumulantUmbra :: [Check]
cumulantUmbra =
  [ Check "cumulant umbra: two allocations, moments the linear coefficients of q_m" (momentsAlloc d 6 (cumulant d (Old 'a')) == (map linear [1 .. 6], 2)),
    Check "cumulant umbra: Bell cumulants are all 1" (cumulantsOf bellNumbers == replicate 6 1),
    Check "cumulant umbra: Gaussian cumulants are 0, 1, 0, 0, ..." (cumulantsOf gaussianMoments == [0, 1, 0, 0, 0, 0]),
    Check "cumulant umbra: symbolic, agrees with the cumulant formulas" symbolicAgrees
  ]
  where
    d = momentModel (uniform (listMoments [1, 2, -1, 3, 0, 4, 2])) :: ModelQ
    a i = moment d i (Old 'a')
    -- the linear coefficient of q(t) = Σₖ cₖ C(t,k) is Σ_{k ≥ 1} cₖ (-1)^{k-1}/k
    linear m = sum [c * (-1) ^ (k - 1) / fromIntegral k | (k, c) <- zip [0 :: Natural ..] (forwardDiffs m (\n -> dotMoments a n m)), k >= 1]
    cumulantsOf xs = runFresh $ do
      let dz = momentModel (uniform (streamMoments xs)) :: ModelZ
      c <- cumulant dz (Old 'a')
      return [moment dz k c | k <- [1 .. 6]]
    symbolicAgrees = runFresh $ do
      c <- cumulant symbolic (Old 'a')
      return
        ( [moment symbolic k c | k <- [2, 3, 4]]
            == [variance symbolic (Old 'a'), cumulant3 symbolic (Old 'a'), cumulant4 symbolic (Old 'a')]
        )

-- | With a Bell umbra outside, @β.α@ is compound Poisson: its moments are the
-- complete Bell polynomials of the moments of @α@, computed here independently
-- by @Y_{n+1} = Σᵢ C(n,i) a_{i+1} Y_{n-i}@.
compoundPoissonChecks :: [Check]
compoundPoissonChecks =
  [Check ("compound Poisson, k = " <> tshow k) (got k == completeBell k) | k <- [1 .. 6]]
  where
    d :: ModelS
    d = momentModel (\n i -> if n == 'b' then fromInt (streamMoments bellNumbers i) else var (Sym n i))
    got k = runFresh $ do
      g <- compose d (Old 'b') (Old 'a')
      return (moment d k g)
    a i = var (Sym 'a' i) :: Formula
    completeBell :: Natural -> Formula
    completeBell 0 = one
    completeBell n = sumR [binomN (n - 1) i *. a (i + 1) .*. completeBell (n - 1 - i) | i <- [0 .. n - 1]]

-- ** Representation independence

-- | Every context takes the same value under 'new' and 'newAfterUnused'.
freshCopyIndependence :: [Check]
freshCopyIndependence =
  concat [numeric, symbolicCtx, notVacuous]
  where
    numeric =
      [ Check ("representation independence of the fresh copy, " <> name <> ", " <> label) (runFresh (c d (new d) (Old 'a')) == runFresh (c d (newAfterUnused d) (Old 'a')))
      | (label, d) <- models,
        NamedCtxNew name c <- newContexts
      ]
    symbolicCtx =
      [ Check ("representation independence of the fresh copy, symbolic, " <> name) (runFresh (c symbolic (new symbolic) (Old 'a')) == runFresh (c symbolic (newAfterUnused symbolic) (Old 'a')))
      | NamedCtxNew name c <- newContexts
      ]
    notVacuous =
      [ Check
          "not vacuous: a copy with shifted moments is seen by some context"
          (or [runFresh (c symbolic shifted (Old 'a')) /= runFresh (c symbolic (new symbolic) (Old 'a')) | NamedCtxNew _ c <- newContexts])
      ]
    shifted u = mk symbolic (\i -> moment symbolic (i + 1) u)

-- | Every context takes the same value under the symbolic and the constructed
-- dot product, numerically and symbolically.
dotProductIndependence :: [Check]
dotProductIndependence =
  concat [numeric, symbolicCtx, notVacuous]
  where
    numeric =
      [ Check ("representation independence of the dot product, " <> name <> ", " <> label) (runFresh (c d (dotSymbolic d) (Old 'a')) == runFresh (c d (dotConstructed d) (Old 'a')))
      | (label, d) <- models,
        NamedCtxDot name c <- dotContexts
      ]
    symbolicCtx =
      [ Check ("representation independence of the dot product, symbolic, " <> name) (runFresh (c symbolic (dotSymbolic symbolic) (Old 'a')) == runFresh (c symbolic (dotConstructed symbolic) (Old 'a')))
      | NamedCtxDot name c <- dotContexts
      ]
    notVacuous =
      [ Check
          "not vacuous: the scaling n·α is not n.α, and some context sees it"
          (or [runFresh (c symbolic scaled (Old 'a')) /= runFresh (c symbolic (dotSymbolic symbolic) (Old 'a')) | NamedCtxDot _ c <- dotContexts]),
        Check
          "not vacuous: an allocating expression separates non-similar umbrae"
          (or [runFresh (e symbolic (Old 'a')) /= runFresh (e symbolic (Old 'c')) | NamedM1 _ e <- allocatingExamples])
      ]
    scaled n u = return (toInteger n *. inj symbolic u)

-- | The composition transform takes binomial convolution to binomial
-- convolution, on integer sequences; and @(β + β′).α ≡ β.α + β′.α@ for
-- uncorrelated @β@, @β′@, symbolically.
distributivity :: [Check]
distributivity =
  concat [convolutions, sums]
  where
    convolutions =
      [ Check ("distributivity: compT a (x ⋆ y) = compT a x ⋆ compT a y, m = " <> tshow m) (compT (conv x y) m == conv (compT x) (compT y) m)
      | m <- [0 .. 7]
      ]
    sums = [Check ("distributivity: (β + β′).α ≡ β.α + β′.α, k = " <> tshow k) (lhs k == rhs k) | k <- [1 .. 4]]
    a = genericIndex [1, 2, -1, 3, 0, 5, -2, 4 :: Integer]
    x = genericIndex [3, 1, 4, 1, -5, 9, 2, 6 :: Integer]
    y = genericIndex [2, 7, 1, -8, 2, 8, 1, 8 :: Integer]
    b = bell a
    compT s m = sum [s j * b j m | j <- [0 .. m]]
    d = symbolic
    i = inj d
    lhs k = runFresh $ do
      g <- composeA d (i (Old 'b') .+. i (Old 'c')) (Old 'a')
      return (moment d k g)
    rhs k = runFresh $ do
      g1 <- compose d (Old 'b') (Old 'a')
      g2 <- compose d (Old 'c') (Old 'a')
      return (eval d ((i g1 .+. i g2) .^ k))

-- | Every context takes the same value under the fused and the split
-- composition of a sum.
compositionOfSumIndependence :: [Check]
compositionOfSumIndependence =
  concat [numeric, symbolicCtx]
  where
    numeric =
      [ Check ("representation independence of the composition of a sum, " <> name <> ", " <> label) (runFresh (c d (composeSumFused d) (Old 'a')) == runFresh (c d (composeSumSplit d) (Old 'a')))
      | (label, d) <- models,
        NamedCtxSum name c <- sumContexts
      ]
    symbolicCtx =
      [ Check ("representation independence of the composition of a sum, symbolic, " <> name) (runFresh (c symbolic (composeSumFused symbolic) (Old 'a')) == runFresh (c symbolic (composeSumSplit symbolic) (Old 'a')))
      | NamedCtxSum name c <- sumContexts
      ]

-- | The Sheffer identity and the binomial type at umbral arguments,
-- symbolically.
shefferUmbral :: [Check]
shefferUmbral =
  concat [sheffer, binomialType]
  where
    sheffer = [Check ("Sheffer identity at umbral arguments, n = " <> tshow n) (lhs n == rhs n) | n <- [0 .. 4]]
    binomialType = [Check ("binomial type at umbral arguments, n = " <> tshow n) (lhsB n == rhsB n) | n <- [0 .. 4]]
    d = symbolic
    i = inj d
    alpha = i (Old 'a')
    setup = do
      beta <- new d (Old 'b')
      beta' <- new d (Old 'd')
      delta1 <- composeA d (i beta .+. i beta') (Old 'c')
      d1 <- compose d beta (Old 'c')
      d2 <- compose d beta' (Old 'c')
      return (i delta1, i d1, i d2)
    e = eval d
    binomSum n f = sumR [binomN n k *. f k | k <- [0 .. n]]
    lhs n = runFresh $ do
      (delta1, _, _) <- setup
      return $ e ((alpha .+. delta1) .^ n)
    rhs n = runFresh $ do
      (_, d1, d2) <- setup
      return $ binomSum n (\k -> e ((alpha .+. d1) .^ k) .*. e (d2 .^ (n - k)))
    lhsB n = runFresh $ do
      (delta1, _, _) <- setup
      return (e (delta1 .^ n))
    rhsB n = runFresh $ do
      (_, d1, d2) <- setup
      return $ binomSum n (\k -> e (d1 .^ k) .*. e (d2 .^ (n - k)))

-- | The two dot products allocate 1 and @n@ umbrae, which differ for @n ≠ 1@;
-- and the count is invariant under mapping the result.
allocationCount :: [Check]
allocationCount =
  concat [differ, others]
  where
    differ =
      [ Check ("allocation count: 1 for the symbolic and n for the constructed dot product, n = " <> tshow n) (count dotSymbolic n == 1 && count dotConstructed n == n)
      | n <- [0, 2, 3, 5]
      ]
    others =
      [ Check "allocation count: equal at n = 1" $ count dotSymbolic 1 == count dotConstructed 1,
        Check "allocation count: invariant under mapping the result" $ and [snd (countFresh (fmap (eval d) (dot d 3 (Old 'a')))) == snd (countFresh (dot d 3 (Old 'a'))) | dot <- [dotSymbolic, dotConstructed]]
      ]
    d = symbolic
    count :: (ModelS -> Natural -> Name Char Formula -> Fresh (Poly (Name Char Formula) Formula)) -> Natural -> Natural
    count dot n = snd $ countFresh $ dot d n (Old 'a') >>= \p -> return (eval d (p .^ 2))

-- * The library

-- | The compositional inverse: its allocation and moments, @α⁽⁻¹⁾.β.α ≡ χ@ and
-- @α.β.α⁽⁻¹⁾ ≡ χ@, uniqueness, Lagrange's formula, and Cayley's formula.
inverseChecks :: [Check]
inverseChecks =
  concat [allocation, leftSide, rightSide, others]
  where
    allocation =
      [ Check ("compositional inverse: one fresh umbra, " <> label) (momentsAlloc d 6 (inverse d (Old 'a')) == ([inverseMoments d (Old 'a') i | i <- [1 .. 6]], 1))
      | (label, d) <- modelsA1
      ]
    leftSide =
      [ Check ("compositional inverse: α⁽⁻¹⁾.β.α ≡ χ, " <> label) (sides d True)
      | (label, d) <- modelsA1
      ]
    rightSide =
      [ Check ("compositional inverse: α.β.α⁽⁻¹⁾ ≡ χ, " <> label) (sides d False)
      | (label, d) <- modelsA1
      ]
    others =
      [ Check "compositional inverse: both sides, symbolically, with a1 = 1" (sides symbolicA1 True && sides symbolicA1 False),
        Check "compositional inverse: the direct recursion gives the same moments" (and [inverseMoments dq (Old 'a') m == direct m | m <- [1 .. 7]]),
        Check "Lagrange inversion: gₙ = (n-1)! [tⁿ⁻¹] (t/F(t))ⁿ" (and [inverseMoments dq (Old 'a') n == lagrange n | n <- [1 .. 7]]),
        Check "Cayley: the inverse of t e⁻ᵗ counts rooted trees, nⁿ⁻¹" (S.take 10 (S.drop 1 (compositionalInverse cayley)) == [toInteger n ^ (n - 1) | n <- [1 .. 10 :: Natural]])
      ]
    cayley = S.cons 1 (S.generate (\i -> if even i then toInteger i + 1 else negate (toInteger i + 1)))
    modelsA1 =
      [ ("Bell", momentModel (uniform (streamMoments bellNumbers)) :: ModelZ),
        ("t e⁻ᵗ", momentModel (uniform (S.index cayley)))
      ]
    symbolicA1 :: ModelS
    symbolicA1 = momentModel (\n i -> if i == 1 then one else var (Sym n i))
    -- α⁽⁻¹⁾.β.α (True) or α.β.α⁽⁻¹⁾ (False), with β the Bell umbra
    sides :: (Ring k) => Umbral Fresh k (Name Char k) (Poly (Name Char k) k) -> Bool -> Bool
    sides d left = runFresh $ do
      g <- inverse d (Old 'a')
      b <- bellUmbra d
      let (outer, inner) = if left then (g, Old 'a') else (Old 'a', g)
      ob <- compose d outer b
      h <- compose d ob inner
      return ([moment d k h | k <- [1 .. 6]] == [singletonMoments k | k <- [1 .. 6]])
    as = [1, 1, 3, -2, 5, 0, 7, 2] :: [Rational]
    dq = momentModel (uniform (listMoments as)) :: ModelQ
    a = listMoments as
    direct :: Natural -> Rational
    direct m = (if m == 1 then 1 else 0) - sum [direct j * partialBellRef a m j | j <- [1 .. m - 1]]
    -- truncated power series over ℚ, as lists of coefficients
    lagrange n =
      let fOverT = [a (k + 1) / fromInteger (product [1 .. toInteger k + 1]) | k <- [0 .. n]]
       in fromInteger (product [1 .. toInteger n - 1]) * genericIndex (seriesPow (seriesInv fOverT) n) (n - 1)
    len :: [b] -> Natural
    len = genericLength
    seriesMul xs ys = [sum [genericIndex xs i * genericIndex ys (k - i) | i <- [0 .. k]] | k <- [0 .. len xs - 1]]
    seriesInv [] = []
    seriesInv xs@(x0 : _) =
      let ys = [if k == 0 then 1 / x0 else negate (sum [genericIndex xs i * genericIndex ys (k - i) | i <- [1 .. k]]) / x0 | k <- [0 .. len xs - 1]]
       in ys
    seriesPow xs n = iterate (`seriesMul` xs) (1 : replicate (length xs - 1) 0) `genericIndex` n

-- | Large computations, which need memoisation.
memoisation :: [Check]
memoisation =
  [ Check "memoisation: connected labelled graphs up to 25 vertices" (S.take 25 (S.drop 1 (closedMoments connectedGraphsTerm)) == S.take 25 (S.drop 1 connectedGraphsRef)),
    Check "memoisation: the Bell umbra's cumulants up to 40 are all 1" (S.take 40 (S.drop 1 (cumulants (bellSeq :: Stream Integer))) == replicate 40 1)
  ]

-- | Naturality along @ℤ → ℤ/n@: an expression over @Mod n@ is the reduction of
-- the same expression over 'Integer'. Touchard's congruence
-- @B_{n+p} ≡ Bₙ + B_{n+1} (mod p)@.
modular :: [Check]
modular =
  concat [naturality, naturalityAllocating, congruences]
  where
    naturality =
      [ Check ("modular: naturality along ℤ → ℤ/97, " <> name) (e dm (Old 'a') == toMod (e dz (Old 'a')))
      | Named1 name e <- oneUmbraExamples
      ]
    naturalityAllocating =
      [ Check ("modular: naturality along ℤ → ℤ/97, with allocation, " <> name) (runFresh (e dm (Old 'a')) == toMod (runFresh (e dz (Old 'a'))))
      | NamedM1 name e <- allocatingExamples
      ]
    congruences =
      [ Check "Touchard's congruence mod 2" (touchard (Proxy :: Proxy 2)),
        Check "Touchard's congruence mod 3" (touchard (Proxy :: Proxy 3)),
        Check "Touchard's congruence mod 5" (touchard (Proxy :: Proxy 5)),
        Check "Touchard's congruence mod 7" (touchard (Proxy :: Proxy 7))
      ]
    dz = momentModel (uniform (streamMoments bellNumbers)) :: ModelZ
    dm = momentModel (uniform (toMod . streamMoments bellNumbers)) :: Umbral Fresh (Mod 97) (Name Char (Mod 97)) (Poly (Name Char (Mod 97)) (Mod 97))
    touchard :: forall p. (KnownNat p) => Proxy p -> Bool
    touchard _ =
      let bs = bellSeq :: Stream (Mod p)
          p = modulus (zero :: Mod p)
       in and [S.index bs (n + p) == S.index bs n .+. S.index bs (n + 1) | n <- [0 .. 12]]

-- | Exactly, under the product of finite laws over ℚ, every expression takes
-- its value in the moment model of the laws' moments. Rademacher: @X² = 1@ in
-- the algebra. Monte Carlo: close to the exact values.
probability :: [Check]
probability =
  concat [oneUmbra, twoUmbrae, allocating, dotProduct, others]
  where
    oneUmbra =
      [ Check ("probabilistic soundness, " <> name <> " at " <> T.singleton x) (e dp (Old x) == e dm (Old x))
      | Named1 name e <- oneUmbraExamples,
        x <- "abc"
      ]
    twoUmbrae =
      [ Check ("probabilistic soundness, " <> name <> " at " <> T.pack [x, y]) (e dp (Old x) (Old y) == e dm (Old x) (Old y))
      | Named2 name e <- twoUmbraExamples,
        (x, y) <- [('a', 'b'), ('b', 'c'), ('c', 'a')]
      ]
    allocating =
      [ Check ("probabilistic soundness with allocation, " <> name) (runFresh (e dp (Old 'a')) == runFresh (e dm (Old 'a')))
      | NamedM1 name e <- allocatingExamples
      ]
    dotProduct =
      [ Check ("probabilistic soundness with allocation, dot-product context " <> name) (runFresh (c dp (dotConstructed dp) (Old 'a')) == runFresh (c dm (dotSymbolic dm) (Old 'a')))
      | NamedCtxDot name c <- dotContexts
      ]
    others =
      [ Check "Rademacher: X² = 1 in the algebra, which is not a polynomial ring" (inj dp (Old 'b') .*. inj dp (Old 'b') == one),
        Check "Rademacher: E[X⁴] = 1, but E[X X′] = 0 for a fresh copy" (moment dp 4 (Old 'b') == 1 && runFresh (new dp (Old 'b') >>= \b' -> return (eval dp (inj dp (Old 'b') .*. inj dp b'))) == 0),
        Check "random Faulhaber: the moment model at the die's moments gives the probability model's value" ([runFresh (faulhaberAt m dm (inj dm (Old 'a'))) | m <- [0 .. 8]] == map randomFaulhaberTerm [0 .. 8]),
        Check "Monte Carlo: E[N²] ≈ 1 for a standard normal N" (close 0.03 (moment mc 2 (Old 'n')) 1),
        Check "Monte Carlo: the variance of Exp(1) ≈ 1" (close 0.05 (variance mc (Old 'x')) 1),
        Check "Monte Carlo: E[(N + X)²] ≈ 3" (close 0.1 (sumMoment 2 mc (Old 'n') (Old 'x')) 3),
        Check "Monte Carlo: the third cumulant of Exp(1) ≈ 2, through the cumulant umbra" (close 0.3 (runFresh (cumulant mc (Old 'x') >>= \c -> return (moment mc 3 c))) 2),
        Check "Monte Carlo: deterministic given the seed" (moment mc 3 (Old 'x') == moment (probabilityModel (monteCarlo 100000 7 laws)) 3 (Old 'x'))
      ]
    die = [(fromInteger j, 1 / 6) | j <- [1 .. 6]]
    rad = [(-1, 1 / 2), (1, 1 / 2)]
    ber = [(0, 2 / 3), (1, 1 / 3)]
    lawsQ = [('a', die), ('b', rad), ('c', ber)] :: [(Char, [(Rational, Rational)])]
    dp = probabilityModel (exact lawsQ)
    lawMoment n i = sum [p * v ^ i | (v, p) <- fromMaybe [] (lookup n lawsQ)]
    dm = momentModel lawMoment :: ModelQ
    laws = [('n', normal 0 1), ('x', exponential 1)]
    mc = probabilityModel (monteCarlo 100000 7 laws)
    close :: Double -> Double -> Double -> Bool
    close tol est expected = abs (est - expected) <= tol

-- | "Umbral.Sequences".
sequenceChecks :: [Check]
sequenceChecks =
  [ Check "bellSeq: the Bell numbers" (S.take 12 bellSeq == S.take 12 bellNumbers),
    Check "cumulants agrees with cumulantsByComposition (Bell numbers)" (S.take 15 (cumulants bellNumbers) == S.take 15 (cumulantsByComposition bellNumbers)),
    Check "cumulants agrees with cumulantsByComposition (Gaussian moments)" (S.take 15 (cumulants gaussianMoments) == S.take 15 (cumulantsByComposition gaussianMoments)),
    Check "cumulants agrees with cumulantsByComposition (labelled graphs)" (S.take 20 (cumulants graphCounts) == S.take 20 (cumulantsByComposition graphCounts)),
    Check "fromCumulants inverts cumulants (Bell numbers)" (S.take 10 (fromCumulants (cumulants bellNumbers)) == S.take 10 bellNumbers),
    Check "fromCumulants inverts cumulants (Gaussian moments)" (S.take 10 (fromCumulants (cumulants gaussianMoments)) == S.take 10 gaussianMoments),
    Check "partitionsWithBlocks (≤ 2): the involutions" (S.take 10 (partitionsWithBlocks (<= 2)) == [1, 1, 2, 4, 10, 26, 76, 232, 764, 2620]),
    Check "the compositional inverse of the inverse is the umbra" (S.take 9 (compositionalInverse (compositionalInverse bellNumbers)) == S.take 9 bellNumbers),
    Check "compoundPoisson 1 of the unity umbra: the Bell numbers" (S.take 10 (compoundPoisson 1 (S.repeat 1)) == S.take 10 bellNumbers),
    Check "sumOfIid 2 of the Bell umbra: Touchard T_n(2)" (S.take 8 (S.drop 1 (sumOfIid 2 bellNumbers)) == map touchard2 [1 .. 8]),
    Check "factorialMoments of the Bell umbra are all 1" (S.take 10 (factorialMoments bellNumbers) == replicate 10 1),
    Check "bernoulliSeq: the Bernoulli numbers" (S.take 15 bernoulliSeq == S.take 15 bernoulliNumbers)
  ]
  where
    graphCounts = S.generate (\n -> 2 ^ ((n * n - n) `div` 2)) :: Stream Integer

-- | "Umbral.Showcase": every worked computation agrees with its reference, and
-- the pitfall is a pitfall.
showcaseChecks :: [Check]
showcaseChecks =
  concat [agreement, pitfall]
  where
    agreement = [Check ("showcase: " <> title s) (agrees s) | s <- showcases]
    pitfall =
      [ Check
          "Blissard's pitfall differs from Euler's sum from n = 2 on"
          $ and (zipWith (/=) (drop 2 (S.take 11 eulerRef)) (drop 2 (S.take 11 pitfallRef)))
      ]

main :: IO ()
main = do
  let failed = [name | Check name ok <- checks, not ok]
  mapM_ (T.putStrLn . ("FAILED: " <>)) failed
  T.putStrLn (tshow (length checks - length failed) <> " of " <> tshow (length checks) <> " checks passed")
  unless (null failed) exitFailure
  where
    checks =
      concat
        [ withoutAllocation,
          substitutionWithAllocation,
          auxiliaryUmbrae,
          independence,
          library
        ]
    withoutAllocation =
      concat
        [ substitution,
          exchangeability,
          binomialConvolution,
          bernoulli,
          cumulantFormulas,
          uncorrelation
        ]
    auxiliaryUmbrae =
      concat
        [ freshCopy,
          dotConstructedChecks,
          dotSymbolicChecks,
          dotMomentsCopies,
          dotMomentsBell,
          composition,
          compositionMoments,
          compositionConstant,
          cumulantUmbra,
          compoundPoissonChecks
        ]
    independence =
      concat
        [ freshCopyIndependence,
          dotProductIndependence,
          distributivity,
          compositionOfSumIndependence,
          shefferUmbral,
          allocationCount
        ]
    library =
      concat
        [ inverseChecks,
          memoisation,
          modular,
          probability,
          sequenceChecks,
          showcaseChecks
        ]
