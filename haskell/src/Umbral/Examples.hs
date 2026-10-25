{-# LANGUAGE OverloadedStrings #-}

-- | Expressions of the umbral language, and moment sequences to run them on.
--
-- Every expression below is written against the umbral dictionary and the ring
-- operations alone, so it has a polymorphic type and runs in any model:
-- numerically and symbolically in the moment model, modulo @n@, and as an
-- expectation in the probability model.
module Umbral.Examples
  ( -- * Expressions in one umbra
    Named1 (..),
    variance,
    cumulant3,
    cumulant4,
    factorialMoment,
    bernoulliDefect,
    oneUmbraExamples,

    -- * Expressions in two umbrae
    Named2 (..),
    sumMoment,
    productMoment,
    mixedMoment,
    covarianceLike,
    twoUmbraExamples,

    -- * Expressions that allocate
    NamedM1 (..),
    allocatingExamples,

    -- * Contexts for an implementation of an interface
    NamedCtxDot (..),
    dotContexts,
    NamedCtxNew (..),
    newContexts,
    NamedCtxSum (..),
    sumContexts,

    -- * Moment sequences
    bellNumbers,
    bernoulliNumbers,
    gaussianMoments,
    touchard2,
  )
where

import Data.Stream (Stream)
import Data.Stream qualified as S
import Data.Text (Text)
import Umbral.Auxiliary
import Umbral.Language

-- | An expression in one umbra, with a name for printing.
data Named1 = Named1 Text Expr1

-- | An expression in two umbrae, with a name for printing.
data Named2 = Named2 Text Expr2

-- | The variance @E[α²] - E[α]²@.
variance :: Expr1
variance d x = moment d 2 x .-. moment d 1 x .^ 2

-- | The third cumulant @a3 - 3 a1 a2 + 2 a1³@.
cumulant3 :: Expr1
cumulant3 d x = m 3 .-. 3 *. (m 1 .*. m 2) .+. 2 *. m 1 .^ 3
  where
    m i = moment d i x

-- | The fourth cumulant @a4 - 4 a1 a3 - 3 a2² + 12 a1² a2 - 6 a1⁴@.
cumulant4 :: Expr1
cumulant4 d x =
  m 4 .-. 4 *. (m 1 .*. m 3) .-. 3 *. m 2 .^ 2 .+. 12 *. (m 1 .^ 2 .*. m 2) .-. 6 *. m 1 .^ 4
  where
    m i = moment d i x

-- | The factorial moment @E[α(α-1)⋯(α-n+1)]@.
factorialMoment :: Natural -> Expr1
factorialMoment n d x = eval d (fallingFactorial (inj d x) n)

-- | @E[(α+1)ⁿ] - E[αⁿ]@. At the Bernoulli umbra it vanishes for @n >= 2@: this
-- relation is what determines the Bernoulli numbers.
bernoulliDefect :: Natural -> Expr1
bernoulliDefect n d x = eval d ((inj d x .+. one) .^ n) .-. moment d n x

-- | The one-umbra examples, for printing and testing.
oneUmbraExamples :: [Named1]
oneUmbraExamples =
  [ Named1 "E[α]" (`moment` 1),
    Named1 "E[α²]" (`moment` 2),
    Named1 "variance" variance,
    Named1 "third cumulant" cumulant3,
    Named1 "fourth cumulant" cumulant4,
    Named1 "E[α(α-1)]" (factorialMoment 2),
    Named1 "E[α(α-1)(α-2)]" (factorialMoment 3),
    Named1 "E[(α+1)³] - E[α³]" (bernoulliDefect 3)
  ]

-- | @E[(α+β)ⁿ]@, the moments of the sum of two umbrae.
sumMoment :: Natural -> Expr2
sumMoment n d x y = eval d ((inj d x .+. inj d y) .^ n)

-- | @E[αβ]@.
productMoment :: Expr2
productMoment d x y = eval d (inj d x .*. inj d y)

-- | @E[αⁱ βʲ]@. Not symmetric in the two umbrae unless they are similar.
mixedMoment :: Natural -> Natural -> Expr2
mixedMoment i j d x y = eval d (inj d x .^ i .*. inj d y .^ j)

-- | @E[α²β] - E[α]E[αβ]@: an asymmetric expression mixing evaluations.
covarianceLike :: Expr2
covarianceLike d x y = mixedMoment 2 1 d x y .-. moment d 1 x .*. productMoment d x y

-- | The two-umbra examples, for printing and testing.
twoUmbraExamples :: [Named2]
twoUmbraExamples =
  [ Named2 "E[αβ]" productMoment,
    Named2 "E[(α+β)²]" (sumMoment 2),
    Named2 "E[(α+β)³]" (sumMoment 3),
    Named2 "E[(α+β)⁴]" (sumMoment 4),
    Named2 "E[α²β]" (mixedMoment 2 1),
    Named2 "E[α³β²]" (mixedMoment 3 2),
    Named2 "E[α²β] - E[α]E[αβ]" covarianceLike
  ]

-- | An expression in one umbra that may allocate, with a name for printing.
data NamedM1 = NamedM1 Text ExprM1

-- | Expressions that allocate fresh umbrae through 'mk'.
allocatingExamples :: [NamedM1]
allocatingExamples =
  [ NamedM1 "E[(α+α′)³]" $ \d x -> do
      x' <- new d x
      return $ eval d ((inj d x .+. inj d x') .^ 3),
    NamedM1 "E[α²α′] - E[α]E[αα′]" $ \d x -> do
      x' <- new d x
      return $ eval d (inj d x .^ 2 .*. inj d x') .-. moment d 1 x .*. eval d (inj d x .*. inj d x'),
    NamedM1 "third moment of χ.α" $ \d x -> do
      c <- cumulant d x
      return $ moment d 3 c,
    NamedM1 "E[(α.α)²]" $ \d x -> do
      c <- compose d x x
      return $ moment d 2 c,
    NamedM1 "E[(α′.α)³], α′ a fresh copy" $ \d x -> do
      x' <- new d x
      c <- compose d x' x
      return $ moment d 3 c
  ]

-- | A context for an implementation of the dot product, with a name.
data NamedCtxDot = NamedCtxDot Text CtxDot

-- | Contexts that use an implementation @dot@ of @n.α@ without knowing how it
-- allocates. Each takes the same value under 'dotSymbolic' and
-- 'dotConstructed'.
dotContexts :: [NamedCtxDot]
dotContexts =
  [ NamedCtxDot "E[(3.α)⁴]" $ \d dot x -> do
      p <- dot 3 x
      return (eval d (p .^ 4)),
    NamedCtxDot "E[(2.α)²(3.α′ + α)]·E[2.α]" $ \d dot x -> do
      p <- dot 2 x
      x' <- new d x
      q <- dot 3 x'
      return (eval d (p .^ 2 .*. (q .+. inj d x)) .*. eval d p),
    NamedCtxDot "E[p²p′³], two independent 2.α" $ \d dot x -> do
      p <- dot 2 x
      p' <- dot 2 x
      return (eval d (p .^ 2 .*. p' .^ 3)),
    NamedCtxDot "third moment of (2.α).α" $ \d dot x -> do
      p <- dot 2 x
      g <- composeA d p x
      return (moment d 3 g),
    NamedCtxDot "E[(0.α + 1.α + 2)³]" $ \d dot x -> do
      p <- dot 0 x
      q <- dot 1 x
      return (eval d ((p .+. q .+. fromInt 2) .^ 3))
  ]

-- | A context for an implementation of the fresh copy, with a name.
data NamedCtxNew = NamedCtxNew Text CtxNew

-- | Contexts that use an implementation @fresh@ of the fresh copy. Each takes
-- the same value under 'new' and 'newAfterUnused'.
newContexts :: [NamedCtxNew]
newContexts =
  [ NamedCtxNew "E[(α+α′)³]" $ \d fresh x -> do
      x' <- fresh x
      return (eval d ((inj d x .+. inj d x') .^ 3)),
    NamedCtxNew "E[α′²α″]·E[α′], α″ a copy of α′" $ \d fresh x -> do
      x1 <- fresh x
      x2 <- fresh x1
      return (eval d (inj d x1 .^ 2 .*. inj d x2) .*. moment d 1 x1),
    NamedCtxNew "third moment of α′.α″" $ \d fresh x -> do
      x1 <- fresh x
      x2 <- fresh x
      g <- compose d x1 x2
      return (moment d 3 g),
    NamedCtxNew "E[(2.α′)²α]" $ \d fresh x -> do
      x1 <- fresh x
      p <- dotSymbolic d 2 x1
      return (eval d (p .^ 2 .*. inj d x))
  ]

-- | A context for an implementation of the composition of a sum, with a name.
data NamedCtxSum = NamedCtxSum Text CtxSum

-- | Contexts that use an implementation @cs@ of @(b, b′, a) ↦ (β + β′).a@. Each
-- takes the same value under 'composeSumFused' and 'composeSumSplit'.
sumContexts :: [NamedCtxSum]
sumContexts =
  [ NamedCtxSum "E[p³], p = (α′ + α″).α" $ \d cs x -> do
      p <- cs x x x
      return (eval d (p .^ 3)),
    NamedCtxSum "E[p²q]·E[p], nested arguments" $ \d cs x -> do
      b <- mk d $ \i -> fromInt (toInteger i + 1)
      p <- cs x x b
      q <- cs b x x
      return $ eval d (p .^ 2 .*. q) .*. eval d p,
    NamedCtxSum "E[(α + p)³], p = (χ.α + α′).α" $ \d cs x -> do
      c <- cumulant d x
      p <- cs c x x
      return $ eval d ((inj d x .+. p) .^ 3)
  ]

-- | The Bell numbers @1, 1, 2, 5, 15, ...@: the moments of the Bell umbra
-- (a Poisson variable of mean one), by @B(n+1) = Σ C(n,k) B(k)@.
bellNumbers :: Stream Integer
bellNumbers = S.generate bellAt
  where
    bellAt :: Natural -> Integer
    bellAt 0 = 1
    bellAt n = sum [binom (n - 1) k * S.index bellNumbers k | k <- [0 .. n - 1]]

-- | The Bernoulli numbers with @B1 = -1/2@, from
-- @Σ_{k=0}^{n} C(n+1,k) B(k) = 0@ for @n >= 1@.
bernoulliNumbers :: Stream Rational
bernoulliNumbers = S.generate bern
  where
    bern :: Natural -> Rational
    bern 0 = 1
    bern n =
      negate (sum [fromInteger (binom (n + 1) k) * S.index bernoulliNumbers k | k <- [0 .. n - 1]])
        / fromInteger (binom (n + 1) n)

-- | The moments of a standard Gaussian: @(n-1)!!@ for even @n@, zero for odd.
gaussianMoments :: Stream Integer
gaussianMoments = S.generate g
  where
    g n
      | odd n = 0
      | otherwise = product [1, 3 .. toInteger n - 1]

-- | The Touchard polynomial at 2, @Σₖ S(n,k) 2ᵏ@, computed from the Stirling
-- numbers of the second kind. It is the moment sequence of a Poisson variable
-- of mean two, so it equals @E[(β+β′)ⁿ]@ for two Bell umbrae.
touchard2 :: Natural -> Integer
touchard2 n = sum [stirling n k * 2 ^ k | k <- [0 .. n]]
  where
    stirling :: Natural -> Natural -> Integer
    stirling 0 0 = 1
    stirling _ 0 = 0
    stirling 0 _ = 0
    stirling m k = toInteger k * stirling (m - 1) k + stirling (m - 1) (k - 1)

binom :: Natural -> Natural -> Integer
binom n k
  | k > n = 0
  | otherwise = toInteger (product [n - k + 1 .. n] `div` product [1 .. k])
