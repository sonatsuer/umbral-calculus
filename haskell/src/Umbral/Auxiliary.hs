-- | Rota and Taylor's auxiliary umbrae, as terms of the language.
--
-- Every function here uses the umbral dictionary and the ring operations and
-- nothing else, and allocates only through 'mk'. None of them is a primitive:
-- the fresh copy, the dot product, the composition, the singleton umbra, the
-- cumulant umbra and the compositional inverse are all written in the language.
--
-- Functions on moment sequences alone need only the ring of scalars. Sequences
-- are memoised ("Data.Memo"), which no expression can observe.
module Umbral.Auxiliary
  ( -- * The fresh copy and the dot product
    new,
    dotConstructed,
    shift,
    conv,
    delta,
    dotMoments,
    dotSymbolic,

    -- * Partial Bell polynomials and composition
    cons,
    bellStep,
    bell,
    fallingFactorial,
    sumTo,
    composeMoments,
    composeMomentsA,
    compose,
    composeA,
    singletonMoments,
    singleton,
    cumulant,

    -- * The composition of a sum
    newAfterUnused,
    fusedComposition,
    splitComposition,
    onFreshCopies,
    composeSumFused,
    composeSumSplit,

    -- * The compositional inverse
    inverseStep,
    inverseMoments,
    inverse,

    -- * Umbrae with given moments
    constantUmbra,
    poisson,
    bellUmbra,
  )
where

import Algebra.Binomial
import Data.Memo
import Data.Stream qualified as S
import Umbral.Language

-- * The fresh copy and the dot product

-- | @new u@: a fresh umbra similar to @u@, @α′ ≡ α@.
new :: (Ring a) => Umbral m k u a -> u -> m u
new d u = mk d (\n -> moment d n u)

-- | The dot product @n.α@, by construction:
-- @α₁ ← new u; …; αₙ ← new u; return (α₁ + ⋯ + αₙ)@.
dotConstructed :: (Monad m, Ring a) => Umbral m k u a -> Natural -> u -> m a
dotConstructed d n u = go n
  where
    go 0 = return zero
    go i = do
      p <- go (i - 1)
      g <- new d u
      return (p .+. inj d g)

-- | The shift @(Sx)ᵢ = xᵢ₊₁@.
shift :: (Natural -> k) -> Natural -> k
shift x i = x (i + 1)

-- | The binomial convolution @(x ⋆ y)ⱼ = Σᵢ C(j,i) xᵢ y_{j-i}@: the moments of
-- a sum of two uncorrelated umbrae.
conv :: (Ring k) => (Natural -> k) -> (Natural -> k) -> Natural -> k
conv x y j = sumR [binomial j i *. (x i .*. y (j - i)) | i <- [0 .. j]]

-- | @[j = 0]@: the moments of the umbra @0@.
delta :: (Ring k) => Natural -> k
delta j = if j == 0 then one else zero

-- | The moments of @n.α@ from the moments @a@ of @α@: the @n@-fold binomial
-- convolution of @a@. Partially applied to @a@, the table is shared between
-- all @n@.
dotMoments :: (Ring k) => (Natural -> k) -> Natural -> Natural -> k
dotMoments a = S.index table
  where
    table = S.iterate (\s -> memoSeq (conv s a)) (memoSeq delta)

-- | The dot product @n.α@, symbolically: one fresh umbra with the moments of
-- @n.α@.
dotSymbolic :: (Monad m, Ring k, Ring a) => Umbral m k u a -> Natural -> u -> m a
dotSymbolic d n u = inj d <$> mk d (dotMoments (\i -> moment d i u) n)

-- * Partial Bell polynomials and composition

-- | @c@ followed by @s@.
cons :: k -> (Natural -> k) -> Natural -> k
cons c _ 0 = c
cons _ s j = s (j - 1)

-- | One step of the Bell recurrence, @B ↦ (0, (B ⋆ Sa)₀, (B ⋆ Sa)₁, …)@.
bellStep :: (Ring k) => (Natural -> k) -> (Natural -> k) -> Natural -> k
bellStep a b = cons zero $ conv b (shift a)

-- | The partial Bell polynomials: @bell a j m = B_{m,j}(a)@. Partially applied
-- to @a@, the table is shared between all @j@ and @m@.
bell :: (Ring k) => (Natural -> k) -> Natural -> Natural -> k
bell a = S.index table
  where
    table = S.iterate (memoSeq . bellStep a) (memoSeq delta)

-- | The falling factorial @p(p - 1)⋯(p - j + 1)@.
fallingFactorial :: (Ring a) => a -> Natural -> a
fallingFactorial p j = productR [p .-. fromInt i | i <- [0 .. toInteger j - 1]]

-- | @f 0 + ⋯ + f (m - 1)@.
sumTo :: (Ring k) => Natural -> (Natural -> k) -> k
sumTo m f = if m == 0 then zero else sumR (map f [0 .. m - 1])

-- | The moments of the composition @β.α@: @Σ_{j ≤ m} E[(β)ⱼ] B_{m,j}(a)@, with
-- @a@ the moments of @α@.
composeMoments :: (Ring k, Ring a) => Umbral m k u a -> u -> u -> Natural -> k
composeMoments d b = composeMomentsA d (inj d b)

-- | The moments of @p.α@ for a polynomial @p@: @Σ_{j ≤ m} E[(p)ⱼ] B_{m,j}(a)@.
-- They need only the factorial moments of @p@, so @p@ may be a sum of umbrae.
composeMomentsA :: (Ring k, Ring a) => Umbral m k u a -> a -> u -> Natural -> k
composeMomentsA d p x = memoSeq (\m -> sumTo (m + 1) (\j -> fm j .*. b j m))
  where
    falling = snd <$> S.iterate (\(i, q) -> (i + 1, q .*. (p .-. fromInt i))) (0, one)
    fm = memoSeq $ eval d . S.index falling
    b = bell $ memoSeq (\i -> moment d i x)

-- | The composition @β.α@, as a fresh umbra.
compose :: (Ring k, Ring a) => Umbral m k u a -> u -> u -> m u
compose d b x = mk d (composeMoments d b x)

-- | The composition @p.α@ for a polynomial @p@, as a fresh umbra.
composeA :: (Ring k, Ring a) => Umbral m k u a -> a -> u -> m u
composeA d p x = mk d (composeMomentsA d p x)

-- | The moments of the singleton umbra, @(0, 1, 0, 0, …)@.
singletonMoments :: (Ring k) => Natural -> k
singletonMoments j = if j == 1 then one else zero

-- | The singleton umbra @χ@.
singleton :: (Ring k) => Umbral m k u a -> m u
singleton d = mk d singletonMoments

-- | The cumulant umbra @χ.α@ of Di Nardo and Senato: @c ← χ; c.α@. Its moments
-- are the cumulants of @α@.
cumulant :: (Monad m, Ring k, Ring a) => Umbral m k u a -> u -> m u
cumulant d u = do
  c <- singleton d
  compose d c u

-- * The composition of a sum

-- | @_ ← mk 0; new u@: a fresh copy, allocated after an unused umbra. No
-- context distinguishes it from 'new': only the moments of an auxiliary umbra
-- are observable.
newAfterUnused :: (Monad m, Ring k, Ring a) => Umbral m k u a -> u -> m u
newAfterUnused d u = do
  _ <- mk d (const zero)
  new d u

-- | @λβ β′ a. γ ← (β + β′).a; return γ@.
fusedComposition :: (Monad m, Ring k, Ring a) => Umbral m k u a -> u -> u -> u -> m a
fusedComposition d b b' a = inj d <$> composeA d (inj d b .+. inj d b') a

-- | @λβ β′ a. δ ← β.a; δ′ ← β′.a; return (δ + δ′)@.
splitComposition :: (Monad m, Ring k, Ring a) => Umbral m k u a -> u -> u -> u -> m a
splitComposition d b b' a = do
  delta1 <- compose d b a
  delta2 <- compose d b' a
  return (inj d delta1 .+. inj d delta2)

-- | @λb b′ a. β ← new b; β′ ← new b′; cont β β′ a@: run a continuation on two
-- fresh copies, which are uncorrelated even when @b = b′@.
onFreshCopies :: (Monad m, Ring a) => Umbral m k u a -> (u -> u -> u -> m a) -> u -> u -> u -> m a
onFreshCopies d cont b b' a = do
  beta <- new d b
  beta' <- new d b'
  cont beta beta' a

-- | The composition of a sum of fresh copies, fused:
-- @β ← new b; β′ ← new b′; γ ← (β + β′).a; return γ@.
composeSumFused :: (Monad m, Ring k, Ring a) => Umbral m k u a -> u -> u -> u -> m a
composeSumFused d = onFreshCopies d (fusedComposition d)

-- | The same, split by distributivity:
-- @β ← new b; β′ ← new b′; δ ← β.a; δ′ ← β′.a; return (δ + δ′)@. No context
-- distinguishes it from 'composeSumFused'.
composeSumSplit :: (Monad m, Ring k, Ring a) => Umbral m k u a -> u -> u -> u -> m a
composeSumSplit d = onFreshCopies d (splitComposition d)

-- * The compositional inverse

-- | One step of the inversion at the moments @a@:
-- @s ↦ (j ↦ χⱼ - Σ_{i ≤ j} sᵢ B_{j,i}(a) + sⱼ)@. When @a₁ = 1@ the diagonal
-- @B_{j,j}(a)@ is 1, so the step changes the @j@-th entry only through the
-- entries below it. Partially applied to @a@, the Bell table is shared between
-- all steps.
inverseStep :: (Ring k) => (Natural -> k) -> (Natural -> k) -> Natural -> k
inverseStep a = step
  where
    b = bell a
    step s = memoSeq $ \j ->
      singletonMoments j .-. sumTo (j + 1) (\i -> s i .*. b i j) .+. s j

-- | The moments of the compositional inverse: the @m@-th moment is the @m@-th
-- entry of the @m@-th iterate of 'inverseStep' from the moments of @χ@. The
-- iterates are memoised, so the @m@-th moment costs @O(m³)@ ring operations.
inverseMoments :: (Ring k, Ring a) => Umbral m k u a -> u -> Natural -> k
inverseMoments d u = memoSeq (\m -> S.index iterates m m)
  where
    iterates = S.iterate (inverseStep (memoSeq (\i -> moment d i u))) singletonMoments

-- | The compositional inverse @α⁽⁻¹⁾@ of Di Nardo and Senato, for an umbra with
-- @E[α] = 1@: a fresh umbra with @α⁽⁻¹⁾.β.α ≡ α.β.α⁽⁻¹⁾ ≡ χ@, where @β@ is the
-- Bell umbra. In generating functions, @g[f(t) - 1] = f[g(t) - 1] = 1 + t@:
-- Lagrange inversion.
inverse :: (Ring k, Ring a) => Umbral m k u a -> u -> m u
inverse d u = mk d (inverseMoments d u)

-- * Umbrae with given moments

-- | A fresh umbra with moments @c, c², c³, …@: the constant @c@ as an umbra.
-- Composing with it is the dot product: @c̄.α ≡ c.α@, for every scalar @c@.
constantUmbra :: (Ring k) => Umbral m k u a -> k -> m u
constantUmbra d c = mk d (c .^)

-- | The Poisson umbra of parameter @λ@: its moments are the Touchard
-- polynomials @Σⱼ S(n,j) λʲ = Σⱼ B_{n,j}(1, 1, …) λʲ@. With @λ = 1@ it is the
-- Bell umbra.
poisson :: (Ring k) => Umbral m k u a -> k -> m u
poisson d lam = mk d (\n -> sumTo (n + 1) (\j -> b j n .*. lam .^ j))
  where
    b = bell (const one)

-- | The Bell umbra @β@: Poisson of parameter 1, moments the Bell numbers.
bellUmbra :: (Ring k) => Umbral m k u a -> m u
bellUmbra d = poisson d one
