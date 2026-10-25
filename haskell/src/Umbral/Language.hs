-- | The umbral language.
--
-- An expression of the umbral calculus uses the ring operations of the scalars
-- @k@ and of the umbral polynomials @a@, the inclusion of scalars, the
-- inclusion of umbrae, the evaluation, and the allocation 'mk' of a fresh umbra
-- with prescribed moments in an abstract monad @m@. The ring operations are the
-- 'Ring' instances of @k@ and @a@. The four umbral operations are not a type
-- class: they are the fields of the record 'Umbral', a dictionary that every
-- expression takes as an explicit argument, because a model depends on data
-- chosen at run time, such as a moment assignment.
--
-- Two kinds of expressions are written against it.
--
-- * 'Expr1', 'Expr2' and 'Op' do not mention @m@ in their result, so they cannot
--   allocate.
--
-- * 'ExprM1' and 'ExprM2' return in the abstract monad @m@: they may allocate,
--   but only through 'mk', and they cannot run the allocator. A context
--   ('CtxDot', 'CtxNew', 'CtxSum') receives an implementation of an interface
--   and cannot tell how that implementation allocates.
module Umbral.Language
  ( Umbral (..),
    Expr1,
    Expr2,
    Op,
    ExprM1,
    ExprM2,
    CtxDot,
    CtxNew,
    CtxSum,
    moment,

    -- * Re-exports
    module Algebra.Ring,
    Natural,
  )
where

import Algebra.Ring
import Numeric.Natural (Natural)

-- | A dictionary of the umbral operations, with allocation in the monad @m@.
data Umbral m k u a = Umbral
  { -- | a scalar is a constant polynomial
    scalar :: k -> a,
    -- | an umbra is a polynomial
    inj :: u -> a,
    -- | the evaluation
    eval :: a -> k,
    -- | a fresh umbra with the given moments; the zeroth entry is never used
    mk :: (Natural -> k) -> m u
  }

-- | A scalar-valued expression in one umbra, which cannot allocate.
type Expr1 = forall m k u a. (Ring k, Ring a) => Umbral m k u a -> u -> k

-- | A scalar-valued expression in two umbrae, which cannot allocate.
type Expr2 = forall m k u a. (Ring k, Ring a) => Umbral m k u a -> u -> u -> k

-- | An operator on the scalars.
type Op = forall m k u a. (Ring k, Ring a) => Umbral m k u a -> k -> k

-- | A scalar-valued expression in one umbra that may allocate.
type ExprM1 = forall m k u a. (Monad m, Ring k, Ring a) => Umbral m k u a -> u -> m k

-- | A scalar-valued expression in two umbrae that may allocate.
type ExprM2 = forall m k u a. (Monad m, Ring k, Ring a) => Umbral m k u a -> u -> u -> m k

-- | A context for an implementation of the dot product @n.α@.
type CtxDot = forall m k u a. (Monad m, Ring k, Ring a) => Umbral m k u a -> (Natural -> u -> m a) -> u -> m k

-- | A context for an implementation of the fresh copy @α′ ≡ α@.
type CtxNew = forall m k u a. (Monad m, Ring k, Ring a) => Umbral m k u a -> (u -> m u) -> u -> m k

-- | A context for an implementation of the composition of a sum,
-- @(b, b′, a) ↦ (β + β′).a@ with @β@, @β′@ fresh copies of @b@, @b′@.
type CtxSum = forall m k u a. (Monad m, Ring k, Ring a) => Umbral m k u a -> (u -> u -> u -> m a) -> u -> m k

-- | The @n@-th moment, @E[αⁿ]@.
moment :: (Ring a) => Umbral m k u a -> Natural -> u -> k
moment d n x = eval d (inj d x .^ n)
