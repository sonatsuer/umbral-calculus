-- | The moment model of Rota and Taylor.
--
-- An umbra is a name, an assignment gives each name a moment sequence, and the
-- evaluation sends a monomial in distinct umbrae to the product of their
-- moments. Uncorrelation is built into 'evaluate': each name in a monomial
-- contributes the moment of its own exponent.
--
-- The umbrae of the model are the old names of the assignment together with the
-- fresh names that 'mk' allocates. A fresh name is distinct from every other,
-- so it is uncorrelated with everything already present. Its moment sequence is
-- memoised, so each moment is computed once, however often it is read.
module Umbral.Moment
  ( Assign,
    uniform,
    evaluate,
    momentModel,
  )
where

import Algebra.Polynomial
import Control.Monad.Fresh
import Data.Map.Strict qualified as Map
import Data.Memo
import Umbral.Language
import Umbral.Name

-- | An assignment: @rho n i@ is the @i@-th moment of the umbra @n@. Only
-- @i >= 1@ is consulted, since @E[α⁰] = E[1] = 1@.
type Assign name c = name -> Natural -> c

-- | Every umbra gets the same moment sequence, so all umbrae are similar.
uniform :: (Natural -> c) -> Assign name c
uniform f _ = f

-- | The evaluation: linear, and on a monomial the product of the moments of its
-- distinct umbrae.
evaluate :: (Ring c) => Assign name c -> Poly name c -> c
evaluate rho p = sumR [c .*. weight m | (m, c) <- terms p]
  where
    weight m = productR [rho n e | (n, e) <- Map.toList m]

-- | The moment model: scalars @c@, umbrae the old and fresh names, umbral
-- polynomials with coefficients in @c@, allocation in 'Fresh'.
momentModel :: (Ring c) => Assign name c -> Umbral Fresh c (Name name c) (Poly (Name name c) c)
momentModel rho =
  Umbral
    { scalar = constant,
      inj = var,
      eval = evaluate moments,
      mk = \f -> do
        i <- fresh
        return $ New i (memoSeq f)
    }
  where
    moments (Old n) = rho n
    moments (New _ f) = f
