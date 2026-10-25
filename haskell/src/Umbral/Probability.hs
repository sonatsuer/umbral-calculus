-- | The probability model: umbrae as random variables, the evaluation as the
-- expectation.
--
-- The umbral polynomials are polynomials in the fresh umbrae whose coefficients
-- are random variables on a finite space ("Probability.Space"). An old umbra is
-- its random variable, placed as a coefficient. A fresh umbra made by 'mk'
-- stays a formal variable with its own moments, because a moment sequence need
-- not be that of a random variable: the singleton umbra @χ@ has @E[χ] = 1@ and
-- @E[χ²] = 0@. The evaluation is the expectation of each coefficient times the
-- moments of the fresh part, which is uncorrelation of the fresh umbrae with
-- everything else.
--
-- The algebra is not a polynomial ring in the old umbrae: a Rademacher
-- variable satisfies @X² = 1@. For an independent family whose moments are
-- those of an assignment, the exact space gives every expression the value it
-- has in the moment model; a Monte Carlo space approximates it.
module Umbral.Probability (probabilityModel) where

import Algebra.Polynomial
import Control.Monad.Fresh
import Data.Map.Strict qualified as Map
import Data.Memo
import Probability.Space
import Umbral.Language
import Umbral.Name

-- | The probability model of a space.
probabilityModel ::
  (Ord name, Show name, Ring c) =>
  Space name c ->
  Umbral Fresh c (Name name c) (Poly (Name name c) (RV c))
probabilityModel space =
  Umbral
    { scalar = constant . Const,
      inj = injection,
      eval = expectation,
      mk = \f -> do
        i <- fresh
        return $ New i (memoSeq f)
    }
  where
    injection (Old n) = case column space n of
      Just x -> constant x
      Nothing -> error ("probabilityModel: no law for the umbra " ++ show n)
    injection v = var v
    expectation p = sumR [mean space c .*. weight m | (m, c) <- terms p]
    weight m = productR [f e | (New _ f, e) <- Map.toList m]
