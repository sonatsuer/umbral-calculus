-- | Binomial coefficients, from a memoised Pascal triangle.
module Algebra.Binomial
  ( binomial,
  )
where

import Data.Memo (memoSeq2)
import Numeric.Natural (Natural)

-- | The binomial coefficient @C(n, k)@, zero for @k > n@. The triangle is
-- shared between all calls, so each entry is computed once, by one addition.
binomial :: Natural -> Natural -> Integer
binomial = memoSeq2 pascal
  where
    pascal n k
      | k > n = 0
      | k == 0 || k == n = 1
      | otherwise = binomial (n - 1) (k - 1) + binomial (n - 1) k
