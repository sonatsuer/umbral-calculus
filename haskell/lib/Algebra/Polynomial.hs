{-# LANGUAGE OverloadedStrings #-}

-- | Sparse multivariate polynomials over a commutative ring.
module Algebra.Polynomial
  ( Poly,
    Monomial,
    var,
    constant,
    terms,
    render,
  )
where

import Algebra.Ring
import Data.List (sortOn)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import Numeric.Natural (Natural)

-- | A monomial: each variable with a positive exponent.
type Monomial v = Map v Natural

-- | A polynomial: each monomial with a non-zero coefficient.
newtype Poly v c = Poly (Map (Monomial v) c)
  deriving (Eq, Ord)

normalize :: (Ring c) => Map (Monomial v) c -> Poly v c
normalize = Poly . Map.filter (/= zero)

-- | A constant polynomial.
constant :: (Ring c) => c -> Poly v c
constant c = normalize (Map.singleton Map.empty c)

-- | A variable.
var :: (Ring c) => v -> Poly v c
var v = Poly (Map.singleton (Map.singleton v 1) one)

-- | The monomials and their coefficients.
terms :: Poly v c -> [(Monomial v, c)]
terms (Poly m) = Map.toList m

instance (Ord v, Ring c) => Ring (Poly v c) where
  zero = Poly Map.empty
  one = constant one
  Poly p .+. Poly q = normalize (Map.unionWith (.+.) p q)
  Poly p .*. Poly q =
    normalize $
      Map.fromListWith
        (.+.)
        [ (Map.unionWith (+) m1 m2, c1 .*. c2)
        | (m1, c1) <- Map.toList p,
          (m2, c2) <- Map.toList q
        ]
  neg (Poly p) = Poly (Map.map neg p)

-- | Print a polynomial with integer coefficients, lowest total degree first.
render :: (v -> Text) -> Poly v Integer -> Text
render showVar p = case sortOn (degree . fst) (terms p) of
  [] -> "0"
  (t : ts) -> T.concat (first t : map rest ts)
  where
    degree = sum . Map.elems
    first (m, c)
      | c < 0 = "-" <> body m (negate c)
      | otherwise = body m c
    rest (m, c)
      | c < 0 = " - " <> body m (negate c)
      | otherwise = " + " <> body m c
    body m c
      | Map.null m = tshow c
      | c == 1 = mono m
      | otherwise = tshow c <> "*" <> mono m
    mono m = T.intercalate "*" [power v e | (v, e) <- Map.toList m]
    power v 1 = showVar v
    power v e = showVar v <> "^" <> tshow e
    tshow :: (Show s) => s -> Text
    tshow = T.pack . show
