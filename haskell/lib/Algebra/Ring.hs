{-# LANGUAGE DerivingVia #-}

-- | Commutative rings, with only the operations a ring has.
--
-- 'Num' is not used, because it also asks for 'abs' and 'signum', which a
-- polynomial ring does not have.
module Algebra.Ring
  ( Ring (..),
    (.-.),
    (.^),
    (*.),
    fromInt,
    sumR,
    productR,
    ViaNum (..),
  )
where

import Numeric.Natural (Natural)

-- | A commutative ring. The 'Eq' superclass lets polynomials discard zero
-- coefficients.
class (Eq r) => Ring r where
  zero :: r
  one :: r
  (.+.) :: r -> r -> r
  (.*.) :: r -> r -> r
  neg :: r -> r

infixl 6 .+.

infixl 6 .-.

infixl 7 .*.

infixl 7 *.

infixr 8 .^

-- | Subtraction.
(.-.) :: (Ring r) => r -> r -> r
x .-. y = x .+. neg y

-- | Powers, by repeated squaring.
(.^) :: (Ring r) => r -> Natural -> r
x .^ n
  | n == 0 = one
  | even n = let h = x .^ (n `div` 2) in h .*. h
  | otherwise = x .*. x .^ (n - 1)

-- | Multiplication by an integer.
(*.) :: (Ring r) => Integer -> r -> r
c *. x = fromInt c .*. x

-- | The image of an integer, by doubling: @O(log n)@ ring operations.
fromInt :: (Ring r) => Integer -> r
fromInt n
  | n < 0 = neg $ fromInt $ negate n
  | n == 0 = zero
  | even n = let h = fromInt (n `div` 2) in h .+. h
  | otherwise = fromInt (n - 1) .+. one

-- | The sum of a list.
sumR :: (Ring r) => [r] -> r
sumR = foldr (.+.) zero

-- | The product of a list.
productR :: (Ring r) => [r] -> r
productR = foldr (.*.) one

-- | The ring of a 'Num' instance, for deriving: a type whose 'Num' instance is
-- a commutative ring gets its 'Ring' instance with
-- @deriving via ViaNum T instance Ring T@.
newtype ViaNum a = ViaNum a
  deriving newtype (Eq)

instance (Eq a, Num a) => Ring (ViaNum a) where
  zero = ViaNum 0
  one = ViaNum 1
  ViaNum a .+. ViaNum b = ViaNum (a + b)
  ViaNum a .*. ViaNum b = ViaNum (a * b)
  neg (ViaNum a) = ViaNum (negate a)

deriving via ViaNum Integer instance Ring Integer

deriving via ViaNum Rational instance Ring Rational

-- | Floating point numbers. The laws hold only up to rounding.
deriving via ViaNum Double instance Ring Double
