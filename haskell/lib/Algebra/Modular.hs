{-# LANGUAGE DataKinds #-}

-- | The ring @ℤ/n@, with the modulus in the type.
module Algebra.Modular
  ( Mod,
    toMod,
    residue,
    modulus,
  )
where

import Algebra.Ring
import Data.Proxy (Proxy (..))
import GHC.TypeNats (KnownNat, Nat, natVal)
import Numeric.Natural (Natural)

-- | A residue modulo @n@, kept in @[0, n)@.
newtype Mod (n :: Nat) = Mod Natural
  deriving (Eq, Ord)

instance Show (Mod n) where
  show (Mod a) = show a

-- | The modulus.
modulus :: forall n. (KnownNat n) => Mod n -> Natural
modulus _ = natVal (Proxy :: Proxy n)

-- | The residue class of an integer.
toMod :: forall n. (KnownNat n) => Integer -> Mod n
toMod a = Mod $ fromInteger $ a `mod` toInteger (natVal (Proxy :: Proxy n))

-- | The representative in @[0, n)@.
residue :: Mod n -> Natural
residue (Mod a) = a

instance (KnownNat n) => Ring (Mod n) where
  zero = toMod 0
  one = toMod 1
  Mod a .+. Mod b = toMod (toInteger a + toInteger b)
  Mod a .*. Mod b = toMod (toInteger a * toInteger b)
  neg (Mod a) = toMod (negate (toInteger a))
