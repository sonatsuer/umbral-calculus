-- | Umbrae as names.
--
-- An umbra is either an old name, whose moments come from an assignment, or a
-- fresh name made by 'Umbral.Language.mk', which carries its own moment sequence.
-- Carrying the moments in the name keeps the evaluation pure: the set of
-- allocated umbrae is implicit in the names themselves.
module Umbral.Name (Name (..)) where

import Numeric.Natural (Natural)

-- | An umbra: an old name, or a fresh one with a tag and its moment sequence.
data Name n c = Old n | New Natural (Natural -> c)

-- | Equality and order look at the name or the tag only; they cannot be
-- derived, because the moment sequence is a function.
instance (Eq n) => Eq (Name n c) where
  Old a == Old b = a == b
  New i _ == New j _ = i == j
  _ == _ = False

instance (Ord n) => Ord (Name n c) where
  compare (Old a) (Old b) = compare a b
  compare (Old _) (New _ _) = LT
  compare (New _ _) (Old _) = GT
  compare (New i _) (New j _) = compare i j
