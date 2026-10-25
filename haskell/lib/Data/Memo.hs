-- | Memoised sequences.
--
-- A sequence @Natural -> k@ is stored in a lazy infinite trie: an entry is
-- computed the first time it is read and then shared. 'memoSeq' is
-- extensionally the identity, so it changes the cost of a computation and
-- nothing else.
module Data.Memo
  ( memoSeq,
    memoSeq2,
  )
where

import Numeric.Natural (Natural)

-- | An infinite binary trie on the natural numbers: the root holds 0, the left
-- subtree the odd numbers, the right subtree the positive even ones.
data Trie a = Trie a (Trie a) (Trie a)

build :: (Natural -> a) -> Trie a
build f = Trie (f 0) (build (\n -> f (2 * n + 1))) (build (\n -> f (2 * n + 2)))

index :: Trie a -> Natural -> a
index (Trie x l r) n
  | n == 0 = x
  | odd n = index l ((n - 1) `div` 2)
  | otherwise = index r ((n - 2) `div` 2)

-- | The same sequence, with each entry computed at most once. Lookup costs
-- @O(log n)@.
memoSeq :: (Natural -> k) -> Natural -> k
memoSeq f = index t
  where
    t = build f

-- | A memoised doubly indexed sequence.
memoSeq2 :: (Natural -> Natural -> k) -> Natural -> Natural -> k
memoSeq2 f = memoSeq (memoSeq . f)
