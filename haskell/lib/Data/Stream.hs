-- | Infinite streams, as lists that are infinite by construction.
--
-- The constructor is not exported, and every way of building a stream produces
-- an infinite list, so 'index', 'head' and 'tail' are total.
module Data.Stream
  ( Stream,

    -- * Building streams
    generate,
    iterate,
    repeat,
    cons,
    prepend,

    -- * Reading streams
    index,
    head,
    tail,
    take,
    drop,
    toList,

    -- * Combining streams
    zipWith,
  )
where

import Data.List qualified as List
import Numeric.Natural (Natural)
import Prelude hiding (drop, head, iterate, repeat, tail, take, zipWith)

-- | An infinite sequence.
newtype Stream a = Stream [a]
  deriving (Functor)

-- | The stream @f 0, f 1, f 2, …@.
generate :: (Natural -> a) -> Stream a
generate f = Stream (map f [0 ..])

-- | The stream @x, f x, f (f x), …@.
iterate :: (a -> a) -> a -> Stream a
iterate f = Stream . List.iterate f

-- | The constant stream.
repeat :: a -> Stream a
repeat = Stream . List.repeat

-- | An element followed by a stream.
cons :: a -> Stream a -> Stream a
cons x (Stream xs) = Stream (x : xs)

-- | A list followed by a stream.
prepend :: [a] -> Stream a -> Stream a
prepend ys (Stream xs) = Stream (ys ++ xs)

-- | The entry at a position, counting from 0.
index :: Stream a -> Natural -> a
index (Stream xs) = List.genericIndex xs

-- | The first entry.
head :: Stream a -> a
head s = index s 0

-- | The stream without its first entry.
tail :: Stream a -> Stream a
tail (Stream xs) = Stream (List.drop 1 xs)

-- | The first @n@ entries.
take :: Natural -> Stream a -> [a]
take n (Stream xs) = List.genericTake n xs

-- | The stream without its first @n@ entries.
drop :: Natural -> Stream a -> Stream a
drop n (Stream xs) = Stream (List.genericDrop n xs)

-- | The entries, as an infinite list.
toList :: Stream a -> [a]
toList (Stream xs) = xs

-- | Combine two streams entry by entry.
zipWith :: (a -> b -> c) -> Stream a -> Stream b -> Stream c
zipWith f (Stream xs) (Stream ys) = Stream (List.zipWith f xs ys)
