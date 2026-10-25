{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

-- | Worked umbral computations.
--
-- Each entry is a classical result computed by a term of the language, written
-- in Rota and Taylor's notation through the dictionary and the auxiliary umbrae
-- of "Umbral.Auxiliary": fresh copies, dot products, compositions, cumulant
-- umbrae and compositional inverses. Each comes with a reference computation
-- that does not go through the umbral code (brute-force enumeration, or a
-- classical recurrence), and the test suite checks that the two agree.
module Umbral.Showcase
  ( Showcase (..),
    agrees,
    showcases,
    printShowcase,

    -- * The terms
    graphs,
    connectedGraphsTerm,
    involutionsTerm,
    derangementsTerm,
    blocksTerm,
    rootedTreesTerm,
    forestsTerm,
    bernoulliTerm,
    eulerTerm,
    pitfallTerm,
    faulhaberAt,
    faulhaberTerm,
    randomFaulhaberTerm,
    hermiteTerm,
    touchardTerm,
    cumulantsInMomentsTerm,

    -- * References
    connectedGraphsRef,
    cumulantsInMomentsRef,
    eulerRef,
    pitfallRef,
  )
where

import Algebra.Modular
import Algebra.Polynomial
import Control.Monad.Fresh
import Data.List (genericLength, permutations)
import Data.Ratio (denominator, numerator)
import Data.Stream (Stream)
import Data.Stream qualified as S
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as T
import Probability.Space (exact)
import Umbral.Auxiliary
import Umbral.Examples (bernoulliNumbers)
import Umbral.Language
import Umbral.Name
import Umbral.Probability
import Umbral.Sequences
import Umbral.Symbolic

-- | A worked computation: a title, what it computes and from which term, a
-- printer, the values the term computes, and the reference values.
data Showcase = forall v. (Eq v) => Showcase
  { title :: Text,
    about :: Text,
    display :: v -> Text,
    computed :: [v],
    reference :: [v]
  }

-- | The term and the reference agree.
agrees :: Showcase -> Bool
agrees (Showcase _ _ _ c r) = c == r

printShowcase :: Showcase -> IO ()
printShowcase Showcase {..} = do
  T.putStrLn $ "TITLE: " <> title
  T.putStrLn $ "ABOUT: " <> about
  T.putStrLn $ "COMPUTED:\n" <> displayList computed
  T.putStrLn $ "REFERENCE:\n" <> displayList reference
  T.putStrLn ""
  where
    displayList xs = T.concat [display x <> ", " | x <- xs]

-- | All the worked computations.
showcases :: [Showcase]
showcases =
  [ Showcase
      "Connected labelled graphs (OEIS A001187)"
      "The cumulant umbra χ.γ of the umbra γ with E[γⁿ] = 2^C(n,2), the number of labelled graphs: \
      \the exponential formula, as a composition with the singleton umbra."
      tshow
      (S.take 14 (S.drop 1 (closedMoments connectedGraphsTerm)))
      (S.take 14 (S.drop 1 connectedGraphsRef)),
    Showcase
      "Involutions (OEIS A000085)"
      "β.α with β the Bell umbra and E[αⁿ] = 1 for n ≤ 2, 0 after: set partitions into blocks of size 1 or 2."
      tshow
      (S.take 14 (closedMoments involutionsTerm))
      (S.take 14 involutionsRef),
    Showcase
      "Derangements (OEIS A000166)"
      "β.α with E[αⁿ] = (n-1)! for n ≥ 2 and 0 for n = 1: permutations made of cycles of length at least 2. \
      \Reference: counting the permutations without fixed points."
      showI
      (S.take 9 (closedMoments derangementsTerm))
      [genericLength [p | p <- permutations [1 .. n], and (zipWith (/=) p [1 .. n])] | n <- [0 .. 8 :: Natural]],
    Showcase
      "Set partitions into blocks of size 2 or 3"
      "β.α with α the indicator of the sizes {2, 3}. Reference: enumerating all set partitions."
      showI
      (S.take 10 (closedMoments blocksTerm))
      [genericLength [q | q <- setPartitions [1 .. n], all ((`elem` [2, 3]) . length) q] | n <- [0 .. 9 :: Natural]],
    Showcase
      "Stirling numbers of the second kind"
      "S(n,k) = B_{n,k}(1, 1, 1, …), the partial Bell polynomials of the term bellT, rows n = 0..8."
      tshow
      [[stirling2 n k | k <- [0 .. n]] | n <- [0 .. 8]]
      [[s2 n k | k <- [0 .. n]] | n <- [0 .. 8]],
    Showcase
      "Stirling numbers of the first kind (unsigned)"
      "c(n,k) = B_{n,k}(0!, 1!, 2!, …), rows n = 0..8."
      tshow
      [[stirling1 n k | k <- [0 .. n]] | n <- [0 .. 8]]
      [[s1 n k | k <- [0 .. n]] | n <- [0 .. 8]],
    Showcase
      "Rooted labelled trees, nⁿ⁻¹ (OEIS A000169)"
      "The compositional inverse of the umbra with moments n(-1)ⁿ⁻¹, whose generating function is t e⁻ᵗ: \
      \Lagrange inversion as a term."
      tshow
      (S.take 12 (S.drop 1 (closedMoments rootedTreesTerm)))
      [toInteger n ^ (n - 1) | n <- [1 .. 12 :: Natural]],
    Showcase
      "Rooted labelled forests, (n+1)ⁿ⁻¹ (OEIS A000272, shifted)"
      "β.τ, with τ the rooted-tree umbra above: a forest is a set of trees."
      tshow
      (S.take 12 (closedMoments forestsTerm))
      (1 : [toInteger (n + 1) ^ (n - 1) | n <- [1 .. 11 :: Natural]]),
    Showcase
      "Moments of the sum of three fair dice"
      "E[(3.δ)ᵏ], k = 0..6, with δ uniform on 1..6, by the symbolic dot product. Reference: the 216 outcomes."
      showQ
      (S.take 7 (closedMoments diceTerm))
      [sum [fromIntegral (a + b + c) ^ k | a <- [1 .. 6 :: Natural], b <- [1 .. 6], c <- [1 .. 6]] / 216 | k <- [0 .. 6 :: Natural]],
    Showcase
      "A random sum: Poisson(2) many exponential variables"
      "The composition of the Poisson umbra of mean 2 with the umbra of moments n!. \
      \Reference: the complete Bell polynomials of 2·n!."
      tshow
      (S.take 10 (closedMoments compoundTerm))
      (S.take 10 compoundRef),
    Showcase
      "Bernoulli numbers"
      "-1.U, with U uniform on [0, 1]: the dot product with -1, as a composition with the constant umbra -1. \
      \Reference: the recurrence Σ_{k ≤ n} C(n+1,k) B_k = 0."
      showQ
      (S.take 13 (closedMoments bernoulliTerm))
      (S.take 13 bernoulliNumbers),
    Showcase
      "Euler's identity for products of Bernoulli numbers"
      "E[(ι + ι′)ⁿ] with ι′ ← new ι, which is Σ C(n,k) B_k B_{n-k}, against -n B_{n-1} - (n-1) B_n."
      showQ
      (S.take 11 (closedMoments eulerTerm))
      (S.take 11 eulerRef),
    Showcase
      "Blissard's pitfall"
      "The same expression without a fresh copy, E[(ι + ι)ⁿ], is 2ⁿ Bₙ, not Euler's sum."
      showQ
      (S.take 11 (closedMoments pitfallTerm))
      (S.take 11 pitfallRef),
    Showcase
      "Faulhaber: Σ_{j<n} j³"
      "(E[(ι + n)⁴] - E[ι⁴]) / 4, with ι the Bernoulli umbra, for n = 1..10."
      showQ
      [faulhaberTerm 3 n | n <- [1 .. 10]]
      [sum [fromIntegral j ^ (3 :: Natural) | j <- [0 .. n - 1]] | n <- [1 .. 10 :: Natural]],
    Showcase
      "Faulhaber with a random upper limit: E[Σ_{j<N} jᵐ]"
      "(E[(ι + N)ᵐ⁺¹] - E[ιᵐ⁺¹]) / (m + 1) in the probability model, m = 0..8, with N a fair die on the exact \
      \space and ι the Bernoulli umbra, which is no random variable (E[ι⁴] = -1/30). Reference: the six \
      \outcomes of N."
      showQ
      [randomFaulhaberTerm m | m <- [0 .. 8]]
      [sum [sum [fromIntegral j ^ m | j <- [0 .. n - 1]] | n <- [1 .. 6 :: Natural]] / 6 | m <- [0 .. 8 :: Natural]],
    Showcase
      "Hermite polynomials Heₙ(x)"
      "E[(x + ν)ⁿ] over the scalars ℤ[x], with ν the umbra of moments (-1)ⁿ⸍²(n-1)!! (i times a Gaussian; \
      \no real random variable). Reference: He_{n+1} = x Heₙ - n He_{n-1}."
      (render T.singleton)
      [hermiteTerm n | n <- [0 .. 7]]
      (S.take 8 hermiteRef),
    Showcase
      "Touchard polynomials Tₙ(x)"
      "The moments of x̄.β over ℤ[x]: the dot product x.β of the Bell umbra, as a composition with the \
      \degenerate umbra x̄. Reference: Σₖ S(n,k) xᵏ."
      (render T.singleton)
      (S.take 8 (closedMoments touchardTerm))
      [polyX [stirling2 n k | k <- [0 .. n]] | n <- [0 .. 7]],
    Showcase
      "Cumulants of the Poisson law of mean 3"
      "The cumulant umbra of the Poisson umbra: every cumulant is the mean."
      showI
      (S.take 10 (S.drop 1 (cumulants (closedMoments (`poisson` 3)))))
      (replicate 10 3),
    Showcase
      "Cumulants of the standard Gaussian law"
      "The cumulant umbra of the umbra with moments (n-1)!! for even n: 0, 1, 0, 0, …"
      tshow
      (S.take 10 (S.drop 1 (cumulants gaussian)))
      (0 : 1 : replicate 8 0),
    Showcase
      "Cumulants in terms of moments"
      "The moments of the cumulant umbra χ.α, n = 1..6, at the umbra with symbolic moments a1, a2, …: the \
      \moment-cumulant formula. Reference: the Möbius sum over the set partitions π of n points, \
      \Σ_π (-1)^{|π|-1} (|π|-1)! ∏_{B ∈ π} a_{|B|}."
      showFormula
      (S.take 6 cumulantsInMomentsTerm)
      (S.take 6 cumulantsInMomentsRef),
    Showcase
      "Connected labelled graphs on 50..60 vertices, modulo 10⁹+7"
      "The term of the first entry, run over the scalars ℤ/(10⁹+7). Reference: the same term over ℤ, \
      \reduced. That the two agree is naturality along the ring map ℤ → ℤ/(10⁹+7)."
      tshow
      (S.take 11 (S.drop 50 (closedMoments connectedGraphsTerm :: Stream (Mod 1000000007))))
      (map toMod (S.take 11 (S.drop 50 (closedMoments connectedGraphsTerm :: Stream Integer))))
  ]

-- * The terms

-- | The umbra γ with @E[γⁿ] = 2^C(n,2)@, the number of labelled graphs on @n@
-- points.
graphs :: (Ring k) => Umbral m k u a -> m u
graphs d = mk d $ \n -> fromInt 2 .^ ((n * n - n) `div` 2)

-- | @γ ← graphs; χ.γ@.
connectedGraphsTerm :: (Monad m, Ring k, Ring a) => Umbral m k u a -> m u
connectedGraphsTerm d = graphs d >>= cumulant d

-- | @β.α@, with @α@ the indicator of the sizes 1 and 2.
involutionsTerm :: (Monad m, Ring k, Ring a) => Umbral m k u a -> m u
involutionsTerm d = do
  b <- bellUmbra d
  a <- mk d (\n -> if n <= 2 then one else zero)
  compose d b a

-- | @β.α@, with @α@ the cycles of length at least 2.
derangementsTerm :: (Monad m, Ring k, Ring a) => Umbral m k u a -> m u
derangementsTerm d = do
  b <- bellUmbra d
  a <- mk d (\n -> if n < 2 then zero else fromInt (toInteger (product [1 .. n - 1])))
  compose d b a

-- | @β.α@, with @α@ the indicator of the sizes 2 and 3.
blocksTerm :: (Monad m, Ring k, Ring a) => Umbral m k u a -> m u
blocksTerm d = do
  b <- bellUmbra d
  a <- mk d (\n -> if n == 2 || n == 3 then one else zero)
  compose d b a

-- | The compositional inverse of the umbra with moments @n(-1)ⁿ⁻¹@.
rootedTreesTerm :: (Monad m, Ring k, Ring a) => Umbral m k u a -> m u
rootedTreesTerm d = do
  a <- mk d (\n -> fromInt (if odd n then toInteger n else negate (toInteger n)))
  inverse d a

-- | @β.τ@, with @τ@ the rooted trees.
forestsTerm :: (Monad m, Ring k, Ring a) => Umbral m k u a -> m u
forestsTerm d = do
  t <- rootedTreesTerm d
  b <- bellUmbra d
  compose d b t

-- | @3.δ@, with @δ@ uniform on @1..6@.
diceTerm :: MomentDict Rational -> Fresh (Name () Rational)
diceTerm d = do
  delta1 <- mk d (\k -> sum [fromIntegral j ^ k | j <- [1 .. 6 :: Natural]] / 6)
  p <- dotSymbolic d 3 delta1
  -- the moments of a polynomial, as an umbra: one more fresh umbra
  mk d (\k -> eval d (p .^ k))

-- | The Poisson umbra of mean 2, composed with the umbra of moments @n!@.
compoundTerm :: (Monad m, Ring k, Ring a) => Umbral m k u a -> m u
compoundTerm d = do
  a <- mk d (\n -> fromInt (toInteger (product [1 .. n])))
  p <- poisson d (fromInt 2)
  compose d p a

-- | The Bernoulli umbra @ι = -1.U@.
bernoulliTerm :: (Monad m, Ring a) => Umbral m Rational u a -> m u
bernoulliTerm d = do
  u <- mk d (\n -> 1 / fromIntegral (n + 1))
  c <- constantUmbra d $ fromInt (-1)
  compose d c u

-- | @ι ← bernoulli; ι′ ← new ι@, and the umbra with the moments of @ι + ι′@.
eulerTerm :: MomentDict Rational -> Fresh (Name () Rational)
eulerTerm d = do
  iota <- bernoulliTerm d
  iota' <- new d iota
  let s = inj d iota .+. inj d iota'
  mk d (\n -> eval d (s .^ n))

-- | @ι + ι@: no fresh copy.
pitfallTerm :: MomentDict Rational -> Fresh (Name () Rational)
pitfallTerm d = do
  iota <- bernoulliTerm d
  let s = inj d iota .+. inj d iota
  mk d (\n -> eval d (s .^ n))

-- | @(E[(ι + p)^{m+1}] - E[ι^{m+1}]) / (m + 1)@, with @ι@ the Bernoulli umbra.
faulhaberAt :: (Monad m, Ring a) => Natural -> Umbral m Rational u a -> a -> m Rational
faulhaberAt m d p = do
  iota <- bernoulliTerm d
  let e q = eval d (q .^ (m + 1))
  return $ (e (inj d iota .+. p) - e (inj d iota)) / fromIntegral (m + 1)

-- | @(E[(ι + n)^{m+1}] - E[ι^{m+1}]) / (m + 1)@.
faulhaberTerm :: Natural -> Natural -> Rational
faulhaberTerm m n = runFresh (faulhaberAt m dictOf0 (fromInt (toInteger n)))

-- | @(E[(ι + N)^{m+1}] - E[ι^{m+1}]) / (m + 1)@ in the probability model, with
-- @N@ a fair die.
randomFaulhaberTerm :: Natural -> Rational
randomFaulhaberTerm m = runFresh (faulhaberAt m d (inj d (Old 'N')))
  where
    d = probabilityModel (exact [('N', [(fromIntegral j, 1 / 6) | j <- [1 .. 6 :: Natural]])])

-- | @E[(x + ν)ⁿ]@ over @ℤ[x]@.
hermiteTerm :: Natural -> Poly Char Integer
hermiteTerm n = runFresh $ do
  nu <- mk d (\i -> if odd i then zero else fromInt ((-1) ^ (i `div` 2) * product [1, 3 .. toInteger i - 1]))
  return (eval d ((scalar d (var 'x') .+. inj d nu) .^ n))
  where
    d = dictOf0

-- | @x̄.β@ over @ℤ[x]@.
touchardTerm :: MomentDict (Poly Char Integer) -> Fresh (Name () (Poly Char Integer))
touchardTerm d = do
  c <- constantUmbra d (var 'x')
  b <- bellUmbra d
  compose d c b

-- | The moments of @χ.α@, from the first on, at the umbra with symbolic
-- moments @a1, a2, …@.
cumulantsInMomentsTerm :: Stream Formula
cumulantsInMomentsTerm = runFresh $ do
  c <- cumulant symbolic (Old 'a')
  return (S.generate (\i -> moment symbolic (i + 1) c))

-- * References

-- | @cₙ = 2^C(n,2) - Σ_{k=1}^{n-1} C(n-1,k-1) cₖ 2^C(n-k,2)@.
connectedGraphsRef :: Stream Integer
connectedGraphsRef = S.generate c
  where
    g n = 2 ^ ((n * n - n) `div` 2)
    c :: Natural -> Integer
    c 0 = 1
    c n = g n - sum [binomI (n - 1) (k - 1) * S.index connectedGraphsRef k * g (n - k) | k <- [1 .. n - 1]]

-- | @κₙ = Σ_π (-1)^{|π|-1} (|π|-1)! ∏_{B ∈ π} a_{|B|}@, over the set partitions
-- @π@ of @n@ points, from @n = 1@ on.
cumulantsInMomentsRef :: Stream Formula
cumulantsInMomentsRef = S.generate (\i -> kappa (i + 1))
  where
    kappa n =
      sumR [mobius (genericLength p) *. productR [var (Sym 'a' (genericLength b)) | b <- p] | p <- setPartitions [1 .. n]]
    mobius :: Integer -> Integer
    mobius k = (-1) ^ (k - 1) * product [1 .. k - 1]

involutionsRef :: Stream Integer
involutionsRef = (\(_, a, _) -> a) <$> S.iterate step (1, 1, 1)
  where
    step :: (Natural, Integer, Integer) -> (Natural, Integer, Integer)
    step (n, a, b) = (n + 1, b, b + toInteger n * a)

compoundRef :: Stream Integer
compoundRef = ys
  where
    a i = 2 * toInteger (product [1 .. i])
    ys = S.cons 1 (S.generate (\n -> sum [binomI n i * a (i + 1) * S.index ys (n - i) | i <- [0 .. n]]))

-- | @1@, then @-n B_{n-1} - (n-1) B_n@.
eulerRef :: Stream Rational
eulerRef = S.cons 1 (S.generate (\i -> negate (fromIntegral (i + 1) * b i) - fromIntegral i * b (i + 1)))
  where
    b = S.index bernoulliNumbers

-- | @2ⁿ Bₙ@.
pitfallRef :: Stream Rational
pitfallRef = S.zipWith (\n b -> 2 ^ n * b) (S.generate id) bernoulliNumbers

hermiteRef :: Stream (Poly Char Integer)
hermiteRef = (\(_, h0, _) -> h0) <$> S.iterate step (0, one, var 'x')
  where
    step :: (Natural, Poly Char Integer, Poly Char Integer) -> (Natural, Poly Char Integer, Poly Char Integer)
    step (n, h0, h1) = (n + 1, h1, var 'x' .*. h1 .-. fromInt (toInteger n + 1) .*. h0)

s2 :: Natural -> Natural -> Integer
s2 0 0 = 1
s2 _ 0 = 0
s2 0 _ = 0
s2 n k = toInteger k * s2 (n - 1) k + s2 (n - 1) (k - 1)

s1 :: Natural -> Natural -> Integer
s1 0 0 = 1
s1 _ 0 = 0
s1 0 _ = 0
s1 n k = toInteger (n - 1) * s1 (n - 1) k + s1 (n - 1) (k - 1)

-- * Helpers

gaussian :: Stream Integer
gaussian = S.generate (\n -> if odd n then 0 else product [1, 3 .. toInteger n - 1])

dictOf0 :: (Ring k) => MomentDict k
dictOf0 = momentDict (S.repeat zero)

polyX :: [Integer] -> Poly Char Integer
polyX cs = sumR [fromInt c .*. productR (replicate i (var 'x')) | (i, c) <- zip [0 ..] cs]

setPartitions :: [a] -> [[[a]]]
setPartitions [] = [[]]
setPartitions (x : xs) =
  [q' | q <- setPartitions xs, q' <- ([x] : q) : [before ++ [x : blk] ++ after | (before, blk : after) <- splits q]]
  where
    splits q = [splitAt i q | i <- [0 .. length q - 1]]

binomI :: Natural -> Natural -> Integer
binomI n k
  | k > n = 0
  | otherwise = toInteger (product [n - k + 1 .. n] `div` product [1 .. k])

tshow :: (Show s) => s -> Text
tshow = T.pack . show

showI :: Integer -> Text
showI = tshow

showQ :: Rational -> Text
showQ q
  | denominator q == 1 = tshow (numerator q)
  | otherwise = tshow (numerator q) <> "/" <> tshow (denominator q)
