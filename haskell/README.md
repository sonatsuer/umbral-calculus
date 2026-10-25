# umbral: Rota's Umbral Calculus as a Polymorphic Language

The umbral calculus as a small language embedded in Haskell, and a library for
computing with it.

## The Language

An expression of the umbral calculus uses:
- the ring operations of the scalars `k`;
- the ring operations of the umbral polynomials `a`;
- the inclusion of scalars;
- the inclusion of umbrae;
- the evaluation;
- an allocator of fresh umbrae with prescribed moments.

Here the two ring structures are type classes (`Ring k`, `Ring a`, with the
operators `.+.`, `.-.`, `.*.`, `.^` and `*.`). The four umbral operations are
not a type class. They form a dictionary, the record `Umbral`, which every
expression takes as an explicit argument, because a model depends on data
chosen at run time, such as a moment assignment:

```haskell
data Umbral m k u a = Umbral
  { scalar :: k -> a,                -- a scalar is a constant polynomial
    inj    :: u -> a,                -- an umbra is a polynomial
    eval   :: a -> k,                -- the evaluation
    mk     :: (Natural -> k) -> m u  -- a fresh umbra with these moments
  }
```

An expression that cannot allocate has the type

```haskell
type Expr1 = forall m k u a. (Ring k, Ring a) => Umbral m k u a -> u -> k

variance :: Expr1
variance d x = moment d 2 x .-. moment d 1 x .^ 2
```

Its result does not mention `m`, so it cannot allocate.

An expression that may allocate returns in the abstract monad `m`:

```haskell
type ExprM1 = forall m k u a. (Monad m, Ring k, Ring a) => Umbral m k u a -> u -> m k
```

It allocates only through `mk`, and it cannot run the allocator. Rota and
Taylor's auxiliary umbrae are such expressions (`Umbral.Auxiliary`):
- the fresh copy `new`;
- the dot product `n.α`, both symbolically and by construction;
- the composition `β.α`;
- the singleton and cumulant umbrae;
- the compositional inverse.

A context (`CtxDot`, `CtxNew`, `CtxSum`) receives an implementation of an
interface and cannot tell how it allocates. So the symbolic and the constructed
dot product, for example, are interchangeable in every context. Yet one
allocates a single umbra and the other allocates `n`.

## Layout

The package has two libraries.

**`umbral-lib`** (`lib/`) is general-purpose and knows nothing of umbrae:

| Module | Contents |
|---|---|
| `Algebra.Ring` | commutative rings, with the derived operators |
| `Algebra.Binomial` | binomial coefficients, from a memoized Pascal triangle |
| `Algebra.Polynomial` | sparse multivariate polynomials |
| `Algebra.Modular` | the ring `ℤ/n` (`Mod n`), with the modulus in the type |
| `Data.Memo` | memoized sequences, a lazy trie on the naturals |
| `Data.Stream` | infinite streams, as lists that are infinite by construction |
| `Control.Monad.Fresh` | a supply of fresh tags |
| `Probability.Random` | a SplitMix64 generator and some laws |
| `Probability.Space` | finite probability spaces: exact products of finite laws, Monte Carlo samples |

**`umbral`** (`src/`) is the umbral calculus:

| Module | Contents |
|---|---|
| `Umbral.Language` | the dictionary, the expression and context types, `moment` |
| `Umbral.Name` | umbrae as old names or fresh names carrying their moments |
| `Umbral.Moment` | the moment model of Rota and Taylor, over any ring |
| `Umbral.Symbolic` | the moment model with symbolic moments, so that the variance prints as `a2 - a1^2` |
| `Umbral.Probability` | umbrae as random variables, the evaluation as the expectation |
| `Umbral.Auxiliary` | the auxiliary umbrae as terms |
| `Umbral.Sequences` | the library on sequences |
| `Umbral.Examples` | example expressions and contexts |
| `Umbral.Showcase` | worked computations, each with an independent reference |

## Using It

`Umbral.Sequences` takes and returns moment sequences as streams
(`Data.Stream`) indexed from 0, with entry 0 equal to 1:

```haskell
>>> import qualified Data.Stream as S
>>> S.take 8 (connected (S.generate (\n -> 2 ^ ((n * n - n) `div` 2))))  -- connected labeled graphs
[1,1,1,4,38,728,26704,1866256]
>>> S.take 10 (partitionsWithBlocks (<= 2))                              -- involutions
[1,1,2,4,10,26,76,232,764,2620]
>>> S.take 8 (compositionalInverse bellNumbers)                          -- Lagrange inversion
[1,1,-2,7,-35,228,-1834,17582]
```

Below that layer, a computation is a term written in Rota and Taylor's
notation:

```haskell
-- the rooted labeled trees: the compositional inverse of t e⁻ᵗ
rootedTrees :: (Monad m, Ring k, Ring a) => Umbral m k u a -> m u
rootedTrees d = do
  a <- mk d (\n -> fromInt (if odd n then toInteger n else negate (toInteger n)))
  inverse d a
```

The same term runs in every model:
- over `Integer` or `Rational`, numerically;
- over `Formula`, symbolically;
- over `Mod 1000000007`, for large sizes;
- over a probability space, as an expectation.

`Umbral.Showcase` collects such terms, each with a reference computation that
does not go through the umbral code:
- connected graphs;
- derangements;
- set partitions with restricted blocks;
- Stirling numbers;
- rooted trees and forests;
- moments of dice sums;
- random sums;
- Euler's identity for Bernoulli numbers and Blissard's pitfall;
- Faulhaber's formula, and its expectation at a random upper limit in the
  probability model;
- Hermite and Touchard polynomials;
- the cumulants in terms of the moments, symbolically.

### Models

- **The moment model** (`momentModel`) is exact over any `Ring`. A fresh
  umbra's moments are memoized, so a composite umbra computes each moment once.
  Connected graphs on 60 vertices take a fraction of a second.
- **Modular arithmetic.** `momentModel` at `Mod n`. Naturality along `ℤ → ℤ/n`
  says the result is the reduction of the integer result.
- **Probability** (`probabilityModel`).
  - An old umbra is a random variable on a finite space, and the evaluation is
    the expectation.
  - A fresh umbra stays formal, because its moments need not be those of a
    random variable: χ has E[χ] = 1 and E[χ²] = 0.
  - The space is the exact product of finite laws (`exact`, over `Rational`)
    or a Monte Carlo sample (`monteCarlo`).
  - The algebra is not a polynomial ring: a Rademacher variable satisfies
    `X² = 1`.

## Build and Test

The toolchain (GHC 9.10.3, cabal, hlint, ormolu) comes from the flake. The
libraries are `base`, `containers`, `text` and `transformers`.

```
nix develop
cabal repl umbral           # then, e.g., :m + Umbral.Sequences
cabal test                  # 446 checks, in under a second
```

The checks cover:

- **Without allocation.**
  - The substitution principle for every example expression, numerically and
    symbolically.
  - Exchangeability.
  - The binomial convolution.
  - The Bernoulli relation.
  - The cumulant formulas.
  - Uncorrelation: `E[αβ] = a1*b1` against `E[αα] = a2`.
- **With allocation.**
  - The substitution principle again, and independence from which fresh tags
    are used.
- **The auxiliary umbrae.**
  - What each one allocates and the moments it gives.
  - The dot-moment identity.
  - The composition as `E[q_m(β)]`, by Newton interpolation over ℚ.
  - `n̄.α ≡ n.α`.
  - The cumulant umbra.
  - Compound Poisson.
- **Representation independence.**
  - For the fresh copy, the dot product and the composition of a sum, every
    context gives the same value under both implementations, numerically and
    symbolically, with non-vacuity checks.
  - Distributivity.
  - The Sheffer identity at umbral arguments.
  - The allocation counts, which differ.
- **The library.**
  - The compositional inverse: both sides, uniqueness, Lagrange's formula,
    Cayley's nⁿ⁻¹.
  - Memoization: connected graphs on 25 vertices, Bell cumulants up to 40.
  - Modular naturality, and Touchard's congruence.
  - Probabilistic soundness, exactly over ℚ.
  - Rademacher's `X² = 1`.
  - Monte Carlo estimates.
  - `Umbral.Sequences`, and every worked computation of `Umbral.Showcase`.
