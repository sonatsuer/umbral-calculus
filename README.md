# Free Theorems for Umbral Calculus

This project defines a language for
[umbral calculus](https://en.wikipedia.org/wiki/Umbral_calculus) 
and studies the free theorems (in the sense of Wadler) of the types of its expressions.

The project has three parts:
- **The write-up** is a mostly self contained exposition of both umbral calculus and relational parametricity.
- **The Lean development** proves its results.
- **The Haskell library** implements the language and also has tests for theorems proved in Lean.

## Layout

```
docs/umbral-free-theorems.tex  the write-up
FreeThms/                      the Lean development.
haskell/                       the language as a Haskell library (see its README)
scripts/check.sh               build, and fail on any `sorry` or on a `free_*`
                               theorem not closed by a bare abstraction theorem
```

## Building

Lean (requires `elan`; Mathlib is fetched by Lake):

```
lake exe cache get   # optional: download prebuilt Mathlib
lake build
scripts/check.sh
```

Haskell (requires Nix with flakes):

```
cd haskell
nix develop
cabal test
cabal repl umbral
```

The write-up: `cd docs && latexmk -pdf umbral-free-theorems.tex`.
