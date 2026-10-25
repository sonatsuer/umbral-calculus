/-
# The monomorphic fragment of the full language

Programs written against the dictionary `Umbral(K, U, A)`, such as the auxiliary
umbrae of the full language, live under the three type quantifiers and the dictionary binders.
They contain no type abstraction. This file isolates that fragment, `MTm`, with
its embedding into terms of the full language. One program is made available to another by a
`let`, that is by an application of a `λ`, so no weakening is needed.

Mathlib-free.
-/

import FreeThms.Core.Kripke

namespace FreeThms.Kripke

open FreeThms

/-- Monomorphic terms of the full language: the terms of `QTm` other than `tlam`, over a fixed
number of free type variables. -/
inductive MTm {n : Nat} : QCtx n → QTy n → Type
  | var {Γ τ} : QVar Γ τ → MTm Γ τ
  | lam {Γ τ σ} : MTm (.cons Γ τ) σ → MTm Γ (τ ⇛ σ)
  | app {Γ τ σ} : MTm Γ (τ ⇛ σ) → MTm Γ τ → MTm Γ σ
  | pair {Γ τ σ} : MTm Γ τ → MTm Γ σ → MTm Γ (.prod τ σ)
  | fst {Γ τ σ} : MTm Γ (.prod τ σ) → MTm Γ τ
  | snd {Γ τ σ} : MTm Γ (.prod τ σ) → MTm Γ σ
  | zero {Γ} : MTm Γ .nat
  | succ {Γ} : MTm Γ .nat → MTm Γ .nat
  | iter {Γ τ} : MTm Γ .nat → MTm Γ (τ ⇛ τ) → MTm Γ τ → MTm Γ τ
  | ret {Γ τ} : MTm Γ τ → MTm Γ (.comp τ)
  | bind {Γ σ τ} : MTm Γ (.comp σ) → MTm Γ (σ ⇛ .comp τ) → MTm Γ (.comp τ)

namespace MTm

variable {n : Nat}

/-- A monomorphic term is a term of the full language. -/
def toQ : {Γ : QCtx n} → {τ : QTy n} → MTm Γ τ → QTm Γ τ
  | _, _, .var x => .var x
  | _, _, .lam t => .lam (toQ t)
  | _, _, .app f a => .app (toQ f) (toQ a)
  | _, _, .pair s t => .pair (toQ s) (toQ t)
  | _, _, .fst t => .fst (toQ t)
  | _, _, .snd t => .snd (toQ t)
  | _, _, .zero => .zero
  | _, _, .succ t => .succ (toQ t)
  | _, _, .iter k f x => .iter (toQ k) (toQ f) (toQ x)
  | _, _, .ret t => .ret (toQ t)
  | _, _, .bind m f => .bind (toQ m) (toQ f)

end MTm

/-! ## Renamings of variables -/

/-- A renaming of variables from one context into another. -/
abbrev Ren {n : Nat} (Γ Δ : QCtx n) : Type := ∀ {τ : QTy n}, QVar Γ τ → QVar Δ τ

end FreeThms.Kripke
