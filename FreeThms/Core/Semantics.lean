/-
# The denotation of simple types

An interpretation assigns a set to every base sort, and a simple type denotes by
recursion.
-/

import FreeThms.Core.Ty

namespace FreeThms

universe u v

open Ty

/--
Denotation of simple types, given a denotation of base sorts.

Marked `@[reducible]`, which is not cosmetic. Typeclass synthesis and numeral
elaboration unfold only reducible definitions, so without it a goal at a base
sort that denotes `Int` cannot find `+` at type `TyD Ib (.base b)`, even though
that type *is* `Int`.
-/
@[reducible] def TyD {B : Type u} (Ib : B → Type v) : Ty B → Type v
  | .base b => Ib b
  | .arrow τ σ => TyD Ib τ → TyD Ib σ

@[simp] theorem TyD_base {B : Type u} (Ib : B → Type v) (b : B) :
    TyD Ib (.base b) = Ib b := rfl
@[simp] theorem TyD_arrow {B : Type u} (Ib : B → Type v) (τ σ : Ty B) :
    TyD Ib (τ ⇒ σ) = (TyD Ib τ → TyD Ib σ) := rfl

end FreeThms
