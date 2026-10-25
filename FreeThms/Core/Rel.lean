/-
# Relations, graphs, and isomorphisms

Heterogeneous relations `Rel A B`, graphs of functions, and isomorphisms.
Mathlib-free, so the substrate depends on nothing.
-/

namespace FreeThms

universe u v w

/-- A relation between two types. Valued in `Prop`, so the whole first-order
development stays proof-irrelevant (at
higher kinds the relational interpretation becomes a proof-*relevant* relator
landing in `Type`, and this economy ends).

What `Prop`-valuedness buys and does not buy is worth stating once, since
conflating the two is the standard route into an inconsistent model.
Impredicative `Prop` makes the **logical relation** cheap to define, even at
quantifiers over all relations. It says nothing whatever about the
**denotation** — `TyD` in `Core/Semantics.lean` — which is where Reynolds'
obstruction lives. This file is silent on that; see `Semantics.lean`. -/
abbrev Rel (A : Type u) (B : Type v) : Type (max u v) := A → B → Prop

namespace Rel

/-- The graph of a function. Relating `f` to itself at `graph g` is the
equivariance statement `f ∘ g = g ∘ f`. -/
def graph {A : Type u} {B : Type v} (f : A → B) : Rel A B := fun a b => f a = b

/-- The identity relation, i.e. the graph of `id`. -/
def id' (A : Type u) : Rel A A := graph (fun a => a)

/-- Converse. -/
def inv {A : Type u} {B : Type v} (R : Rel A B) : Rel B A := fun b a => R a b

/-- Relational composition. -/
def comp {A : Type u} {B : Type v} {C : Type w} (R : Rel A B) (S : Rel B C) :
    Rel A C := fun a c => ∃ b, R a b ∧ S b c

/-- The empty relation. Instantiating at this is how emptiness theorems are
obtained. -/
def empty (A : Type u) (B : Type v) : Rel A B := fun _ _ => False

/-- The relation relating exactly `a₀` to `b₀`. Instantiating at this is how
"only one inhabitant" theorems are obtained. -/
def single {A : Type u} {B : Type v} (a₀ : A) (b₀ : B) : Rel A B :=
  fun a b => a = a₀ ∧ b = b₀

@[simp] theorem graph_apply {A : Type u} {B : Type v} (f : A → B) (a : A) (b : B) :
    graph f a b ↔ f a = b := Iff.rfl

@[simp] theorem id'_apply {A : Type u} (a a' : A) : id' A a a' ↔ a = a' := Iff.rfl

@[simp] theorem inv_apply {A : Type u} {B : Type v} (R : Rel A B) (b : B) (a : A) :
    inv R b a ↔ R a b := Iff.rfl

@[simp] theorem empty_apply {A : Type u} {B : Type v} (a : A) (b : B) :
    empty A B a b ↔ False := Iff.rfl

@[simp] theorem single_apply {A : Type u} {B : Type v} (a₀ : A) (b₀ : B) (a : A) (b : B) :
    single a₀ b₀ a b ↔ (a = a₀ ∧ b = b₀) := Iff.rfl

theorem graph_id {A : Type u} : graph (fun a : A => a) = id' A := rfl

end Rel

/-! ## Isomorphisms

Graphs of arbitrary functions lift through the logical relation at covariant
positions only; an isomorphism lifts at both. `Iso` is the minimum structure
that buys both variances. -/

/-- An isomorphism of types. Mathlib's `Equiv` under another name; kept local so
that `Core/` has no dependencies. -/
structure Iso (A : Type u) (B : Type v) where
  toFun : A → B
  invFun : B → A
  left_inv : ∀ a, invFun (toFun a) = a
  right_inv : ∀ b, toFun (invFun b) = b

namespace Iso

variable {A : Type u} {B : Type v} {C : Type w}

/-- The identity isomorphism. -/
protected def refl (A : Type u) : Iso A A :=
  { toFun := fun a => a, invFun := fun a => a,
    left_inv := fun _ => rfl, right_inv := fun _ => rfl }

/-- Inverse isomorphism. -/
protected def symm (e : Iso A B) : Iso B A :=
  { toFun := e.invFun, invFun := e.toFun,
    left_inv := e.right_inv, right_inv := e.left_inv }

/-- Composition, in diagrammatic order. -/
protected def trans (e : Iso A B) (f : Iso B C) : Iso A C :=
  { toFun := fun a => f.toFun (e.toFun a)
    invFun := fun c => e.invFun (f.invFun c)
    left_inv := fun a => by simp [e.left_inv, f.left_inv]
    right_inv := fun c => by simp [e.right_inv, f.right_inv] }

@[simp] theorem refl_toFun (A : Type u) : (Iso.refl A).toFun = fun a => a := rfl
@[simp] theorem symm_toFun (e : Iso A B) : e.symm.toFun = e.invFun := rfl
@[simp] theorem symm_invFun (e : Iso A B) : e.symm.invFun = e.toFun := rfl

theorem toFun_injective (e : Iso A B) {a a' : A} (h : e.toFun a = e.toFun a') : a = a' := by
  have := congrArg e.invFun h
  rwa [e.left_inv, e.left_inv] at this

/-- An isomorphism is determined by its forward map. -/
theorem ext {e f : Iso A B} (h : e.toFun = f.toFun) : e = f := by
  obtain ⟨t, i, li, ri⟩ := e
  obtain ⟨t', i', li', ri'⟩ := f
  cases h
  have : i = i' := by
    funext b
    have h1 : t (i b) = b := ri b
    have h2 : t (i' b) = b := ri' b
    exact toFun_injective ⟨t, i, li, ri⟩ (h1.trans h2.symm)
  cases this
  rfl

end Iso

end FreeThms
