/-
# Predicative prenex System F, and its abstraction theorem

The language of the write-up, Chapter 2. Its types are

    τ ::= X | τ → τ | ∀X. τ

and its terms are variables, `λ`, application and type abstraction. There are no
base sorts and no constants in the syntax. Base sorts occur only in the
semantics, as the sets at which type variables are instantiated.

The logical relation at `∀X. τ` ranges over **all** relations between the two
instantiations of `X`. That is what makes free theorems more than equations: a
relation need not be the graph of a function.

## Two restrictions, and what each costs

**Predicative.** `∀` quantifies over the simple types `Ty B` over a set `B` of
base sorts, so a type environment maps type variables to `Ty B`. The denotation
of `all` is then a product indexed by `Ty B`, which is itself in `Type 0`.

**Prenex.** `tlam` abstracts a type variable over a term whose *term* context is
empty, so a `Λ` never appears underneath a `λ`. The theorems are statements
about the denotation of a polymorphic term, which is already a function of the
instantiation, so nothing needs more.

Everything is at `Type 0`.

## The classical examples

`poly_id`, `poly_bool` and `poly_church` are the free theorems of `∀X. X → X`,
`∀X. X → X → X` and `∀X. (X → X) → X → X`. Each is proved by instantiating the
quantifier at a relation that is **not** a graph: a singleton, a two-point set,
and the graph of a predicate.
-/

import FreeThms.Core.Semantics
import FreeThms.Core.Rel

namespace FreeThms

/-! ## Types

`PTy n` is a type with `n` free type variables, as de Bruijn indices, so `all`
binds variable `0`.

The index `n` is the type-variable context `Θ` of the usual presentation of
System F. It is there only so that the syntax is well scoped. The write-up has
no `Θ` (Chapter 2, the definition of terms): there a type environment is defined
on all type variables, and the prenex restriction already makes the side
condition of type abstraction vacuous. -/

/-- Types: type variables, function types and universal quantification. -/
inductive PTy : Nat → Type
  | tvar {n} : Fin n → PTy n
  /-- Function types. -/
  | arrow {n} : PTy n → PTy n → PTy n
  | all {n} : PTy (n + 1) → PTy n

@[inherit_doc] infixr:25 " ⇛ " => PTy.arrow

/-! ## Type environments

A type environment sends each type variable to a simple type. That is
predicativity. -/

/-- Extend an environment with a new innermost entry. Reducible, so that the
denotation of an instantiated quantifier unfolds during instance search. -/
@[reducible] def scons {α : Type} {n : Nat} (a : α) (f : Fin n → α) : Fin (n + 1) → α
  | ⟨0, _⟩ => a
  | ⟨i + 1, h⟩ => f ⟨i, Nat.lt_of_succ_lt_succ h⟩

@[simp] theorem scons_zero {α : Type} {n : Nat} (a : α) (f : Fin n → α) :
    scons a f 0 = a := rfl

@[simp] theorem scons_succ {α : Type} {n : Nat} (a : α) (f : Fin n → α) (i : Fin n) :
    scons a f i.succ = f i := rfl

/-! ## Denotation

The clause that matters is the last: a polymorphic value is a *function of its
instantiation*, so a free theorem about it holds at every instantiation at once. -/

/-- The denotation of a type, given an interpretation of the base sorts and a
type environment. -/
@[reducible] def PTyD {B : Type} (Ib : B → Type) :
    {n : Nat} → PTy n → (Fin n → Ty B) → Type
  | _, .tvar i, η => TyD Ib (η i)
  | _, .arrow τ σ, η => PTyD Ib τ η → PTyD Ib σ η
  | _, .all τ, η => ∀ σ : Ty B, PTyD Ib τ (scons σ η)

/-! ## Contexts and terms -/

/-- A term context over `n` free type variables. -/
inductive PCtx (n : Nat) : Type
  | nil : PCtx n
  /-- Context extension. -/
  | cons : PCtx n → PTy n → PCtx n

@[inherit_doc] infixl:50 " ▹ " => PCtx.cons

/-- A de Bruijn term variable. -/
inductive PVar {n : Nat} : PCtx n → PTy n → Type
  | zero {Γ τ} : PVar (Γ ▹ τ) τ
  | succ {Γ τ σ} : PVar Γ τ → PVar (Γ ▹ σ) τ

/-- Intrinsically typed terms. -/
inductive PTm : {n : Nat} → PCtx n → PTy n → Type
  | var {n} {Γ : PCtx n} {τ} : PVar Γ τ → PTm Γ τ
  | lam {n} {Γ : PCtx n} {τ σ} : PTm (Γ ▹ τ) σ → PTm Γ (τ ⇛ σ)
  | app {n} {Γ : PCtx n} {τ σ} : PTm Γ (τ ⇛ σ) → PTm Γ τ → PTm Γ σ
  /-- Type abstraction. The term context is empty, which is the prenex
  restriction. -/
  | tlam {n} {τ : PTy (n + 1)} :
      PTm (PCtx.nil : PCtx (n + 1)) τ → PTm (PCtx.nil : PCtx n) (.all τ)

/-- Closed terms, with no free type variables either. -/
abbrev PClosedTm (τ : PTy 0) : Type :=
  PTm (PCtx.nil : PCtx 0) τ

/-! ## Environments and evaluation -/

/-- A term environment. -/
def PEnv {B : Type} (Ib : B → Type) {n : Nat} (η : Fin n → Ty B) : PCtx n → Type
  | .nil => PUnit
  | .cons Γ τ => PEnv Ib η Γ × PTyD Ib τ η

/-- Looking a variable up in an environment. -/
def PEnv.lookup {B : Type} (Ib : B → Type) {n : Nat} (η : Fin n → Ty B) :
    {Γ : PCtx n} → {τ : PTy n} → PVar Γ τ → PEnv Ib η Γ → PTyD Ib τ η
  | _, _, .zero, e => e.2
  | _, _, .succ x, e => PEnv.lookup Ib η x e.1

/-- Denotation of terms. -/
def peval {B : Type} (Ib : B → Type) :
    {n : Nat} → {Γ : PCtx n} → {τ : PTy n} → {η : Fin n → Ty B} →
      PTm Γ τ → PEnv Ib η Γ → PTyD Ib τ η
  | _, _, _, η, .var x, e => PEnv.lookup Ib η x e
  | _, _, _, _, .lam t, e => fun x => peval Ib t (e, x)
  | _, _, _, _, .app f a, e => (peval Ib f e) (peval Ib a e)
  | _, _, _, η, .tlam t, _ => fun σ => peval Ib (η := scons σ η) t PUnit.unit

/-- Denotation of a closed term. -/
abbrev pevalC {B : Type} (Ib : B → Type) {τ : PTy 0} (t : PClosedTm τ) :
    PTyD Ib τ (fun i => i.elim0) :=
  peval Ib t PUnit.unit

/-! ## The logical relation

One clause carries everything this file exists for. At `all` the relation
quantifies over two instantiations **and an arbitrary relation between them**.
Nothing forces that relation to be a graph, which is what lets the theorems
below be something other than equivariance. -/

/-- A relation environment: for each type variable, two instantiations and a
relation between their denotations. -/
structure REnv {B : Type} (Ib Jb : B → Type) (n : Nat) where
  /-- The left instantiation of each type variable. -/
  l : Fin n → Ty B
  /-- The right instantiation of each type variable. -/
  r : Fin n → Ty B
  /-- The relation carried at each type variable. -/
  rel : (i : Fin n) → Rel (TyD Ib (l i)) (TyD Jb (r i))

/-- The empty relation environment. -/
@[reducible] def REnv.nil {B : Type} (Ib Jb : B → Type) : REnv Ib Jb 0 where
  l := fun i => i.elim0
  r := fun i => i.elim0
  rel := fun i => i.elim0

/-- Extend a relation environment by an instantiation pair and a relation. -/
@[reducible] def REnv.cons {B : Type} {Ib Jb : B → Type} {n : Nat} (ρ : REnv Ib Jb n)
    (a b : Ty B) (S : Rel (TyD Ib a) (TyD Jb b)) : REnv Ib Jb (n + 1) where
  l := scons a ρ.l
  r := scons b ρ.r
  rel := fun i => match i with
    | ⟨0, _⟩ => S
    | ⟨j + 1, h⟩ => ρ.rel ⟨j, Nat.lt_of_succ_lt_succ h⟩

/-- The logical relation at a type. -/
def PTyRel {B : Type} {Ib Jb : B → Type} :
    {n : Nat} → (τ : PTy n) → (ρ : REnv Ib Jb n) →
      Rel (PTyD Ib τ ρ.l) (PTyD Jb τ ρ.r)
  | _, .tvar i, ρ => ρ.rel i
  | _, .arrow τ σ, ρ => fun f g => ∀ x y, PTyRel τ ρ x y → PTyRel σ ρ (f x) (g y)
  | _, .all τ, ρ => fun f g =>
      ∀ (a b : Ty B) (S : Rel (TyD Ib a) (TyD Jb b)),
        PTyRel τ (ρ.cons a b S) (f a) (g b)

@[simp] theorem PTyRel_all {B : Type} {Ib Jb : B → Type}
    {n : Nat} (τ : PTy (n + 1)) (ρ : REnv Ib Jb n)
    (f : PTyD Ib (.all τ) ρ.l) (g : PTyD Jb (.all τ) ρ.r) :
    PTyRel (.all τ) ρ f g ↔
      ∀ (a b : Ty B) (S : Rel (TyD Ib a) (TyD Jb b)),
        PTyRel τ (ρ.cons a b S) (f a) (g b) := Iff.rfl

/-- Related environments, pointwise. -/
def PEnvRel {B : Type} {Ib Jb : B → Type} {n : Nat} (ρ : REnv Ib Jb n) :
    (Γ : PCtx n) → PEnv Ib ρ.l Γ → PEnv Jb ρ.r Γ → Prop
  | .nil, _, _ => True
  | .cons Γ τ, e₁, e₂ => PEnvRel ρ Γ e₁.1 e₂.1 ∧ PTyRel τ ρ e₁.2 e₂.2

theorem PEnvRel.lookup {B : Type} {Ib Jb : B → Type} {n : Nat} (ρ : REnv Ib Jb n) :
    {Γ : PCtx n} → {τ : PTy n} → (x : PVar Γ τ) →
      {e₁ : PEnv Ib ρ.l Γ} → {e₂ : PEnv Jb ρ.r Γ} → PEnvRel ρ Γ e₁ e₂ →
      PTyRel τ ρ (PEnv.lookup Ib ρ.l x e₁) (PEnv.lookup Jb ρ.r x e₂)
  | _, _, .zero, _, _, h => h.2
  | _, _, .succ x, _, _, h => PEnvRel.lookup ρ x h.1

/-! ## The abstraction theorem -/

/--
**The abstraction theorem.** Every term is related to itself at every relation
environment, given related term environments.

The `tlam` case is the one with content: the goal quantifies over two
instantiations and an arbitrary relation between them, and the inductive
hypothesis supplies exactly that, because the term context is empty and so the
environment relation is vacuous.
-/
theorem pabstraction {B : Type} {Ib Jb : B → Type} :
    {n : Nat} → {Γ : PCtx n} → {τ : PTy n} → (t : PTm Γ τ) →
      (ρ : REnv Ib Jb n) → {e₁ : PEnv Ib ρ.l Γ} → {e₂ : PEnv Jb ρ.r Γ} →
      PEnvRel ρ Γ e₁ e₂ → PTyRel τ ρ (peval Ib t e₁) (peval Jb t e₂)
  | _, _, _, .var x, ρ, _, _, h => PEnvRel.lookup ρ x h
  | _, _, _, .lam t, ρ, _, _, h => fun _ _ hxy => pabstraction t ρ ⟨h, hxy⟩
  | _, _, _, .app f a, ρ, _, _, h => pabstraction f ρ h _ _ (pabstraction a ρ h)
  | _, _, _, .tlam t, ρ, _, _, _ => fun a b S => pabstraction t (ρ.cons a b S) trivial

/-- **The abstraction theorem at a closed term**, which is the form every
theorem below uses. -/
theorem pabstraction_closed {B : Type} (Ib Jb : B → Type) {τ : PTy 0} (t : PClosedTm τ) :
    PTyRel τ (REnv.nil Ib Jb) (pevalC Ib t) (pevalC Jb t) :=
  pabstraction t (REnv.nil Ib Jb) trivial

/-! ## Three theorems λ→ cannot state

Each is proved by instantiating the quantifier at a relation that is **not** the
graph of a function: a graph is total and single-valued, and each relation below
fails to be total. A graph relation carries no more information than a function,
so a free theorem read at a graph can only be an equation between functions. -/

/-! ### The three types, written out

`PTyRel` is a recursion on the type, so `pabstraction_closed` already *is* the
free theorem; the three statements here are what that recursion computes at the
three types, spelled out. Each is closed by the abstraction theorem applied to
nothing but the term, so each is definitionally the logical relation at its
type, neither weaker nor stronger.

The validations below are then corollaries, obtained by fixing one
interpretation and one relation. Separating the two makes it visible which part
is the free theorem and which part is the choice. -/

/-- **The free theorem at `∀X. X → X`, written out.** -/
theorem free_idTy {B : Type} (Ib Jb : B → Type) (t : PClosedTm (.all (.tvar 0 ⇛ .tvar 0))) :
    ∀ (a b : Ty B) (S : Rel (TyD Ib a) (TyD Jb b))
      (x : TyD Ib a) (y : TyD Jb b), S x y →
      S (pevalC Ib t a x) (pevalC Jb t b y) :=
  pabstraction_closed Ib Jb t

/-- **The free theorem at `∀X. X → X → X`, written out.** -/
theorem free_boolTy {B : Type} (Ib Jb : B → Type)
    (t : PClosedTm (.all (.tvar 0 ⇛ .tvar 0 ⇛ .tvar 0))) :
    ∀ (a b : Ty B) (S : Rel (TyD Ib a) (TyD Jb b))
      (x₁ : TyD Ib a) (x₂ : TyD Jb b), S x₁ x₂ →
      ∀ (y₁ : TyD Ib a) (y₂ : TyD Jb b), S y₁ y₂ →
      S (pevalC Ib t a x₁ y₁) (pevalC Jb t b x₂ y₂) :=
  pabstraction_closed Ib Jb t

/-- **The free theorem at `∀X. (X → X) → X → X`, written out.** -/
theorem free_churchTy {B : Type} (Ib Jb : B → Type)
    (t : PClosedTm (.all ((.tvar 0 ⇛ .tvar 0) ⇛ .tvar 0 ⇛ .tvar 0))) :
    ∀ (a b : Ty B) (S : Rel (TyD Ib a) (TyD Jb b))
      (f : TyD Ib a → TyD Ib a) (g : TyD Jb b → TyD Jb b),
      (∀ x y, S x y → S (f x) (g y)) →
      ∀ (x : TyD Ib a) (y : TyD Jb b), S x y →
      S (pevalC Ib t a f x) (pevalC Jb t b g y) :=
  pabstraction_closed Ib Jb t

/-! ### The validations, as instances of them -/

/-- `Λ X. λ (x : X). x`, the only inhabitant of its type up to denotation. -/
def polyId : PClosedTm (.all (.tvar 0 ⇛ .tvar 0)) :=
  .tlam (.lam (.var .zero))

/--
**`∀X. X → X` is the identity.** Every closed term of that type denotes the
identity at every instantiation.

The relation chosen is the singleton `{(x, x)}`, which is not total, hence not a
graph. A graph instantiation would say only that the term commutes with that one
function.
-/
theorem poly_id {B : Type} (Ib : B → Type)
    (t : PClosedTm (.all (.tvar 0 ⇛ .tvar 0))) (σ : Ty B) (x : TyD Ib σ) :
    pevalC Ib t σ x = x :=
  (free_idTy Ib Ib t σ σ (fun u v => u = x ∧ v = x) x x ⟨rfl, rfl⟩).1

/-- `Λ X. λ x. λ y. x` -/
def polyFst : PClosedTm (.all (.tvar 0 ⇛ .tvar 0 ⇛ .tvar 0)) :=
  .tlam (.lam (.lam (.var (.succ .zero))))

/-- `Λ X. λ x. λ y. y` -/
def polySnd : PClosedTm (.all (.tvar 0 ⇛ .tvar 0 ⇛ .tvar 0)) :=
  .tlam (.lam (.lam (.var .zero)))

/--
**`∀X. X → X → X` is a projection.** Every closed term of that type returns one
of its two arguments, so the type has exactly two inhabitants up to denotation:
`polyFst` and `polySnd`.

The relation is the diagonal restricted to `{x, y}`, again not total.
-/
theorem poly_bool {B : Type} (Ib : B → Type)
    (t : PClosedTm (.all (.tvar 0 ⇛ .tvar 0 ⇛ .tvar 0))) (σ : Ty B)
    (x y : TyD Ib σ) :
    pevalC Ib t σ x y = x ∨ pevalC Ib t σ x y = y :=
  (free_boolTy Ib Ib t σ σ (fun u v => u = v ∧ (u = x ∨ u = y)) x x ⟨rfl, Or.inl rfl⟩ y y
    ⟨rfl, Or.inr rfl⟩).2

/--
**`∀X. (X → X) → X → X` satisfies an induction principle.** Every closed term of
that type, applied to `f` and `x`, lands in the closure of `{x}` under `f`.

This is the parametric form of "the Church numerals are exactly the natural
numbers": the type's free theorem *is* the induction principle for the subset
reachable from `x` by `f`. The relation is the diagonal restricted to the
predicate, which is total only when the predicate holds everywhere.
-/
theorem poly_church {B : Type} (Ib : B → Type)
    (t : PClosedTm (.all ((.tvar 0 ⇛ .tvar 0) ⇛ .tvar 0 ⇛ .tvar 0)))
    (σ : Ty B) (f : TyD Ib σ → TyD Ib σ) (x : TyD Ib σ) (P : TyD Ib σ → Prop)
    (hx : P x) (hf : ∀ z, P z → P (f z)) :
    P (pevalC Ib t σ f x) := by
  have hrel := free_churchTy Ib Ib t σ σ (fun u v => u = v ∧ P u)
  have hfrel : ∀ u v, (u = v ∧ P u) → (f u = f v ∧ P (f u)) := by
    rintro u v ⟨rfl, hu⟩
    exact ⟨rfl, hf u hu⟩
  exact (hrel f f hfrel x x ⟨rfl, hx⟩).2

/-! ### The terms are there

The theorems above are not vacuous for want of inhabitants. -/

example {B : Type} (Ib : B → Type) (σ : Ty B) (x : TyD Ib σ) :
    pevalC Ib polyId σ x = x := rfl

example {B : Type} (Ib : B → Type) (σ : Ty B) (x y : TyD Ib σ) :
    pevalC Ib polyFst σ x y = x := rfl

example {B : Type} (Ib : B → Type) (σ : Ty B) (x y : TyD Ib σ) :
    pevalC Ib polySnd σ x y = y := rfl

end FreeThms
