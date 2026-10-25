/-
# The full language: allocation behind the interface, and its Kripke abstraction theorem

`Core/SystemF.lean` interprets the restricted language, predicative prenex
System F, in sets.
There the free theorems of the umbral types collapse to naturality (write-up,
Chapter 2). This
file extends the language by natural numbers with an iterator and by an
allocation monad `T`, and interprets it over **worlds**. The logical relation is
indexed by **world relations** rather than by worlds. That indexing is what lets
the free theorems of types that mention `T` say more than naturality (write-up,
Chapter 3).

## What is abstract here

Everything specific to the umbral calculus enters through two structures.

* `AllocStr` — worlds, their morphisms, blocks of fresh names, and the extension
  `w ⊕ B` of a world by a block. Types denote world-indexed sets with transport
  along morphisms. The allocation monad at `w` is a block together with a value
  at `w ⊕ B`.
* `RelStr` — world relations, the futures of a world relation along a pair of
  morphisms, and the tensor of a world relation with a relation between two
  blocks. Five axioms say that futures compose and are compatible with
  extension, which is all the abstraction theorem needs. In the umbral instance
  the tensor is the extension lemma, whose content is uncorrelation.

## The one change from Pitts and Stark

At `T τ` two computations are related when *some* relation between their blocks
relates their values. The block relation is arbitrary, not a bijection of fresh
names. That is the point: two implementations of one interface may allocate
differently, one name on one side and several on the other.

Mathlib-free, like the rest of `Core/`.
-/

import FreeThms.Core.SystemF

namespace FreeThms.Kripke

open FreeThms

/-! ## Worlds, morphisms and blocks -/

/-- An allocation structure. -/
structure AllocStr where
  /-- Worlds. -/
  W : Type
  /-- Morphisms of worlds. -/
  Hom : W → W → Type
  /-- Identity morphisms. -/
  id : (w : W) → Hom w w
  /-- Composition, in diagrammatic order. -/
  comp : {u v x : W} → Hom u v → Hom v x → Hom u x
  /-- The identity is a left unit. -/
  id_comp : ∀ {u v : W} (σ : Hom u v), comp (id u) σ = σ
  /-- Blocks of fresh names. -/
  Blk : Type
  /-- The empty block. -/
  empty : Blk
  /-- Concatenation of blocks. -/
  app : Blk → Blk → Blk
  /-- The extension `w ⊕ B` of a world by a block. -/
  ext : W → Blk → W
  /-- The inclusion `w → w ⊕ B`. -/
  inl : (w : W) → (B : Blk) → Hom w (ext w B)
  /-- Extension is functorial: `σ ⊕ B`. -/
  extHom : {w v : W} → Hom w v → (B : Blk) → Hom (ext w B) (ext v B)
  /-- Reassociation `(w ⊕ B) ⊕ B' → w ⊕ (B ++ B')`. -/
  assoc : (w : W) → (B B' : Blk) → Hom (ext (ext w B) B') (ext w (app B B'))

variable {A : AllocStr}

/-- A world-indexed interpretation of the base sorts, with transport along
morphisms. Base sorts do not occur in the types of the language; they are the
world-indexed sets at which type variables are instantiated. -/
structure BaseI (A : AllocStr) (B : Type) where
  /-- The carrier of each base sort at each world. -/
  carrier : B → A.W → Type
  /-- Transport along a morphism. -/
  tr : {w v : A.W} → (b : B) → A.Hom w v → carrier b w → carrier b v
  /-- Transport along an identity does nothing. -/
  tr_id : ∀ {w : A.W} (b : B) (x : carrier b w), tr b (A.id w) x = x

/-! ## Types

As in `Core/SystemF.lean`, the index `n` of `QTy n` is the type-variable context,
which is there for the encoding and does not appear in the write-up. -/

/-- Types of the full language: those of the restricted language, products,
natural numbers, and the allocation monad. -/
inductive QTy : Nat → Type
  | tvar {n} : Fin n → QTy n
  /-- Function types. -/
  | arrow {n} : QTy n → QTy n → QTy n
  | prod {n} : QTy n → QTy n → QTy n
  | nat {n} : QTy n
  /-- The allocation monad `T τ`. -/
  | comp {n} : QTy n → QTy n
  | all {n} : QTy (n + 1) → QTy n

@[inherit_doc] infixr:25 " ⇛ " => QTy.arrow

/-- The types a type variable is instantiated at: the simple types over the base
sorts. Predicativity is that the quantifier ranges over these. -/
inductive STy (B : Type) : Type
  | base : B → STy B
  | arrow : STy B → STy B → STy B

variable {B : Type}

/-- The denotation of a simple type at a world. -/
@[reducible] def SD (I : BaseI A B) : STy B → A.W → Type
  | .base b, w => I.carrier b w
  | .arrow τ σ, w => (v : A.W) → A.Hom w v → SD I τ v → SD I σ v

/-- Transport of a value of a simple type along a morphism. -/
def str (I : BaseI A B) : (τ : STy B) → {w v : A.W} → A.Hom w v → SD I τ w → SD I τ v
  | .base b, _, _, h, x => I.tr b h x
  | .arrow _ _, _, _, h, f => fun u k x => f u (A.comp h k) x

/-- The denotation of a type of the full language at a world, under a type environment. -/
@[reducible] def QTyD (I : BaseI A B) : {n : Nat} → QTy n → (Fin n → STy B) → A.W → Type
  | _, .tvar i, η, w => SD I (η i) w
  | _, .arrow τ σ, η, w => (v : A.W) → A.Hom w v → QTyD I τ η v → QTyD I σ η v
  | _, .prod τ σ, η, w => QTyD I τ η w × QTyD I σ η w
  | _, .nat, _, _ => Nat
  | _, .comp τ, η, w => Σ Bk : A.Blk, QTyD I τ η (A.ext w Bk)
  | _, .all τ, η, w => (σ : STy B) → QTyD I τ (scons σ η) w

/-- Transport of a value of a type of the full language along a morphism. -/
def qtr (I : BaseI A B) : {n : Nat} → (τ : QTy n) → (η : Fin n → STy B) →
    {w v : A.W} → A.Hom w v → QTyD I τ η w → QTyD I τ η v
  | _, .tvar i, η, _, _, h, x => str I (η i) h x
  | _, .arrow _ _, _, _, _, h, f => fun u k x => f u (A.comp h k) x
  | _, .prod τ σ, η, _, _, h, p => (qtr I τ η h p.1, qtr I σ η h p.2)
  | _, .nat, _, _, _, _, n => n
  | _, .comp τ, η, _, _, h, c => ⟨c.1, qtr I τ η (A.extHom h c.1) c.2⟩
  | _, .all τ, η, _, _, h, f => fun σ => qtr I τ (scons σ η) h (f σ)

/-! ## Terms -/

/-- A term context over `n` free type variables. -/
inductive QCtx (n : Nat) : Type
  | nil : QCtx n
  | cons : QCtx n → QTy n → QCtx n

/-- A de Bruijn term variable. -/
inductive QVar {n : Nat} : QCtx n → QTy n → Type
  | zero {Γ τ} : QVar (.cons Γ τ) τ
  | succ {Γ τ σ} : QVar Γ τ → QVar (.cons Γ σ) τ

/-- Terms of the full language: those of the restricted language, pairs, the natural numbers with an
iterator, and the unit and bind of the allocation monad. -/
inductive QTm : {n : Nat} → QCtx n → QTy n → Type
  | var {n} {Γ : QCtx n} {τ} : QVar Γ τ → QTm Γ τ
  | lam {n} {Γ : QCtx n} {τ σ} : QTm (.cons Γ τ) σ → QTm Γ (τ ⇛ σ)
  | app {n} {Γ : QCtx n} {τ σ} : QTm Γ (τ ⇛ σ) → QTm Γ τ → QTm Γ σ
  | pair {n} {Γ : QCtx n} {τ σ} : QTm Γ τ → QTm Γ σ → QTm Γ (.prod τ σ)
  | fst {n} {Γ : QCtx n} {τ σ} : QTm Γ (.prod τ σ) → QTm Γ τ
  | snd {n} {Γ : QCtx n} {τ σ} : QTm Γ (.prod τ σ) → QTm Γ σ
  | zero {n} {Γ : QCtx n} : QTm Γ .nat
  | succ {n} {Γ : QCtx n} : QTm Γ .nat → QTm Γ .nat
  /-- `iter n f x` applies `f` to `x`, `n` times. -/
  | iter {n} {Γ : QCtx n} {τ} :
      QTm Γ .nat → QTm Γ (τ ⇛ τ) → QTm Γ τ → QTm Γ τ
  /-- The unit of the allocation monad. -/
  | ret {n} {Γ : QCtx n} {τ} : QTm Γ τ → QTm Γ (.comp τ)
  /-- Bind: run the first computation, then the continuation in the extended
  world. -/
  | bind {n} {Γ : QCtx n} {σ τ} :
      QTm Γ (.comp σ) → QTm Γ (σ ⇛ .comp τ) → QTm Γ (.comp τ)
  /-- Type abstraction over a term with an empty context: the prenex
  restriction. -/
  | tlam {n} {τ : QTy (n + 1)} :
      QTm (QCtx.nil : QCtx (n + 1)) τ → QTm (QCtx.nil : QCtx n) (.all τ)

/-- Closed terms of the full language. -/
abbrev QClosedTm (τ : QTy 0) : Type :=
  QTm (QCtx.nil : QCtx 0) τ

/-! ## Environments and evaluation -/

/-- `iterN f k x` applies `f` to `x`, `k` times. Mathlib's `Nat.iterate` is not
available in `Core/`. -/
def iterN {X : Type} (f : X → X) : Nat → X → X
  | 0, x => x
  | k + 1, x => iterN f k (f x)

/-- A term environment at a world. -/
def QEnv (I : BaseI A B) {n : Nat} (η : Fin n → STy B) : QCtx n → A.W → Type
  | .nil, _ => PUnit
  | .cons Γ τ, w => QEnv I η Γ w × QTyD I τ η w

/-- Transport of an environment along a morphism. -/
def envTr (I : BaseI A B) {n : Nat} (η : Fin n → STy B) :
    (Γ : QCtx n) → {w v : A.W} → A.Hom w v → QEnv I η Γ w → QEnv I η Γ v
  | .nil, _, _, _, _ => PUnit.unit
  | .cons Γ τ, _, _, h, e => (envTr I η Γ h e.1, qtr I τ η h e.2)

/-- Looking a variable up in an environment. -/
def lookup (I : BaseI A B) {n : Nat} (η : Fin n → STy B) {w : A.W} :
    {Γ : QCtx n} → {τ : QTy n} → QVar Γ τ → QEnv I η Γ w → QTyD I τ η w
  | _, _, .zero, e => e.2
  | _, _, .succ x, e => lookup I η x e.1

/-- The denotation of a term at a world.

A function value is a family over the morphisms out of its world, so `lam`
evaluates its body at the target of the morphism, with the environment
transported there. `app` uses the identity component. `bind` runs the
continuation in the world extended by the first block, and reassociates. -/
def eval (I : BaseI A B) :
    {n : Nat} → {Γ : QCtx n} → {τ : QTy n} → {η : Fin n → STy B} →
      QTm Γ τ → (w : A.W) → QEnv I η Γ w → QTyD I τ η w
  | _, _, _, η, .var x, _, e => lookup I η x e
  | _, Γ, _, η, .lam t, _, e => fun v h x => eval I t v (envTr I η Γ h e, x)
  | _, _, _, _, .app f a, w, e => (eval I f w e) w (A.id w) (eval I a w e)
  | _, _, _, _, .pair s t, w, e => (eval I s w e, eval I t w e)
  | _, _, _, _, .fst t, w, e => (eval I t w e).1
  | _, _, _, _, .snd t, w, e => (eval I t w e).2
  | _, _, _, _, .zero, _, _ => (0 : Nat)
  | _, _, _, _, .succ t, w, e => (eval I t w e : Nat) + 1
  | _, _, _, _, .iter k f x, w, e =>
      iterN ((eval I f w e) w (A.id w)) (eval I k w e) (eval I x w e)
  | _, _, .comp τ, η, .ret t, w, e =>
      ⟨A.empty, qtr I τ η (A.inl w A.empty) (eval I t w e)⟩
  | _, _, .comp τ, η, .bind m k, w, e =>
      let c := eval I m w e
      let c' := (eval I k w e) (A.ext w c.1) (A.inl w c.1) c.2
      ⟨A.app c.1 c'.1, qtr I τ η (A.assoc w c.1 c'.1) c'.2⟩
  | _, _, _, η, .tlam t, w, _ => fun σ => eval I (η := scons σ η) t w PUnit.unit

/-- The denotation of a closed term. -/
abbrev evalC (I : BaseI A B) {τ : QTy 0} (t : QClosedTm τ) (w : A.W) :
    QTyD I τ (fun i => i.elim0) w :=
  eval I t w PUnit.unit

/-! ## World relations -/

/-- World relations, their futures, and their extension by block relations. -/
structure RelStr (A : AllocStr) where
  /-- World relations. -/
  R : A.W → A.W → Type
  /-- `Fut φ σ₁ σ₂ φ'`: `φ'` is a future of `φ` along `σ₁` and `σ₂`. -/
  Fut : {w₁ w₂ v₁ v₂ : A.W} → R w₁ w₂ → A.Hom w₁ v₁ → A.Hom w₂ v₂ → R v₁ v₂ → Prop
  /-- Every world relation is a future of itself along the identities. -/
  fut_refl : ∀ {w₁ w₂ : A.W} (φ : R w₁ w₂), Fut φ (A.id w₁) (A.id w₂) φ
  /-- Futures compose. -/
  fut_trans : ∀ {w₁ w₂ v₁ v₂ u₁ u₂ : A.W} {φ : R w₁ w₂} {φ' : R v₁ v₂} {φ'' : R u₁ u₂}
    {σ₁ : A.Hom w₁ v₁} {σ₂ : A.Hom w₂ v₂} {τ₁ : A.Hom v₁ u₁} {τ₂ : A.Hom v₂ u₂},
    Fut φ σ₁ σ₂ φ' → Fut φ' τ₁ τ₂ φ'' → Fut φ (A.comp σ₁ τ₁) (A.comp σ₂ τ₂) φ''
  /-- Relations between blocks. -/
  BR : A.Blk → A.Blk → Type
  /-- The tensor of a world relation with a block relation. -/
  tensor : {w₁ w₂ : A.W} → {B₁ B₂ : A.Blk} → R w₁ w₂ → BR B₁ B₂ →
    R (A.ext w₁ B₁) (A.ext w₂ B₂)
  /-- The tensor is a future along the inclusions. -/
  fut_inl : ∀ {w₁ w₂ : A.W} {B₁ B₂ : A.Blk} (φ : R w₁ w₂) (ψ : BR B₁ B₂),
    Fut φ (A.inl w₁ B₁) (A.inl w₂ B₂) (tensor φ ψ)
  /-- Futures extend across a block. -/
  fut_ext : ∀ {w₁ w₂ v₁ v₂ : A.W} {B₁ B₂ : A.Blk} {φ : R w₁ w₂} {φ' : R v₁ v₂}
    {σ₁ : A.Hom w₁ v₁} {σ₂ : A.Hom w₂ v₂} (ψ : BR B₁ B₂),
    Fut φ σ₁ σ₂ φ' → Fut (tensor φ ψ) (A.extHom σ₁ B₁) (A.extHom σ₂ B₂) (tensor φ' ψ)
  /-- The empty blocks are related. -/
  bempty : BR A.empty A.empty
  /-- Block relations concatenate. -/
  bapp : {B₁ B₂ B₁' B₂' : A.Blk} → BR B₁ B₂ → BR B₁' B₂' → BR (A.app B₁ B₁') (A.app B₂ B₂')
  /-- Reassociation is a future. -/
  fut_assoc : ∀ {w₁ w₂ : A.W} {B₁ B₂ B₁' B₂' : A.Blk} (φ : R w₁ w₂) (ψ : BR B₁ B₂)
    (ψ' : BR B₁' B₂'),
    Fut (tensor (tensor φ ψ) ψ') (A.assoc w₁ B₁ B₁') (A.assoc w₂ B₂ B₂')
      (tensor φ (bapp ψ ψ'))

variable {RS : RelStr A}

/-! ## The Kripke logical relation -/

/-- A Kripke relation between two simple types: a relation at every world
relation, monotone along futures. Type variables carry these. -/
structure KRel (RS : RelStr A) (I₁ I₂ : BaseI A B) (σ₁ σ₂ : STy B) where
  /-- The relation at each world relation. -/
  rel : {w₁ w₂ : A.W} → RS.R w₁ w₂ → SD I₁ σ₁ w₁ → SD I₂ σ₂ w₂ → Prop
  /-- Monotonicity along futures. -/
  mono : ∀ {w₁ w₂ v₁ v₂ : A.W} {φ : RS.R w₁ w₂} {φ' : RS.R v₁ v₂}
    {h₁ : A.Hom w₁ v₁} {h₂ : A.Hom w₂ v₂} {x y},
    rel φ x y → RS.Fut φ h₁ h₂ φ' → rel φ' (str I₁ σ₁ h₁ x) (str I₂ σ₂ h₂ y)

/-- A relation environment: for each type variable, two instantiations and a
Kripke relation between them. -/
structure KREnv (RS : RelStr A) (I₁ I₂ : BaseI A B) (n : Nat) where
  /-- The left instantiation of each type variable. -/
  l : Fin n → STy B
  /-- The right instantiation of each type variable. -/
  r : Fin n → STy B
  /-- The Kripke relation carried at each type variable. -/
  rel : (i : Fin n) → KRel RS I₁ I₂ (l i) (r i)

/-- Extend a relation environment by an innermost type variable. -/
def KREnv.cons {RS : RelStr A} {I₁ I₂ : BaseI A B} {n : Nat} (ρ : KREnv RS I₁ I₂ n)
    (σ₁ σ₂ : STy B) (S : KRel RS I₁ I₂ σ₁ σ₂) : KREnv RS I₁ I₂ (n + 1) where
  l := scons σ₁ ρ.l
  r := scons σ₂ ρ.r
  rel := fun i => match i with
    | ⟨0, _⟩ => S
    | ⟨j + 1, h⟩ => ρ.rel ⟨j, Nat.lt_of_succ_lt_succ h⟩

variable {I₁ I₂ : BaseI A B}

/-- The logical relation at a type of the full language and a world relation. -/
def QRel : {n : Nat} → (τ : QTy n) → (ρ : KREnv RS I₁ I₂ n) →
    {w₁ w₂ : A.W} → RS.R w₁ w₂ → QTyD I₁ τ ρ.l w₁ → QTyD I₂ τ ρ.r w₂ → Prop
  | _, .tvar i, ρ, _, _, φ => (ρ.rel i).rel φ
  | _, .arrow τ σ, ρ, w₁, w₂, φ => fun f g =>
      ∀ (v₁ v₂ : A.W) (h₁ : A.Hom w₁ v₁) (h₂ : A.Hom w₂ v₂) (φ' : RS.R v₁ v₂),
        RS.Fut φ h₁ h₂ φ' → ∀ x y, QRel τ ρ φ' x y → QRel σ ρ φ' (f v₁ h₁ x) (g v₂ h₂ y)
  | _, .prod τ σ, ρ, _, _, φ => fun p q => QRel τ ρ φ p.1 q.1 ∧ QRel σ ρ φ p.2 q.2
  | _, .nat, _, _, _, _ => fun m n => m = n
  | _, .comp τ, ρ, _, _, φ => fun c d => ∃ ψ : RS.BR c.1 d.1, QRel τ ρ (RS.tensor φ ψ) c.2 d.2
  | _, .all τ, ρ, _, _, φ => fun f g =>
      ∀ (σ₁ σ₂ : STy B) (S : KRel RS I₁ I₂ σ₁ σ₂), QRel τ (ρ.cons σ₁ σ₂ S) φ (f σ₁) (g σ₂)

/-- **Monotonicity.** The logical relation is preserved along futures. -/
theorem QRel.mono : {n : Nat} → (τ : QTy n) →
    (ρ : KREnv RS I₁ I₂ n) → {w₁ w₂ v₁ v₂ : A.W} → {φ : RS.R w₁ w₂} → {φ' : RS.R v₁ v₂} →
    {h₁ : A.Hom w₁ v₁} → {h₂ : A.Hom w₂ v₂} → {x : QTyD I₁ τ ρ.l w₁} → {y : QTyD I₂ τ ρ.r w₂} →
    QRel τ ρ φ x y → RS.Fut φ h₁ h₂ φ' →
      QRel τ ρ φ' (qtr I₁ τ ρ.l h₁ x) (qtr I₂ τ ρ.r h₂ y)
  | _, .tvar i, ρ, _, _, _, _, _, _, _, _, _, _, hxy, hf => (ρ.rel i).mono hxy hf
  | _, .arrow _ _, _, _, _, _, _, _, _, _, _, _, _, hxy, hf =>
      fun u₁ u₂ k₁ k₂ φ'' hf' a b hab => hxy u₁ u₂ _ _ φ'' (RS.fut_trans hf hf') a b hab
  | _, .prod τ σ, ρ, _, _, _, _, _, _, _, _, _, _, hxy, hf =>
      ⟨QRel.mono τ ρ hxy.1 hf, QRel.mono σ ρ hxy.2 hf⟩
  | _, .nat, _, _, _, _, _, _, _, _, _, _, _, hxy, _ => hxy
  | _, .comp τ, ρ, _, _, _, _, _, _, _, _, _, _, hxy, hf => by
      obtain ⟨ψ, h⟩ := hxy
      exact ⟨ψ, QRel.mono τ ρ h (RS.fut_ext ψ hf)⟩
  | _, .all τ, ρ, _, _, _, _, _, _, _, _, _, _, hxy, hf =>
      fun σ₁ σ₂ S => QRel.mono τ (ρ.cons σ₁ σ₂ S) (hxy σ₁ σ₂ S) hf

/-- Related environments, pointwise. -/
def QEnvRel {n : Nat} (ρ : KREnv RS I₁ I₂ n) :
    (Γ : QCtx n) → {w₁ w₂ : A.W} → RS.R w₁ w₂ →
      QEnv I₁ ρ.l Γ w₁ → QEnv I₂ ρ.r Γ w₂ → Prop
  | .nil, _, _, _, _, _ => True
  | .cons Γ τ, _, _, φ, e₁, e₂ => QEnvRel ρ Γ φ e₁.1 e₂.1 ∧ QRel τ ρ φ e₁.2 e₂.2

theorem QEnvRel.mono {n : Nat} (ρ : KREnv RS I₁ I₂ n) :
    (Γ : QCtx n) → {w₁ w₂ v₁ v₂ : A.W} → {φ : RS.R w₁ w₂} → {φ' : RS.R v₁ v₂} →
    {h₁ : A.Hom w₁ v₁} → {h₂ : A.Hom w₂ v₂} → {e₁ : QEnv I₁ ρ.l Γ w₁} →
    {e₂ : QEnv I₂ ρ.r Γ w₂} → QEnvRel ρ Γ φ e₁ e₂ → RS.Fut φ h₁ h₂ φ' →
      QEnvRel ρ Γ φ' (envTr I₁ ρ.l Γ h₁ e₁) (envTr I₂ ρ.r Γ h₂ e₂)
  | .nil, _, _, _, _, _, _, _, _, _, _, _, _ => trivial
  | .cons Γ τ, _, _, _, _, _, _, _, _, _, _, he, hf =>
      ⟨QEnvRel.mono ρ Γ he.1 hf, QRel.mono τ ρ he.2 hf⟩

theorem QEnvRel.lookup {n : Nat} (ρ : KREnv RS I₁ I₂ n)
    {w₁ w₂ : A.W} (φ : RS.R w₁ w₂) :
    {Γ : QCtx n} → {τ : QTy n} → (x : QVar Γ τ) →
      {e₁ : QEnv I₁ ρ.l Γ w₁} → {e₂ : QEnv I₂ ρ.r Γ w₂} → QEnvRel ρ Γ φ e₁ e₂ →
      QRel τ ρ φ (Kripke.lookup I₁ ρ.l x e₁) (Kripke.lookup I₂ ρ.r x e₂)
  | _, _, .zero, _, _, h => h.2
  | _, _, .succ x, _, _, h => QEnvRel.lookup ρ φ x h.1

/-! ## The abstraction theorem -/

/-- Iterating related functions on related arguments gives related results. -/
theorem iterate_rel {X Y : Type} (Rxy : X → Y → Prop) (f : X → X) (g : Y → Y)
    (hfg : ∀ x y, Rxy x y → Rxy (f x) (g y)) :
    ∀ (k : Nat) (x : X) (y : Y), Rxy x y → Rxy (iterN f k x) (iterN g k y)
  | 0, _, _, h => h
  | k + 1, x, y, h => iterate_rel Rxy f g hfg k (f x) (g y) (hfg x y h)

/--
**The Kripke abstraction theorem.** Every term is related to itself at every
world relation, given related environments.

The cases with content are three. `lam` quantifies over futures, and the
environment follows by monotonicity. `ret` relates the empty blocks. `bind`
composes the two block relations: the first computation's witness `ψ`, then the
continuation's `ψ'` at the future `tensor φ ψ`, and reassociation turns
`tensor (tensor φ ψ) ψ'` into `tensor φ (bapp ψ ψ')`.
-/
theorem abstraction :
    {n : Nat} → {Γ : QCtx n} → {τ : QTy n} → (t : QTm Γ τ) →
      (ρ : KREnv RS I₁ I₂ n) → {w₁ w₂ : A.W} → (φ : RS.R w₁ w₂) →
      {e₁ : QEnv I₁ ρ.l Γ w₁} → {e₂ : QEnv I₂ ρ.r Γ w₂} → QEnvRel ρ Γ φ e₁ e₂ →
      QRel τ ρ φ (eval I₁ t w₁ e₁) (eval I₂ t w₂ e₂)
  | _, _, _, .var x, ρ, _, _, φ, _, _, h => QEnvRel.lookup ρ φ x h
  | _, Γ, _, .lam t, ρ, _, _, _, _, _, h => fun v₁ v₂ h₁ h₂ φ' hf x y hxy =>
      abstraction t ρ φ' ⟨QEnvRel.mono ρ Γ h hf, hxy⟩
  | _, _, _, .app f a, ρ, w₁, w₂, φ, _, _, h =>
      abstraction f ρ φ h w₁ w₂ (A.id w₁) (A.id w₂) φ (RS.fut_refl φ) _ _
        (abstraction a ρ φ h)
  | _, _, _, .pair s t, ρ, _, _, φ, _, _, h =>
      ⟨abstraction s ρ φ h, abstraction t ρ φ h⟩
  | _, _, _, .fst t, ρ, _, _, φ, _, _, h => (abstraction t ρ φ h).1
  | _, _, _, .snd t, ρ, _, _, φ, _, _, h => (abstraction t ρ φ h).2
  | _, _, _, .zero, _, _, _, _, _, _, _ => rfl
  | _, _, _, .succ t, ρ, _, _, φ, _, _, h => by
      have ih : eval I₁ t _ _ = eval I₂ t _ _ := abstraction t ρ φ h
      show (eval I₁ t _ _ : Nat) + 1 = (eval I₂ t _ _ : Nat) + 1
      rw [ih]
  | _, _, τ, .iter k f x, ρ, w₁, w₂, φ, _, _, h => by
      have hk : eval I₁ k _ _ = eval I₂ k _ _ := abstraction k ρ φ h
      show QRel τ ρ φ (iterN _ (eval I₁ k _ _) _) (iterN _ (eval I₂ k _ _) _)
      rw [hk]
      exact iterate_rel (QRel τ ρ φ) _ _
        (fun a b hab => abstraction f ρ φ h w₁ w₂ (A.id w₁) (A.id w₂) φ
          (RS.fut_refl φ) a b hab)
        _ _ _ (abstraction x ρ φ h)
  | _, _, .comp τ, .ret t, ρ, w₁, w₂, φ, _, _, h =>
      ⟨RS.bempty, QRel.mono τ ρ (abstraction t ρ φ h) (RS.fut_inl φ RS.bempty)⟩
  | _, _, .comp τ, .bind m k, ρ, w₁, w₂, φ, _, _, h => by
      obtain ⟨ψ, hm⟩ := abstraction m ρ φ h
      obtain ⟨ψ', hk⟩ := abstraction k ρ φ h _ _ _ _ (RS.tensor φ ψ) (RS.fut_inl φ ψ) _ _ hm
      exact ⟨RS.bapp ψ ψ', QRel.mono τ ρ hk (RS.fut_assoc φ ψ ψ')⟩
  | _, _, _, .tlam t, ρ, _, _, φ, _, _, _ => fun σ₁ σ₂ S =>
      abstraction t (ρ.cons σ₁ σ₂ S) φ trivial

/-- **The abstraction theorem at a closed term**, the form the umbral results
use. -/
theorem abstraction_closed {τ : QTy 0} (t : QClosedTm τ) {w₁ w₂ : A.W} (φ : RS.R w₁ w₂) :
    QRel τ (⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩ : KREnv RS I₁ I₂ 0) φ
      (evalC I₁ t w₁) (evalC I₂ t w₂) :=
  abstraction t _ φ trivial

end FreeThms.Kripke
