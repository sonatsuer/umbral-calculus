/-
# Conservativity of the full language over the restricted language

Terms of the restricted language embed into the full language. This file proves
that the embedding preserves meaning. At every world `w`, the Kripke denotation of
an embedded term of the restricted language simulates its set-theoretic
denotation in the interpretation that reads every base sort at `w`. Hence every
result about denotations in the restricted language holds verbatim inside the
full language. This is the bridge between Chapters 2 and 3 of the write-up.

## The simulation

At a base sort, the simulation is equality. At a function type, it compares the
Kripke function's component at the identity morphism with the set function. Two
laws make that comparison stable: transport along an identity is the identity
(`BaseI.tr_id`), and the identity is a left unit (`AllocStr.id_comp`).

Type variables carry simulation relations, in the manner of a logical relation.
The restricted language instantiates a type variable at a simple type, and the
full language at its embedding. The two type environments are therefore related by a relation, not
equal, which avoids a cast.
-/

import FreeThms.Core.Kripke

namespace FreeThms.Kripke

open FreeThms

variable {A : AllocStr} {B : Type}

/-! ## The embedding -/

/-- Simple types of the restricted language are those of the full language. -/
def STy.embed : Ty B → STy B
  | .base b => .base b
  | .arrow τ σ => .arrow (STy.embed τ) (STy.embed σ)

/-- Types of the restricted language embed into types of the full language. -/
def QTy.embed : {n : Nat} → PTy n → QTy n
  | _, .tvar i => .tvar i
  | _, .arrow τ σ => .arrow (QTy.embed τ) (QTy.embed σ)
  | _, .all τ => .all (QTy.embed τ)

/-- Contexts of the restricted language embed into contexts of the full language. -/
def QCtx.embed {n : Nat} : PCtx n → QCtx n
  | .nil => .nil
  | .cons Γ τ => .cons (QCtx.embed Γ) (QTy.embed τ)

/-- Variables of the restricted language embed into variables of the full language. -/
def QVar.embed {n : Nat} : {Γ : PCtx n} → {τ : PTy n} → PVar Γ τ →
    QVar (QCtx.embed Γ) (QTy.embed τ)
  | _, _, .zero => .zero
  | _, _, .succ x => .succ (QVar.embed x)

/-- Terms of the restricted language embed into terms of the full language. -/
def QTm.embed : {n : Nat} → {Γ : PCtx n} → {τ : PTy n} →
    PTm Γ τ → QTm (QCtx.embed Γ) (QTy.embed τ)
  | _, _, _, .var x => .var (QVar.embed x)
  | _, _, _, .lam t => .lam (QTm.embed t)
  | _, _, _, .app f a => .app (QTm.embed f) (QTm.embed a)
  | _, _, _, .tlam t => .tlam (QTm.embed t)

/-! ## The simulation at a world -/

variable (I : BaseI A B) (w : A.W)

/-- The interpretation of the restricted language that reads every base sort at the world `w`. -/
abbrev atWorld : B → Type := fun b => I.carrier b w

/-- The simulation at a simple type. -/
def SSim : (σ : Ty B) → SD I (STy.embed σ) w → TyD (atWorld I w) σ → Prop
  | .base _ => fun x y => x = y
  | .arrow τ σ => fun f g => ∀ x y, SSim τ x y → SSim σ (f w (A.id w) x) (g y)

/-- The simulation is stable under transport along the identity. -/
theorem SSim.tr_id : (σ : Ty B) → {x : SD I (STy.embed σ) w} → {y : TyD (atWorld I w) σ} →
    SSim I w σ x y → SSim I w σ (str I (STy.embed σ) (A.id w) x) y
  | .base b, x, _, h => Eq.trans (I.tr_id (w := w) b x) h
  | .arrow _ _, f, _, h => by
      intro a b hab
      show SSim I w _ (f w (A.comp (A.id w) (A.id w)) a) _
      rw [A.id_comp]; exact h a b hab

/-- A simulation environment: for each type variable, an instantiation in the full
language, an instantiation in the restricted language, and a relation between
them that is stable under transport along the identity. -/
structure SimEnv (n : Nat) where
  /-- The instantiation of each type variable in the full language. -/
  l : Fin n → STy B
  /-- The instantiation of each type variable in the restricted language. -/
  r : Fin n → Ty B
  /-- The simulation carried at each type variable. -/
  rel : (i : Fin n) → SD I (l i) w → TyD (atWorld I w) (r i) → Prop
  /-- Stability under transport along the identity. -/
  rel_tr : ∀ (i : Fin n) {x y}, rel i x y → rel i (str I (l i) (A.id w) x) y

/-- Extend a simulation environment by the embedding of a simple type. -/
def SimEnv.cons {n : Nat} (ε : SimEnv I w n) (σ : Ty B) : SimEnv I w (n + 1) where
  l := scons (STy.embed σ) ε.l
  r := scons σ ε.r
  rel := fun i => match i with
    | ⟨0, _⟩ => SSim I w σ
    | ⟨j + 1, h⟩ => ε.rel ⟨j, Nat.lt_of_succ_lt_succ h⟩
  rel_tr := fun i => match i with
    | ⟨0, _⟩ => fun h => SSim.tr_id I w σ h
    | ⟨j + 1, h⟩ => fun hxy => ε.rel_tr ⟨j, Nat.lt_of_succ_lt_succ h⟩ hxy

/-- The simulation at a type of the restricted language. -/
def QSim : {n : Nat} → (τ : PTy n) → (ε : SimEnv I w n) →
    QTyD I (QTy.embed τ) ε.l w → PTyD (atWorld I w) τ ε.r → Prop
  | _, .tvar i, ε => ε.rel i
  | _, .arrow τ σ, ε => fun f g => ∀ x y, QSim τ ε x y → QSim σ ε (f w (A.id w) x) (g y)
  | _, .all τ, ε => fun f g => ∀ σ : Ty B, QSim τ (SimEnv.cons I w ε σ) (f (STy.embed σ)) (g σ)

/-- The simulation is stable under transport along the identity. -/
theorem QSim.tr_id : {n : Nat} → (τ : PTy n) → (ε : SimEnv I w n) →
    {x : QTyD I (QTy.embed τ) ε.l w} → {y : PTyD (atWorld I w) τ ε.r} →
    QSim I w τ ε x y → QSim I w τ ε (qtr I (QTy.embed τ) ε.l (A.id w) x) y
  | _, .tvar i, ε, _, _, h => ε.rel_tr i h
  | _, .arrow _ _, _, f, _, h => by
      intro a b hab
      show QSim I w _ _ (f w (A.comp (A.id w) (A.id w)) a) _
      rw [A.id_comp]; exact h a b hab
  | _, .all τ, ε, _, _, h => fun σ => QSim.tr_id τ (SimEnv.cons I w ε σ) (h σ)

/-- Simulated environments. -/
def EnvSim {n : Nat} (ε : SimEnv I w n) : (Γ : PCtx n) →
    QEnv I ε.l (QCtx.embed Γ) w → PEnv (atWorld I w) ε.r Γ → Prop
  | .nil => fun _ _ => True
  | .cons Γ τ => fun e₁ e₂ => EnvSim ε Γ e₁.1 e₂.1 ∧ QSim I w τ ε e₁.2 e₂.2

theorem EnvSim.tr_id {n : Nat} (ε : SimEnv I w n) : (Γ : PCtx n) →
    {e₁ : QEnv I ε.l (QCtx.embed Γ) w} → {e₂ : PEnv (atWorld I w) ε.r Γ} →
    EnvSim I w ε Γ e₁ e₂ → EnvSim I w ε Γ (envTr I ε.l (QCtx.embed Γ) (A.id w) e₁) e₂
  | .nil, _, _, _ => trivial
  | .cons Γ τ, _, _, h => ⟨EnvSim.tr_id ε Γ h.1, QSim.tr_id I w τ ε h.2⟩

theorem EnvSim.lookup {n : Nat} (ε : SimEnv I w n) : {Γ : PCtx n} → {τ : PTy n} →
    (x : PVar Γ τ) → {e₁ : QEnv I ε.l (QCtx.embed Γ) w} → {e₂ : PEnv (atWorld I w) ε.r Γ} →
    EnvSim I w ε Γ e₁ e₂ →
      QSim I w τ ε (Kripke.lookup I ε.l (QVar.embed x) e₁) (PEnv.lookup (atWorld I w) ε.r x e₂)
  | _, _, .zero, _, _, h => h.2
  | _, _, .succ x, _, _, h => EnvSim.lookup ε x h.1

/--
**Conservativity.** At every world, the Kripke denotation of an embedded term of
the restricted language simulates its denotation in the restricted language, in
the interpretation that reads every base sort at that world.
-/
theorem conservative :
    {n : Nat} → {Γ : PCtx n} → {τ : PTy n} → (t : PTm Γ τ) →
      (ε : SimEnv I w n) → {e₁ : QEnv I ε.l (QCtx.embed Γ) w} →
      {e₂ : PEnv (atWorld I w) ε.r Γ} → EnvSim I w ε Γ e₁ e₂ →
      QSim I w τ ε (eval I (QTm.embed t) w e₁) (peval (atWorld I w) t e₂)
  | _, _, _, .var x, ε, _, _, h => EnvSim.lookup I w ε x h
  | _, Γ, _, .lam t, ε, _, _, h => fun _ _ hxy =>
      conservative t ε ⟨EnvSim.tr_id I w ε Γ h, hxy⟩
  | _, _, _, .app f a, ε, _, _, h => conservative f ε h _ _ (conservative a ε h)
  | _, _, _, .tlam t, ε, _, _, _ => fun σ => conservative t (SimEnv.cons I w ε σ) trivial

/-- The empty simulation environment. -/
def SimEnv.nil : SimEnv I w 0 where
  l := fun i => i.elim0
  r := fun i => i.elim0
  rel := fun i => i.elim0
  rel_tr := fun i => i.elim0

/-- **Conservativity at a closed term.** -/
theorem conservative_closed {τ : PTy 0} (t : PClosedTm τ) :
    QSim I w τ (SimEnv.nil I w) (evalC I (QTm.embed t) w) (pevalC (atWorld I w) t) :=
  conservative I w t (SimEnv.nil I w) trivial

end FreeThms.Kripke
