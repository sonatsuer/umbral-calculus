/-
# The auxiliary umbrae as terms

Rota and Taylor's working notation allocates auxiliary umbrae: a fresh copy of an
umbra, the dot product `n.α`, the composition `β.α`, the singleton umbra `χ`, and
from it the cumulant umbra `χ.α`. In the full language each of these is a **term** of the
language, written against the class `Umbral(K, U, A)` with `mk`. Each is a
monomorphic term (`Kripke.MTm`) in the context `Δ` of the fourteen dictionary
methods. This file defines them and computes their denotations at the moment
dictionary.

## Programs and their shapes

Write `K`, `U`, `A` for the three sorts and `N` for the natural numbers.

* `powT : A → N → A` and `momT : U → N → K`, the moment sequence `n ↦ E[uⁿ]`;
* `newT : U → T U`, the fresh copy `mk (momT u)`;
* `dotConstructedT : N → U → T A`, the sum of `n` fresh copies (constructed);
* `dotSymbolicT : N → U → T A`, one fresh umbra with the moments of `n.α` (symbolic),
  computed by iterated binomial convolution;
* `composeT : U → U → T U`, the composition `β.α`, through the partial Bell
  polynomials and the falling factorials of `β`;
* `singletonT : T U` and `cumulantT : U → T U`.

Binomial convolution is computed without binomial coefficients, by the Leibniz
rule `S(x ⋆ y) = Sx ⋆ y + x ⋆ Sy` for the shift `S`: iteration at the type
`(N → K) → (N → K) → K`. This is Gödel's T at higher type, and it is the only
place where the iterator is used at a function type in an essential way.
-/

import FreeThms.Core.Monomorphic
import FreeThms.Umbral.DotMoments

namespace FreeThms.Umbral.Full

open MvPolynomial (X C rename rename_X)
open FreeThms.Umbral.Restricted (Slot)
open FreeThms.Kripke (QTy QCtx QVar MTm Ren QTyD QEnv)

noncomputable section

variable {k : Type} [CommRing k]

/-! ## The dictionary context -/

/-- The sort of scalars. -/
abbrev tK : QTy 3 := .tvar 2
/-- The sort of umbrae. -/
abbrev tU : QTy 3 := .tvar 1
/-- The sort of umbral polynomials. -/
abbrev tA : QTy 3 := .tvar 0
/-- Sequences of scalars. -/
abbrev tSeq : QTy 3 := .nat ⇛ tK

/-- The context of the fourteen dictionary methods, in the order of `dictTy`:
`zeroK` is outermost and `mk` innermost. -/
def Δ : QCtx 3 :=
  .cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons
    (.cons .nil tK) tK) (tK ⇛ tK ⇛ tK)) (tK ⇛ tK ⇛ tK)) (tK ⇛ tK))
    tA) tA) (tA ⇛ tA ⇛ tA)) (tA ⇛ tA ⇛ tA)) (tA ⇛ tA))
    (tK ⇛ tA)) (tU ⇛ tA)) (tA ⇛ tK)) mkTy

/-- Monomorphic programs over the class. -/
abbrev Prog (Γ : QCtx 3) (τ : QTy 3) : Type := MTm Γ τ

/-- `Γ'` extends `Γ` by finitely many binders. Resolved by instance search, so
that a dictionary method can be named under any number of binders. -/
class Ext (Γ Γ' : QCtx 3) where
  /-- The weakening renaming. -/
  ren : Ren Γ Γ'

instance Ext.refl (Γ : QCtx 3) : Ext Γ Γ := ⟨fun x => x⟩

instance Ext.step (Γ Γ' : QCtx 3) (σ : QTy 3) [Ext Γ Γ'] : Ext Γ (.cons Γ' σ) :=
  ⟨fun x => .succ (Ext.ren x)⟩

section methods

variable {Γ : QCtx 3} [Ext Δ Γ]

/-- A dictionary method, named under binders. -/
abbrev meth {τ : QTy 3} (x : QVar Δ τ) : Prog Γ τ := .var (Ext.ren x)

/-- Application to two arguments. -/
abbrev app2 {Γ : QCtx 3} {τ σ ρ : QTy 3} (f : Prog Γ (τ ⇛ σ ⇛ ρ)) (a : Prog Γ τ)
    (b : Prog Γ σ) : Prog Γ ρ := .app (.app f a) b

def zeroK : Prog Γ tK := meth (Γ := Γ) (τ := tK) (.succ (.succ (.succ (.succ (.succ (.succ
  (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))))
def oneK : Prog Γ tK := meth (Γ := Γ) (τ := tK) (.succ (.succ (.succ (.succ (.succ (.succ
  (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))))))
def addK (a b : Prog Γ tK) : Prog Γ tK := app2 (meth (τ := tK ⇛ tK ⇛ tK) (.succ (.succ (.succ
  (.succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))))) a b
def mulK (a b : Prog Γ tK) : Prog Γ tK := app2 (meth (τ := tK ⇛ tK ⇛ tK) (.succ (.succ (.succ
  (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))))))) a b
def negK (a : Prog Γ tK) : Prog Γ tK := .app (meth (τ := tK ⇛ tK) (.succ (.succ (.succ
  (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))))) a
def zeroA : Prog Γ tA := meth (Γ := Γ) (τ := tA) (.succ (.succ (.succ (.succ (.succ (.succ
  (.succ (.succ .zero))))))))
def oneA : Prog Γ tA := meth (Γ := Γ) (τ := tA) (.succ (.succ (.succ (.succ (.succ (.succ
  (.succ .zero)))))))
def addA (a b : Prog Γ tA) : Prog Γ tA := app2 (meth (τ := tA ⇛ tA ⇛ tA) (.succ (.succ (.succ
  (.succ (.succ (.succ .zero))))))) a b
def mulA (a b : Prog Γ tA) : Prog Γ tA := app2 (meth (τ := tA ⇛ tA ⇛ tA) (.succ (.succ (.succ
  (.succ (.succ .zero)))))) a b
def negA (a : Prog Γ tA) : Prog Γ tA := .app (meth (τ := tA ⇛ tA) (.succ (.succ (.succ
  (.succ .zero))))) a
def constA (a : Prog Γ tK) : Prog Γ tA := .app (meth (τ := tK ⇛ tA) (.succ (.succ (.succ
  .zero)))) a
def injA (a : Prog Γ tU) : Prog Γ tA := .app (meth (τ := tU ⇛ tA) (.succ (.succ .zero))) a
def evalA (a : Prog Γ tA) : Prog Γ tK := .app (meth (τ := tA ⇛ tK) (.succ .zero)) a
def mk (a : Prog Γ tSeq) : Prog Γ (.comp tU) := .app (meth (τ := mkTy) .zero) a

end methods

/-! ## The moment dictionary as an environment -/

/-- The moment dictionary at a world, as an environment for `Δ`. -/
def dictEnv (w : World k) : QEnv (base k) sortEnv Δ w :=
  ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨PUnit.unit, (0 : k)⟩, (1 : k)⟩,
    fun _ _ (x : k) _ _ (y : k) => x + y⟩,
    fun _ _ (x : k) _ _ (y : k) => x * y⟩,
    fun _ _ (x : k) => -x⟩,
    (0 : MvPolynomial (Fin w.size) k)⟩,
    (1 : MvPolynomial (Fin w.size) k)⟩,
    fun _ _ (p : MvPolynomial _ k) _ (σ : Hom _ _) (q : MvPolynomial _ k) =>
      rename σ.toFun p + q⟩,
    fun _ _ (p : MvPolynomial _ k) _ (σ : Hom _ _) (q : MvPolynomial _ k) =>
      rename σ.toFun p * q⟩,
    fun _ _ (p : MvPolynomial _ k) => -p⟩,
    fun _ _ (c : k) => (C c : MvPolynomial _ k)⟩,
    fun _ _ (x : Fin _) => (X x : MvPolynomial _ k)⟩,
    fun (v : World k) _ (p : MvPolynomial (Fin v.size) k) => (Umbral.eval v.mom p : k)⟩,
    momentMk w⟩

/-- The methods of the moment dictionary, as projections of `dictEnv`. -/
@[simp] theorem dictEnv_zeroK (w : World k) :
    (dictEnv w).1.1.1.1.1.1.1.1.1.1.1.1.1.2 = (0 : k) := rfl
@[simp] theorem dictEnv_oneK (w : World k) :
    (dictEnv w).1.1.1.1.1.1.1.1.1.1.1.1.2 = (1 : k) := rfl
@[simp] theorem dictEnv_addK (w : World k) :
    (dictEnv w).1.1.1.1.1.1.1.1.1.1.1.2 = fun _ _ (x : k) _ _ (y : k) => x + y := rfl
@[simp] theorem dictEnv_mulK (w : World k) :
    (dictEnv w).1.1.1.1.1.1.1.1.1.1.2 = fun _ _ (x : k) _ _ (y : k) => x * y := rfl
@[simp] theorem dictEnv_negK (w : World k) :
    (dictEnv w).1.1.1.1.1.1.1.1.1.2 = fun _ _ (x : k) => -x := rfl
@[simp] theorem dictEnv_zeroA (w : World k) :
    (dictEnv w).1.1.1.1.1.1.1.1.2 = (0 : MvPolynomial (Fin w.size) k) := rfl
@[simp] theorem dictEnv_oneA (w : World k) :
    (dictEnv w).1.1.1.1.1.1.1.2 = (1 : MvPolynomial (Fin w.size) k) := rfl
@[simp] theorem dictEnv_addA (w : World k) :
    (dictEnv w).1.1.1.1.1.1.2 = fun _ _ (p : MvPolynomial _ k) _ (σ : Hom _ _) (q : MvPolynomial _ k) => rename σ.toFun p + q := rfl
@[simp] theorem dictEnv_mulA (w : World k) :
    (dictEnv w).1.1.1.1.1.2 = fun _ _ (p : MvPolynomial _ k) _ (σ : Hom _ _) (q : MvPolynomial _ k) => rename σ.toFun p * q := rfl
@[simp] theorem dictEnv_negA (w : World k) :
    (dictEnv w).1.1.1.1.2 = fun _ _ (p : MvPolynomial _ k) => -p := rfl
@[simp] theorem dictEnv_constA (w : World k) :
    (dictEnv w).1.1.1.2 = fun _ _ (c : k) => (C c : MvPolynomial _ k) := rfl
@[simp] theorem dictEnv_injA (w : World k) :
    (dictEnv w).1.1.2 = fun _ _ (x : Fin _) => (X x : MvPolynomial _ k) := rfl
@[simp] theorem dictEnv_evalA (w : World k) :
    (dictEnv w).1.2 = fun (v : World k) _ (p : MvPolynomial (Fin v.size) k) => (Umbral.eval v.mom p : k) := rfl
@[simp] theorem dictEnv_mk (w : World k) :
    (dictEnv w).2 = momentMk w := rfl

/-- **The moment dictionary is natural**: transported along a morphism, it is the
moment dictionary of the target. Only the constants `0` and `1` of the algebra
need an argument, since renaming fixes them. -/
theorem envTr_dictEnv {w v : World k} (h : Hom w v) :
    Kripke.envTr (base k) sortEnv Δ h (dictEnv w) = dictEnv v := by
  have h0 : rename h.toFun (0 : MvPolynomial (Fin w.size) k) = 0 := map_zero _
  have h1 : rename h.toFun (1 : MvPolynomial (Fin w.size) k) = 1 := map_one _
  show (⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨PUnit.unit, _⟩, _⟩, _⟩, _⟩, _⟩, rename h.toFun 0⟩, rename h.toFun 1⟩,
    _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ : QEnv (base k) sortEnv Δ v) = _
  rw [h0, h1]
  rfl

/-- The denotation of a program over `Δ` at the moment dictionary of a world.
A macro, so that statements about it are literally about `Kripke.eval`. -/
macro "⟦" P:term "⟧" w:term:max : term =>
  `(Kripke.eval (base _) (MTm.toQ $P) $w (dictEnv $w))

/-- `let x = P in body`: a program over `Δ` made available to another, as a
λ-bound variable. -/
def letP {σ τ : QTy 3} (P : Prog Δ σ) (body : Prog (.cons Δ σ) τ) : Prog Δ τ :=
  .app (.lam body) P

/-- `let x = P; y = Q in body`, for two programs over `Δ`. -/
def let2P {σ σ' τ : QTy 3} (P : Prog Δ σ) (Q : Prog Δ σ')
    (body : Prog (.cons (.cons Δ σ) σ') τ) : Prog Δ τ :=
  .app (.app (.lam (.lam body)) P) Q

/-- `let` for three programs over `Δ`. -/
def let3P {σ₁ σ₂ σ₃ τ : QTy 3} (P₁ : Prog Δ σ₁) (P₂ : Prog Δ σ₂) (P₃ : Prog Δ σ₃)
    (body : Prog (.cons (.cons (.cons Δ σ₁) σ₂) σ₃) τ) : Prog Δ τ :=
  .app (.app (.app (.lam (.lam (.lam body))) P₁) P₂) P₃

/-- `let` for four programs over `Δ`. -/
def let4P {σ₁ σ₂ σ₃ σ₄ τ : QTy 3} (P₁ : Prog Δ σ₁) (P₂ : Prog Δ σ₂) (P₃ : Prog Δ σ₃)
    (P₄ : Prog Δ σ₄) (body : Prog (.cons (.cons (.cons (.cons Δ σ₁) σ₂) σ₃) σ₄) τ) : Prog Δ τ :=
  .app (.app (.app (.app (.lam (.lam (.lam (.lam body)))) P₁) P₂) P₃) P₄

omit [CommRing k] in
@[simp] theorem Hom.id_comp' {w v : World k} (σ : Hom w v) : (Hom.id w).comp σ = σ := rfl
omit [CommRing k] in
@[simp] theorem Hom.comp_id' {w v : World k} (σ : Hom w v) : σ.comp (Hom.id v) = σ := rfl

/-- Unfold the denotation of a program at the moment dictionary: evaluate, look
the methods up, and collapse the transports along identities. -/
macro "unfold_sem" : tactic =>
  `(tactic| (simp only [Kripke.MTm.toQ, Kripke.eval, letP, let2P, let3P, let4P, meth, app2, Ext.ren, Kripke.lookup,
      Kripke.envTr, Kripke.qtr, Kripke.str, envTr_dictEnv, trS, Hom.id_toFun, Hom.id_comp',
      Hom.comp_id', MvPolynomial.rename_id_apply, id_eq, zeroK, oneK, addK, mulK, negK, zeroA, oneA,
      addA, mulA, negA, constA, injA, evalA, mk, dictEnv_zeroK, dictEnv_oneK, dictEnv_addK, dictEnv_mulK, dictEnv_negK, dictEnv_zeroA, dictEnv_oneA, dictEnv_addA, dictEnv_mulA, dictEnv_negA, dictEnv_constA, dictEnv_injA, dictEnv_evalA, dictEnv_mk]))

/-! ## Powers, moments and the fresh copy -/

open Kripke.MTm in
/-- `λp n. pⁿ`, by iteration. -/
def powT : Prog Δ (tA ⇛ .nat ⇛ tA) :=
  lam (lam (iter (var .zero) (lam (mulA (var .zero) (var (.succ (.succ .zero))))) oneA))

open Kripke.MTm in
/-- `λu n. E[uⁿ]`: the moment sequence of an umbra. -/
def momT : Prog Δ (tU ⇛ tSeq) :=
  letP powT (lam (lam (evalA (app2 (var (.succ (.succ .zero))) (injA (var (.succ .zero)))
    (var .zero)))))

open Kripke.MTm in
/-- `λu. mk (momT u)`: **the fresh copy** `new u`, a fresh umbra similar to `u`. -/
def newT : Prog Δ (tU ⇛ .comp tU) :=
  letP momT (lam (mk (.app (var (.succ .zero)) (var .zero))))

theorem iterN_mul_right {R : Type} [Monoid R] (p : R) :
    ∀ (n : ℕ) (q : R), Kripke.iterN (fun x => x * p) n q = q * p ^ n
  | 0, q => by rw [pow_zero, mul_one]; rfl
  | n + 1, q => by rw [Kripke.iterN, iterN_mul_right p n, mul_assoc, ← pow_succ']

omit [CommRing k] in
@[simp] theorem Hom.comp_toFun {u v x : World k} (σ : Hom u v) (τ : Hom v x) :
    (σ.comp τ).toFun = τ.toFun ∘ σ.toFun := rfl

@[simp] theorem sem_pow {w v v' : World k} (h : Hom w v) (p : MvPolynomial (Fin v.size) k)
    (h' : Hom v v') (n : ℕ) :
    (⟦powT⟧ w) v h p v' h' n = rename h'.toFun p ^ n := by
  simp only [powT]
  unfold_sem
  rw [iterN_mul_right, one_mul]

@[simp] theorem sem_mom {w v v' : World k} (h : Hom w v) (x : Fin v.size) (h' : Hom v v') :
    (⟦momT⟧ w) v h x v' h' = momOf v' (h'.toFun x) := by
  funext n
  simp only [momT]
  unfold_sem
  simp only [sem_pow, rename_X, Hom.id_toFun, id_eq]

/-- **The fresh copy.** `new u` allocates one fresh name, whose moments are those
of `u`, and returns it. -/
theorem sem_new {w v : World k} (h : Hom w v) (x : Fin v.size) :
    (⟦newT⟧ w) v h x = ⟨World.single (momOf v x), Fin.natAdd v.size 0⟩ := by
  simp only [newT]
  unfold_sem
  simp only [momentMk]
  rw [sem_mom]
  rfl

/-! ## The dot product, constructed -/

open Kripke.MTm in
/-- `λn u. α₁ ← new u; …; αₙ ← new u; return (α₁ + ⋯ + αₙ)`: **the constructed
dot product** `n.α`, by iteration on `n`. -/
def dotConstructedT : Prog Δ (.nat ⇛ tU ⇛ .comp tA) :=
  -- context: new, n, u
  letP newT (lam (lam (iter (var (.succ .zero))
    -- context: new, n, u, c
    (lam (bind (var .zero)
      -- context: new, n, u, c, p
      (lam (bind (.app (var (.succ (.succ (.succ (.succ .zero))))) (var (.succ (.succ .zero))))
        -- context: new, n, u, c, p, g
        (lam (ret (addA (var (.succ .zero)) (injA (var .zero)))))))))
    (ret zeroA))))

theorem iterN_succ' {X : Type} (f : X → X) : ∀ (n : ℕ) (x : X),
    Kripke.iterN f (n + 1) x = f (Kripke.iterN f n x)
  | 0, _ => rfl
  | n + 1, x => iterN_succ' f n (f x)

/-- Induction along an iteration. -/
theorem iterN_induction {X : Type} (f : X → X) (P : ℕ → X → Prop) (x : X) (h0 : P 0 x)
    (hs : ∀ i c, P i c → P (i + 1) (f c)) : ∀ n, P n (Kripke.iterN f n x)
  | 0 => h0
  | n + 1 => by rw [iterN_succ']; exact hs n _ (iterN_induction f P x h0 hs n)

/-- What the constructed dot product computes after `i` steps: a block of `i`
names, and the sum of those names, which has the moments of `i.α`. -/
def DotInv (w : World k) (s : ℕ → k) (i : ℕ)
    (c : Σ B : World k, MvPolynomial (Fin (w.size + B.size)) k) : Prop :=
  c.1.size = i ∧ c.2 = rename (Fin.natAdd w.size) (sumX c.1.size) ∧
    ∀ j, Umbral.eval c.1.mom (sumX c.1.size ^ j) = dotMoments s i j

/-- A computation returning a polynomial in its fresh block alone, with moments
`a`. -/
def MomInv (w : World k) (a : ℕ → k)
    (c : Σ B : World k, MvPolynomial (Fin (w.size + B.size)) k) : Prop :=
  ∃ q : MvPolynomial (Fin c.1.size) k,
    c.2 = rename (Fin.natAdd w.size) q ∧ ∀ j, Umbral.eval c.1.mom (q ^ j) = a j

/-- One step of the constructed dot product: allocate a fresh copy `N` in the
world extended by the block so far, and add it to the running sum. -/
theorem dotInv_step (w : World k) (x : Fin w.size) (i : ℕ) (B : World k) (hB : B.size = i)
    (hq : ∀ j, Umbral.eval B.mom (sumX B.size ^ j) = dotMoments (momOf w x) i j)
    (N : Σ B' : World k, Fin (w.size + B.size + B'.size))
    (hN : N = ⟨World.single (momOf (w.append B) ((Hom.inl w B).toFun x)), Fin.natAdd _ 0⟩) :
    DotInv w (momOf w x) (i + 1)
      ⟨B.append (N.1.append World.empty),
        rename (Hom.assoc w B (N.1.append World.empty)).toFun
          (rename (Hom.assoc (w.append B) N.1 World.empty).toFun
            (rename (Hom.inl ((w.append B).append N.1) World.empty).toFun
              (rename (Hom.inl (w.append B) N.1).toFun (rename (Fin.natAdd w.size) (sumX B.size))
                + X N.2)))⟩ := by
  subst hN
  dsimp only
  set s' := momOf (w.append B) ((Hom.inl w B).toFun x) with hs'
  have hs : s' = momOf w x := momOf_hom (Hom.inl w B) x
  set B₁ : World k := (World.single s').append World.empty
  have hsum : (sumX (B.size + B₁.size) : MvPolynomial _ k) = rename (Fin.castAdd B₁.size) (sumX B.size)
      + rename (Fin.natAdd B.size) (X ((Hom.inl (World.single s') World.empty).toFun 0)) := by
    rw [sumX, Fin.sum_univ_add, sumX, map_sum]
    simp only [rename_X]
    congr 1
    refine Finset.sum_eq_single _ (fun b _ hb => absurd (Fin.ext ?_) hb)
      (fun h => absurd (Finset.mem_univ _) h)
    have h1 := b.isLt
    have h2 := ((Hom.inl (World.single s') World.empty).toFun 0).isLt
    change b.val < 1 + 0 at h1
    change _ < 1 + 0 at h2
    omega
  refine ⟨by simp [World.empty, hB], ?_, ?_⟩
  · change _ = rename (Fin.natAdd w.size) (sumX (B.size + B₁.size))
    rw [hsum]
    simp only [map_add, MvPolynomial.rename_rename, rename_X]
    congr 1
  · intro j
    change Umbral.eval (B.append B₁).mom (sumX (B.size + B₁.size) ^ j) = _
    rw [hsum, eval_blocks_pow]
    have hm : (fun i => Umbral.eval B₁.mom (X ((Hom.inl (World.single s') World.empty).toFun 0) ^ i))
        = momOf w x := by
      funext i
      rw [← momOf, momOf_hom, momOf_single _ (by simp [hs', momOf]), hs]
    rw [hm]
    exact congrArg (fun a => conv a (momOf w x) j) (funext hq)

/-- **The constructed dot product.** `dotConstructed n u` allocates a block of `n`
names, fresh copies of `u`, and returns their sum, whose moments are the moments
of `n.α`. -/
theorem sem_dotConstructed {w v v' : World k} (h : Hom w v) (n : ℕ) (h' : Hom v v') (x : Fin v'.size) :
    DotInv v' (momOf v' x) n ((⟦dotConstructedT⟧ w) v h n v' h' x) := by
  simp only [dotConstructedT]
  unfold_sem
  refine iterN_induction _ (DotInv v' (momOf v' x)) _ ?_ ?_ n
  · refine ⟨rfl, ?_, fun j => ?_⟩
    · change _ = rename (Fin.natAdd v'.size) (sumX 0 : MvPolynomial (Fin 0) k)
      simp [sumX]
      rfl
    · change Umbral.eval _ ((sumX 0 : MvPolynomial (Fin 0) k) ^ j) = _
      rcases eq_or_ne j 0 with rfl | hj
      · simp [dotMoments]
        exact Umbral.eval_one _
      · simp [sumX, dotMoments, hj, zero_pow hj]
        exact Umbral.eval_zero _
  · rintro i ⟨B, p⟩ ⟨hB, hp, hq⟩
    change B.size = i at hB
    change ∀ j, Umbral.eval B.mom (sumX B.size ^ j) = _ at hq
    have hp' : p = rename (Fin.natAdd v'.size) (sumX B.size : MvPolynomial (Fin B.size) k) := hp
    clear hp
    subst hp'
    exact dotInv_step v' x i B hB hq _ (sem_new _ _)

/-! ## The dot product, symbolic -/

open Kripke.MTm in
/-- `λx j. x (j + 1)`: the shift of a sequence. -/
def shiftT : Prog Δ (tSeq ⇛ tSeq) :=
  lam (lam (.app (var (.succ .zero)) (succ (var .zero))))

/-- The type of a binary operation on sequences with a scalar result. -/
abbrev tConvF : QTy 3 := tSeq ⇛ tSeq ⇛ tK

open Kripke.MTm in
/-- `λj x y. (x ⋆ y)ⱼ`: **binomial convolution**, without binomial coefficients,
by the Leibniz rule `(x ⋆ y)ⱼ₊₁ = (Sx ⋆ y)ⱼ + (x ⋆ Sy)ⱼ`. The iteration is at
the type `(N → K) → (N → K) → K`. -/
def convT : Prog Δ (.nat ⇛ tConvF) :=
  -- context: shift, j
  letP shiftT (lam (iter (var .zero)
    -- context: shift, j, G, x, y
    (lam (lam (lam (addK
      (app2 (var (.succ (.succ .zero))) (.app (var (.succ (.succ (.succ (.succ .zero)))))
        (var (.succ .zero))) (var .zero))
      (app2 (var (.succ (.succ .zero))) (var (.succ .zero))
        (.app (var (.succ (.succ (.succ (.succ .zero))))) (var .zero)))))))
    -- context: shift, j, x, y
    (lam (lam (mulK (.app (var (.succ .zero)) zero) (.app (var .zero) zero))))))

@[simp] theorem sem_shift {w v : World k} (h : Hom w v) (f : Val tSeq v) :
    (⟦shiftT⟧ w) v h f = fun v' h' j => f v' h' (j + 1) := by
  funext v' h' j
  simp only [shiftT]
  unfold_sem

/-- **Binomial convolution, as computed by the term**, at any later worlds. -/
theorem sem_conv {w v v' v'' : World k} (h : Hom w v) (j : ℕ) (h' : Hom v v') (f : Val tSeq v')
    (h'' : Hom v' v'') (g : Val tSeq v'') :
    (⟦convT⟧ w) v h j v' h' f v'' h'' g = conv (f v'' h'') (g v'' (Hom.id v'')) j := by
  simp only [convT]
  unfold_sem
  simp only [sem_shift]
  refine iterN_induction _ (fun j (G : Val tConvF v) => ∀ (v' : World k) (h' : Hom v v')
    (f : Val tSeq v') (v'' : World k) (h'' : Hom v' v'') (g : Val tSeq v''),
      G v' h' f v'' h'' g = conv (f v'' h'') (g v'' (Hom.id v'')) j) _ ?_ ?_ j v' h' f v'' h'' g
  · intro v' h' f v'' h'' g
    simp [conv]
  · intro i G hG v' h' f v'' h'' g
    simp only [hG, Hom.comp_id', conv_succ]

open Kripke.MTm in
/-- `λj. [j = 0]`: the moments of the umbra `0`. -/
def deltaT : Prog Δ tSeq :=
  lam (iter (var .zero) (lam zeroK) oneK)

open Kripke.MTm in
/-- `λn a. a ⋆ ⋯ ⋆ a` (`n` factors): **the moments of `n.α`**, from the moments
`a` of `α`, by iterated binomial convolution. -/
def dotMomentsT : Prog Δ (.nat ⇛ tSeq ⇛ tSeq) :=
  -- context: conv, delta, n, a
  let2P convT deltaT (lam (lam (iter (var (.succ .zero))
    -- context: conv, delta, n, a, T, j
    (lam (lam (.app (app2 (var (.succ (.succ (.succ (.succ (.succ .zero)))))) (var .zero)
      (var (.succ .zero))) (var (.succ (.succ .zero))))))
    (var (.succ (.succ .zero))))))

theorem iterN_const_zero (j : ℕ) :
    Kripke.iterN (fun _ : k => (0 : k)) j 1 = if j = 0 then 1 else 0 := by
  cases j with
  | zero => rfl
  | succ j =>
    simp only [Nat.succ_ne_zero, if_false]
    induction j with
    | zero => rfl
    | succ j ih => exact ih

@[simp] theorem sem_delta {w v : World k} (h : Hom w v) (j : ℕ) :
    (⟦deltaT⟧ w) v h j = dotMoments (fun _ => (0 : k)) 0 j := by
  simp only [deltaT]
  unfold_sem
  exact iterN_const_zero j

/-- **The moments of `n.α`, as computed by the term**, for a sequence argument
whose value does not depend on the world it is read at. -/
theorem sem_dotMoments {w v : World k} (h : Hom w v) (n : ℕ) {v' : World k} (h' : Hom v v')
    (a : Val tSeq v') (s : ℕ → k) (ha : ∀ (u : World k) (g : Hom v' u), a u g = s)
    {v'' : World k} (h'' : Hom v' v'') : (⟦dotMomentsT⟧ w) v h n v' h' a v'' h'' = dotMoments s n := by
  simp only [dotMomentsT]
  unfold_sem
  simp only [sem_conv, sem_delta, Hom.comp_id', ha]
  refine iterN_induction _ (fun i (T : Val tSeq v') => ∀ (u : World k) (g : Hom v' u),
    T u g = dotMoments s i) _ (fun _ _ => funext fun _ => rfl) ?_ n v'' h''
  intro i T hT u g
  funext j
  simp only [hT]
  rfl

open Kripke.MTm in
/-- `λn u. γ ← mk (dotMoments n (mom u)); return γ`: **the symbolic dot product**
`n.α`, one fresh umbra with the moments of `n.α`. -/
def dotSymbolicT : Prog Δ (.nat ⇛ tU ⇛ .comp tA) :=
  -- context: dotMoments, mom, n, u
  let2P dotMomentsT momT (lam (lam (bind
    (mk (app2 (var (.succ (.succ (.succ .zero)))) (var (.succ .zero))
      (.app (var (.succ (.succ .zero))) (var .zero))))
    -- context: dotMoments, mom, n, u, g
    (lam (ret (injA (var .zero)))))))

/-- A computation that allocates exactly one fresh name, with moments `a`, and
returns it. -/
def OneName (w : World k) (a : ℕ → k)
    (c : Σ B : World k, MvPolynomial (Fin (w.size + B.size)) k) : Prop :=
  c.1.size = 1 ∧ ∃ i : Fin c.1.size,
    c.2 = rename (Fin.natAdd w.size) (X i) ∧ ∀ j, Umbral.eval c.1.mom (X i ^ j) = a j

/-- The block of one fresh name with moments `d`, returned as a polynomial:
what `γ ← mk d; return γ` computes. -/
theorem mk_ret (w : World k) (d : ℕ → k) (hd : d 0 = 1)
    (N : Σ B : World k, Fin (w.size + B.size)) (hN : N = ⟨World.single d, Fin.natAdd w.size 0⟩) :
    OneName w d ⟨N.1.append World.empty,
        rename (Hom.assoc w N.1 World.empty).toFun
          (rename (Hom.inl (w.append N.1) World.empty).toFun (X N.2))⟩ := by
  subst hN
  refine ⟨rfl, (Hom.inl (World.single d) World.empty).toFun 0, ?_, fun j => ?_⟩
  · simp only [rename_X]
    exact congrArg X (Fin.ext (by simp [Hom.assoc, Hom.inl]))
  · rw [← momOf, momOf_hom, momOf_single _ hd]

/-- **The symbolic dot product.** `dotSymbolic n u` allocates one fresh name and
returns it; its moments are the moments of `n.α`. -/
theorem sem_dotSymbolic {w v v' : World k} (h : Hom w v) (n : ℕ) (h' : Hom v v') (x : Fin v'.size) :
    OneName v' (dotMoments (momOf v' x) n) ((⟦dotSymbolicT⟧ w) v h n v' h' x) := by
  have hs : momOf v' x 0 = 1 := by simp [momOf]
  have hd := sem_dotMoments (w := w) (h.comp (h'.comp (Hom.id v'))) n (Hom.id v')
    ((⟦momT⟧ w) v' (h.comp (h'.comp (Hom.id v'))) x) (momOf v' x)
    (fun u g => by rw [sem_mom, momOf_hom]) (Hom.id v')
  simp only [dotSymbolicT]
  unfold_sem
  rw [← hd]
  exact mk_ret v' _ (hd ▸ dotMoments_zero _ hs n) _ rfl

end

end FreeThms.Umbral.Full
