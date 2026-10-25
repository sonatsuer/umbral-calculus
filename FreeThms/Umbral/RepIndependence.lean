/-
# Representation independence

The relational payoff of the full language (write-up, Chapter 3).

* `repind` — the general form. A **context** is a closed term of type
  `∀K U A. Umbral(K, U, A) ⇒ σ → U → T K`: it receives an implementation of an
  interface `σ` and an umbra. Two implementations related by the logical relation
  at the identity world relation give every context the same scalar value. This
  is the Kripke abstraction theorem, applied once.
* `WRel.ofOne` — the world relations that do the work. Out of a block with a
  single name `γ`, the algebra map `γ ↦ q` preserves the evaluation as soon as
  `q` has the moments of `γ`. It is not a renaming: `q` may be any polynomial,
  for instance a sum of `n` fresh names.
* **The dot product** (`repind_dot`): no context distinguishes the symbolic dot product, one
  fresh name with the moments of `n.α`, from the constructed one, `n` fresh
  copies summed.
* **The fresh copy** (`repind_new`): no context distinguishes `new` from an implementation
  that allocates an unused umbra first. Only the moments of an auxiliary umbra
  are observable, not its name nor what else was allocated.
* **The composition of a sum** (`repind_composeSum`): no context distinguishes
  `β ← new b; β' ← new b'; (β + β').a` from
  `β ← new b; β' ← new b'; δ ← β.a; δ' ← β'.a; return (δ + δ')`. The relation is
  built along the binds (`bindUA_rel`); its last step needs distributivity
  (`Umbral/Distributivity.lean`) and uncorrelation of the two fresh copies.
* **The Sheffer identity at umbral arguments** (`sheffer`), from distributivity
  and uncorrelation.
-/

import FreeThms.Umbral.Composition
import FreeThms.Umbral.Distributivity

namespace FreeThms.Umbral.Full

open MvPolynomial (X C rename rename_X)
open FreeThms.Umbral.Restricted (Slot)
open FreeThms.Kripke (QTy QCtx QVar MTm QTyD QEnv QClosedTm evalC abstraction_closed)

noncomputable section

variable {k : Type} [CommRing k]

/-! ## World relations out of a one-name block -/

/-- In a world with one name `i`, every monomial is a power of `X i`. -/
theorem monomial_one_name {B : World k} (i : Fin B.size) (hi : ∀ j, j = i)
    (d : Fin B.size →₀ ℕ) (c : k) :
    MvPolynomial.monomial d c = C c * X i ^ d i := by
  rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Fintype.prod_eq_single i (fun j hj => absurd (hi j) hj)]

/-- **The world relation `γ ↦ q`** out of a block whose only name is `γ`, for
any polynomial `q` with the moments of `γ`. -/
def WRel.ofOne (B₁ B₂ : World k) (hB : B₁.size = 1) (i : Fin B₁.size)
    (q : MvPolynomial (Fin B₂.size) k)
    (hq : ∀ j, Umbral.eval B₂.mom (q ^ j) = Umbral.eval B₁.mom (X i ^ j)) : WRel B₁ B₂ where
  toAlgHom := MvPolynomial.aeval fun _ => q
  eval_eq := by
    have hi : ∀ j, j = i := fun j => Fin.ext (by have := j.isLt; have := i.isLt; omega)
    intro p
    induction p using MvPolynomial.induction_on' with
    | monomial d c =>
      rw [monomial_one_name i hi, map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
        MvPolynomial.algebraMap_eq, eval_C_mul, eval_C_mul, hq]
    | add p p' hp hp' => rw [map_add, eval_add, eval_add, hp, hp']

@[simp] theorem WRel.ofOne_X (B₁ B₂ : World k) (hB : B₁.size = 1) (i : Fin B₁.size)
    (q : MvPolynomial (Fin B₂.size) k) (hq) (j : Fin B₁.size) :
    (WRel.ofOne B₁ B₂ hB i q hq).toAlgHom (X j) = q := by
  simp [WRel.ofOne]

/-- Related names have the same moments. -/
theorem momOf_rel {w₁ w₂ : World k} (φ : WRel w₁ w₂) {x : Fin w₁.size} {y : Fin w₂.size}
    (hxy : φ.toAlgHom (X x) = X y) : momOf w₁ x = momOf w₂ y := by
  funext j
  rw [momOf, momOf, ← φ.eval_eq, map_pow, hxy]

/-! ## Contexts, and the general theorem -/

/-- A **context** for an interface `σ`: a closed term of type
`∀K U A. Umbral(K, U, A) ⇒ σ → U → T K`. -/
abbrev CtxTerm (σ : QTy 3) : Type := QClosedTm (quantTy (σ ⇛ tU ⇛ .comp tK))

/-- The value of a context at the moment dictionary of a world, an
implementation of the interface, and a name. -/
def denCtx {σ : QTy 3} (Cx : CtxTerm σ) (w : World k) (impl : Val σ w) (x : Fin w.size) :
    Σ _ : World k, k :=
  (applyDict w (evalC (base k) Cx w (.base .K) (.base .U) (.base .A)))
    w (Hom.id w) impl w (Hom.id w) x

/-- **Representation independence, in general.** Two implementations of an
interface that are related by the logical relation at the identity world
relation give every context the same scalar value. -/
theorem repind {σ : QTy 3} (Cx : CtxTerm σ) (w : World k) (impl₁ impl₂ : Val σ w)
    (h : Related σ (WRel.id w) impl₁ impl₂) (x : Fin w.size) :
    (denCtx Cx w impl₁ x).2 = (denCtx Cx w impl₂ x).2 := by
  have hC := abstraction_closed (A := alloc k) (RS := rel k) (I₁ := base k) (I₂ := base k) Cx (WRel.id w)
  have hd := applyDict_rel (WRel.id w) (hC (.base .K) (.base .K) relK (.base .U) (.base .U) relU
    (.base .A) (.base .A) relA)
  obtain ⟨_, hψ⟩ := hd w w (Hom.id w) (Hom.id w) (WRel.id w) (Fut.refl _) impl₁ impl₂ h
    w w (Hom.id w) (Hom.id w) (WRel.id w) (Fut.refl _) x x rfl
  exact hψ

/-! ## Representation independence of the dot product -/

/-- The interface of the dot product, `N → U → T A`. -/
abbrev dotTy : QTy 3 := .nat ⇛ tU ⇛ .comp tA

/-- **The two dot products are related** at every world relation. Related
arguments have the same moments. The symbolic implementation allocates one name
`γ`; the constructed one returns the sum `q` of its `n` fresh names, which has
the moments of `γ`. The witness is `WRel.ofOne`, the world relation `γ ↦ q`. -/
theorem dot_rel {w₁ w₂ : World k} (φ : WRel w₁ w₂) : Related dotTy φ (⟦dotSymbolicT⟧ w₁) (⟦dotConstructedT⟧ w₂) := by
  intro (v₁ : World k) (v₂ : World k) (h₁ : Hom w₁ v₁) (h₂ : Hom w₂ v₂) (φ' : WRel v₁ v₂) _
    (n : ℕ) (m : ℕ) (hnm : n = m) (u₁ : World k) (u₂ : World k) (g₁ : Hom v₁ u₁)
    (g₂ : Hom v₂ u₂) (φ'' : WRel u₁ u₂) _ (x : Fin u₁.size) (y : Fin u₂.size)
    (hxy : φ''.toAlgHom (X x) = X y)
  subst hnm
  obtain ⟨hs₁, i, he₁, hm₁⟩ := sem_dotSymbolic h₁ n g₁ x
  obtain ⟨-, he₂, hm₂⟩ := sem_dotConstructed h₂ n g₂ y
  have hmom := momOf_rel φ'' hxy
  refine ⟨WRel.ofOne _ _ hs₁ i (sumX _) (fun j => by rw [hm₂, hm₁, hmom]), ?_⟩
  show tensorHom φ'' (WRel.ofOne _ _ hs₁ i (sumX _) _) _ = _
  rw [he₁, he₂, tensorHom_natAdd, WRel.ofOne_X]

/-- **Representation independence of the dot product.** No context
distinguishes the symbolic dot product from the constructed one. -/
theorem repind_dot (Cx : CtxTerm dotTy) (w : World k) (x : Fin w.size) :
    (denCtx Cx w (⟦dotSymbolicT⟧ w) x).2 = (denCtx Cx w (⟦dotConstructedT⟧ w) x).2 :=
  repind Cx w _ _ (dot_rel (WRel.id w)) x

/-! ## The fresh copy: only the moments of an auxiliary umbra are observable -/

open Kripke.MTm in
/-- `λu. _ ← mk 0; new u`: a fresh copy, allocated after an unused umbra. -/
def newAfterUnusedT : Prog Δ (tU ⇛ .comp tU) :=
  -- context: new, u
  letP newT (lam (bind (mk (lam zeroK))
    -- context: new, u, j
    (lam (.app (var (.succ (.succ .zero))) (var (.succ .zero))))))

/-- What `_ ← mk 0; new y` allocates, with the two allocations as equations, is
related to `new x` whenever `x` and `y` have the same moments. -/
theorem newAfterUnused_rel {v₁ v₂ : World k} (φ : WRel v₁ v₂) (x : Fin v₁.size) (y : Fin v₂.size)
    (hmom : momOf v₁ x = momOf v₂ y) (N : Σ B : World k, Fin (v₂.size + B.size))
    (hN : N = ⟨World.single (fun _ => 0), Fin.natAdd v₂.size 0⟩)
    (G : Σ B : World k, Fin (v₂.size + N.1.size + B.size))
    (hG : G = ⟨World.single (momOf (v₂.append N.1) ((Hom.inl v₂ N.1).toFun y)), Fin.natAdd _ 0⟩) :
    Related (.comp tU) φ (⟨World.single (momOf v₁ x), Fin.natAdd v₁.size 0⟩ : Val (.comp tU) v₁)
      ⟨N.1.append G.1, (Hom.assoc v₂ N.1 G.1).toFun G.2⟩ := by
  subst hN
  subst hG
  have hm : momOf (v₂.append (World.single fun _ => 0)) ((Hom.inl v₂ _).toFun y) = momOf v₁ x := by
    rw [momOf_hom, hmom]
  refine ⟨WRel.ofOne _ _ rfl 0 (X ((Hom.inr (World.single fun _ => 0) (World.single _)).toFun 0))
    (fun j => ?_), ?_⟩
  · rw [← momOf, ← momOf, momOf_hom, momOf_single _ (by simp [momOf]),
      momOf_single _ (by simp [momOf]), hm]
  · show tensorHom φ _ (X (Fin.natAdd v₁.size 0)) = X _
    rw [tensorHom_X_natAdd, WRel.ofOne_X, rename_X]
    exact congrArg X (Fin.ext (by simp [Hom.assoc, Hom.inr]))

/-- `new` and `_ ← mk 0; new` are related at every world relation. -/
theorem new_rel {w₁ w₂ : World k} (φ : WRel w₁ w₂) :
    Related (tU ⇛ .comp tU) φ (⟦newT⟧ w₁) (⟦newAfterUnusedT⟧ w₂) := by
  intro (v₁ : World k) (v₂ : World k) (h₁ : Hom w₁ v₁) (h₂ : Hom w₂ v₂) (φ' : WRel v₁ v₂) _
    (x : Fin v₁.size) (y : Fin v₂.size) (hxy : φ'.toAlgHom (X x) = X y)
  rw [sem_new]
  simp only [newAfterUnusedT]
  unfold_sem
  exact newAfterUnused_rel φ' x y (momOf_rel φ' hxy) _
    (by simp only [envTr_dictEnv, dictEnv_mk, dictEnv_zeroK, momentMk]) _ (sem_new _ _)

/-- **Auxiliary umbrae are defined up to similarity.** No context of type
`(U → T U) → U → T K` distinguishes `new` from an implementation that allocates
an unused umbra first: only the moments of the umbra it returns are
observable. -/
theorem repind_new (Cx : CtxTerm (tU ⇛ .comp tU)) (w : World k) (x : Fin w.size) :
    (denCtx Cx w (⟦newT⟧ w) x).2 = (denCtx Cx w (⟦newAfterUnusedT⟧ w) x).2 :=
  repind Cx w _ _ (new_rel (WRel.id w)) x

/-! ## Representation independence of the composition of a sum -/

open Kripke.MTm in
/-- `λp a m. ∑_{j ≤ m} E[(p)ⱼ] B_{m,j}(E[a^·])`: the moments of `p.α` for a
polynomial `p`. -/
def composeMomentsAT : Prog Δ (tA ⇛ tU ⇛ tSeq) :=
  -- context: sum, ff, bell, mom, p, a, m
  let4P sumToT fallingFactorialT bellT momT (lam (lam (lam (app2 (var (.succ (.succ (.succ (.succ (.succ (.succ
    .zero))))))) (succ (var .zero))
    -- context: sum, ff, bell, mom, p, a, m, j
    (lam (mulK
      (evalA (app2 (var (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))
        (var (.succ (.succ (.succ .zero)))) (var .zero)))
      (.app (app2 (var (.succ (.succ (.succ (.succ (.succ .zero))))))
        (.app (var (.succ (.succ (.succ (.succ .zero))))) (var (.succ (.succ .zero)))) (var .zero))
        (var (.succ .zero)))))))))

/-- The moments of `p.α` in a world. -/
def composeMomentsA (w : World k) (p : MvPolynomial (Fin w.size) k) (x : Fin w.size) (m : ℕ) : k :=
  ∑ j ∈ Finset.range (m + 1),
    Umbral.eval w.mom (∏ i ∈ Finset.range j, (p - C (i : k))) * pBell (momOf w x) j m

theorem sem_composeMomentsA {w v v' : World k} (h : Hom w v) (p : MvPolynomial (Fin v.size) k)
    (h' : Hom v v') (x : Fin v'.size) {v'' : World k} (h'' : Hom v' v'') :
    (⟦composeMomentsAT⟧ w) v h p v' h' x v'' h''
      = composeMomentsA v'' (rename h''.toFun (rename h'.toFun p)) (h''.toFun x) := by
  funext m
  simp only [composeMomentsAT]
  unfold_sem
  simp only [sem_sumTo, sem_fallingFactorial, Hom.id_toFun, id_eq, MvPolynomial.rename_id_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have hu : Unif ((⟦momT⟧ w) v'' (h.comp (h'.comp (h''.comp (Hom.id v'')))) (h''.toFun x))
      (momOf v'' (h''.toFun x)) := fun u g => by rw [sem_mom, momOf_hom]
  rw [sem_bell _ _ _ hu]

open Kripke.MTm in
/-- `λp a. mk (composeMomentsA p a)`: **the composition `p.α`** with a polynomial. -/
def composeAT : Prog Δ (tA ⇛ tU ⇛ .comp tU) :=
  letP composeMomentsAT (lam (lam (mk (app2 (var (.succ (.succ .zero))) (var (.succ .zero)) (var .zero)))))

theorem sem_composeA {w v v' : World k} (h : Hom w v) (p : MvPolynomial (Fin v.size) k)
    (h' : Hom v v') (x : Fin v'.size) :
    (⟦composeAT⟧ w) v h p v' h' x
      = ⟨World.single (composeMomentsA v' (rename h'.toFun p) x), Fin.natAdd v'.size 0⟩ := by
  simp only [composeAT]
  unfold_sem
  simp only [momentMk]
  rw [sem_composeMomentsA]
  simp

/-- The interface of `cs`: three umbrae, a polynomial computation. -/
abbrev composeSumTy : QTy 3 := tU ⇛ tU ⇛ tU ⇛ .comp tA

open Kripke.MTm in
/-- `λβ β' a. γ ← (β + β').a; return γ`. -/
def fusedCompositionT : Prog Δ composeSumTy :=
  -- context: cA, β, β', a; then γ
  letP composeAT (lam (lam (lam (bind
    (app2 (var (.succ (.succ (.succ .zero)))) (addA (injA (var (.succ (.succ .zero)))) (injA (var (.succ .zero)))) (var .zero))
    (lam (ret (injA (var .zero))))))))

open Kripke.MTm in
/-- `λβ β' a. δ ← β.a; δ' ← β'.a; return (δ + δ')`. -/
def splitCompositionT : Prog Δ composeSumTy :=
  -- context: comp, β, β', a; then δ; then δ'
  letP composeT (lam (lam (lam (bind
    (app2 (var (.succ (.succ (.succ .zero)))) (var (.succ (.succ .zero))) (var .zero))
    (lam (bind
      (app2 (var (.succ (.succ (.succ (.succ .zero))))) (var (.succ (.succ .zero))) (var (.succ .zero)))
      (lam (ret (addA (injA (var (.succ .zero))) (injA (var .zero)))))))))))

open Kripke.MTm in
/-- `λb b' a. β ← new b; β' ← new b'; cont β β' a`: run `cont` on two fresh
copies. -/
def onFreshCopiesT (cont : Prog Δ composeSumTy) : Prog Δ composeSumTy :=
  -- context: new, cont, b, b', a
  let2P newT cont (lam (lam (lam (bind (.app (var (.succ (.succ (.succ (.succ .zero)))))
      (var (.succ (.succ .zero))))
    -- context: new, cont, b, b', a, β
    (lam (bind (.app (var (.succ (.succ (.succ (.succ (.succ .zero)))))) (var (.succ (.succ .zero))))
      -- context: new, cont, b, b', a, β, β'
      (lam (app2 (.app (var (.succ (.succ (.succ (.succ (.succ .zero)))))) (var (.succ .zero)))
        (var .zero) (var (.succ (.succ .zero)))))))))))

/-- `β ← new b; β' ← new b'; γ ← (β + β').a; return γ`. -/
abbrev composeSumFusedT : Prog Δ composeSumTy := onFreshCopiesT fusedCompositionT

/-- `β ← new b; β' ← new b'; δ ← β.a; δ' ← β'.a; return (δ + δ')`. -/
abbrev composeSumSplitT : Prog Δ composeSumTy := onFreshCopiesT splitCompositionT

/-- Bind, for a computation returning a name followed by one returning a
polynomial: the denotation of `bind` at these types. -/
def bindUA {w : World k} (c : Val (.comp tU) w)
    (K : (c : Val (.comp tU) w) → Val (.comp tA) (w.append c.1)) : Val (.comp tA) w :=
  ⟨c.1.append (K c).1, Kripke.qtr (base k) tA sortEnv (Hom.assoc w c.1 (K c).1) (K c).2⟩

/-- **The bind case of the abstraction theorem, for given continuations.** If the
first computations are related through the block relation `ψ`, and the
continuations are related at `φ ⊗ ψ`, the binds are related at `φ`. -/
theorem bindUA_rel {w₁ w₂ : World k} (φ : WRel w₁ w₂) (c₁ : Val (.comp tU) w₁)
    (c₂ : Val (.comp tU) w₂) (K₁ K₂) (ψ : WRel c₁.1 c₂.1)
    (hK : Related (.comp tA) (φ.tensor ψ) (K₁ c₁) (K₂ c₂)) :
    Related (.comp tA) φ (bindUA c₁ K₁) (bindUA c₂ K₂) := by
  obtain ⟨ψ', h⟩ := hK
  exact ⟨ψ.tensor ψ', relA.mono h (Fut.assoc φ ψ ψ')⟩

/-- **What `onFreshCopiesT cont` computes**: two fresh copies, then `cont`. -/
theorem sem_onFreshCopies (cont : Prog Δ composeSumTy) {w v : World k} (h : Hom w v) (b : Fin v.size) {u : World k}
    (g : Hom v u) (b' : Fin u.size) {t : World k} (g' : Hom u t) (a : Fin t.size) :
    (⟦onFreshCopiesT cont⟧ w) v h b u g b' t g' a
      = bindUA ((⟦newT⟧ w) t (h.comp (g.comp g')) (g'.toFun (g.toFun b))) fun c₁ =>
          bindUA ((⟦newT⟧ w) (t.append c₁.1) (h.comp (g.comp (g'.comp (Hom.inl t c₁.1))))
              ((Hom.inl t c₁.1).toFun (g'.toFun b'))) fun c₂ =>
            (⟦cont⟧ w) ((t.append c₁.1).append c₂.1)
              (h.comp (g.comp (g'.comp ((Hom.inl t c₁.1).comp (Hom.inl (t.append c₁.1) c₂.1)))))
              ((Hom.inl (t.append c₁.1) c₂.1).toFun c₁.2) _ (Hom.id _) c₂.2 _ (Hom.id _)
              ((Hom.inl (t.append c₁.1) c₂.1).toFun ((Hom.inl t c₁.1).toFun a)) := by
  simp only [onFreshCopiesT, bindUA]
  unfold_sem
  congr 1

theorem composeMoments_zero (w : World k) (b x : Fin w.size) : composeMoments w b x 0 = 1 := by
  simp [composeMoments, pBell]

theorem composeMomentsA_zero (w : World k) (p : MvPolynomial (Fin w.size) k) (x : Fin w.size) :
    composeMomentsA w p x 0 = 1 := by
  simp [composeMomentsA, pBell]

/-- Composition moments are preserved by world morphisms. -/
theorem composeMoments_hom {w v : World k} (h : Hom w v) (b x : Fin w.size) :
    composeMoments v (h.toFun b) (h.toFun x) = composeMoments w b x := by
  funext m
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [momOf_hom, ← eval_rename_hom h]
  simp [map_prod, map_sub]

/-- What `γ ← (β + β').a; return γ` computes: one fresh name. -/
theorem fusedComposition_val (W : World k) (b b' a : Fin W.size) (p : MvPolynomial (Fin W.size) k)
    (hp : p = X b + X b') (N : Σ B : World k, Fin (W.size + B.size))
    (hN : N = ⟨World.single (composeMomentsA W (rename (Hom.id W).toFun p) a), Fin.natAdd W.size 0⟩) :
    OneName W (composeMomentsA W (X b + X b') a) ⟨N.1.append World.empty,
        rename (Hom.assoc W N.1 World.empty).toFun
          (rename (Hom.inl (W.append N.1) World.empty).toFun (X N.2))⟩ := by
  subst hp
  rw [Hom.id_toFun, MvPolynomial.rename_id_apply] at hN
  exact mk_ret W _ (composeMomentsA_zero W _ a) N hN

theorem sem_fusedComposition {w W : World k} (m : Hom w W) (b b' a : Fin W.size) :
    OneName W (composeMomentsA W (X b + X b') a)
      ((⟦fusedCompositionT⟧ w) W m b W (Hom.id W) b' W (Hom.id W) a) := by
  simp only [fusedCompositionT]
  unfold_sem
  exact fusedComposition_val W b b' a _ (by simp only [envTr_dictEnv, dictEnv_addA, dictEnv_injA, Hom.id_toFun,
    MvPolynomial.rename_id_apply]) _ (sem_composeA _ _ _ _)

/-- What `δ ← β.a; δ' ← β'.a; return (δ + δ')` computes: two fresh names, and
their sum, whose moments are the binomial convolution of the two compositions. -/
theorem splitComposition_val (W : World k) (b b' a : Fin W.size) (N₁ : Σ B : World k, Fin (W.size + B.size))
    (h₁ : N₁ = ⟨World.single (composeMoments W ((Hom.id W).toFun b) a), Fin.natAdd W.size 0⟩)
    (N₂ : Σ B : World k, Fin (W.size + N₁.1.size + B.size))
    (h₂ : N₂ = ⟨World.single (composeMoments (W.append N₁.1)
      ((Hom.id (W.append N₁.1)).toFun ((Hom.inl W N₁.1).toFun b')) ((Hom.inl W N₁.1).toFun a)),
      Fin.natAdd _ 0⟩) :
    MomInv W (conv (composeMoments W b a) (composeMoments W b' a))
      ⟨N₁.1.append (N₂.1.append World.empty),
        rename (Hom.assoc W N₁.1 (N₂.1.append World.empty)).toFun
          (rename (Hom.assoc (W.append N₁.1) N₂.1 World.empty).toFun
            (rename (Hom.inl ((W.append N₁.1).append N₂.1) World.empty).toFun
              (X ((Hom.inl (W.append N₁.1) N₂.1).toFun N₁.2) + X N₂.2)))⟩ := by
  subst h₁
  rw [Hom.id_toFun, id_eq, Hom.id_toFun, id_eq, composeMoments_hom] at h₂
  subst h₂
  set d₁ := composeMoments W b a
  set d₂ := composeMoments W b' a
  set B₂ : World k := (World.single d₂).append World.empty
  refine ⟨rename (Fin.castAdd B₂.size) (X 0)
      + rename (Fin.natAdd 1) (X ((Hom.inl (World.single d₂) World.empty).toFun 0)), ?_, fun j => ?_⟩
  · simp only [map_add, rename_X]
    congr 1
  · change Umbral.eval ((World.single d₁).append B₂).mom _ = _
    rw [eval_blocks_pow]
    congr 1
    · funext i
      exact momOf_single _ (composeMoments_zero W b a) i
    · funext i
      rw [← momOf, momOf_hom, momOf_single _ (composeMoments_zero W b' a)]

theorem sem_splitComposition {w W : World k} (m : Hom w W) (b b' a : Fin W.size) :
    MomInv W (conv (composeMoments W b a) (composeMoments W b' a))
      ((⟦splitCompositionT⟧ w) W m b W (Hom.id W) b' W (Hom.id W) a) := by
  simp only [splitCompositionT]
  unfold_sem
  exact splitComposition_val W b b' a _ (sem_compose _ _ _ _) _ (sem_compose _ _ _ _)

/-! ### Uncorrelation of distinct names, and the moments of a composed sum -/

/-- **Distinct names are uncorrelated**: `E[P(x) Q(y)] = E[P(x)] E[Q(y)]` for
`x ≠ y`. -/
theorem eval_aeval_mul_distinct (v : World k) {x y : Fin v.size} (hxy : x ≠ y)
    (P Q : Polynomial k) :
    Umbral.eval v.mom (Polynomial.aeval (X x) P * Polynomial.aeval (X y) Q)
      = Umbral.eval v.mom (Polynomial.aeval (X x) P) * Umbral.eval v.mom (Polynomial.aeval (X y) Q) := by
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range, Finset.sum_mul_sum]
  simp only [eval_sum]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [MvPolynomial.smul_eq_C_mul]
  rw [show C (P.coeff i) * X x ^ i * (C (Q.coeff j) * X y ^ j)
      = C (P.coeff i * Q.coeff j) * (X x ^ i * X y ^ j) by rw [map_mul]; ring,
    eval_C_mul, eval_C_mul, eval_C_mul, eval_X_pow_mul_X_pow _ hxy]
  simp only [moments]
  ring

theorem prod_sub_C_eq_ffSeq {σ : Type} (p : MvPolynomial σ k) (j : ℕ) :
    ∏ i ∈ Finset.range j, (p - C (i : k)) = ffSeq p j :=
  Finset.prod_congr rfl fun i _ => by rw [map_natCast]

/-- **The moments of a composed sum.** If `Φ` relates `β₁, β'₁, a₁` to
`β₂, β'₂, a₂` and `β₂ ≠ β'₂`, then `(β₁ + β'₁).a₁` has the moments of
`β₂.a₂ + β'₂.a₂`. Vandermonde, uncorrelation of `β₂` and `β'₂`, and
distributivity (`compTransform_conv`). -/
theorem moments_distrib {W₁ W₂ : World k} (Φ : WRel W₁ W₂) {β₁ β'₁ a₁ : Fin W₁.size}
    {β₂ β'₂ a₂ : Fin W₂.size} (hβ : Φ.toAlgHom (X β₁) = X β₂) (hβ' : Φ.toAlgHom (X β'₁) = X β'₂)
    (ha : Φ.toAlgHom (X a₁) = X a₂) (hne : β₂ ≠ β'₂) :
    composeMomentsA W₁ (X β₁ + X β'₁) a₁ = conv (composeMoments W₂ β₂ a₂) (composeMoments W₂ β'₂ a₂) := by
  funext m
  have hE : ∀ j, Umbral.eval W₁.mom (∏ i ∈ Finset.range j, (X β₁ + X β'₁ - C (i : k)))
      = conv (fun i => Umbral.eval W₂.mom (∏ l ∈ Finset.range i, (X β₂ - C (l : k))))
          (fun i => Umbral.eval W₂.mom (∏ l ∈ Finset.range i, (X β'₂ - C (l : k)))) j := by
    intro j
    rw [← Φ.eval_eq]
    simp only [map_prod, map_sub, map_add, hβ, hβ', MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq]
    rw [prod_sub_C_eq_ffSeq, ffSeq_add, conv, eval_sum, conv]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← map_natCast (C : k →+* MvPolynomial _ k), eval_C_mul, ← prod_sub_C_eq_ffSeq,
      ← prod_sub_C_eq_ffSeq, ← aeval_descPochhammer, ← aeval_descPochhammer,
      eval_aeval_mul_distinct W₂ hne, aeval_descPochhammer, aeval_descPochhammer]
  have h1 : composeMomentsA W₁ (X β₁ + X β'₁) a₁ m
      = compTransform (momOf W₂ a₂) (conv (fun i => Umbral.eval W₂.mom (∏ l ∈ Finset.range i,
          (X β₂ - C (l : k)))) (fun i => Umbral.eval W₂.mom (∏ l ∈ Finset.range i,
          (X β'₂ - C (l : k))))) m := by
    rw [← momOf_rel Φ ha]
    exact Finset.sum_congr rfl fun j _ => by rw [hE]
  rw [h1, compTransform_conv]
  rfl

/-- **`fusedCompositionT` and `splitCompositionT` are related** at every world
relation that sends the two umbrae to distinct names. -/
theorem fused_split_rel {w₁ w₂ W₁ W₂ : World k} (Φ : WRel W₁ W₂) (m₁ : Hom w₁ W₁) (m₂ : Hom w₂ W₂)
    {β₁ β'₁ a₁ : Fin W₁.size} {β₂ β'₂ a₂ : Fin W₂.size} (hβ : Φ.toAlgHom (X β₁) = X β₂)
    (hβ' : Φ.toAlgHom (X β'₁) = X β'₂) (ha : Φ.toAlgHom (X a₁) = X a₂) (hne : β₂ ≠ β'₂) :
    Related (.comp tA) Φ ((⟦fusedCompositionT⟧ w₁) W₁ m₁ β₁ W₁ (Hom.id W₁) β'₁ W₁ (Hom.id W₁) a₁)
      ((⟦splitCompositionT⟧ w₂) W₂ m₂ β₂ W₂ (Hom.id W₂) β'₂ W₂ (Hom.id W₂) a₂) := by
  obtain ⟨hs, i, he₁, hm₁⟩ := sem_fusedComposition m₁ β₁ β'₁ a₁
  obtain ⟨q, he₂, hm₂⟩ := sem_splitComposition m₂ β₂ β'₂ a₂
  refine ⟨WRel.ofOne _ _ hs i q (fun j => by rw [hm₂, hm₁, moments_distrib Φ hβ hβ' ha hne]), ?_⟩
  show tensorHom Φ (WRel.ofOne _ _ hs i q _) _ = _
  rw [he₁, he₂, tensorHom_natAdd, WRel.ofOne_X]

/-- The world relation between two one-name blocks with the same moments. -/
def WRel.single (s s' : ℕ → k) (hs : s = s') (h0 : s 0 = 1) :
    WRel (World.single s) (World.single s') :=
  WRel.ofOne _ _ rfl 0 (X 0) (fun j => by
    rw [← momOf, ← momOf, momOf_single _ (hs ▸ h0), momOf_single _ h0, hs])

theorem tensor_single_castAdd {w₁ w₂ : World k} (φ : WRel w₁ w₂) (s s' : ℕ → k) (hs : s = s')
    (h0 : s 0 = 1) (i : Fin w₁.size) :
    (φ.tensor (WRel.single s s' hs h0)).toAlgHom (X (Fin.castAdd 1 i))
      = rename (Fin.castAdd 1) (φ.toAlgHom (X i)) :=
  tensorHom_X_castAdd φ _ i

theorem tensor_single_natAdd {w₁ w₂ : World k} (φ : WRel w₁ w₂) (s s' : ℕ → k) (hs : s = s')
    (h0 : s 0 = 1) :
    (φ.tensor (WRel.single s s' hs h0)).toAlgHom (X (Fin.natAdd w₁.size 0))
      = X (Fin.natAdd w₂.size 0) := by
  show tensorHom φ _ (X (Fin.natAdd w₁.size 0)) = _
  rw [tensorHom_X_natAdd, WRel.single, WRel.ofOne_X, rename_X]

omit [CommRing k] in
@[simp] theorem Hom.inl_toFun (w B : World k) : (Hom.inl w B).toFun = Fin.castAdd B.size := rfl

/-- **The two implementations of the composition of a sum are related** at every
world relation. -/
theorem composeSum_rel {w₁ w₂ : World k} (φ : WRel w₁ w₂) : Related composeSumTy φ (⟦composeSumFusedT⟧ w₁) (⟦composeSumSplitT⟧ w₂) := by
  intro (v₁ : World k) (v₂ : World k) (h₁ : Hom w₁ v₁) (h₂ : Hom w₂ v₂) (φ₁ : WRel v₁ v₂) _
    (b₁ : Fin v₁.size) (b₂ : Fin v₂.size) (hb : φ₁.toAlgHom (X b₁) = X b₂)
    (u₁ : World k) (u₂ : World k) (g₁ : Hom v₁ u₁) (g₂ : Hom v₂ u₂) (φ₂ : WRel u₁ u₂)
    (hf₂ : Fut φ₁ g₁ g₂ φ₂) (b'₁ : Fin u₁.size) (b'₂ : Fin u₂.size)
    (hb' : φ₂.toAlgHom (X b'₁) = X b'₂)
    (t₁ : World k) (t₂ : World k) (g'₁ : Hom u₁ t₁) (g'₂ : Hom u₂ t₂) (φ₃ : WRel t₁ t₂)
    (hf₃ : Fut φ₂ g'₁ g'₂ φ₃) (a₁ : Fin t₁.size) (a₂ : Fin t₂.size)
    (ha : φ₃.toAlgHom (X a₁) = X a₂)
  have hb₃ : φ₃.toAlgHom (X (g'₁.toFun (g₁.toFun b₁))) = X (g'₂.toFun (g₂.toFun b₂)) := by
    rw [hf₃.apply_X, hf₂.apply_X, hb, rename_X, rename_X]
  have hb'₃ : φ₃.toAlgHom (X (g'₁.toFun b'₁)) = X (g'₂.toFun b'₂) := by
    rw [hf₃.apply_X, hb', rename_X]
  rw [sem_onFreshCopies, sem_onFreshCopies, sem_new, sem_new]
  have hs₁ := momOf_rel φ₃ hb₃
  refine bindUA_rel φ₃ _ _ _ _ (WRel.single _ _ hs₁ (by simp [momOf])) ?_
  dsimp only
  rw [sem_new, sem_new]
  have hs₂ : momOf (t₁.append (World.single (momOf t₁ (g'₁.toFun (g₁.toFun b₁)))))
      ((Hom.inl t₁ _).toFun (g'₁.toFun b'₁))
      = momOf (t₂.append (World.single (momOf t₂ (g'₂.toFun (g₂.toFun b₂)))))
      ((Hom.inl t₂ _).toFun (g'₂.toFun b'₂)) := by
    rw [momOf_hom (Hom.inl t₁ _), momOf_hom (Hom.inl t₂ _), momOf_rel φ₃ hb'₃]
  refine bindUA_rel _ _ _ _ _ (WRel.single _ _ hs₂ (by simp [momOf])) ?_
  dsimp only
  refine fused_split_rel _ _ _ ?_ ?_ ?_ ?_
  · refine (tensor_single_castAdd _ _ _ _ _ _).trans ?_
    refine (congrArg (rename _) (tensor_single_natAdd _ _ _ _ _)).trans ?_
    exact rename_X _ _
  · exact tensor_single_natAdd _ _ _ _ _
  · refine (tensor_single_castAdd _ _ _ _ _ _).trans ?_
    refine (congrArg (rename _) (tensor_single_castAdd _ _ _ _ _ _)).trans ?_
    rw [ha, rename_X, rename_X]
    rfl
  · simp [Fin.ext_iff]

/-- **Representation independence of the composition of a sum.**
No context of type `(U → U → U → T A) → U → T K` distinguishes
`β ← new b; β' ← new b'; (β + β').a` from
`β ← new b; β' ← new b'; δ ← β.a; δ' ← β'.a; return (δ + δ')`
(write-up, Chapter 3). -/
theorem repind_composeSum (Cx : CtxTerm composeSumTy) (w : World k) (x : Fin w.size) :
    (denCtx Cx w (⟦composeSumFusedT⟧ w) x).2 = (denCtx Cx w (⟦composeSumSplitT⟧ w) x).2 :=
  repind Cx w _ _ (composeSum_rel (WRel.id w)) x

/-! ## The Sheffer identity at umbral arguments -/

/-- **The Sheffer identity and binomial type at umbral arguments.** Let `β ≠ β'`
be names of a world, and let `δ`, `δ₁`, `δ₂` be names with the moments of
`(β + β').v`, `β.v` and `β'.v`, where `δ` and `δ₁` differ from `α`. Then
`E[(α + δ)ⁿ] = ∑ᵢ C(n,i) E[(α + δ₁)ⁱ] E[δ₂ⁿ⁻ⁱ]` and
`E[δⁿ] = ∑ᵢ C(n,i) E[δ₁ⁱ] E[δ₂ⁿ⁻ⁱ]`. Uncorrelation, distributivity
(`moments_distrib`) and associativity of the binomial convolution. -/
theorem sheffer (W : World k) {α δ δ₁ δ₂ β β' v : Fin W.size} (hβ : β ≠ β') (hαδ : α ≠ δ)
    (hαδ₁ : α ≠ δ₁) (hδ : momOf W δ = composeMomentsA W (X β + X β') v)
    (hδ₁ : momOf W δ₁ = composeMoments W β v) (hδ₂ : momOf W δ₂ = composeMoments W β' v)
    (n : ℕ) :
    Umbral.eval W.mom ((X α + X δ) ^ n)
        = ∑ i ∈ Finset.range (n + 1), (n.choose i : k) *
            (Umbral.eval W.mom ((X α + X δ₁) ^ i) * Umbral.eval W.mom (X δ₂ ^ (n - i))) ∧
      Umbral.eval W.mom (X δ ^ n)
        = ∑ i ∈ Finset.range (n + 1), (n.choose i : k) *
            (Umbral.eval W.mom (X δ₁ ^ i) * Umbral.eval W.mom (X δ₂ ^ (n - i))) := by
  have hd : momOf W δ = conv (momOf W δ₁) (momOf W δ₂) := by
    rw [hδ, hδ₁, hδ₂]
    exact moments_distrib (WRel.id W) rfl rfl rfl hβ
  refine ⟨?_, congrFun hd n⟩
  rw [eval_add_pow _ hαδ]
  change conv (momOf W α) (momOf W δ) n
    = conv (fun i => Umbral.eval W.mom ((X α + X δ₁) ^ i)) (momOf W δ₂) n
  rw [hd, ← conv_assoc]
  congr 1
  funext i
  exact (eval_add_pow _ hαδ₁ i).symm

end

end FreeThms.Umbral.Full
