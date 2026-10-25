/-
# The compositional inverse umbra, as a term

Di Nardo and Senato's compositional inverse `α⁽⁻¹⁾` of an umbra `α` with
`E[α] = 1` is characterised by `α⁽⁻¹⁾.β.α ≡ χ`, with `β` the Bell umbra and `χ`
the singleton umbra. The factorial moments of `γ.β` are the moments of `γ`, so
in moments the condition reads `compTransform a g = (0, 1, 0, 0, …)`, where `a` are the
moments of `α`, `g` those of `α⁽⁻¹⁾`, and `compTransform` is the composition transform
of `Distributivity.lean`. In generating functions, `1 + G(F(t)) = 1 + t` with
`1 + F` and `1 + G` the moment generating functions of `α` and `α⁽⁻¹⁾`: this is
Lagrange inversion.

The inverse is computed without division. With `a₁ = 1` the triangular system
`compTransform a g = χ` has diagonal `B_{m,m}(a) = a₁ᵐ = 1`, so the map
`Φ s = χ - compTransform a s + s` changes the `j`-th entry of `s` only through the
entries below `j`. Its `m`-th iterate from `χ` is therefore correct up to `m`,
and `g m = (Φᵐ χ) m`. As a term this is plain iteration at the type of
sequences.

## Main results

* `inverse_spec`: `compTransform a (inverseMoments a) = χ`, when `a 1 = 1`;
* `inverse_unique`: every solution agrees with `inverseMoments a` from index 1 on;
* `inverse_spec_right`: the other side, `α.β.α⁽⁻¹⁾ ≡ χ`, that is
  `compTransform (inverseMoments a) a = χ` from index 1 on, by associativity of
  composition (`compTransform_assoc`);
* `sem_inverse`: the term `inverseT` allocates one fresh name, with moments
  `inverseMoments` of the moments of its argument.
-/

import FreeThms.Umbral.Composition
import FreeThms.Umbral.Distributivity

namespace FreeThms.Umbral.Full

open MvPolynomial (X C rename rename_X)
open FreeThms.Umbral.Restricted (Slot)
open FreeThms.Kripke (QTy QCtx QVar MTm QTyD QEnv)

noncomputable section

variable {k : Type} [CommRing k]

/-! ## The inverse, as a sequence -/

/-- The diagonal of the partial Bell polynomials: `B_{m,m}(a) = a₁ᵐ`. -/
theorem pBell_diag (a : ℕ → k) : ∀ m, pBell a m m = a 1 ^ m
  | 0 => by simp [pBell]
  | m + 1 => by
    show conv (pBell a m) (fun i => a (i + 1)) m = a 1 ^ (m + 1)
    rw [conv, Finset.sum_range_succ, Finset.sum_eq_zero fun i hi => by
      rw [pBell_eq_zero_of_lt a m i (Finset.mem_range.mp hi), zero_mul, mul_zero], pBell_diag a m]
    simp [pow_succ]

/-- One step of the inversion: the sequence `j ↦ χⱼ - compTransform a s j + sⱼ`. -/
def inverseStep (a s : ℕ → k) (j : ℕ) : k := singletonMoments j - compTransform a s j + s j

/-- The moments of the compositional inverse: `m ↦ (Φᵐ χ) m`. -/
def inverseMoments (a : ℕ → k) (m : ℕ) : k := Kripke.iterN (inverseStep a) m singletonMoments m

variable {a : ℕ → k}

theorem inverseStep_eq (h1 : a 1 = 1) (s : ℕ → k) (j : ℕ) :
    inverseStep a s j = singletonMoments j - ∑ i ∈ Finset.range j, s i * pBell a i j := by
  rw [inverseStep, compTransform, Finset.sum_range_succ, pBell_diag, h1, one_pow, mul_one]
  ring

/-- The iterates of `Φ` stabilise: from step `j` on, the `j`-th entry no longer
changes. -/
theorem iterN_inverseStep_stable (h1 : a 1 = 1) (j : ℕ) :
    ∀ r, j ≤ r → Kripke.iterN (inverseStep a) r singletonMoments j = inverseMoments a j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    have step : ∀ r, j ≤ r + 1 → Kripke.iterN (inverseStep a) (r + 1) singletonMoments j
        = singletonMoments j - ∑ i ∈ Finset.range j, inverseMoments a i * pBell a i j := by
      intro r hr
      rw [iterN_succ', inverseStep_eq h1]
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [ih i (Finset.mem_range.mp hi) r (by have := Finset.mem_range.mp hi; omega)]
    intro r hr
    rcases r with _ | r
    · obtain rfl : j = 0 := by omega
      rfl
    · rw [step r hr]
      rcases j with _ | j
      · simp [inverseMoments, Kripke.iterN]
      · exact (step j le_rfl).symm

/-- The recurrence of the inverse: `gⱼ = χⱼ - ∑_{i<j} gᵢ B_{j,i}(a)`. -/
theorem inverseMoments_eq (h1 : a 1 = 1) (j : ℕ) :
    inverseMoments a j = singletonMoments j - ∑ i ∈ Finset.range j, inverseMoments a i * pBell a i j := by
  rw [← iterN_inverseStep_stable h1 j (j + 1) (by omega), iterN_succ', inverseStep_eq h1]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [iterN_inverseStep_stable h1 i j (Finset.mem_range.mp hi).le]

/-- **The compositional inverse.** With `E[α] = 1`, the composition transform
at the moments of `α` sends `inverseMoments a` to the moments of `χ`: in generating
functions, `G(F(t)) = t`. -/
theorem inverse_spec (h1 : a 1 = 1) (m : ℕ) : compTransform a (inverseMoments a) m = singletonMoments m := by
  rw [compTransform, Finset.sum_range_succ, pBell_diag, h1, one_pow, mul_one, inverseMoments_eq h1 m]
  ring

/-- **The inverse is unique**: every sequence that `compTransform a` sends to the
moments of `χ` agrees with `inverseMoments a` from index 1 on. -/
theorem inverse_unique (h1 : a 1 = 1) (g : ℕ → k)
    (hg : ∀ m, m ≠ 0 → compTransform a g m = singletonMoments m) : ∀ m, m ≠ 0 → g m = inverseMoments a m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    have hgm := hg m hm
    rw [compTransform, Finset.sum_range_succ, pBell_diag, h1, one_pow, mul_one] at hgm
    rw [inverseMoments_eq h1, ← hgm]
    have hsum : ∑ i ∈ Finset.range m, g i * pBell a i m
        = ∑ i ∈ Finset.range m, inverseMoments a i * pBell a i m := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rcases i with _ | i
      · simp [pBell, hm]
      · rw [ih (i + 1) (Finset.mem_range.mp hi) (Nat.succ_ne_zero i)]
    rw [hsum]
    ring

/-! ## The other side: `α.β.α⁽⁻¹⁾ ≡ χ`

The composition transform at the moments of `χ` is the identity, and at any
`a` it sends the moments of `χ` to `a` from index 1 on. With associativity
(`compTransform_assoc`) this gives the second equation: the inverse `h` of the
inverse `g` satisfies `C_a(C_g h) = C_{C_a g} h = h` and `C_a(C_g h) = C_a χ`, so
`h` agrees with `a` from index 1 on, and `C_g a = C_g h = χ`. -/

/-- The partial Bell polynomials of the singleton umbra: `B_{m,i}(χ) = [i = m]`. -/
theorem pBell_singletonMoments : ∀ i m, pBell (singletonMoments : ℕ → k) i m = if i = m then 1 else 0
  | 0, m => by simp [pBell, eq_comm]
  | i + 1, 0 => by simp [pBell]
  | i + 1, m + 1 => by
    show conv (pBell singletonMoments i) (fun r => singletonMoments (r + 1)) m = _
    rw [show (fun r => (singletonMoments (r + 1) : k)) = fun r => if r = 0 then 1 else 0 from
      funext fun r => by simp [singletonMoments], conv_delta_right, pBell_singletonMoments i m]
    simp

/-- The composition transform at the moments of `χ` is the identity: `x.β.χ ≡ x`. -/
theorem compTransform_singletonMoments_left (x : ℕ → k) (m : ℕ) :
    compTransform singletonMoments x m = x m := by
  simp [compTransform, pBell_singletonMoments]

/-- The composition transform sends the moments of `χ` to `a`, from index 1
on: `χ.β.α ≡ α`. -/
theorem compTransform_singletonMoments_right (a : ℕ → k) {m : ℕ} (hm : m ≠ 0) :
    compTransform a singletonMoments m = a m := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  rw [compTransform_succ,
    show shift (singletonMoments : ℕ → k) = pBell a 0 from
      funext fun r => by simp [shift, singletonMoments, pBell],
    ← pBell_compTransform, conv_comm,
    show pBell (compTransform a a) 0 = fun r => if r = 0 then (1 : k) else 0 from rfl,
    conv_delta_right]
  rfl

theorem inverseMoments_one (h1 : a 1 = 1) : inverseMoments a 1 = 1 := by
  rw [inverseMoments_eq h1]
  simp [singletonMoments, pBell]

/-- **The other side of the compositional inverse**, `α.β.α⁽⁻¹⁾ ≡ χ`: the
composition transform at the moments of the inverse sends `a` to the moments of
`χ`, from index 1 on. In generating functions, `F(G(t)) = t`. -/
theorem inverse_spec_right (h1 : a 1 = 1) {m : ℕ} (hm : m ≠ 0) :
    compTransform (inverseMoments a) a m = singletonMoments m := by
  have hg1 : inverseMoments a 1 = 1 := inverseMoments_one h1
  have hag : compTransform a (inverseMoments a) = singletonMoments := funext (inverse_spec h1)
  have hgh : compTransform (inverseMoments a) (inverseMoments (inverseMoments a)) = singletonMoments :=
    funext (inverse_spec hg1)
  -- the inverse of the inverse agrees with `a` from index 1 on
  have hha : ∀ i, i ≠ 0 → inverseMoments (inverseMoments a) i = a i := by
    intro i hi
    have e := compTransform_assoc a (inverseMoments a) (inverseMoments (inverseMoments a)) i
    rw [hgh, hag, compTransform_singletonMoments_left, compTransform_singletonMoments_right a hi] at e
    exact e.symm
  rw [← inverse_spec hg1 m]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases eq_or_ne i 0 with rfl | hi
  · simp [pBell, hm]
  · rw [hha i hi]

/-! ## The inverse, as a term -/

open Kripke.MTm in
/-- `λa s j. χⱼ - ∑_{i ≤ j} sᵢ B_{j,i}(a) + sⱼ`: one step of the inversion. -/
def inverseStepT : Prog Δ (tSeq ⇛ tSeq ⇛ tSeq) :=
  -- context: sum, bell, χ, a, s, j
  let3P sumToT bellT singletonMomentsT (lam (lam (lam (addK
    (addK (.app (var (.succ (.succ (.succ .zero)))) (var .zero))
      (negK (app2 (var (.succ (.succ (.succ (.succ (.succ .zero)))))) (succ (var .zero))
        -- context: sum, bell, χ, a, s, j, i
        (lam (mulK (.app (var (.succ (.succ .zero))) (var .zero))
          (.app (app2 (var (.succ (.succ (.succ (.succ (.succ .zero))))))
            (var (.succ (.succ (.succ .zero)))) (var .zero)) (var (.succ .zero))))))))
    (.app (var (.succ .zero)) (var .zero))))))

theorem sem_inverseStep {w v v' : World k} (h : Hom w v) (a : Val tSeq v) (sa : ℕ → k)
    (ha : Unif a sa) (h' : Hom v v') (S : Val tSeq v') (sS : ℕ → k) (hS : Unif S sS) :
    Unif ((⟦inverseStepT⟧ w) v h a v' h' S) (inverseStep sa sS) := by
  intro u g
  funext j
  simp only [inverseStepT]
  unfold_sem
  simp only [sem_sumTo, sem_singletonMoments, hS _]
  rw [inverseStep, compTransform, sub_eq_add_neg]
  congr 3
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  exact congrFun (sem_bell _ _ sa (fun u' g' => ha _ _) _ i u (Hom.id u)) j

open Kripke.MTm in
/-- `λu m. (Φ_{mom u}ᵐ χ) m`: the moments of the compositional inverse. -/
def inverseMomentsT : Prog Δ (tU ⇛ tSeq) :=
  -- context: step, mom, χ, u, m
  let3P inverseStepT momT singletonMomentsT (lam (lam (.app (iter (var .zero)
    (.app (var (.succ (.succ (.succ (.succ .zero))))) (.app (var (.succ (.succ (.succ .zero))))
      (var (.succ .zero))))
    (var (.succ (.succ .zero)))) (var .zero))))

theorem sem_inverseMoments {w v v' : World k} (h : Hom w v) (x : Fin v.size) (h' : Hom v v') :
    (⟦inverseMomentsT⟧ w) v h x v' h' = inverseMoments (momOf v' (h'.toFun x)) := by
  funext m
  simp only [inverseMomentsT]
  unfold_sem
  refine congrFun (iterN_induction _ (fun i (T : Val tSeq v') =>
    Unif T (Kripke.iterN (inverseStep (momOf v' (h'.toFun x))) i singletonMoments)) _ ?_ ?_ m v' (Hom.id v')) m
  · exact fun u g => sem_singletonMoments _
  · intro i T hT
    rw [iterN_succ']
    exact sem_inverseStep (h.comp h') _ (momOf v' (h'.toFun x)) (fun u g => by rw [sem_mom, momOf_hom])
      (Hom.id v') T _ hT

open Kripke.MTm in
/-- `λu. mk (inverseMomentsT u)`: **the compositional inverse** `α⁽⁻¹⁾`. -/
def inverseT : Prog Δ (tU ⇛ .comp tU) :=
  letP inverseMomentsT (lam (mk (.app (var (.succ .zero)) (var .zero))))

/-- **The compositional inverse, as a term.** `inverseT u` allocates one fresh
name, whose moments are `inverseMoments` of the moments of `u`. -/
theorem sem_inverse {w v : World k} (h : Hom w v) (x : Fin v.size) :
    (⟦inverseT⟧ w) v h x = ⟨World.single (inverseMoments (momOf v x)), Fin.natAdd v.size 0⟩ := by
  simp only [inverseT]
  unfold_sem
  simp only [momentMk]
  rw [sem_inverseMoments]
  rfl

end

end FreeThms.Umbral.Full
