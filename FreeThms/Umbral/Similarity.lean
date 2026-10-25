/-
# The auxiliary umbrae respect similarity

Rota and Taylor define the auxiliary umbrae up to similarity, so a definition is
sound only if similar arguments give similar results (write-up, Chapter 3, the
auxiliary umbrae). For the terms of the language this is a statement about the
moments of what a computation returns, `resultMoments` for an umbra and
`resultMomentsA` for a polynomial.

* The terms of one umbra argument: `new_similar`, `dotSymbolic_similar`,
  `dotConstructed_similar`, `cumulant_similar` and `inverse_similar`. Each
  follows from the moments its `sem_` lemma computes, which depend on the
  moments of the argument alone.
* Composition: `compose_similar` and `composeA_similar`. The moments of `β.α`
  read the factorial moments of `β` and the moments of `α` separately, so no
  condition relates `β` to `α`; in particular `α.α ≡ α'.α'` for `α ≡ α'`. The
  substitution principle with allocation needs the replacing umbra to differ
  from the other argument, and does not give this case.
-/

import FreeThms.Umbral.RepIndependence
import FreeThms.Umbral.Inverse

namespace FreeThms.Umbral.Full

open MvPolynomial (X C rename rename_X)

noncomputable section

variable {k : Type} [CommRing k]

/-! ## The moments of what a computation returns -/

/-- The moments of the umbra that a computation returns. -/
def resultMoments {v : World k} (c : Σ B : World k, Fin (v.size + B.size)) : ℕ → k :=
  momOf (v.append c.1) c.2

/-- The moments of the polynomial that a computation returns. -/
def resultMomentsA {v : World k} (c : Σ B : World k, MvPolynomial (Fin (v.size + B.size)) k)
    (j : ℕ) : k :=
  Umbral.eval (v.append c.1).mom (c.2 ^ j)

/-- One fresh name with moments `s` has moments `s` from the first on. -/
theorem resultMoments_single {v : World k} (s : ℕ → k) :
    resultMoments (⟨World.single s, Fin.natAdd v.size 0⟩ : Σ B : World k, Fin (v.size + B.size))
      = fun i => if i = 0 then 1 else s i := by
  funext i
  rw [resultMoments, show Fin.natAdd v.size (0 : Fin 1) = (Hom.inr v (World.single s)).toFun 0 from rfl,
    momOf_hom]
  rcases eq_or_ne i 0 with rfl | hi
  · simp [momOf]
  · rw [if_neg hi, momOf_single_ne s hi]

/-- A polynomial in the block alone has the moments it has in the block. -/
theorem resultMomentsA_of_rename {v : World k}
    (c : Σ B : World k, MvPolynomial (Fin (v.size + B.size)) k) (q : MvPolynomial (Fin c.1.size) k)
    (hq : c.2 = rename (Fin.natAdd v.size) q) (j : ℕ) :
    resultMomentsA c j = Umbral.eval c.1.mom (q ^ j) := by
  rw [resultMomentsA, hq, ← map_pow,
    show (Fin.natAdd v.size : Fin c.1.size → Fin (v.size + c.1.size)) = (Hom.inr v c.1).toFun from rfl,
    eval_rename_hom]

theorem OneName.resultMomentsA {v : World k} {a : ℕ → k}
    {c : Σ B : World k, MvPolynomial (Fin (v.size + B.size)) k} (h : OneName v a c) :
    Full.resultMomentsA c = a := by
  obtain ⟨_, i, he, hm⟩ := h
  funext j
  rw [resultMomentsA_of_rename c (X i) he, hm]

theorem DotInv.resultMomentsA {v : World k} {s : ℕ → k} {n : ℕ}
    {c : Σ B : World k, MvPolynomial (Fin (v.size + B.size)) k} (h : DotInv v s n c) :
    Full.resultMomentsA c = dotMoments s n := by
  obtain ⟨_, he, hm⟩ := h
  funext j
  rw [resultMomentsA_of_rename c (sumX _) he, hm]

/-! ## The terms of one umbra argument -/

variable {v v' : World k} {x : Fin v.size} {x' : Fin v'.size}

/-- **`new` respects similarity.** -/
theorem new_similar (h : momOf v x = momOf v' x') :
    resultMoments ((⟦newT⟧ v) v (Hom.id v) x) = resultMoments ((⟦newT⟧ v') v' (Hom.id v') x') := by
  rw [sem_new, sem_new, resultMoments_single, resultMoments_single, h]

/-- **The symbolic dot product respects similarity.** -/
theorem dotSymbolic_similar (h : momOf v x = momOf v' x') (n : ℕ) :
    resultMomentsA ((⟦dotSymbolicT⟧ v) v (Hom.id v) n v (Hom.id v) x)
      = resultMomentsA ((⟦dotSymbolicT⟧ v') v' (Hom.id v') n v' (Hom.id v') x') := by
  rw [(sem_dotSymbolic (Hom.id v) n (Hom.id v) x).resultMomentsA,
    (sem_dotSymbolic (Hom.id v') n (Hom.id v') x').resultMomentsA, h]

/-- **The constructed dot product respects similarity.** -/
theorem dotConstructed_similar (h : momOf v x = momOf v' x') (n : ℕ) :
    resultMomentsA ((⟦dotConstructedT⟧ v) v (Hom.id v) n v (Hom.id v) x)
      = resultMomentsA ((⟦dotConstructedT⟧ v') v' (Hom.id v') n v' (Hom.id v') x') := by
  rw [(sem_dotConstructed (Hom.id v) n (Hom.id v) x).resultMomentsA,
    (sem_dotConstructed (Hom.id v') n (Hom.id v') x').resultMomentsA, h]

/-- **The cumulant umbra respects similarity.** -/
theorem cumulant_similar (h : momOf v x = momOf v' x') :
    resultMoments ((⟦cumulantT⟧ v) v (Hom.id v) x)
      = resultMoments ((⟦cumulantT⟧ v') v' (Hom.id v') x') := by
  funext m
  rcases eq_or_ne m 0 with rfl | hm
  · simp [resultMoments, momOf]
  · rw [resultMoments, resultMoments, (sem_cumulant v x).2 m hm, (sem_cumulant v' x').2 m hm, h]

/-- **The compositional inverse respects similarity.** -/
theorem inverse_similar (h : momOf v x = momOf v' x') :
    resultMoments ((⟦inverseT⟧ v) v (Hom.id v) x)
      = resultMoments ((⟦inverseT⟧ v') v' (Hom.id v') x') := by
  rw [sem_inverse, sem_inverse, resultMoments_single, resultMoments_single, h]

/-! ## Composition -/

/-- Evaluating a polynomial in `p` reads only the moments of `p`. -/
theorem eval_aeval_eq_sum (w : World k) (p : MvPolynomial (Fin w.size) k) (P : Polynomial k) :
    Umbral.eval w.mom (Polynomial.aeval p P)
      = ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * Umbral.eval w.mom (p ^ i) := by
  rw [Polynomial.aeval_eq_sum_range, eval_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [MvPolynomial.smul_eq_C_mul, eval_C_mul]

theorem eval_aeval_similar {p : MvPolynomial (Fin v.size) k} {p' : MvPolynomial (Fin v'.size) k}
    (hp : ∀ j, Umbral.eval v.mom (p ^ j) = Umbral.eval v'.mom (p' ^ j)) (P : Polynomial k) :
    Umbral.eval v.mom (Polynomial.aeval p P) = Umbral.eval v'.mom (Polynomial.aeval p' P) := by
  rw [eval_aeval_eq_sum, eval_aeval_eq_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [hp]

theorem prod_sub_C_eq_aeval {σ : Type} (p : MvPolynomial σ k) (j : ℕ) :
    ∏ i ∈ Finset.range j, (p - C (i : k))
      = Polynomial.aeval p (∏ i ∈ Finset.range j, (Polynomial.X - Polynomial.C (i : k))) := by
  simp [map_prod]

/-- **The moments of `p.α` read the moments of `p` and of `α` separately.** -/
theorem composeMomentsA_similar {p : MvPolynomial (Fin v.size) k} {p' : MvPolynomial (Fin v'.size) k}
    (hp : ∀ j, Umbral.eval v.mom (p ^ j) = Umbral.eval v'.mom (p' ^ j))
    (hx : momOf v x = momOf v' x') :
    composeMomentsA v p x = composeMomentsA v' p' x' := by
  funext m
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [prod_sub_C_eq_aeval, prod_sub_C_eq_aeval, eval_aeval_similar hp, hx]

theorem composeMoments_similar {b : Fin v.size} {b' : Fin v'.size} (hb : momOf v b = momOf v' b')
    (hx : momOf v x = momOf v' x') :
    composeMoments v b x = composeMoments v' b' x' :=
  composeMomentsA_similar (p := X b) (p' := X b') (fun j => congrFun hb j) hx

/-- **Composition respects similarity**, with no condition relating `β` to
`α`. -/
theorem compose_similar {b : Fin v.size} {b' : Fin v'.size} (hb : momOf v b = momOf v' b')
    (hx : momOf v x = momOf v' x') :
    resultMoments ((⟦composeT⟧ v) v (Hom.id v) b v (Hom.id v) x)
      = resultMoments ((⟦composeT⟧ v') v' (Hom.id v') b' v' (Hom.id v') x') := by
  rw [sem_compose, sem_compose, resultMoments_single, resultMoments_single, Hom.id_toFun,
    Hom.id_toFun, id_eq, id_eq, composeMoments_similar hb hx]

/-- **Composition with a polynomial respects similarity**: `p.α` depends on the
moments of `p` and of `α` alone. -/
theorem composeA_similar {p : MvPolynomial (Fin v.size) k} {p' : MvPolynomial (Fin v'.size) k}
    (hp : ∀ j, Umbral.eval v.mom (p ^ j) = Umbral.eval v'.mom (p' ^ j))
    (hx : momOf v x = momOf v' x') :
    resultMoments ((⟦composeAT⟧ v) v (Hom.id v) p v (Hom.id v) x)
      = resultMoments ((⟦composeAT⟧ v') v' (Hom.id v') p' v' (Hom.id v') x') := by
  rw [sem_composeA, sem_composeA, resultMoments_single, resultMoments_single, Hom.id_toFun,
    Hom.id_toFun, MvPolynomial.rename_id_apply, MvPolynomial.rename_id_apply,
    composeMomentsA_similar hp hx]

end

end FreeThms.Umbral.Full
