/-
# Umbral composition, the singleton umbra and the cumulant umbra, as terms

The composition `β.α` is a fresh umbra whose `m`-th
moment is `∑ⱼ E[(β)ⱼ] B_{m,j}(a)`, with `a` the moments of `α`, `(β)ⱼ` the
falling factorial and `B_{m,j}` the partial Bell polynomials. Rota and Taylor
define `β.α` by its moments `E[q_m(β)]`, where `q_m` is the polynomial whose
value at every natural number `n` is the `m`-th moment of `n.α`. By
`bell_dotMoments` the two agree (`sem_compose`).

The singleton umbra `χ` has moments `1, 0, 0, …`, and `χ.α` is the cumulant
umbra of Di Nardo and Senato.
-/

import FreeThms.Umbral.AuxiliaryUmbrae

namespace FreeThms.Umbral.Full

open MvPolynomial (X C rename rename_X)
open FreeThms.Umbral.Restricted (Slot)
open FreeThms.Kripke (QTy QCtx QVar MTm QTyD QEnv)

noncomputable section

variable {k : Type} [CommRing k]

/-! ## Sequences: cons -/

open Kripke.MTm in
/-- `λc s j. if j = 0 then c else s (j - 1)`, by iteration on pairs. -/
def consT : Prog Δ (tK ⇛ tSeq ⇛ tSeq) :=
  -- context: shift, c, s, j
  letP shiftT (lam (lam (lam (fst (iter (var .zero)
    -- context: shift, c, s, j, p
    (lam (pair (.app (snd (var .zero)) zero) (.app (var (.succ (.succ (.succ (.succ .zero)))))
      (snd (var .zero)))))
    (pair (var (.succ (.succ .zero))) (var (.succ .zero))))))))

/-- `c` followed by `s`. -/
def consSeq (c : k) (s : ℕ → k) : ℕ → k
  | 0 => c
  | j + 1 => s j

@[simp] theorem sem_cons {w v v' v'' : World k} (h : Hom w v) (c : k) (h' : Hom v v')
    (f : Val tSeq v') (h'' : Hom v' v'') (j : ℕ) :
    (⟦consT⟧ w) v h c v' h' f v'' h'' j = consSeq c (f v'' h'') j := by
  simp only [consT]
  unfold_sem
  simp only [sem_shift]
  refine (iterN_induction _ (fun i (st : k × Val tSeq v'') => st.1 = consSeq c (f v'' h'') i ∧
      ∀ (u : World k) (g : Hom v'' u) (x : ℕ), st.2 u g x = f u (h''.comp g) (x + i))
    _ ⟨rfl, fun _ _ _ => rfl⟩ ?_ j).1
  rintro i ⟨x, F⟩ ⟨hx, hF⟩
  dsimp only at hx hF
  refine ⟨?_, fun u g y => ?_⟩
  · show F v'' (Hom.id v'') 0 = _
    rw [hF, Hom.comp_id', Nat.zero_add]
    rfl
  · show F u g (y + 1) = _
    rw [hF, Nat.add_right_comm, Nat.add_assoc]

/-! ## Partial Bell polynomials -/

open Kripke.MTm in
/-- `λa B. cons 0 (λm. (B ⋆ Sa)ₘ)`: one step of the Bell recurrence. -/
def bellStepT : Prog Δ (tSeq ⇛ tSeq ⇛ tSeq) :=
  -- context: cons, conv, shift, a, B
  let3P consT convT shiftT (lam (lam (app2 (var (.succ (.succ (.succ (.succ .zero))))) zeroK
    -- context: cons, conv, shift, a, B, m
    (lam (.app (app2 (var (.succ (.succ (.succ (.succ .zero))))) (var .zero) (var (.succ .zero)))
      (.app (var (.succ (.succ (.succ .zero)))) (var (.succ (.succ .zero)))))))))

open Kripke.MTm in
/-- `λa j. (m ↦ B_{m,j}(a))`: **the partial Bell polynomials**, by iteration on
`j`. -/
def bellT : Prog Δ (tSeq ⇛ .nat ⇛ tSeq) :=
  -- context: step, delta, a, j
  let2P bellStepT deltaT (lam (lam (iter (var .zero)
    -- context: step, delta, a, j, B
    (lam (app2 (var (.succ (.succ (.succ (.succ .zero))))) (var (.succ (.succ .zero))) (var .zero)))
    (var (.succ (.succ .zero))))))

/-- A sequence argument whose value does not depend on the world it is read at. -/
def Unif {v : World k} (a : Val tSeq v) (s : ℕ → k) : Prop :=
  ∀ (u : World k) (g : Hom v u), a u g = s

theorem Unif.tr {v v' : World k} {a : Val tSeq v} {s : ℕ → k} (ha : Unif a s) (h : Hom v v') :
    Unif (v := v') (fun u g => a u (h.comp g)) s := fun u g => ha u (h.comp g)

theorem sem_bellStep {w v v' : World k} (h : Hom w v) (a : Val tSeq v) (sa : ℕ → k)
    (ha : Unif a sa) (h' : Hom v v') (B : Val tSeq v') (sB : ℕ → k) (hB : Unif B sB) :
    Unif ((⟦bellStepT⟧ w) v h a v' h' B) (consSeq 0 (conv sB (fun i => sa (i + 1)))) := by
  intro u g
  funext m
  simp only [bellStepT]
  unfold_sem
  simp only [sem_cons, sem_conv, sem_shift, ha _, hB _]

theorem pBell_succ (a : ℕ → k) (j : ℕ) :
    pBell a (j + 1) = consSeq 0 (conv (pBell a j) (fun i => a (i + 1))) := by
  funext m
  cases m <;> rfl

/-- **The partial Bell polynomials, as computed by the term.** -/
theorem sem_bell {w v v' : World k} (h : Hom w v) (a : Val tSeq v) (sa : ℕ → k)
    (ha : Unif a sa) (h' : Hom v v') (j : ℕ) :
    Unif ((⟦bellT⟧ w) v h a v' h' j) (pBell sa j) := by
  simp only [bellT]
  unfold_sem
  refine iterN_induction _ (fun i (T : Val tSeq v') => Unif T (pBell sa i)) _ ?_ ?_ j
  · intro u g
    funext m
    simp only [sem_delta]
    rfl
  · intro i T hT
    rw [pBell_succ]
    exact sem_bellStep _ _ sa (ha.tr h') _ T _ hT

/-! ## Scalars from natural numbers, falling factorials, finite sums -/

open Kripke.MTm in
/-- `λi. 1 + ⋯ + 1` (`i` terms). -/
def natKT : Prog Δ (.nat ⇛ tK) :=
  lam (iter (var .zero) (lam (addK (var .zero) oneK)) zeroK)

theorem iterN_add_one (i : ℕ) : Kripke.iterN (fun c : k => c + 1) i 0 = (i : k) := by
  induction i with
  | zero => exact Nat.cast_zero.symm
  | succ i ih => rw [iterN_succ', ih, Nat.cast_succ]

@[simp] theorem sem_natK {w v : World k} (h : Hom w v) (i : ℕ) : (⟦natKT⟧ w) v h i = (i : k) := by
  simp only [natKT]
  unfold_sem
  exact iterN_add_one i

open Kripke.MTm in
/-- `λp j. p (p - 1) ⋯ (p - j + 1)`: **the falling factorial**, by iteration on
pairs `(i, (p)ᵢ)`. -/
def fallingFactorialT : Prog Δ (tA ⇛ .nat ⇛ tA) :=
  -- context: natK, p, j
  letP natKT (lam (lam (snd (iter (var .zero)
    -- context: natK, p, j, q
    (lam (pair (succ (fst (var .zero))) (mulA (snd (var .zero))
      (addA (var (.succ (.succ .zero)))
        (negA (constA (.app (var (.succ (.succ (.succ .zero)))) (fst (var .zero)))))))))
    (pair zero oneA)))))

@[simp] theorem sem_fallingFactorial {w v v' : World k} (h : Hom w v) (p : MvPolynomial (Fin v.size) k)
    (h' : Hom v v') (j : ℕ) :
    (⟦fallingFactorialT⟧ w) v h p v' h' j = ∏ i ∈ Finset.range j, (rename h'.toFun p - C (i : k)) := by
  simp only [fallingFactorialT]
  unfold_sem
  simp only [sem_natK]
  refine congrArg Prod.snd (iterN_induction _ (fun i (st : ℕ × MvPolynomial (Fin v'.size) k) =>
    st = (i, ∏ l ∈ Finset.range i, (rename h'.toFun p - C (l : k)))) _ (by simp) ?_ j)
  rintro i ⟨i', q⟩ hst
  simp only [Prod.mk.injEq] at hst
  obtain ⟨rfl, rfl⟩ := hst
  simp [Finset.prod_range_succ, sub_eq_add_neg]

open Kripke.MTm in
/-- `λm f. f 0 + ⋯ + f (m - 1)`, by iteration on pairs. -/
def sumToT : Prog Δ (.nat ⇛ tSeq ⇛ tK) :=
  -- context: m, f
  lam (lam (snd (iter (var (.succ .zero))
    -- context: m, f, q
    (lam (pair (succ (fst (var .zero))) (addK (snd (var .zero)) (.app (var (.succ .zero))
      (fst (var .zero))))))
    (pair zero zeroK))))

@[simp] theorem sem_sumTo {w v v' : World k} (h : Hom w v) (m : ℕ) (h' : Hom v v') (f : Val tSeq v') :
    (⟦sumToT⟧ w) v h m v' h' f = ∑ i ∈ Finset.range m, f v' (Hom.id v') i := by
  simp only [sumToT]
  unfold_sem
  refine congrArg Prod.snd (iterN_induction _ (fun i (st : ℕ × k) =>
    st = (i, ∑ l ∈ Finset.range i, f v' (Hom.id v') l)) _ (by simp) ?_ m)
  rintro i ⟨i', q⟩ hst
  simp only [Prod.mk.injEq] at hst
  obtain ⟨rfl, rfl⟩ := hst
  simp [Finset.sum_range_succ]

/-! ## Composition -/

open Kripke.MTm in
/-- `λb a m. ∑_{j ≤ m} E[(b)ⱼ] B_{m,j}(E[a^·])`: the moments of `β.α`. -/
def composeMomentsT : Prog Δ (tU ⇛ tU ⇛ tSeq) :=
  -- context: sum, ff, bell, mom, b, a, m
  let4P sumToT fallingFactorialT bellT momT (lam (lam (lam (app2 (var (.succ (.succ (.succ (.succ (.succ (.succ
    .zero))))))) (succ (var .zero))
    -- context: sum, ff, bell, mom, b, a, m, j
    (lam (mulK
      (evalA (app2 (var (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))
        (injA (var (.succ (.succ (.succ .zero))))) (var .zero)))
      (.app (app2 (var (.succ (.succ (.succ (.succ (.succ .zero))))))
        (.app (var (.succ (.succ (.succ (.succ .zero))))) (var (.succ (.succ .zero)))) (var .zero))
        (var (.succ .zero)))))))))

/-- The moments of the composition `β.α` in a world: `∑_{j ≤ m} E[(β)ⱼ] B_{m,j}(a)`,
with `a` the moments of `α`. -/
def composeMoments (w : World k) (b x : Fin w.size) (m : ℕ) : k :=
  ∑ j ∈ Finset.range (m + 1),
    Umbral.eval w.mom (∏ i ∈ Finset.range j, (X b - C (i : k))) * pBell (momOf w x) j m

theorem sem_composeMoments {w v v' : World k} (h : Hom w v) (b : Fin v.size) (h' : Hom v v')
    (x : Fin v'.size) {v'' : World k} (h'' : Hom v' v'') :
    (⟦composeMomentsT⟧ w) v h b v' h' x v'' h'' = composeMoments v'' (h''.toFun (h'.toFun b)) (h''.toFun x) := by
  funext m
  simp only [composeMomentsT]
  unfold_sem
  simp only [sem_sumTo, sem_fallingFactorial, Hom.id_toFun, id_eq, MvPolynomial.rename_id_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have hu : Unif ((⟦momT⟧ w) v'' (h.comp (h'.comp (h''.comp (Hom.id v'')))) (h''.toFun x))
      (momOf v'' (h''.toFun x)) := fun u g => by rw [sem_mom, momOf_hom]
  rw [sem_bell _ _ _ hu]

open Kripke.MTm in
/-- `λb a. mk (composeMoments b a)`: **the composition** `β.α`. -/
def composeT : Prog Δ (tU ⇛ tU ⇛ .comp tU) :=
  letP composeMomentsT (lam (lam (mk (app2 (var (.succ (.succ .zero))) (var (.succ .zero)) (var .zero)))))

/-- **The composition.** `β.α` allocates one fresh name, whose moments are
`∑_{j ≤ m} E[(β)ⱼ] B_{m,j}(a)`. -/
theorem sem_compose {w v v' : World k} (h : Hom w v) (b : Fin v.size) (h' : Hom v v')
    (x : Fin v'.size) :
    (⟦composeT⟧ w) v h b v' h' x
      = ⟨World.single (composeMoments v' (h'.toFun b) x), Fin.natAdd v'.size 0⟩ := by
  simp only [composeT]
  unfold_sem
  simp only [momentMk]
  rw [sem_composeMoments]
  rfl

/-- The moments of the singleton umbra: `1` at `1`, and `0` from `2` on. -/
def singletonMoments (j : ℕ) : k := if j = 1 then 1 else 0

open Kripke.MTm in
/-- `λj. (0, 1, 0, 0, …)ⱼ`: the moment sequence of `χ`, by iteration on pairs. -/
def singletonMomentsT : Prog Δ tSeq :=
  lam (fst (iter (var .zero) (lam (pair (snd (var .zero)) zeroK)) (pair zeroK oneK)))

/-- `mk singletonMomentsT`: **the singleton umbra** `χ`. The zeroth entry is never read. -/
def singletonT : Prog Δ (.comp tU) :=
  mk singletonMomentsT

theorem iterN_zero_pair (j : ℕ) : (Kripke.iterN (fun p : k × k => (p.2, 0)) j (0, 0)).1 = 0 := by
  induction j with
  | zero => rfl
  | succ j ih => exact ih

theorem iterN_singletonMoments : ∀ j : ℕ,
    (Kripke.iterN (fun p : k × k => (p.2, 0)) j (0, 1)).1 = if j = 1 then 1 else 0
  | 0 => by simp [Kripke.iterN]
  | 1 => by simp [Kripke.iterN]
  | j + 2 => by rw [if_neg (by omega)]; exact iterN_zero_pair j

omit [CommRing k] in
@[simp] theorem Hom.ext_id_apply (w B : World k) (i : Fin (w.size + B.size)) :
    ((Hom.id w).ext B).toFun i = i := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [Hom.ext]

@[simp] theorem sem_singletonMoments {w v : World k} (h : Hom w v) : (⟦singletonMomentsT⟧ w) v h = singletonMoments := by
  funext j
  simp only [singletonMomentsT]
  unfold_sem
  exact iterN_singletonMoments j

theorem sem_singleton (w : World k) :
    (⟦singletonT⟧ w) = ⟨World.single (fun j => if j = 1 then 1 else 0), Fin.natAdd w.size 0⟩ := by
  simp only [singletonT, singletonMomentsT]
  unfold_sem
  simp only [momentMk]
  congr
  funext j
  exact iterN_singletonMoments j

open Kripke.MTm in
/-- `λa. c ← χ; c.a`: **the cumulant umbra** `χ.α` of Di Nardo and Senato. -/
def cumulantT : Prog Δ (tU ⇛ .comp tU) :=
  -- context: χ, compose, a
  let2P singletonT composeT (lam (bind (var (.succ (.succ .zero)))
    -- context: χ, compose, a, c
    (lam (app2 (var (.succ (.succ .zero))) (var .zero) (var (.succ .zero))))))

/-! ## What the composition and the cumulant umbra mean -/

theorem aeval_descPochhammer {σ : Type} (p : MvPolynomial σ k) (j : ℕ) :
    Polynomial.aeval p (descPochhammer k j) = ∏ i ∈ Finset.range j, (p - C (i : k)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [descPochhammer_succ_right, map_mul, ih, Finset.prod_range_succ, map_sub,
      Polynomial.aeval_X, map_natCast, ← map_natCast (C : k →+* MvPolynomial σ k)]

/-- **The composition is Rota and Taylor's.** The moments of `β.α` are
`E[q_m(β)]`, where `q_m = bellPoly a m` is the polynomial whose value at every
natural number `n` is the `m`-th moment of `n.α` (`bellPoly_eval_nat`). -/
theorem composeMoments_eq (v : World k) (b x : Fin v.size) (m : ℕ) :
    composeMoments v b x m = Umbral.eval v.mom (Polynomial.aeval (X b) (bellPoly (momOf v x) m)) := by
  rw [composeMoments, bellPoly, map_sum, eval_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, Polynomial.aeval_C, MvPolynomial.algebraMap_eq, eval_C_mul, aeval_descPochhammer,
    mul_comm]

/-- The inclusion of a block into the world it extends. -/
def Hom.inr (v B : World k) : Hom B (v.append B) :=
  ⟨Fin.natAdd v.size, Fin.natAdd_injective _ _, fun _ _ _ => by simp⟩

theorem momOf_single_ne (f : ℕ → k) {i : ℕ} (hi : i ≠ 0) : momOf (World.single f) 0 i = f i :=
  moments_eq _ _ _ hi

/-- Evaluation of a polynomial in an umbra with the moments of `χ`: only the
constant and the linear coefficient survive. -/
theorem eval_aeval_singleton (v : World k) (c : Fin v.size) (hc : ∀ n, n ≠ 0 → momOf v c n = singletonMoments n)
    (q : Polynomial k) :
    Umbral.eval v.mom (Polynomial.aeval (X c) q) = q.coeff 0 + q.coeff 1 := by
  induction q using Polynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, eval_add, hp, hq, Polynomial.coeff_add, Polynomial.coeff_add]; ring
  | monomial n a _ =>
    rw [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X, MvPolynomial.algebraMap_eq,
      eval_C_mul, ← momOf, hc _ (Nat.succ_ne_zero n)]
    simp only [singletonMoments, Polynomial.coeff_C_mul_X_pow]
    rcases n with _ | n <;> simp

/-- The moments of the name returned by `c ← χ; c.α`, computed from the two
allocations as equations. -/
theorem cumulant_moments (w : World k) (x : Fin w.size) (N : Σ B : World k, Fin (w.size + B.size))
    (hN : N = ⟨World.single singletonMoments, Fin.natAdd w.size 0⟩) (b : Fin (w.size + N.1.size))
    (hb : b = N.2) (G : Σ B : World k, Fin (w.size + N.1.size + B.size))
    (hG : G = ⟨World.single (composeMoments (w.append N.1) b ((Hom.inl w N.1).toFun x)), Fin.natAdd _ 0⟩)
    (m : ℕ) (hm : m ≠ 0) :
    momOf (w.append (N.1.append G.1)) ((Hom.assoc w N.1 G.1).toFun G.2) m
      = (bellPoly (momOf w x) m).coeff 1 := by
  rw [momOf_hom (Hom.assoc w N.1 G.1) G.2]
  subst hG
  rw [show (Fin.natAdd (w.size + N.1.size) 0 : Fin (w.size + N.1.size + 1))
      = (Hom.inr (w.append N.1) (World.single _)).toFun 0 from rfl, momOf_hom,
    momOf_single_ne _ hm]
  subst hb
  subst hN
  rw [composeMoments_eq, momOf_hom (Hom.inl w _) x]
  rw [eval_aeval_singleton _ _ (fun n hn => by
      rw [show (Fin.natAdd w.size 0 : Fin (w.size + 1))
        = (Hom.inr w (World.single singletonMoments)).toFun 0 from rfl, momOf_hom, momOf_single_ne _ hn])]
  rw [Polynomial.coeff_zero_eq_eval_zero, show (0 : k) = ((0 : ℕ) : k) from Nat.cast_zero.symm,
    bellPoly_eval_nat _ (by simp [momOf])]
  simp [dotMoments, hm]

/-- **The cumulant umbra.** `χ.α` allocates the singleton umbra and then one more
fresh name, and returns the latter. Its `m`-th moment, for `m ≥ 1`, is the linear
coefficient of the polynomial `n ↦ E[(n.α)ᵐ]`: the `m`-th cumulant of `α`. -/
theorem sem_cumulant (w : World k) (x : Fin w.size) :
    ((⟦cumulantT⟧ w) w (Hom.id w) x).1.size = 2 ∧
      ∀ m, m ≠ 0 → momOf (w.append ((⟦cumulantT⟧ w) w (Hom.id w) x).1)
        ((⟦cumulantT⟧ w) w (Hom.id w) x).2 m = (bellPoly (momOf w x) m).coeff 1 := by
  simp only [cumulantT]
  unfold_sem
  refine ⟨?_, fun m hm => cumulant_moments w x _ (sem_singleton w) _
    (by simp only [Hom.ext_id_apply]; rfl) _ (sem_compose _ _ _ _) m hm⟩
  rw [sem_compose, sem_singleton]
  rfl

/-- Evaluation of a polynomial in a degenerate umbra, one with moments `cⁱ`, is
evaluation at `c`. -/
theorem eval_aeval_degenerate (v : World k) (b : Fin v.size) (c : k)
    (hb : ∀ n, n ≠ 0 → momOf v b n = c ^ n) (q : Polynomial k) :
    Umbral.eval v.mom (Polynomial.aeval (X b) q) = q.eval c := by
  induction q using Polynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, eval_add, hp, hq, Polynomial.eval_add]
  | monomial n a _ =>
    rw [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X, MvPolynomial.algebraMap_eq,
      eval_C_mul, ← momOf, hb _ (Nat.succ_ne_zero n)]
    simp

/-- **`n̄.α ≡ n.α`.** Composing with the degenerate umbra `n̄`, whose moments are
`nⁱ`, gives the moments of the dot product `n.α`. -/
theorem composeMoments_const (v : World k) (b x : Fin v.size) (n : ℕ)
    (hb : ∀ i, i ≠ 0 → momOf v b i = (n : k) ^ i) (m : ℕ) :
    composeMoments v b x m = dotMoments (momOf v x) n m := by
  rw [composeMoments_eq, eval_aeval_degenerate v b _ hb, bellPoly_eval_nat _ (by simp [momOf])]

end

end FreeThms.Umbral.Full
