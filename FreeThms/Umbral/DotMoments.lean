/-
# The moments of `n.α`, and the partial Bell polynomials

The specification layer for the auxiliary umbrae. Nothing here is
about terms; `Umbral/AuxiliaryUmbrae.lean` proves that the terms compute these
quantities.

* `conv`, the binomial convolution, is the moment sequence of a sum of two
  uncorrelated umbrae (`eval_blocks_pow`), and `dotMoments a n` is its `n`-fold
  power: the moments of `n.α` (`eval_copies`).
* `pBell a j k` is the partial Bell polynomial `B_{k,j}(a)`, defined by its
  recurrence.
* **`bell_dotMoments`**: `∑ⱼ (n)ⱼ B_{k,j}(a) = E[(n.α)ᵏ]`, the dot-moment
  identity of Chapter 3 of the write-up. The proof is umbral. In the world of `n + 1` uncorrelated copies
  of `α`, exchangeability (a swap of two copies is a world morphism) gives
  `E[(n+1).α]^{k+1} = (n + 1) · (E[(n.α)^·] ⋆ Sa)ₖ`. The Bell side satisfies
  the same recurrence by algebra.
-/

import FreeThms.Umbral.Worlds
import Mathlib.RingTheory.Polynomial.Pochhammer

namespace FreeThms.Umbral.Full

open MvPolynomial (X C rename rename_X)

noncomputable section

variable {k : Type} [CommRing k]

/-! ## Moments in a world -/

/-- The moments an umbra has in a world. -/
abbrev momOf (w : World k) (x : Fin w.size) : ℕ → k := fun n => Umbral.eval w.mom (X x ^ n)

/-- A morphism preserves the moments of each name. -/
theorem momOf_hom {w v : World k} (h : Hom w v) (x : Fin w.size) :
    momOf v (h.toFun x) = momOf w x := by
  funext n
  rw [momOf, momOf, ← rename_X, ← map_pow, eval_rename_hom]

/-- The moments of the name of a one-name world. -/
theorem momOf_single (f : ℕ → k) (hf : f 0 = 1) (i : ℕ) : momOf (World.single f) 0 i = f i := by
  rcases eq_or_ne i 0 with rfl | hi
  · show Umbral.eval _ (X 0 ^ 0) = f 0
    rw [pow_zero, eval_one, hf]
  · exact moments_eq _ _ _ hi

/-! ## Binomial convolution -/

/-- The binomial convolution of two sequences: the moments of a sum of two
uncorrelated umbrae. -/
def conv (a b : ℕ → k) (j : ℕ) : k :=
  ∑ i ∈ Finset.range (j + 1), (j.choose i : k) * (a i * b (j - i))

/-- The Leibniz rule for the shift `S`: `S(a ⋆ b) = Sa ⋆ b + a ⋆ Sb`. -/
theorem conv_succ (a b : ℕ → k) (j : ℕ) :
    conv a b (j + 1) = conv (fun i => a (i + 1)) b j + conv a (fun i => b (i + 1)) j := by
  simp only [conv]
  rw [Finset.sum_range_succ' _ (j + 1)]
  simp only [Nat.choose_succ_succ', Nat.cast_add, add_mul, Finset.sum_add_distrib]
  rw [add_assoc]
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    congr 3
    have := Finset.mem_range.mp hi
    omega
  · rw [Finset.sum_range_succ, Nat.choose_succ_self, Nat.cast_zero, zero_mul, add_zero,
      Finset.sum_range_succ' (fun i => (j.choose i : k) * (a i * b (j - i + 1)))]
    simp only [Nat.choose_zero_right, Nat.sub_zero]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    congr 3
    have := Finset.mem_range.mp hi
    omega

/-- The convolution at `j` reads its first argument only up to `j`. -/
theorem conv_congr_left {a a' : ℕ → k} (b : ℕ → k) (j : ℕ) (h : ∀ i ≤ j, a i = a' i) :
    conv a b j = conv a' b j :=
  Finset.sum_congr rfl fun i hi => by rw [h i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]

/-- **The moments of `n.α`**, for an umbra with moments `a`: the `n`-fold binomial
convolution of `a`, starting from the moments of `0`. -/
def dotMoments (a : ℕ → k) : ℕ → ℕ → k
  | 0 => fun j => if j = 0 then 1 else 0
  | n + 1 => conv (dotMoments a n) a

theorem dotMoments_zero (s : ℕ → k) (hs : s 0 = 1) : ∀ n, dotMoments s n 0 = 1
  | 0 => rfl
  | n + 1 => by simp [dotMoments, conv, dotMoments_zero s hs n, hs]

/-- The moments of a sum of polynomials in two disjoint blocks are the binomial
convolution of their moments. -/
theorem eval_blocks_pow (B B' : World k) (p : MvPolynomial (Fin B.size) k)
    (q : MvPolynomial (Fin B'.size) k) (j : ℕ) :
    Umbral.eval (B.append B').mom
        ((rename (Fin.castAdd B'.size) p + rename (Fin.natAdd B.size) q) ^ j)
      = conv (fun i => Umbral.eval B.mom (p ^ i)) (fun i => Umbral.eval B'.mom (q ^ i)) j := by
  rw [add_pow, eval_sum, conv]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← map_natCast (C : k →+* MvPolynomial _ k) (j.choose i), mul_comm _ (C _), eval_C_mul,
    ← map_pow, ← map_pow, eval_blocks]

/-! ## `n` uncorrelated copies -/

/-- The world of `n` names, all with the moments `a`. -/
abbrev copies (a : ℕ → k) (n : ℕ) : World k := ⟨n, fun _ => a⟩

/-- The sum of the names `0, …, n - 1`. -/
def sumX (n : ℕ) : MvPolynomial (Fin n) k := ∑ i, X i

omit [CommRing k] in
theorem copies_mom_succ (a : ℕ → k) (n : ℕ) :
    (copies a (n + 1)).mom = ((copies a n).append (World.single a)).mom := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [copies, World.single]

theorem sumX_succ (n : ℕ) :
    (sumX (n + 1) : MvPolynomial (Fin (n + 1)) k)
      = rename (Fin.castAdd 1) (sumX n) + rename (Fin.natAdd n) (X (0 : Fin 1)) := by
  rw [sumX, sumX, Fin.sum_univ_castSucc, map_sum]
  simp only [rename_X]
  rfl

/-- **The moments of `n` uncorrelated copies**: `E[(α₁ + ⋯ + αₙ)ᵏ]` is the `n`-fold
binomial convolution of the moments of `α`. -/
theorem eval_copies (a : ℕ → k) (ha : a 0 = 1) :
    ∀ (n j : ℕ), Umbral.eval (copies a n).mom (sumX n ^ j) = dotMoments a n j
  | 0, j => by
    rcases eq_or_ne j 0 with rfl | hj
    · simp [dotMoments]
    · simp [sumX, dotMoments, hj, zero_pow hj]
  | n + 1, j => by
    rw [copies_mom_succ, sumX_succ]
    rw [eval_blocks_pow (copies a n) (World.single a) (sumX n) (X 0) j, dotMoments]
    congr 1
    · funext i
      exact eval_copies a ha n i
    · funext i
      exact momOf_single a ha i

/-- The transposition of two names of `copies a n` is a world morphism. -/
def copiesSwap (a : ℕ → k) (n : ℕ) (x y : Fin n) : Hom (copies a n) (copies a n) where
  toFun := Equiv.swap x y
  inj := (Equiv.swap x y).injective
  mom := fun _ _ _ => rfl

theorem rename_swap_sumX (n : ℕ) (x y : Fin n) :
    rename (Equiv.swap x y) (sumX n : MvPolynomial (Fin n) k) = sumX n := by
  rw [sumX, map_sum]
  simp only [rename_X]
  exact Equiv.sum_comp (Equiv.swap x y) (fun i => (X i : MvPolynomial (Fin n) k))

/-- **Exchangeability gives the recurrence of `n.α`.** Each copy contributes the
same to `E[(n+1).α]^{k+1}`, by the swap morphisms; the last copy contributes
`(E[(n.α)^·] ⋆ Sa)ₖ`, by uncorrelation of the last copy from the others. -/
theorem dotMoments_succ_succ (a : ℕ → k) (ha : a 0 = 1) (n j : ℕ) :
    dotMoments a (n + 1) (j + 1) = (n + 1 : k) * conv (dotMoments a n) (fun i => a (i + 1)) j := by
  rw [← eval_copies a ha, pow_succ]
  -- every copy contributes what the last one does
  have hswap : ∀ m : Fin (n + 1),
      Umbral.eval (copies a (n + 1)).mom (sumX (n + 1) ^ j * X m)
        = Umbral.eval (copies a (n + 1)).mom (sumX (n + 1) ^ j * X (Fin.last n)) := by
    intro m
    rw [← eval_rename_hom (copiesSwap a (n + 1) m (Fin.last n)) (sumX (n + 1) ^ j * X (Fin.last n))]
    simp only [copiesSwap, map_mul, map_pow, rename_swap_sumX, rename_X, Equiv.swap_apply_right]
  have hsplit : (sumX (n + 1) ^ j * sumX (n + 1) : MvPolynomial (Fin (n + 1)) k)
      = ∑ m, sumX (n + 1) ^ j * X m := by
    rw [← Finset.mul_sum]; rfl
  rw [hsplit, eval_sum, Finset.sum_congr rfl fun m _ => hswap m, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_succ]
  congr 1
  -- the last copy, against the block of the others
  rw [copies_mom_succ, sumX_succ, show (Fin.last n : Fin (n + 1)) = Fin.natAdd n 0 from rfl,
    ← rename_X (Fin.natAdd n), add_pow, Finset.sum_mul, eval_sum, conv]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [mul_comm _ ((j.choose i : ℕ) : MvPolynomial _ k), mul_assoc, mul_assoc, ← pow_succ,
    ← map_natCast (C : k →+* MvPolynomial _ k) (j.choose i), eval_C_mul, ← map_pow, ← map_pow,
    eval_blocks, eval_copies a ha n i]
  show _ * (_ * momOf (World.single a) 0 (j - i + 1)) = _
  rw [momOf_single a ha]

/-! ## The partial Bell polynomials -/

/-- The partial Bell polynomial `B_{k,j}(a)`, as `pBell a j k`, by the
recurrence `B_{k+1,j+1} = ∑ᵢ C(k,i) B_{i,j} a_{k-i+1}`. -/
def pBell (a : ℕ → k) : ℕ → ℕ → k
  | 0 => fun m => if m = 0 then 1 else 0
  | j + 1 => fun m => match m with
    | 0 => 0
    | m + 1 => conv (pBell a j) (fun i => a (i + 1)) m

theorem pBell_eq_zero_of_lt (a : ℕ → k) : ∀ (j m : ℕ), m < j → pBell a j m = 0
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | j + 1, 0, _ => rfl
  | j + 1, m + 1, h => by
    show conv (pBell a j) (fun i => a (i + 1)) m = 0
    refine Finset.sum_eq_zero fun i hi => ?_
    have := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [pBell_eq_zero_of_lt a j i (by omega), zero_mul, mul_zero]

/-- `∑ⱼ (n)ⱼ B_{m,j}(a)`. -/
def bellSum (a : ℕ → k) (n m : ℕ) : k :=
  ∑ j ∈ Finset.range (m + 1), (n.descFactorial j : k) * pBell a j m

/-- The sum may run over any range containing `0, …, m`. -/
theorem bellSum_eq_of_le (a : ℕ → k) (n m M : ℕ) (h : m ≤ M) :
    bellSum a n m = ∑ j ∈ Finset.range (M + 1), (n.descFactorial j : k) * pBell a j m := by
  refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun j hj hj' => ?_
  rw [pBell_eq_zero_of_lt a j m (by simp at hj hj'; omega), mul_zero]

theorem bellSum_succ_succ (a : ℕ → k) (n m : ℕ) :
    bellSum a (n + 1) (m + 1) = (n + 1 : k) * conv (bellSum a n) (fun i => a (i + 1)) m := by
  rw [bellSum, Finset.sum_range_succ']
  simp only [Nat.succ_descFactorial_succ, Nat.cast_mul, Nat.cast_succ]
  rw [show pBell a 0 (m + 1) = 0 from rfl, mul_zero, add_zero]
  simp only [show ∀ j, pBell a (j + 1) (m + 1) = conv (pBell a j) (fun i => a (i + 1)) m
    from fun _ => rfl, conv, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [bellSum_eq_of_le a n i m hi', Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **The dot-moment identity** (write-up, Chapter 3):
`∑ⱼ (n)ⱼ B_{k,j}(a) = E[(n.α)ᵏ]`, for every natural number `n`. -/
theorem bell_dotMoments (a : ℕ → k) (ha : a 0 = 1) : ∀ (m n : ℕ), bellSum a n m = dotMoments a n m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro n
    rcases m with _ | m
    · simp [bellSum, pBell, dotMoments_zero a ha]
    · rcases n with _ | n
      · simp only [bellSum, dotMoments, Nat.succ_ne_zero, if_false]
        refine Finset.sum_eq_zero fun j _ => ?_
        rcases j with _ | j
        · simp [pBell]
        · simp
      · rw [bellSum_succ_succ, dotMoments_succ_succ a ha]
        congr 1
        exact conv_congr_left _ m fun i hi => ih i (by omega) n

/-- The polynomial `q_k(x) = ∑ⱼ (x)ⱼ B_{k,j}(a)`. By `bell_dotMoments`, its value at
every natural number `n` is the `k`-th moment of `n.α`. -/
def bellPoly (a : ℕ → k) (m : ℕ) : Polynomial k :=
  ∑ j ∈ Finset.range (m + 1), Polynomial.C (pBell a j m) * descPochhammer k j

theorem bellPoly_eval_nat (a : ℕ → k) (ha : a 0 = 1) (m n : ℕ) :
    (bellPoly a m).eval (n : k) = dotMoments a n m := by
  rw [← bell_dotMoments a ha, bellPoly, bellSum, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, descPochhammer_eval_eq_descFactorial, mul_comm]

end

end FreeThms.Umbral.Full
