/-
# Distributivity of composition, over any commutative ring

The algebra behind the representation independence of the composition of a sum
(write-up, Chapter 3, distributivity of composition):
`(p + q).α` has the moments of `p.α + q.α` when `p` and `q` are uncorrelated.
The proof by exponential generating functions needs `ℚ ⊆ k`.
Here everything is derived from the Leibniz rule `conv_succ`:

* the binomial convolution is commutative and associative;
* **Vandermonde** for falling factorials: `(P + Q)ⱼ = ∑ᵢ C(j,i) (P)ᵢ (Q)_{j-i}`;
* **the Bell convolution identity**
  `C(i + l, i) B_{m,i+l} = ∑ᵣ C(m,r) B_{r,i} B_{m-r,l}`;
* **distributivity**: the composition transform `x ↦ (m ↦ ∑ᵢ xᵢ B_{m,i}(a))`
  turns binomial convolution into binomial convolution;
* **associativity** of composition, `C_a ∘ C_b = C_{C_a b}`, from the chain
  rule and distributivity.
-/

import FreeThms.Umbral.DotMoments
import Mathlib.Algebra.BigOperators.Intervals

namespace FreeThms.Umbral.Full

noncomputable section

variable {R : Type} [CommRing R]

/-! ## The convolution algebra -/

/-- The shift of a sequence. -/
def shift (x : ℕ → R) : ℕ → R := fun i => x (i + 1)

theorem conv_succ_shift (x y : ℕ → R) (j : ℕ) : conv x y (j + 1) = conv (shift x) y j + conv x (shift y) j :=
  conv_succ x y j

theorem conv_add_left (x x' y : ℕ → R) (j : ℕ) :
    conv (fun i => x i + x' i) y j = conv x y j + conv x' y j := by
  simp only [conv, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem conv_add_right (x y y' : ℕ → R) (j : ℕ) :
    conv x (fun i => y i + y' i) j = conv x y j + conv x y' j := by
  simp only [conv, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem conv_smul_left (c : R) (x y : ℕ → R) (j : ℕ) :
    conv (fun i => c * x i) y j = c * conv x y j := by
  simp only [conv, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem shift_conv (x y : ℕ → R) : shift (conv x y) = fun j => conv (shift x) y j + conv x (shift y) j :=
  funext fun j => conv_succ x y j

theorem conv_comm : ∀ (j : ℕ) (x y : ℕ → R), conv x y j = conv y x j
  | 0, x, y => by simp [conv, mul_comm]
  | j + 1, x, y => by
    rw [conv_succ, conv_succ, conv_comm j (fun i => x (i + 1)) y,
      conv_comm j x (fun i => y (i + 1)), add_comm]

theorem conv_assoc : ∀ (j : ℕ) (x y z : ℕ → R), conv (conv x y) z j = conv x (conv y z) j
  | 0, x, y, z => by simp [conv, mul_assoc]
  | j + 1, x, y, z => by
    rw [conv_succ, conv_succ x, show (fun i => conv x y (i + 1)) = shift (conv x y) from rfl,
      shift_conv, conv_add_left, conv_assoc j, conv_assoc j, conv_assoc j,
      show (fun i => conv y z (i + 1)) = shift (conv y z) from rfl, shift_conv, conv_add_right,
      add_assoc]
    rfl

/-! ## Vandermonde for falling factorials -/

/-- The falling factorial `(P)ⱼ = P (P - 1) ⋯ (P - j + 1)`. -/
def ffSeq (P : R) (j : ℕ) : R := ∏ r ∈ Finset.range j, (P - (r : R))

theorem ffSeq_succ (P : R) (j : ℕ) : ffSeq P (j + 1) = ffSeq P j * (P - j) :=
  Finset.prod_range_succ _ _

/-- **Vandermonde for falling factorials**: `(P + Q)ⱼ = ((P)_· ⋆ (Q)_·)ⱼ`. -/
theorem ffSeq_add (P Q : R) : ∀ j, ffSeq (P + Q) j = conv (ffSeq P) (ffSeq Q) j
  | 0 => by simp [ffSeq, conv]
  | j + 1 => by
    rw [ffSeq_succ, ffSeq_add P Q j, conv_succ]
    simp only [conv, ffSeq_succ, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [Nat.cast_sub hi']
    ring

/-! ## The Bell convolution identity -/

theorem shift_pBell_succ (a : ℕ → R) (j : ℕ) : shift (pBell a (j + 1)) = conv (pBell a j) (shift a) :=
  rfl

theorem shift_pBell_zero (a : ℕ → R) : shift (pBell a 0) = fun _ => 0 := by
  funext m; simp [shift, pBell]

theorem conv_zero_left (y : ℕ → R) (j : ℕ) : conv (fun _ => (0 : R)) y j = 0 := by
  simp [conv]

theorem conv_zero_right (x : ℕ → R) (j : ℕ) : conv x (fun _ => (0 : R)) j = 0 := by
  simp [conv]

/-- **The Bell convolution identity**:
`C(i + l, i) B_{m,i+l}(a) = ∑ᵣ C(m,r) B_{r,i}(a) B_{m-r,l}(a)`. -/
theorem bell_conv (a : ℕ → R) : ∀ (m i l : ℕ),
    ((i + l).choose i : R) * pBell a (i + l) m = conv (pBell a i) (pBell a l) m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro i l
    rcases m with _ | m
    · rcases i with _ | i <;> rcases l with _ | l <;> simp [conv, pBell]
    · rw [conv_succ_shift]
      -- the two terms of the Leibniz rule
      have hl : ∀ i', conv (shift (pBell a (i' + 1))) (pBell a l) m
          = ((i' + l).choose i' : R) * pBell a (i' + l + 1) (m + 1) := by
        intro i'
        rw [shift_pBell_succ, conv_assoc,
          show conv (shift a) (pBell a l) = conv (pBell a l) (shift a) from funext fun r => conv_comm r _ _,
          ← conv_assoc, conv_congr_left _ m (fun r hr => (ih r (by omega) i' l).symm),
          conv_smul_left]
        rfl
      have hr : ∀ l', conv (pBell a i) (shift (pBell a (l' + 1))) m
          = ((i + l').choose i : R) * pBell a (i + l' + 1) (m + 1) := by
        intro l'
        rw [shift_pBell_succ, ← conv_assoc,
          conv_congr_left _ m (fun r hr => (ih r (by omega) i l').symm), conv_smul_left]
        rfl
      rcases i with _ | i <;> rcases l with _ | l
      · rw [shift_pBell_zero, conv_zero_left, conv_zero_right]
        simp [pBell]
      · rw [shift_pBell_zero, conv_zero_left, zero_add, hr]
        simp
      · rw [shift_pBell_zero, conv_zero_right, add_zero, hl]
        simp
      · rw [hl, hr, show i + 1 + (l + 1) = (i + l + 1) + 1 by omega,
          show i + (l + 1) + 1 = (i + l + 1) + 1 by omega,
          show i + 1 + l = i + l + 1 by omega, Nat.choose_succ_succ', Nat.cast_add]
        ring_nf

/-! ## Distributivity -/

/-- The composition transform of a sequence `x`: `m ↦ ∑_{i ≤ m} xᵢ B_{m,i}(a)`.
With `xᵢ = E[(β)ᵢ]` it is the moment sequence of `β.α`. -/
def compTransform (a x : ℕ → R) (m : ℕ) : R :=
  ∑ i ∈ Finset.range (m + 1), x i * pBell a i m

theorem compTransform_eq_of_le (a x : ℕ → R) (m M : ℕ) (h : m ≤ M) :
    compTransform a x m = ∑ i ∈ Finset.range (M + 1), x i * pBell a i m := by
  refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun i hi hi' => ?_
  rw [pBell_eq_zero_of_lt a i m (by simp at hi hi'; omega), mul_zero]

/-- **Distributivity**: the composition transform takes binomial convolution to
binomial convolution. Read at `xᵢ = E[(β)ᵢ]` and `yᵢ = E[(β')ᵢ]` for
uncorrelated `β`, `β'`, it says that `(β + β').α` has the moments of
`β.α + β'.α`. -/
theorem compTransform_conv (a x y : ℕ → R) (m : ℕ) :
    compTransform a (conv x y) m = conv (compTransform a x) (compTransform a y) m := by
  -- the right side, as a double sum over `i, l ≤ m`
  have hR : conv (compTransform a x) (compTransform a y) m
      = ∑ i ∈ Finset.range (m + 1), ∑ l ∈ Finset.range (m + 1),
          x i * y l * (((i + l).choose i : R) * pBell a (i + l) m) := by
    calc conv (compTransform a x) (compTransform a y) m
        = ∑ r ∈ Finset.range (m + 1), ∑ i ∈ Finset.range (m + 1), ∑ l ∈ Finset.range (m + 1),
            x i * y l * ((m.choose r : R) * (pBell a i r * pBell a l (m - r))) := by
          unfold conv
          refine Finset.sum_congr rfl fun r hr => ?_
          have hr' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
          rw [compTransform_eq_of_le a x r m hr', compTransform_eq_of_le a y (m - r) m (by omega),
            Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun l _ => by ring
      _ = ∑ i ∈ Finset.range (m + 1), ∑ l ∈ Finset.range (m + 1), ∑ r ∈ Finset.range (m + 1),
            x i * y l * ((m.choose r : R) * (pBell a i r * pBell a l (m - r))) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
          rw [← Finset.mul_sum, bell_conv]
          rfl
  set f : ℕ → ℕ → R := fun i l => x i * y l * (((i + l).choose i : R) * pBell a (i + l) m) with hf
  calc compTransform a (conv x y) m
      = ∑ j ∈ Finset.range (m + 1), ∑ i ∈ Finset.range (j + 1), f i (j - i) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [conv, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hi' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        show _ = x i * y (j - i) * (((i + (j - i)).choose i : R) * pBell a (i + (j - i)) m)
        rw [show i + (j - i) = j by omega]
        ring
    _ = ∑ i ∈ Finset.range (m + 1), ∑ l ∈ Finset.range (m + 1 - i), f i l :=
        Finset.sum_range_diag_flip (m + 1) f
    _ = ∑ i ∈ Finset.range (m + 1), ∑ l ∈ Finset.range (m + 1), f i l := by
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun l hl hl' => ?_
        simp only [Finset.mem_range] at hl hl'
        show x i * y l * (((i + l).choose i : R) * pBell a (i + l) m) = 0
        rw [pBell_eq_zero_of_lt a (i + l) m (by omega), mul_zero, mul_zero]
    _ = conv (compTransform a x) (compTransform a y) m := hR.symm

/-! ## Associativity of composition

In generating functions, with `A(t) = ∑_{i ≥ 1} aᵢ tⁱ/i!`, the composition
transform `C_a` sends the series `X` to `X ∘ A`. The chain rule, distributivity
and induction on `j` give `B_{·,j}(C_a b) = C_a(B_{·,j}(b))`, and associativity
`C_a ∘ C_b = C_{C_a b}` follows by exchanging two finite sums. -/

/-- The convolution is linear in its first argument over a finite sum. -/
theorem conv_sum_left {ι : Type} (s : Finset ι) (f : ι → ℕ → R) (y : ℕ → R) (j : ℕ) :
    conv (fun r => ∑ i ∈ s, f i r) y j = ∑ i ∈ s, conv (f i) y j := by
  simp only [conv, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

/-- The convolution with `(1, 0, 0, …)` is the identity. -/
theorem conv_delta_right (x : ℕ → R) (m : ℕ) : conv x (fun r => if r = 0 then 1 else 0) m = x m := by
  rw [conv, Finset.sum_eq_single m]
  · simp
  · intro i hi him
    have := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    simp [show m - i ≠ 0 by omega]
  · exact fun h => absurd (Finset.mem_range.mpr (Nat.lt_succ_self m)) h

/-- **The chain rule**: `C_a(x)_{m+1} = (C_a(Sx) ⋆ Sa)_m`. In generating
functions, `(X ∘ A)' = (X' ∘ A) · A'`. -/
theorem compTransform_succ (a x : ℕ → R) (m : ℕ) :
    compTransform a x (m + 1) = conv (compTransform a (shift x)) (shift a) m := by
  rw [compTransform, Finset.sum_range_succ',
    conv_congr_left _ m (fun r hr => compTransform_eq_of_le a (shift x) r m hr), conv_sum_left]
  simp only [conv_smul_left]
  rw [show pBell a 0 (m + 1) = 0 by simp [pBell], mul_zero, add_zero]
  rfl

/-- **Composition commutes with the partial Bell polynomials**:
`B_{·,j}(C_a b) = C_a(B_{·,j}(b))`. In generating functions,
`(B ∘ A)ʲ/j! = (Bʲ/j!) ∘ A`. -/
theorem pBell_compTransform (a b : ℕ → R) :
    ∀ j, pBell (compTransform a b) j = compTransform a (pBell b j)
  | 0 => by
    funext m
    simp only [compTransform]
    rw [Finset.sum_eq_single 0 (fun i _ hi => by simp [pBell, hi])
      (fun h => absurd (Finset.mem_range.mpr (Nat.succ_pos m)) h)]
    simp [pBell]
  | j + 1 => by
    funext m
    rcases m with _ | m
    · simp [compTransform, pBell]
    · show conv (pBell (compTransform a b) j) (fun i => compTransform a b (i + 1)) m
        = compTransform a (pBell b (j + 1)) (m + 1)
      rw [compTransform_succ a (pBell b (j + 1)), shift_pBell_succ, pBell_compTransform a b j,
        show (fun i => compTransform a b (i + 1)) = conv (compTransform a (shift b)) (shift a) from
          funext fun i => compTransform_succ a b i,
        show compTransform a (conv (pBell b j) (shift b))
          = conv (compTransform a (pBell b j)) (compTransform a (shift b)) from
          funext fun i => compTransform_conv a _ _ i]
      exact (conv_assoc m _ _ _).symm

/-- **Associativity of composition**: `C_a ∘ C_b = C_{C_a b}`. In generating
functions, `(X ∘ B) ∘ A = X ∘ (B ∘ A)`. -/
theorem compTransform_assoc (a b x : ℕ → R) (m : ℕ) :
    compTransform a (compTransform b x) m = compTransform (compTransform a b) x m := by
  calc compTransform a (compTransform b x) m
      = ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1), x j * (pBell b j i * pBell a i m) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [compTransform_eq_of_le b x i m (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)),
          Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ j ∈ Finset.range (m + 1), ∑ i ∈ Finset.range (m + 1), x j * (pBell b j i * pBell a i m) :=
        Finset.sum_comm
    _ = compTransform (compTransform a b) x m := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [pBell_compTransform, compTransform, Finset.mul_sum]

end

end FreeThms.Umbral.Full
