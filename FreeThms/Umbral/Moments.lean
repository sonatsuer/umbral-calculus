/-
# The moment model, and which renamings it admits

The semantics: an umbra is a **name**, an assignment gives
each name a moment sequence, and the evaluation functional `E` of a monomial in
*distinct* umbrae is the product of the corresponding moments. Uncorrelation —
Rota's axiom (2) — is definitional in this model rather than assumed.

This file is the mathematical core of the development. It explains why the
substitution principle renames along injections and not along similarity itself.

## What goes wrong with similarity as a relation

The obvious candidate is Rota's similarity itself: relate `α` to `β` when they
have the same moments, and close up under the polynomial operations. **That
relation does not respect the dictionary**, and `E` is exactly the method that
rejects it.

Suppose `α ≠ α'` are distinct names with the same moment sequence, and `β` has
that sequence too. Similarity relates `α ~ β` and `α' ~ β`, so closure under
multiplication relates `α·α'` to `β²`. But

    E[α·α'] = a₁·a₁        (distinct names — uncorrelation applies)
    E[β²]   = a₂           (one name squared — it does not)

and `a₁² ≠ a₂` unless the variance `a₂ - a₁²` is zero. The relation relates two
distinct umbrae to one, which uncorrelation forbids once the variance is
nonzero (`Restricted.no_common_target`). See `injectivity_necessary` below for the
same failure for a renaming.

## Injective renamings respect the dictionary

The graphs of **injective** moment-preserving renamings do. If `σ : Name → Name` is
injective and carries each name to one with the same moments, then `E` is
preserved (`eval_rename`), and so is everything built from it.

So the load-bearing hypothesis is injectivity, and that is not a technical
convenience — it *is* uncorrelation, in the form the abstraction theorem can
consume. Distinctness of names does load-bearing semantic work, and it does it
here, in the fresh-name-free fragment, as the condition that renamings be
injective.
-/

import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Rat.Defs

namespace FreeThms.Umbral

open MvPolynomial Finsupp

noncomputable section

variable {k : Type*} [CommRing k] {Name : Type*}

/-- An assignment of moment sequences to names. `ρ a n` is the `n`-th moment of
the umbra named `a`; only `n ≥ 1` is ever consulted, since `E[α⁰] = E[1] = 1`. -/
abbrev Assign (Name : Type*) (k : Type*) := Name → ℕ → k

/-- The weight of a monomial: the product of the moments its exponents select.
The product runs over the *support*, so distinct names contribute independently —
this single definition is Rota's uncorrelation axiom. -/
def weight (ρ : Assign Name k) (d : Name →₀ ℕ) : k :=
  d.prod fun a i => ρ a i

/--
**The umbral evaluation functional.** Linear in the polynomial, and on a monomial
the product of the moments of its distinct umbrae.

`E` is emphatically *not* a ring homomorphism: `E[α²] = a₂`, not `a₁²`. That is
the whole point of the umbral calculus, and it is why `MvPolynomial.eval` cannot
be reused here.
-/
def eval (ρ : Assign Name k) (p : MvPolynomial Name k) : k :=
  ∑ d ∈ p.support, p.coeff d * weight ρ d

@[simp] theorem weight_zero (ρ : Assign Name k) : weight ρ (0 : Name →₀ ℕ) = 1 := by
  simp [weight]

/-- `eval` may be computed over any finite set containing the support; the extra
terms have zero coefficient. This is the form additivity is proved from. -/
theorem eval_eq_sum_of_subset (ρ : Assign Name k) (p : MvPolynomial Name k)
    {s : Finset (Name →₀ ℕ)} (hs : p.support ⊆ s) :
    eval ρ p = ∑ d ∈ s, p.coeff d * weight ρ d :=
  Finset.sum_subset hs fun d _ hd => by
    have hz : p.coeff d = 0 := by
      by_contra h
      exact hd (MvPolynomial.mem_support_iff.mpr h)
    rw [hz, zero_mul]

@[simp] theorem eval_monomial (ρ : Assign Name k) (d : Name →₀ ℕ) (c : k) :
    eval ρ (MvPolynomial.monomial d c) = c * weight ρ d := by
  classical
  rw [eval_eq_sum_of_subset ρ _ (MvPolynomial.support_monomial_subset (s := d) (a := c))]
  simp [MvPolynomial.coeff_monomial]

theorem eval_add (ρ : Assign Name k) (p q : MvPolynomial Name k) :
    eval ρ (p + q) = eval ρ p + eval ρ q := by
  classical
  have hp : p.support ⊆ p.support ∪ q.support := Finset.subset_union_left
  have hq : q.support ⊆ p.support ∪ q.support := Finset.subset_union_right
  have hpq : (p + q).support ⊆ p.support ∪ q.support := MvPolynomial.support_add
  rw [eval_eq_sum_of_subset ρ _ hpq, eval_eq_sum_of_subset ρ _ hp,
      eval_eq_sum_of_subset ρ _ hq, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun d _ => by rw [MvPolynomial.coeff_add, add_mul]

@[simp] theorem eval_C (ρ : Assign Name k) (c : k) :
    eval ρ (MvPolynomial.C c) = c := by
  rw [MvPolynomial.C_apply, eval_monomial, weight_zero, mul_one]

@[simp] theorem eval_zero (ρ : Assign Name k) : eval ρ (0 : MvPolynomial Name k) = 0 := by
  simpa using eval_C ρ (0 : k)

@[simp] theorem eval_one (ρ : Assign Name k) : eval ρ (1 : MvPolynomial Name k) = 1 := by
  simpa using eval_C ρ (1 : k)

theorem eval_neg (ρ : Assign Name k) (p : MvPolynomial Name k) :
    eval ρ (-p) = - eval ρ p := by
  have h : eval ρ p + eval ρ (-p) = 0 := by
    rw [← eval_add, add_neg_cancel, eval_zero]
  exact eq_neg_of_add_eq_zero_right h

theorem eval_sub (ρ : Assign Name k) (p q : MvPolynomial Name k) :
    eval ρ (p - q) = eval ρ p - eval ρ q := by
  rw [sub_eq_add_neg, eval_add, eval_neg, sub_eq_add_neg]

/-- The moment sequence an assignment gives a name, read off from `E` itself.
`μ ρ a 0 = 1` automatically, which is the normalization Rota–Taylor impose by
hand. -/
def moments (ρ : Assign Name k) (a : Name) : ℕ → k :=
  fun n => eval ρ (MvPolynomial.X a ^ n)

theorem moments_eq (ρ : Assign Name k) (a : Name) (n : ℕ) (hn : n ≠ 0) :
    moments ρ a n = ρ a n := by
  classical
  rw [moments, MvPolynomial.X_pow_eq_monomial, eval_monomial, one_mul, weight,
      Finsupp.prod, Finsupp.support_single a hn, Finset.prod_singleton,
      Finsupp.single_eq_same]

@[simp] theorem moments_zero (ρ : Assign Name k) (a : Name) : moments ρ a 0 = 1 := by
  simp [moments]

/-- `E` of a single umbra is its first moment. -/
@[simp] theorem eval_X (ρ : Assign Name k) (a : Name) :
    eval ρ (MvPolynomial.X a) = ρ a 1 := by
  have h := moments_eq ρ a 1 one_ne_zero
  rwa [moments, pow_one] at h

/--
**Similarity.** Two umbrae are similar when they have the same moment sequence —
Rota's `α ≡ β`. Note this is a relation *across* two assignments, which is what
lets it relate umbrae under two different assignments.
-/
def Similar (ρ₁ ρ₂ : Assign Name k) (a b : Name) : Prop :=
  ∀ n, moments ρ₁ a n = moments ρ₂ b n

theorem Similar.of_forall_ne_zero {ρ₁ ρ₂ : Assign Name k} {a b : Name}
    (h : ∀ n, n ≠ 0 → ρ₁ a n = ρ₂ b n) : Similar ρ₁ ρ₂ a b := by
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [moments_eq _ _ _ hn, moments_eq _ _ _ hn]
    exact h n hn

/-! ## The renaming theorem

The technical heart: `E` is preserved by injective moment-preserving renamings.
Injectivity is used exactly once, and the failure without it is the content of
`injectivity_necessary`. -/

/-- A renaming that preserves moments, from one assignment to another. -/
structure MomentMap (ρ₁ ρ₂ : Assign Name k) where
  /-- The underlying map on names. -/
  toFun : Name → Name
  /-- **Injective** — this is uncorrelation, and it is what the whole file turns
  on. Without it `E` is not preserved. -/
  inj : Function.Injective toFun
  /-- Each name goes to one with the same moments. -/
  similar : ∀ a, Similar ρ₁ ρ₂ a (toFun a)

/-- The weight of a monomial is preserved: the renamed monomial selects the same
moments, because injectivity keeps the exponents apart. -/
theorem weight_mapDomain {ρ₁ ρ₂ : Assign Name k} (σ : MomentMap ρ₁ ρ₂)
    (d : Name →₀ ℕ) :
    weight ρ₂ (d.mapDomain σ.toFun) = weight ρ₁ d := by
  classical
  rw [weight, weight, Finsupp.prod_mapDomain_index_inj σ.inj]
  refine Finsupp.prod_congr ?_
  intro a ha
  have hne : d a ≠ 0 := Finsupp.mem_support_iff.mp ha
  have h := (σ.similar a) (d a)
  rw [moments_eq ρ₁ a (d a) hne, moments_eq ρ₂ (σ.toFun a) (d a) hne] at h
  exact h.symm

/--
**`E` is preserved by injective moment-preserving renaming.** The parametricity
obligation for the evaluation method, and the only hard lemma of the development.
-/
theorem eval_rename {ρ₁ ρ₂ : Assign Name k} (σ : MomentMap ρ₁ ρ₂)
    (p : MvPolynomial Name k) :
    eval ρ₂ (MvPolynomial.rename σ.toFun p) = eval ρ₁ p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial d c => rw [MvPolynomial.rename_monomial, eval_monomial, eval_monomial,
                        weight_mapDomain σ d]
  | add p q hp hq => rw [map_add, eval_add, eval_add, hp, hq]

/--
The transposition of two **similar** umbrae is a moment map: it preserves
moments because `a` and `b` have the same ones, and it is injective because a
transposition is a bijection.
-/
def swapMap [DecidableEq Name] (ρ : Assign Name k) {a b : Name} (h : Similar ρ ρ a b) :
    MomentMap ρ ρ where
  toFun := Equiv.swap a b
  inj := (Equiv.swap a b).injective
  similar := by
    intro c
    rcases eq_or_ne c a with rfl | hca
    · rw [Equiv.swap_apply_left]; exact h
    · rcases eq_or_ne c b with rfl | hcb
      · rw [Equiv.swap_apply_right]; intro n; exact (h n).symm
      · rw [Equiv.swap_apply_of_ne_of_ne hca hcb]; intro n; rfl

/-! ## Injectivity is necessary, not convenient

The theorem above assumes `σ` injective. This section shows the assumption cannot
be dropped. -/

theorem X_eq_monomial_single (c : Name) :
    (MvPolynomial.X c : MvPolynomial Name k) = MvPolynomial.monomial (Finsupp.single c 1) 1 := by
  rw [← MvPolynomial.X_pow_eq_monomial, pow_one]

/-- The weight of a two-name monomial factors — uncorrelation, concretely. -/
theorem weight_single_add_single (ρ : Assign Name k) {a b : Name} (hab : a ≠ b)
    {i j : ℕ} (hi : i ≠ 0) (hj : j ≠ 0) :
    weight ρ (Finsupp.single a i + Finsupp.single b j) = ρ a i * ρ b j := by
  classical
  have hsa : (Finsupp.single a i).support = {a} := Finsupp.support_single a hi
  have hsb : (Finsupp.single b j).support = {b} := Finsupp.support_single b hj
  have hdisj : Disjoint (Finsupp.single a i).support (Finsupp.single b j).support := by
    rw [hsa, hsb]; simpa using hab
  have hsupp : (Finsupp.single a i + Finsupp.single b j).support = {a, b} := by
    rw [Finsupp.support_add_eq hdisj, hsa, hsb]; rfl
  rw [weight, Finsupp.prod, hsupp, Finset.prod_pair hab]
  simp [Finsupp.single_eq_of_ne hab, Finsupp.single_eq_of_ne (Ne.symm hab)]

/-- `E` on a product of two *distinct* umbrae is the product of their first
moments. This is Rota's axiom (2) holding definitionally in the moment model. -/
theorem eval_X_mul_X (ρ : Assign Name k) {a b : Name} (hab : a ≠ b) :
    eval ρ (MvPolynomial.X a * MvPolynomial.X b) = ρ a 1 * ρ b 1 := by
  rw [X_eq_monomial_single, X_eq_monomial_single, MvPolynomial.monomial_mul, one_mul,
      eval_monomial, one_mul, weight_single_add_single ρ hab one_ne_zero one_ne_zero]

/-- `E` on a single umbra squared is its *second* moment — not the square of the
first. The gap between this and `eval_X_mul_X` is the entire obstruction. -/
theorem eval_X_sq (ρ : Assign Name k) (a : Name) :
    eval ρ (MvPolynomial.X a ^ 2) = ρ a 2 := by
  rw [← moments, moments_eq ρ a 2 two_ne_zero]

/-! ### Evaluation is linear, and monomials in two umbrae factor

What is needed to compute `E` on an expanded binomial. -/

theorem eval_C_mul (ρ : Assign Name k) (c : k) (p : MvPolynomial Name k) :
    eval ρ (MvPolynomial.C c * p) = c * eval ρ p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial d x =>
      rw [MvPolynomial.C_mul_monomial, eval_monomial, eval_monomial, mul_assoc]
  | add p q hp hq => rw [mul_add, eval_add, eval_add, hp, hq, mul_add]

theorem eval_sum (ρ : Assign Name k) {ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial Name k) :
    eval ρ (∑ i ∈ s, f i) = ∑ i ∈ s, eval ρ (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, eval_add, ih]

/-- The weight of a one-umbra monomial is that umbra's moment — uniformly in the
exponent, including exponent `0`, because `μ(0) = 1`. -/
theorem weight_single (ρ : Assign Name k) (a : Name) (i : ℕ) :
    weight ρ (Finsupp.single a i) = moments ρ a i := by
  classical
  rcases eq_or_ne i 0 with rfl | hi
  · simp [weight]
  · rw [weight, Finsupp.prod, Finsupp.support_single a hi, Finset.prod_singleton,
        Finsupp.single_eq_same, moments_eq ρ a i hi]

/-- **Uncorrelation, in the form the binomial expansion needs**: a monomial in two
distinct umbrae has weight the product of their moments, at *every* pair of
exponents. -/
theorem weight_two (ρ : Assign Name k) {a b : Name} (hab : a ≠ b) (i j : ℕ) :
    weight ρ (Finsupp.single a i + Finsupp.single b j)
      = moments ρ a i * moments ρ b j := by
  rcases eq_or_ne i 0 with rfl | hi
  · simp [weight_single]
  · rcases eq_or_ne j 0 with rfl | hj
    · simp [weight_single]
    · rw [weight_single_add_single ρ hab hi hj, moments_eq ρ a i hi,
          moments_eq ρ b j hj]

theorem eval_X_pow_mul_X_pow (ρ : Assign Name k) {a b : Name} (hab : a ≠ b)
    (i j : ℕ) :
    eval ρ (MvPolynomial.X a ^ i * MvPolynomial.X b ^ j)
      = moments ρ a i * moments ρ b j := by
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial,
      MvPolynomial.monomial_mul, one_mul, eval_monomial, one_mul, weight_two ρ hab]

/--
**The binomial convolution.** `E[(α+β)ⁿ] = ∑ₖ C(n,k)·μ_α(k)·μ_β(n−k)` for
distinct umbrae.

This is the identity that licenses umbral notation: writing `(α+β)ⁿ` and
expanding as if `α` and `β` were numbers computes the convolution of their moment
sequences. Every step of the expansion uses uncorrelation, via `weight_two`.
-/
theorem eval_add_pow (ρ : Assign Name k) {a b : Name} (hab : a ≠ b) (n : ℕ) :
    eval ρ ((MvPolynomial.X a + MvPolynomial.X b) ^ n)
      = ∑ i ∈ Finset.range (n + 1),
          (n.choose i : k) * (moments ρ a i * moments ρ b (n - i)) := by
  classical
  rw [add_pow, eval_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← map_natCast (MvPolynomial.C : k →+* MvPolynomial Name k) (n.choose i),
      mul_comm _ (MvPolynomial.C _), eval_C_mul, eval_X_pow_mul_X_pow ρ hab]

/--
**Injectivity cannot be dropped from `eval_rename`.**

An assignment, a moment-*preserving* but non-injective renaming, and a
polynomial on which `E` is not preserved. The renaming here is constant, so it
trivially preserves moments — every name has the same ones — and it fails only
because it identifies two distinct umbrae.

This is the formal content of Rota's uncorrelation axiom as a constraint on the
respecting relations: **similarity alone does not respect the dictionary at
`U`** once the variance is nonzero. Relating `α ~ β` and `α' ~ β` for distinct `α, α'` would let the
closure under multiplication relate `α·α'` to `β²`, and `E` distinguishes them.
-/
theorem injectivity_necessary :
    ∃ (ρ : Assign ℕ ℤ) (σ : ℕ → ℕ) (p : MvPolynomial ℕ ℤ),
      (∀ a, Similar ρ ρ a (σ a)) ∧
      eval ρ (MvPolynomial.rename σ p) ≠ eval ρ p := by
  classical
  refine ⟨fun _ n => if n = 1 then 0 else 1, fun _ => 0,
          MvPolynomial.X 0 * MvPolynomial.X 1, ?_, ?_⟩
  · -- every name has the same moment sequence, so a constant map preserves moments
    intro a
    refine Similar.of_forall_ne_zero ?_
    intro n _
    rfl
  · rw [map_mul, MvPolynomial.rename_X, MvPolynomial.rename_X, ← sq,
        eval_X_sq, eval_X_mul_X _ (by decide : (0 : ℕ) ≠ 1)]
    norm_num

/-! ## Umbral calculi and moment models

An umbral calculus is a linear evaluation with `E[1] = 1` that factors over
distinct umbrae (write-up, Chapter 1). The moment model of every assignment is
one, and every umbral calculus is the moment model of its own moments. -/

variable (k Name) in
/-- An **umbral calculus** on the umbrae `Name` over `k`: a `k`-linear evaluation
`E : k[Name] → k` with `E[1] = 1` that factors over distinct umbrae. -/
structure UmbralCalculus where
  /-- The evaluation. -/
  E : MvPolynomial Name k →ₗ[k] k
  /-- `E[1] = 1`. -/
  map_one : E 1 = 1
  /-- Uncorrelation: for the distinct umbrae of a finite set `s` and exponents
  `e`, `E[∏ α^{e α}] = ∏ E[α^{e α}]`. -/
  uncorrelation : ∀ (s : Finset Name) (e : Name → ℕ),
    E (∏ a ∈ s, MvPolynomial.X a ^ e a) = ∏ a ∈ s, E (MvPolynomial.X a ^ e a)

/-- Adding a single exponent at a name outside the support multiplies the
weight by the moment of that name. -/
theorem weight_add_single (ρ : Assign Name k) {d : Name →₀ ℕ} {a : Name} (hd : d a = 0)
    (i : ℕ) : weight ρ (d + Finsupp.single a i) = weight ρ d * moments ρ a i := by
  classical
  rcases eq_or_ne i 0 with rfl | hi
  · simp
  · have hdisj : Disjoint d.support (Finsupp.single a i).support := by
      rw [Finsupp.support_single a hi, Finset.disjoint_singleton_right]
      exact Finsupp.notMem_support_iff.mpr hd
    rw [weight, Finsupp.prod_add_index_of_disjoint hdisj, ← weight, ← weight, weight_single]

/-- The weight of `∑_{a ∈ s} single a (e a)` is the product of the moments. -/
theorem weight_sum_single [DecidableEq Name] (ρ : Assign Name k) (e : Name → ℕ) (s : Finset Name) :
    weight ρ (∑ a ∈ s, Finsupp.single a (e a)) = ∏ a ∈ s, moments ρ a (e a) := by
  induction s using Finset.induction with
  | empty => simp
  | insert b s hb ih =>
    rw [Finset.sum_insert hb, Finset.prod_insert hb, add_comm, weight_add_single ρ _ (e b), ih,
      mul_comm]
    rw [Finsupp.finsetSum_apply]
    exact Finset.sum_eq_zero fun a ha => Finsupp.single_eq_of_ne (by rintro rfl; exact hb ha)

/-- The evaluation of the moment model, as a `k`-linear map. -/
def evalLinear (ρ : Assign Name k) : MvPolynomial Name k →ₗ[k] k where
  toFun := eval ρ
  map_add' := eval_add ρ
  map_smul' c p := by rw [MvPolynomial.smul_eq_C_mul, eval_C_mul]; rfl

/-- **The moment model is an umbral calculus.** -/
def momentModel (ρ : Assign Name k) : UmbralCalculus k Name where
  E := evalLinear ρ
  map_one := eval_one ρ
  uncorrelation := by
    classical
    intro s e
    show eval ρ _ = ∏ a ∈ s, eval ρ _
    have h : (∏ a ∈ s, MvPolynomial.X a ^ e a : MvPolynomial Name k)
        = MvPolynomial.monomial (∑ a ∈ s, Finsupp.single a (e a)) 1 := by
      rw [MvPolynomial.monomial_sum_index, map_one, one_mul]
      exact Finset.prod_congr rfl fun a _ => MvPolynomial.X_pow_eq_monomial
    rw [h, eval_monomial, one_mul, weight_sum_single]
    rfl

@[simp] theorem momentModel_E (ρ : Assign Name k) (p : MvPolynomial Name k) :
    (momentModel ρ).E p = eval ρ p := rfl

/-- The moments of an umbral calculus, `ρ(α)ₙ = E[αⁿ]`. -/
def UmbralCalculus.moments (U : UmbralCalculus k Name) : Assign Name k :=
  fun a n => U.E (MvPolynomial.X a ^ n)

/-- **Every umbral calculus is a moment model**: its evaluation is that of the
moment model of its own moments. Both are linear and agree on monomials, by
uncorrelation. -/
theorem UmbralCalculus.eq_eval (U : UmbralCalculus k Name) (p : MvPolynomial Name k) :
    U.E p = eval U.moments p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [eval_monomial, MvPolynomial.monomial_eq, MvPolynomial.C_mul', map_smul, smul_eq_mul,
      Finsupp.prod, U.uncorrelation]
    rfl
  | add p q hp hq => rw [map_add, eval_add, hp, hq]

end

end FreeThms.Umbral
