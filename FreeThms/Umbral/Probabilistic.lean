/-
# Probabilistic soundness of the restricted language

An umbra can be read as a random variable and the evaluation as the expectation.
This file makes that reading exact for the restricted language. The
**probabilistic dictionary** `probDict μ X` has scalars `ℝ`, umbrae the names,
umbral polynomials the real functions on a probability space `Ω`, the pointwise
ring operations, and as evaluation the integral against `μ`. Its umbral algebra
is not a polynomial ring: a Rademacher variable satisfies `X² = 1`.

When the names are realised by an independent family `X` whose moments are
those of an assignment `ρ` (`IsModel μ X ρ`), substituting the random variables
into a polynomial is a homomorphism of dictionaries from the moment model to the
probabilistic one (`realizeHom`). The equation for the evaluation is
uncorrelation becoming independence: the expectation of a product of powers of
independent variables is the product of their moments (`integral_monomial`). So
the probabilistic model `probModel`, the umbral calculus with evaluation
`E[p] = ∫ p(X) dμ`, is the moment model of `ρ` (`integral_realize`). By
naturality (`den_natural`), every closed term then takes the same value formally
and as an expectation, nested evaluations included (`probabilistic_soundness`).

The statement is for the restricted language only. A fresh umbra of the full
language need not be a random variable: the singleton umbra `χ` has `E[χ] = 1` and `E[χ²] = 0`.
-/

import FreeThms.Umbral.Naturality
import Mathlib.Probability.Independence.Integration

namespace FreeThms.Umbral.Restricted

open MeasureTheory ProbabilityTheory

variable {Name Ω : Type} [MeasurableSpace Ω]

/-- **The probabilistic dictionary**: the dictionary whose scalars are `ℝ`,
whose umbrae are the names, whose umbral polynomials are the functions `Ω → ℝ`
with the pointwise operations, whose umbra `a` is the function `X a`, and whose
evaluation is the integral against `μ`. -/
noncomputable def probDict (μ : Measure Ω) (X : Name → Ω → ℝ) : Dict ℝ Name (Ω → ℝ) where
  zeroK := 0
  oneK := 1
  addK := (· + ·)
  mulK := (· * ·)
  negK := (- ·)
  zeroA := 0
  oneA := 1
  addA := (· + ·)
  mulA := (· * ·)
  negA := (- ·)
  constA c := fun _ => c
  injA := X
  evalA f := ∫ ω, f ω ∂μ

/-- A family of random variables **is a model** of an assignment when it is
independent, each variable is measurable with all powers integrable, and its
moments are those of the assignment. -/
structure IsModel (μ : Measure Ω) (X : Name → Ω → ℝ) (ρ : Assign Name ℝ) : Prop where
  indep : iIndepFun X μ
  meas : ∀ a, Measurable (X a)
  integrable : ∀ a n, Integrable (fun ω => X a ω ^ n) μ
  moments : ∀ a n, n ≠ 0 → ∫ ω, X a ω ^ n ∂μ = ρ a n

/-- The random variable `p(X)`: the function `Ω → ℝ` that is the polynomial `p`
evaluated at the values of the family. -/
noncomputable def realize (X : Name → Ω → ℝ) (p : MvPolynomial Name ℝ) : Ω → ℝ :=
  fun ω => MvPolynomial.eval (fun a => X a ω) p

variable {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Name → Ω → ℝ} {ρ : Assign Name ℝ}

/-- A finite product of powers of independent variables is integrable, and its
expectation is the product of the expectations. -/
theorem integral_prod_pow (h : IsModel μ X ρ) (e : Name → ℕ) (s : Finset Name) :
    Integrable (fun ω => ∏ a ∈ s, X a ω ^ e a) μ ∧
      ∫ ω, ∏ a ∈ s, X a ω ^ e a ∂μ = ∏ a ∈ s, ∫ ω, X a ω ^ e a ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert b s hb ih =>
    have hY : iIndepFun (fun a ω => X a ω ^ e a) μ :=
      h.indep.comp (fun a x => x ^ e a) fun a => by fun_prop
    have hind : IndepFun (∏ j ∈ s, fun ω => X j ω ^ e j) (fun ω => X b ω ^ e b) μ :=
      hY.indepFun_finsetProd_of_notMem (fun a => (h.meas a).pow_const _) hb
    rw [show (∏ j ∈ s, fun ω => X j ω ^ e j) = fun ω => ∏ j ∈ s, X j ω ^ e j from by
      funext ω; simp [Finset.prod_apply]] at hind
    have hcomm : (fun ω => ∏ a ∈ insert b s, X a ω ^ e a)
        = fun ω => (∏ j ∈ s, X j ω ^ e j) * X b ω ^ e b := by
      funext ω; rw [Finset.prod_insert hb, mul_comm]
    rw [hcomm, Finset.prod_insert hb]
    refine ⟨hind.integrable_mul ih.1 (h.integrable b (e b)), ?_⟩
    rw [hind.integral_fun_mul_eq_mul_integral ih.1.aestronglyMeasurable
      (h.integrable b (e b)).aestronglyMeasurable, ih.2, mul_comm]

/-- **Uncorrelation is independence**: the expectation of a monomial in the
random variables is the weight of the monomial at the assignment. -/
theorem integral_monomial (h : IsModel μ X ρ) (d : Name →₀ ℕ) :
    Integrable (fun ω => ∏ a ∈ d.support, X a ω ^ d a) μ ∧
      ∫ ω, ∏ a ∈ d.support, X a ω ^ d a ∂μ = Umbral.weight ρ d := by
  obtain ⟨hi, he⟩ := integral_prod_pow h d d.support
  refine ⟨hi, ?_⟩
  rw [he, Umbral.weight, Finsupp.prod]
  exact Finset.prod_congr rfl fun a ha => h.moments a (d a) (Finsupp.mem_support_iff.mp ha)

/-- The expectation of `p(X)` is the umbral evaluation of `p`. -/
theorem integral_realize (h : IsModel μ X ρ) (p : MvPolynomial Name ℝ) :
    ∫ ω, realize X p ω ∂μ = Umbral.eval ρ p := by
  simp only [realize, MvPolynomial.eval_eq]
  rw [integral_finsetSum _ fun d _ => (integral_monomial h d).1.const_mul _]
  simp only [integral_const_mul, (integral_monomial h _).2]
  rfl

/-- **The probabilistic model** of `X` (write-up, Chapter 1): the umbral calculus
whose evaluation is `E[p] = ∫ p(X) dμ`. It is the moment model of `ρ`. -/
noncomputable def probModel (h : IsModel μ X ρ) : UmbralCalculus ℝ Name where
  E :=
    { toFun := fun p => ∫ ω, realize X p ω ∂μ
      map_add' := fun p q => by simp only [integral_realize h, Umbral.eval_add]
      map_smul' := fun c p => by
        simp only [integral_realize h, MvPolynomial.smul_eq_C_mul, Umbral.eval_C_mul]; rfl }
  map_one := by simp only [LinearMap.coe_mk, AddHom.coe_mk, integral_realize h, Umbral.eval_one]
  uncorrelation s e := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, integral_realize h]
    exact (momentModel ρ).uncorrelation s e

theorem probModel_E (h : IsModel μ X ρ) (p : MvPolynomial Name ℝ) :
    (probModel h).E p = ∫ ω, realize X p ω ∂μ := rfl

/-- **Substituting the random variables is a homomorphism of dictionaries** from
the moment model of `ρ` to the probabilistic dictionary. -/
noncomputable def realizeHom (h : IsModel μ X ρ) : DictHom (momDict ρ) (probDict μ X) where
  hK x := x
  hU a := a
  hA := realize X
  zeroK := rfl
  oneK := rfl
  addK _ _ := rfl
  mulK _ _ := rfl
  negK _ := rfl
  zeroA := by funext ω; simp [realize, momDict, probDict]
  oneA := by funext ω; simp [realize, momDict, probDict]
  addA p q := by funext ω; simp [realize, momDict, probDict]
  mulA p q := by funext ω; simp [realize, momDict, probDict]
  negA p := by funext ω; simp [realize, momDict, probDict]
  constA x := by funext ω; simp [realize, momDict, probDict]
  injA u := by funext ω; simp [realize, momDict, probDict]
  evalA p := (integral_realize h p).symm

/-- **Probabilistic soundness.** For an independent family of random variables
with the moments of `ρ`, every closed term of `∀K U A. Umbral K U A ⇒ U → K`
takes the same value in the probabilistic dictionary, where evaluation is the
expectation, as in the moment model. -/
theorem probabilistic_soundness (h : IsModel μ X ρ) (t : PClosedTm oneUmbraTy) (a : Name) :
    den ℝ Name (Ω → ℝ) (probDict μ X) t a = den ℝ Name (MvPolynomial Name ℝ) (momDict ρ) t a :=
  (den_natural t (momDict ρ) (probDict μ X) (realizeHom h) a).symm

end FreeThms.Umbral.Restricted
