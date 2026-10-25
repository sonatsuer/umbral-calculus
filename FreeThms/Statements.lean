/-
# Statements

Every theorem the write-up (`docs/umbral-free-theorems.pdf`) cites, restated so
that a reader can audit the claims without reading the development. Each
statement is closed by a direct term, so the restatement is the theorem, not a
paraphrase of it. The sections follow the chapters of the write-up; its
Chapter 4 tabulates the correspondence.
-/

import FreeThms.Umbral.Naturality
import FreeThms.Umbral.Conservativity
import FreeThms.Umbral.Separation
import FreeThms.Umbral.Similarity
import FreeThms.Umbral.Inverse
import FreeThms.Umbral.Probabilistic

namespace FreeThms.Statements

open FreeThms FreeThms.Umbral FreeThms.Umbral.Restricted

/-! ## Chapter 1: the two models -/

/-- **The moment model is an umbral calculus**, in which the `n`-th moment of a
name `α` is `ρ(α)ₙ` for `n ≥ 1`. -/
theorem moment_model_is_umbral_calculus {k Name : Type} [CommRing k] (ρ : Assign Name k) :
    (∀ p, (momentModel ρ).E p = eval ρ p) ∧
      ∀ a n, n ≠ 0 → (momentModel ρ).E (MvPolynomial.X a ^ n) = ρ a n :=
  ⟨fun _ => rfl, fun a n hn => moments_eq ρ a n hn⟩

/-- **Every umbral calculus is a moment model**: its evaluation is that of the
moment model of its own moments. -/
theorem umbral_calculus_is_moment_model {k Name : Type} [CommRing k] (U : UmbralCalculus k Name)
    (p : MvPolynomial Name k) : U.E p = eval U.moments p :=
  U.eq_eval p

/-- **The probabilistic model is an umbral calculus**: for an independent family
of random variables with the moments of `ρ`, the evaluation `E[p] = ∫ p(X) dμ` is
that of the moment model of `ρ`. -/
theorem probabilistic_model_is_moment_model {Name Ω : Type} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ] {X : Name → Ω → ℝ}
    {ρ : Assign Name ℝ} (h : IsModel μ X ρ) (p : MvPolynomial Name ℝ) :
    (probModel h).E p = ∫ ω, realize X p ω ∂μ ∧ (probModel h).E p = eval ρ p :=
  ⟨probModel_E h p, integral_realize h p⟩

/-! ## Chapter 2: the restricted language -/

/-- The evaluation is preserved by an injective renaming that preserves moments. -/
theorem eval_preserved_by_moment_maps {k Name : Type} [CommRing k]
    {ρ₁ ρ₂ : Assign Name k} (σ : MomentMap ρ₁ ρ₂) (p : MvPolynomial Name k) :
    eval ρ₂ (MvPolynomial.rename σ.toFun p) = eval ρ₁ p :=
  eval_rename σ p

/-- **The free theorem of `∀K U A. Umbral K U A ⇒ U → K`.** -/
theorem umbral_free_theorem {K₁ U₁ A₁ K₂ U₂ A₂ : Type}
    (d₁ : Dict K₁ U₁ A₁) (d₂ : Dict K₂ U₂ A₂)
    (R : K₁ → K₂ → Prop) (S : U₁ → U₂ → Prop) (T : A₁ → A₂ → Prop)
    (h : Respects d₁ d₂ R S T) (t : PClosedTm oneUmbraTy)
    (u₁ : U₁) (u₂ : U₂) (hu : S u₁ u₂) :
    R (den K₁ U₁ A₁ d₁ t u₁) (den K₂ U₂ A₂ d₂ t u₂) :=
  den_rel d₁ d₂ R S T h t u₁ u₂ hu

/-- **Rota's substitution principle.** Similar umbrae give equal values. -/
theorem substitution_principle {k Name : Type} [CommRing k] [DecidableEq Name]
    (ρ : Assign Name k) {a b : Name} (hab : Similar ρ ρ a b)
    (t : PClosedTm oneUmbraTy) :
    den k Name (MvPolynomial Name k) (momDict ρ) t a
      = den k Name (MvPolynomial Name k) (momDict ρ) t b :=
  similarity ρ hab t

/-- **The free theorem of `∀K U A. Umbral K U A ⇒ U → ⋯ → U → K`**, with `m`
umbra arguments. -/
theorem umbral_free_theorem_many {K₁ U₁ A₁ K₂ U₂ A₂ : Type}
    (d₁ : Dict K₁ U₁ A₁) (d₂ : Dict K₂ U₂ A₂)
    (R : K₁ → K₂ → Prop) (S : U₁ → U₂ → Prop) (T : A₁ → A₂ → Prop)
    (h : Respects d₁ d₂ R S T) (m : ℕ) (t : PClosedTm (manyUmbraTy m))
    (u₁ : Fin m → U₁) (u₂ : Fin m → U₂) (hu : ∀ i, S (u₁ i) (u₂ i)) :
    R (denN m K₁ U₁ A₁ d₁ t u₁) (denN m K₂ U₂ A₂ d₂ t u₂) :=
  denN_rel d₁ d₂ R S T h m t u₁ u₂ hu

/-- **Rota's substitution principle, in full.** A similar umbra `b` may replace `a`
in an expression whose other umbrae differ from `a` and `b`. -/
theorem substitution_principle_many {k Name : Type} [CommRing k] [DecidableEq Name]
    (ρ : Assign Name k) {a b : Name} (hab : Similar ρ ρ a b) (m : ℕ)
    (t : PClosedTm (manyUmbraTy (m + 1)))
    (c : Fin m → Name) (hca : ∀ i, c i ≠ a) (hcb : ∀ i, c i ≠ b) :
    denN (m + 1) k Name (MvPolynomial Name k) (momDict ρ) t (Fin.snoc c a)
      = denN (m + 1) k Name (MvPolynomial Name k) (momDict ρ) t (Fin.snoc c b) :=
  substitution ρ hab m t c hca hcb

/-- **Uncorrelation constrains the respecting relations.** A relation that respects the
moment dictionaries, with equality on scalars, and relates distinct umbrae `a`
and `c` to the same umbra `b` forces `E[aⁱ] E[cʲ] = E[b^{i+j}]`; so it cannot
exist when the three are similar and their moments are not those of a constant. -/
theorem uncorrelation_constrains_relations {k Name : Type} [CommRing k]
    {ρ₁ ρ₂ : Assign Name k} {S : Name → Name → Prop}
    {T : MvPolynomial Name k → MvPolynomial Name k → Prop}
    (h : Respects (momDict ρ₁) (momDict ρ₂) (fun x y => x = y) S T)
    {a c b : Name} (hac : a ≠ c) (hab : S a b) (hcb : S c b) :
    (∀ i j, moments ρ₁ a i * moments ρ₁ c j = moments ρ₂ b (i + j)) ∧
      (moments ρ₁ c = moments ρ₁ a → moments ρ₂ b = moments ρ₁ a →
        (∃ n, moments ρ₁ a n ≠ moments ρ₁ a 1 ^ n) → False) :=
  ⟨moments_of_common_target h hac hab hcb, no_common_target h hac hab hcb⟩

/-- **Similar umbrae are exchangeable.** An expression in two similar umbrae is
symmetric in them. -/
theorem similar_umbrae_exchangeable {k Name : Type} [CommRing k] [DecidableEq Name]
    (ρ : Assign Name k) {a b : Name} (hab : Similar ρ ρ a b)
    (t : PClosedTm twoUmbraTy) :
    den2 k Name (MvPolynomial Name k) (momDict ρ) t a b
      = den2 k Name (MvPolynomial Name k) (momDict ρ) t b a :=
  exchangeable ρ hab t

/-- **Integrality.** Every expression is an integer polynomial in the moments. -/
theorem integrality {k Name : Type} [CommRing k] (ρ : Assign Name k)
    (t : PClosedTm oneUmbraTy) (a : Name) :
    den k Name (MvPolynomial Name k) (momDict ρ) t a ∈ momentSubring ρ :=
  integral ρ t a

/-! ## Chapter 2: why the free theorem is naturality, and probabilistic soundness -/

/-- **Parametric is natural**, for functionals of one umbra. -/
theorem parametric_is_natural (F : Family) : Parametric F ↔ Natural F :=
  parametric_iff_natural F

/-- The denotation of every closed term commutes with every homomorphism. -/
theorem terms_are_natural (t : PClosedTm oneUmbraTy) : Natural (denFamily t) :=
  den_natural t

/-- The substitution principle, as naturality along a renaming. -/
theorem substitution_principle_natural {k Name : Type} [CommRing k] [DecidableEq Name]
    (ρ : Assign Name k) {a b : Name} (hab : Similar ρ ρ a b)
    (t : PClosedTm oneUmbraTy) :
    den k Name (MvPolynomial Name k) (momDict ρ) t a
      = den k Name (MvPolynomial Name k) (momDict ρ) t b :=
  similarity_natural ρ hab t

/-- Integrality, as naturality along the inclusion of the moment dictionary over
the subring generated by the moments into the one over `k`. -/
theorem integrality_as_naturality {k Name : Type} [CommRing k] (ρ : Assign Name k)
    (t : PClosedTm oneUmbraTy) (a : Name) :
    den k Name (MvPolynomial Name k) (momDict ρ) t a ∈ momentSubring ρ :=
  integrality_natural ρ t a

/-- **Probabilistic soundness.** For an independent family of random variables
with the moments of `ρ`, every closed term takes the same value when the
evaluation is the expectation as in the moment model. -/
theorem probabilistic_soundness {Name Ω : Type} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ] {X : Name → Ω → ℝ}
    {ρ : Assign Name ℝ} (h : IsModel μ X ρ) (t : PClosedTm oneUmbraTy) (a : Name) :
    den ℝ Name (Ω → ℝ) (probDict μ X) t a = den ℝ Name (MvPolynomial Name ℝ) (momDict ρ) t a :=
  Restricted.probabilistic_soundness h t a

/-! ## Chapter 3: the full language, allocation behind the interface

The Kripke abstraction theorem itself is `Kripke.abstraction`, generic in the
allocation and relational structures. These are its umbral instances. -/

section Full

open FreeThms.Umbral.Full MvPolynomial
open FreeThms.Kripke (QTy)

/-- **The extension lemma.** The tensor of two world
relations preserves the evaluation. Its content is uncorrelation of disjoint
blocks. -/
theorem extension_lemma {k : Type} [CommRing k] {w₁ w₂ B₁ B₂ : World k}
    (φ : WRel w₁ w₂) (ψ : WRel B₁ B₂) (p : MvPolynomial (Fin (w₁.size + B₁.size)) k) :
    Umbral.eval (w₂.append B₂).mom (tensorHom φ ψ p) = Umbral.eval (w₁.append B₁).mom p :=
  extension φ ψ p

/-- **The free theorem of `∀K U A. Umbral K U A ⇒ U → ⋯ → U → T K`**, the type of
expressions of the full language in `m` umbrae: the Kripke abstraction theorem, at the moment
dictionary, which is related to itself. For every expression of this type, a
world relation that sends the arguments on one side to those on the other
relates the scalar values, whatever the expression allocates. -/
theorem umbral_free_theorem_alloc {k : Type} [CommRing k] (m : ℕ) (t : Expr m)
    {w₁ w₂ : World k} (φ : WRel w₁ w₂) (u₁ : Fin m → Fin w₁.size) (u₂ : Fin m → Fin w₂.size)
    (hu : ∀ i, φ.toAlgHom (X (u₁ i)) = X (u₂ i)) :
    (den m t w₁ u₁).2 = (den m t w₂ u₂).2 :=
  den_rel m t φ u₁ u₂ hu

/-- **The substitution principle, with allocation.** -/
theorem substitution_principle_full {k : Type} [CommRing k] (w : World k)
    {a b : Fin w.size} (hab : ∀ n, n ≠ 0 → w.mom a n = w.mom b n) (m : ℕ)
    (t : Expr (m + 1)) (c : Fin m → Fin w.size) (hca : ∀ i, c i ≠ a) (hcb : ∀ i, c i ≠ b) :
    (den (m + 1) t w (Fin.snoc c a)).2 = (den (m + 1) t w (Fin.snoc c b)).2 :=
  Full.substitution w hab m t c hca hcb

/-- **Conservativity over the restricted language.** The reading of an expression
of the restricted language in the full language is its denotation there. -/
theorem full_language_conservative {k : Type} [CommRing k] (m : ℕ)
    (t : PClosedTm (manyUmbraTy m)) (w : World k) (u : Fin m → Fin w.size) :
    denEmbedded m t w u = denN m k (Fin w.size) (MvPolynomial (Fin w.size) k) (momDict w.mom) t u :=
  Full.conservative m t w u

/-! ### The auxiliary umbrae as terms

`⟦P⟧ w` is the denotation of a program `P` over the class at the moment
dictionary of the world `w`. -/

/-- **The fresh copy** `new u`: one fresh name, with the moments of `u`. -/
theorem fresh_copy {k : Type} [CommRing k] (w : World k) (x : Fin w.size) :
    (⟦newT⟧ w) w (Hom.id w) x = ⟨World.single (momOf w x), Fin.natAdd w.size 0⟩ :=
  sem_new (Hom.id w) x

/-- **The constructed dot product** `dotConstructed n u`: `n` fresh names, and their
sum, which has the moments of `n.α`. -/
theorem dot_constructed {k : Type} [CommRing k] (w : World k) (x : Fin w.size) (n : ℕ) :
    DotInv w (momOf w x) n ((⟦dotConstructedT⟧ w) w (Hom.id w) n w (Hom.id w) x) :=
  sem_dotConstructed (Hom.id w) n (Hom.id w) x

/-- **The symbolic dot product** `dotSymbolic n u`: one fresh name, with the moments of
`n.α`. -/
theorem dot_symbolic {k : Type} [CommRing k] (w : World k) (x : Fin w.size) (n : ℕ) :
    OneName w (dotMoments (momOf w x) n) ((⟦dotSymbolicT⟧ w) w (Hom.id w) n w (Hom.id w) x) :=
  sem_dotSymbolic (Hom.id w) n (Hom.id w) x

/-- **The moments of `n.α`** are those of `n` uncorrelated copies. -/
theorem dot_moments_copies {k : Type} [CommRing k] (a : ℕ → k) (ha : a 0 = 1) (n j : ℕ) :
    Umbral.eval (copies a n).mom (sumX n ^ j) = dotMoments a n j :=
  eval_copies a ha n j

/-- **The dot-moment identity**:
`∑ⱼ (n)ⱼ B_{m,j}(a) = E[(n.α)ᵐ]`. -/
theorem dot_moments_bell {k : Type} [CommRing k] (a : ℕ → k) (ha : a 0 = 1) (m n : ℕ) :
    bellSum a n m = dotMoments a n m :=
  bell_dotMoments a ha m n

/-- **The composition** `β.α`: one fresh name, whose moments are
`∑ⱼ E[(β)ⱼ] B_{m,j}(a)`. -/
theorem composition {k : Type} [CommRing k] (w : World k) (b x : Fin w.size) :
    (⟦composeT⟧ w) w (Hom.id w) b w (Hom.id w) x
      = ⟨World.single (composeMoments w b x), Fin.natAdd w.size 0⟩ :=
  sem_compose (Hom.id w) b (Hom.id w) x

/-- **The composition is Rota and Taylor's**: its moments are `E[q_m(β)]`, with
`q_m(n) = E[(n.α)ᵐ]` at every natural number `n`. -/
theorem composition_moments {k : Type} [CommRing k] (w : World k) (b x : Fin w.size) (m : ℕ) :
    composeMoments w b x m = Umbral.eval w.mom (Polynomial.aeval (X b) (bellPoly (momOf w x) m)) ∧
      ∀ n : ℕ, (bellPoly (momOf w x) m).eval (n : k) = dotMoments (momOf w x) n m :=
  ⟨composeMoments_eq w b x m, fun n => bellPoly_eval_nat _ (by simp [momOf]) m n⟩

/-- **`n̄.α ≡ n.α`.** -/
theorem composition_constant {k : Type} [CommRing k] (w : World k) (b x : Fin w.size) (n : ℕ)
    (hb : ∀ i, i ≠ 0 → momOf w b i = (n : k) ^ i) (m : ℕ) :
    composeMoments w b x m = dotMoments (momOf w x) n m :=
  composeMoments_const w b x n hb m

/-- **The cumulant umbra** `χ.α`: two fresh names, and the returned one has as
`m`-th moment the linear coefficient of `n ↦ E[(n.α)ᵐ]`, the `m`-th cumulant. -/
theorem cumulant_umbra {k : Type} [CommRing k] (w : World k) (x : Fin w.size) :
    ((⟦cumulantT⟧ w) w (Hom.id w) x).1.size = 2 ∧
      ∀ m, m ≠ 0 → momOf (w.append ((⟦cumulantT⟧ w) w (Hom.id w) x).1)
        ((⟦cumulantT⟧ w) w (Hom.id w) x).2 m = (bellPoly (momOf w x) m).coeff 1 :=
  sem_cumulant w x

/-! ### The auxiliary umbrae respect similarity -/

/-- **The terms of one umbra argument respect similarity.** At arguments with
equal moments, `new`, the two dot products, the cumulant umbra and the
compositional inverse return results with equal moments. -/
theorem auxiliary_umbrae_similar {k : Type} [CommRing k] {v v' : World k} {x : Fin v.size}
    {x' : Fin v'.size} (h : momOf v x = momOf v' x') (n : ℕ) :
    resultMoments ((⟦newT⟧ v) v (Hom.id v) x) = resultMoments ((⟦newT⟧ v') v' (Hom.id v') x') ∧
      resultMomentsA ((⟦dotSymbolicT⟧ v) v (Hom.id v) n v (Hom.id v) x)
        = resultMomentsA ((⟦dotSymbolicT⟧ v') v' (Hom.id v') n v' (Hom.id v') x') ∧
      resultMomentsA ((⟦dotConstructedT⟧ v) v (Hom.id v) n v (Hom.id v) x)
        = resultMomentsA ((⟦dotConstructedT⟧ v') v' (Hom.id v') n v' (Hom.id v') x') ∧
      resultMoments ((⟦cumulantT⟧ v) v (Hom.id v) x)
        = resultMoments ((⟦cumulantT⟧ v') v' (Hom.id v') x') ∧
      resultMoments ((⟦inverseT⟧ v) v (Hom.id v) x)
        = resultMoments ((⟦inverseT⟧ v') v' (Hom.id v') x') :=
  ⟨new_similar h, dotSymbolic_similar h n, dotConstructed_similar h n, cumulant_similar h,
    inverse_similar h⟩

/-- **Composition respects similarity**: `β ≡ β'` and `α ≡ α'` give
`β.α ≡ β'.α'`, with no condition relating `β` to `α`. -/
theorem composition_similar {k : Type} [CommRing k] {v v' : World k} {b x : Fin v.size}
    {b' x' : Fin v'.size} (hb : momOf v b = momOf v' b') (hx : momOf v x = momOf v' x') :
    resultMoments ((⟦composeT⟧ v) v (Hom.id v) b v (Hom.id v) x)
      = resultMoments ((⟦composeT⟧ v') v' (Hom.id v') b' v' (Hom.id v') x') :=
  compose_similar hb hx

/-- **Composition with a polynomial respects similarity**: `p.α` depends on the
moments of `p` and of `α` alone. -/
theorem composition_polynomial_similar {k : Type} [CommRing k] {v v' : World k}
    {p : MvPolynomial (Fin v.size) k} {p' : MvPolynomial (Fin v'.size) k} {x : Fin v.size}
    {x' : Fin v'.size} (hp : ∀ j, Umbral.eval v.mom (p ^ j) = Umbral.eval v'.mom (p' ^ j))
    (hx : momOf v x = momOf v' x') :
    resultMoments ((⟦composeAT⟧ v) v (Hom.id v) p v (Hom.id v) x)
      = resultMoments ((⟦composeAT⟧ v') v' (Hom.id v') p' v' (Hom.id v') x') :=
  composeA_similar hp hx

/-! ### Representation independence and separation

A context for an interface `σ` is a closed term of type
`∀K U A. Umbral(K, U, A) ⇒ σ → U → T K`, and `denCtx Cx w impl x` is its value
at the moment dictionary of `w`, an implementation `impl` and a name `x`. -/

/-- **Representation independence, in general**: implementations related by the
logical relation at the identity are indistinguishable by every context. -/
theorem representation_independence {k : Type} [CommRing k] {σ : QTy 3}
    (Cx : CtxTerm σ) (w : World k) (impl₁ impl₂ : Val σ w)
    (h : Related σ (WRel.id w) impl₁ impl₂) (x : Fin w.size) :
    (denCtx Cx w impl₁ x).2 = (denCtx Cx w impl₂ x).2 :=
  repind Cx w impl₁ impl₂ h x

/-- **Representation independence of the fresh copy**: only the moments of an
auxiliary umbra are observable. No context
distinguishes `new` from an implementation that allocates an unused umbra
first. -/
theorem repind_fresh_copy {k : Type} [CommRing k] (Cx : CtxTerm (tU ⇛ .comp tU)) (w : World k)
    (x : Fin w.size) :
    (denCtx Cx w (⟦newT⟧ w) x).2 = (denCtx Cx w (⟦newAfterUnusedT⟧ w) x).2 :=
  repind_new Cx w x

/-- **Representation independence of the dot product**: no context
distinguishes the symbolic dot product (one fresh umbra
with the moments of `n.α`) from the constructed one (`n` fresh copies, summed). -/
theorem repind_dot_product {k : Type} [CommRing k] (Cx : CtxTerm dotTy) (w : World k) (x : Fin w.size) :
    (denCtx Cx w (⟦dotSymbolicT⟧ w) x).2 = (denCtx Cx w (⟦dotConstructedT⟧ w) x).2 :=
  repind_dot Cx w x

/-- **Distributivity**, over any commutative ring: the composition transform takes binomial convolution to binomial
convolution. -/
theorem distributivity {R : Type} [CommRing R] (a x y : ℕ → R) (m : ℕ) :
    compTransform a (conv x y) m = conv (compTransform a x) (compTransform a y) m :=
  compTransform_conv a x y m

/-- **Representation independence of the composition of a sum**: no context
distinguishes `(β + β').α` from `β.α + β'.α`, for fresh copies `β`, `β'`. -/
theorem repind_composition_of_sum {k : Type} [CommRing k] (Cx : CtxTerm composeSumTy) (w : World k)
    (x : Fin w.size) :
    (denCtx Cx w (⟦composeSumFusedT⟧ w) x).2 = (denCtx Cx w (⟦composeSumSplitT⟧ w) x).2 :=
  repind_composeSum Cx w x

/-- **The Sheffer identity and binomial type at umbral arguments.** For names
`δ`, `δ₁`, `δ₂` with the moments of `(β + β').v`, `β.v` and `β'.v`, where
`β ≠ β'` and `δ`, `δ₁` differ from `α`. -/
theorem sheffer_identity {k : Type} [CommRing k] (W : World k) {α δ δ₁ δ₂ β β' v : Fin W.size}
    (hβ : β ≠ β') (hαδ : α ≠ δ) (hαδ₁ : α ≠ δ₁) (hδ : momOf W δ = composeMomentsA W (X β + X β') v)
    (hδ₁ : momOf W δ₁ = composeMoments W β v) (hδ₂ : momOf W δ₂ = composeMoments W β' v) (n : ℕ) :
    Umbral.eval W.mom ((X α + X δ) ^ n)
        = ∑ i ∈ Finset.range (n + 1), (n.choose i : k) *
            (Umbral.eval W.mom ((X α + X δ₁) ^ i) * Umbral.eval W.mom (X δ₂ ^ (n - i))) ∧
      Umbral.eval W.mom (X δ ^ n)
        = ∑ i ∈ Finset.range (n + 1), (n.choose i : k) *
            (Umbral.eval W.mom (X δ₁ ^ i) * Umbral.eval W.mom (X δ₂ ^ (n - i))) :=
  sheffer W hβ hαδ hαδ₁ hδ hδ₁ hδ₂ n

/-- **Separation from naturality.** The block-size family is natural along
homomorphisms of pairs of a `𝒲`-dictionary and a dot product; the two dot
products are related by the logical relation; and for `n ≠ 1` the family takes
different values at them. -/
theorem separation_from_naturality {k : Type} [CommRing k] [CharZero k] (w : World k)
    (x : Fin w.size) {n : ℕ} (hn : n ≠ 1) :
    PairFamily.Natural (blockCount (k := k)) ∧
      Related dotTy (WRel.id w) (⟦dotSymbolicT⟧ w) (⟦dotConstructedT⟧ w) ∧
      blockCount (symbolicPair w) n x ≠ blockCount (constructedPair w) n x :=
  separation w x hn

/-! ### The compositional inverse -/

/-- **The compositional inverse** `inverse u`: one fresh name, with moments
`inverseMoments` of the moments of `u`. -/
theorem inverse_umbra {k : Type} [CommRing k] (w : World k) (x : Fin w.size) :
    (⟦inverseT⟧ w) w (Hom.id w) x = ⟨World.single (inverseMoments (momOf w x)), Fin.natAdd w.size 0⟩ :=
  sem_inverse (Hom.id w) x

/-- **`α⁽⁻¹⁾.β.α ≡ χ`**: with `E[α] = 1`, the composition transform at the moments
of `α` sends the moments of the inverse to those of the singleton umbra. In
generating functions this is `G(F(t)) = t`: Lagrange inversion. -/
theorem inverse_composition {k : Type} [CommRing k] (a : ℕ → k) (h1 : a 1 = 1) (m : ℕ) :
    compTransform a (inverseMoments a) m = singletonMoments m :=
  inverse_spec h1 m

/-- **Associativity of composition**, in moments: `C_a ∘ C_b = C_{C_a b}`, where
`C_a x = (m ↦ ∑ᵢ xᵢ B_{m,i}(a))` is the composition transform. -/
theorem composition_associative {k : Type} [CommRing k] (a b x : ℕ → k) (m : ℕ) :
    compTransform a (compTransform b x) m = compTransform (compTransform a b) x m :=
  compTransform_assoc a b x m

/-- **`α.β.α⁽⁻¹⁾ ≡ χ`**, the other side of the inverse: with `E[α] = 1`, the
composition transform at the moments of the inverse sends the moments of `α` to
those of `χ`, from index 1 on. In generating functions, `F(G(t)) = t`. -/
theorem inverse_composition_right {k : Type} [CommRing k] (a : ℕ → k) (h1 : a 1 = 1) {m : ℕ}
    (hm : m ≠ 0) : compTransform (inverseMoments a) a m = singletonMoments m :=
  inverse_spec_right h1 hm

/-- **The inverse is unique** from index 1 on. -/
theorem inverse_uniqueness {k : Type} [CommRing k] (a : ℕ → k) (h1 : a 1 = 1) (g : ℕ → k)
    (hg : ∀ m, m ≠ 0 → compTransform a g m = singletonMoments m) : ∀ m, m ≠ 0 → g m = inverseMoments a m :=
  inverse_unique h1 g hg

end Full

end FreeThms.Statements
