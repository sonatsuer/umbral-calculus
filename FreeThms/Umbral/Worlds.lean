/-
# The full language, the umbral instance: moment worlds and world relations

`Core/Kripke.lean` proves the abstraction theorem for an abstract allocation
structure and an abstract relational structure. This file supplies the umbral
ones (write-up, Chapter 3).

* **Worlds** are finite alphabets `0, …, n - 1` with a moment sequence for each
  name. A **morphism** is an injective map of names that preserves the moments
  from the first on. A **block** is a world, and `w ⊕ B` puts the names of `B`
  after those of `w`.
* A **world relation** `w₁ ⇸ w₂` is a `k`-algebra map `k[w₁] → k[w₂]` that
  preserves the evaluation. It need not send names to names. A **future** of a
  world relation along two morphisms is one that commutes with the renamings.
* The **tensor** `φ ⊗ ψ` of a world relation with a relation between two blocks
  acts as `φ` on the old names and as `ψ` on the block. That it preserves the
  evaluation is the **extension lemma**, `extension`. Its content is
  uncorrelation of disjoint blocks, `eval_blocks`.

The class `Umbral(K, U, A)` of the full language is that of the restricted language with one more
method, `mk : (N → K) → T U`, the allocation of a fresh umbra with prescribed
moments. The moment dictionary interprets it at every world, and
`applyDict_rel` and `mk_rel` show that it is related to itself at every world
relation. Together with the abstraction theorem this gives
`den_rel`, the free theorem of the type of expressions of the full language, and its first
instance,
the substitution principle with allocation.
-/

import FreeThms.Core.Kripke
import FreeThms.Umbral.Language
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic

namespace FreeThms.Umbral.Full

open MvPolynomial (X C rename rename_X rename_rename)
open FreeThms.Umbral.Restricted (Slot)
open FreeThms.Kripke (AllocStr BaseI RelStr KRel KREnv QTy STy QTyD QRel
  QClosedTm evalC abstraction_closed)

noncomputable section

variable {k : Type} [CommRing k]

/-! ## Worlds, morphisms and blocks -/

variable (k) in
/-- A world: the names `0, …, size - 1`, each with a moment sequence. Its entry
`0` is never consulted, since `E[α⁰] = 1`. -/
structure World where
  /-- The number of names. -/
  size : ℕ
  /-- The moments of each name. -/
  mom : Fin size → ℕ → k

/-- The world with no names. -/
def World.empty : World k := ⟨0, Fin.elim0⟩

/-- The extension `w ⊕ B` of a world by a block: the names of `B` come after
those of `w`. Reducible, so that the names of `w ⊕ B` are visibly
`Fin (w.size + B.size)`. -/
abbrev World.append (w B : World k) : World k := ⟨w.size + B.size, Fin.append w.mom B.mom⟩

/-- The world with one name, whose moments are `s`. -/
abbrev World.single (s : ℕ → k) : World k := ⟨1, fun _ => s⟩

/-- A morphism of worlds: an injective map of names that preserves the moments
from the first on. -/
structure Hom (w v : World k) where
  /-- The map on names. -/
  toFun : Fin w.size → Fin v.size
  /-- Injectivity. -/
  inj : Function.Injective toFun
  /-- Preservation of the moments. -/
  mom : ∀ i n, n ≠ 0 → v.mom (toFun i) n = w.mom i n

/-- The identity morphism. -/
def Hom.id (w : World k) : Hom w w := ⟨_root_.id, Function.injective_id, fun _ _ _ => rfl⟩

omit [CommRing k] in
@[simp] theorem Hom.id_toFun (w : World k) : (Hom.id w).toFun = _root_.id := rfl

/-- Composition, in diagrammatic order. -/
def Hom.comp {u v x : World k} (σ : Hom u v) (τ : Hom v x) : Hom u x :=
  ⟨τ.toFun ∘ σ.toFun, τ.inj.comp σ.inj, fun i n hn => (τ.mom _ n hn).trans (σ.mom i n hn)⟩

/-- The inclusion `w → w ⊕ B`. -/
def Hom.inl (w B : World k) : Hom w (w.append B) :=
  ⟨Fin.castAdd B.size, Fin.castAdd_injective _ _, fun i _ _ => by simp⟩

/-- The map on names of `σ ⊕ B`: `σ` on the old names, the identity on the
block. -/
def Hom.extMap {w v : World k} (σ : Hom w v) (B : World k) :
    Fin (w.size + B.size) → Fin (v.size + B.size) :=
  Fin.append (fun i => Fin.castAdd B.size (σ.toFun i)) (Fin.natAdd v.size)

omit [CommRing k] in
@[simp] theorem Hom.extMap_castAdd {w v : World k} (σ : Hom w v) (B : World k)
    (i : Fin w.size) : σ.extMap B (Fin.castAdd B.size i) = Fin.castAdd B.size (σ.toFun i) := by
  simp [Hom.extMap]

omit [CommRing k] in
@[simp] theorem Hom.extMap_natAdd {w v : World k} (σ : Hom w v) (B : World k)
    (j : Fin B.size) : σ.extMap B (Fin.natAdd w.size j) = Fin.natAdd v.size j := by
  simp [Hom.extMap]

/-- `σ ⊕ B`. -/
def Hom.ext {w v : World k} (σ : Hom w v) (B : World k) : Hom (w.append B) (v.append B) where
  toFun := σ.extMap B
  inj := by
    intro i j h
    induction i using Fin.addCases with
    | left a =>
      induction j using Fin.addCases with
      | left b =>
        simp only [Hom.extMap_castAdd] at h
        rw [σ.inj (Fin.castAdd_injective _ _ h)]
      | right b =>
        simp only [Hom.extMap_castAdd, Hom.extMap_natAdd, Fin.ext_iff, Fin.val_castAdd,
          Fin.val_natAdd] at h
        have := (σ.toFun a).isLt
        omega
    | right a =>
      induction j using Fin.addCases with
      | left b =>
        simp only [Hom.extMap_castAdd, Hom.extMap_natAdd, Fin.ext_iff, Fin.val_castAdd,
          Fin.val_natAdd] at h
        have := (σ.toFun b).isLt
        omega
      | right b =>
        simp only [Hom.extMap_natAdd] at h
        rw [Fin.natAdd_injective _ _ h]
  mom := by
    intro i n hn
    induction i using Fin.addCases with
    | left a => simpa using σ.mom a n hn
    | right b => simp

/-- Reassociation `(w ⊕ B) ⊕ B' → w ⊕ (B ⊕ B')`. -/
def Hom.assoc (w B B' : World k) : Hom ((w.append B).append B') (w.append (B.append B')) where
  toFun := Fin.cast (Nat.add_assoc _ _ _)
  inj := Fin.cast_injective _
  mom := fun i n _ => congrFun (congrFun (Fin.append_assoc w.mom B.mom B'.mom) i).symm n

variable (k) in
/-- **The allocation structure of moment worlds.** Blocks are worlds, and
extension is `World.append`. -/
abbrev alloc : AllocStr where
  W := World k
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := fun _ => rfl
  Blk := World k
  empty := World.empty
  app := World.append
  ext := World.append
  inl := Hom.inl
  extHom := Hom.ext
  assoc := Hom.assoc

/-! ## The sorts at a world -/

/-- The three sorts at a world: the scalars, the names, and the polynomials in
the names. -/
abbrev sorts (w : World k) : Slot → Type :=
  Restricted.baseD k (Fin w.size) (MvPolynomial (Fin w.size) k)

/-- Transport along a morphism: the identity on scalars, renaming on names and
on polynomials. -/
def trS {w v : World k} : (b : Slot) → Hom w v → sorts w b → sorts v b
  | .K, _, x => x
  | .U, σ, x => σ.toFun x
  | .A, σ, p => rename σ.toFun p

variable (k) in
/-- The interpretation of the three sorts over moment worlds. -/
abbrev base : BaseI (alloc k) Slot where
  carrier := fun b w => sorts w b
  tr := fun b σ x => trS b σ x
  tr_id := by
    intro w b x
    cases b
    · rfl
    · rfl
    · exact MvPolynomial.rename_id_apply x

/-! ## Renaming preserves the evaluation -/

/-- **`E` is preserved by a morphism of worlds.** The heterogeneous form of
`eval_rename` of the restricted language: the two worlds may have different names. -/
theorem eval_rename_hom {w v : World k} (σ : Hom w v) (p : MvPolynomial (Fin w.size) k) :
    Umbral.eval v.mom (rename σ.toFun p) = Umbral.eval w.mom p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [MvPolynomial.rename_monomial, eval_monomial, eval_monomial, weight, weight,
      Finsupp.prod_mapDomain_index_inj σ.inj]
    congr 1
    refine Finsupp.prod_congr fun a ha => σ.mom a (d a) (Finsupp.mem_support_iff.mp ha)
  | add p q hp hq => rw [map_add, eval_add, eval_add, hp, hq]

/-! ## Uncorrelation of disjoint blocks -/

/-- The weight of a monomial spread over two blocks is the product of the
weights of its parts. -/
theorem weight_blocks (w B : World k) (d : Fin w.size →₀ ℕ) (e : Fin B.size →₀ ℕ) :
    weight (w.append B).mom (d.mapDomain (Fin.castAdd B.size) + e.mapDomain (Fin.natAdd w.size))
      = weight w.mom d * weight B.mom e := by
  classical
  have hdisj : Disjoint (d.mapDomain (Fin.castAdd B.size)).support
      (e.mapDomain (Fin.natAdd w.size)).support := by
    refine Finset.disjoint_left.mpr fun x hx hy => ?_
    rcases Finset.mem_image.mp (Finsupp.mapDomain_support hx) with ⟨a, -, rfl⟩
    rcases Finset.mem_image.mp (Finsupp.mapDomain_support hy) with ⟨b, -, hb⟩
    have h := congrArg Fin.val hb
    simp only [Fin.val_natAdd, Fin.val_castAdd] at h
    have := a.isLt
    omega
  rw [weight, Finsupp.prod_add_index_of_disjoint hdisj,
    Finsupp.prod_mapDomain_index_inj (Fin.castAdd_injective _ _),
    Finsupp.prod_mapDomain_index_inj (Fin.natAdd_injective _ _)]
  simp [weight]

/-- **`E` factors over disjoint blocks.** For a polynomial `p` in the names of
`w` and a polynomial `q` in the names of `B`, `E[p q] = E[p] E[q]` in `w ⊕ B`.
This is uncorrelation for polynomials rather than single umbrae. -/
theorem eval_blocks (w B : World k) (p : MvPolynomial (Fin w.size) k)
    (q : MvPolynomial (Fin B.size) k) :
    Umbral.eval (w.append B).mom (rename (Fin.castAdd B.size) p * rename (Fin.natAdd w.size) q)
      = Umbral.eval w.mom p * Umbral.eval B.mom q := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
    induction q using MvPolynomial.induction_on' with
    | monomial e c' =>
      rw [MvPolynomial.rename_monomial, MvPolynomial.rename_monomial, MvPolynomial.monomial_mul,
        eval_monomial, eval_monomial, eval_monomial, weight_blocks]
      ring
    | add q q' hq hq' => rw [map_add, mul_add, eval_add, eval_add, hq, hq', mul_add]
  | add p p' hp hp' => rw [map_add, add_mul, eval_add, eval_add, hp, hp', add_mul]

/-- A monomial in the names of `w ⊕ B` is a constant times a monomial in the
names of `w` times a monomial in the names of `B`. -/
theorem monomial_split {n m : ℕ} (d : Fin (n + m) →₀ ℕ) (c : k) :
    MvPolynomial.monomial d c = C c * (rename (Fin.castAdd m) (∏ i : Fin n, X i ^ d (Fin.castAdd m i))
      * rename (Fin.natAdd n) (∏ j : Fin m, X j ^ d (Fin.natAdd n j))) := by
  rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Fin.prod_univ_add]
  simp [map_prod]

/-! ## World relations -/

/-- A **world relation** `w₁ ⇸ w₂`: an algebra map between the polynomials in
their names that preserves the evaluation. -/
structure WRel (w₁ w₂ : World k) where
  /-- The algebra map. -/
  toAlgHom : MvPolynomial (Fin w₁.size) k →ₐ[k] MvPolynomial (Fin w₂.size) k
  /-- It preserves the evaluation. -/
  eval_eq : ∀ p, Umbral.eval w₂.mom (toAlgHom p) = Umbral.eval w₁.mom p

/-- The world relation induced by a morphism: renaming. -/
def WRel.ofHom {w v : World k} (σ : Hom w v) : WRel w v :=
  ⟨rename σ.toFun, eval_rename_hom σ⟩

/-- The identity world relation. -/
def WRel.id (w : World k) : WRel w w := ⟨AlgHom.id k _, fun _ => rfl⟩

/-- The algebra map of the tensor: `φ` on the old names, `ψ` on the block. -/
def tensorHom {w₁ w₂ B₁ B₂ : World k} (φ : WRel w₁ w₂) (ψ : WRel B₁ B₂) :
    MvPolynomial (Fin (w₁.size + B₁.size)) k →ₐ[k] MvPolynomial (Fin (w₂.size + B₂.size)) k :=
  MvPolynomial.aeval (Fin.append (fun i => rename (Fin.castAdd B₂.size) (φ.toAlgHom (X i)))
    (fun j => rename (Fin.natAdd w₂.size) (ψ.toAlgHom (X j))))

section tensor

variable {w₁ w₂ B₁ B₂ : World k} (φ : WRel w₁ w₂) (ψ : WRel B₁ B₂)

@[simp] theorem tensorHom_X_castAdd (i : Fin w₁.size) :
    tensorHom φ ψ (X (Fin.castAdd B₁.size i)) = rename (Fin.castAdd B₂.size) (φ.toAlgHom (X i)) := by
  simp [tensorHom]

@[simp] theorem tensorHom_X_natAdd (j : Fin B₁.size) :
    tensorHom φ ψ (X (Fin.natAdd w₁.size j)) = rename (Fin.natAdd w₂.size) (ψ.toAlgHom (X j)) := by
  simp [tensorHom]

theorem tensorHom_comp_castAdd :
    (tensorHom φ ψ).comp (rename (Fin.castAdd B₁.size))
      = (rename (Fin.castAdd B₂.size)).comp φ.toAlgHom :=
  MvPolynomial.algHom_ext fun i => by simp

theorem tensorHom_comp_natAdd :
    (tensorHom φ ψ).comp (rename (Fin.natAdd w₁.size))
      = (rename (Fin.natAdd w₂.size)).comp ψ.toAlgHom :=
  MvPolynomial.algHom_ext fun j => by simp

theorem tensorHom_castAdd (p : MvPolynomial (Fin w₁.size) k) :
    tensorHom φ ψ (rename (Fin.castAdd B₁.size) p) = rename (Fin.castAdd B₂.size) (φ.toAlgHom p) :=
  DFunLike.congr_fun (tensorHom_comp_castAdd φ ψ) p

theorem tensorHom_natAdd (q : MvPolynomial (Fin B₁.size) k) :
    tensorHom φ ψ (rename (Fin.natAdd w₁.size) q) = rename (Fin.natAdd w₂.size) (ψ.toAlgHom q) :=
  DFunLike.congr_fun (tensorHom_comp_natAdd φ ψ) q

/-- **The extension lemma.** The tensor of two world relations preserves the
evaluation, so it is a world relation `w₁ ⊕ B₁ ⇸ w₂ ⊕ B₂`.

A monomial of `w₁ ⊕ B₁` is a product of a monomial `P` of `w₁` and a monomial
`Q` of `B₁`. The tensor sends it to `φ(P) ψ(Q)`, a product of polynomials in
the disjoint blocks `w₂` and `B₂`. Uncorrelation (`eval_blocks`) factors both
evaluations, and `φ` and `ψ` preserve the factors. -/
theorem extension (p : MvPolynomial (Fin (w₁.size + B₁.size)) k) :
    Umbral.eval (w₂.append B₂).mom (tensorHom φ ψ p) = Umbral.eval (w₁.append B₁).mom p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [monomial_split d c, map_mul, map_mul, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq,
      tensorHom_castAdd, tensorHom_natAdd, eval_C_mul, eval_C_mul, eval_blocks, eval_blocks,
      φ.eval_eq, ψ.eval_eq]
  | add p q hp hq => rw [map_add, eval_add, eval_add, hp, hq]

end tensor

/-- The tensor of two world relations, a world relation by the extension
lemma. -/
def WRel.tensor {w₁ w₂ B₁ B₂ : World k} (φ : WRel w₁ w₂) (ψ : WRel B₁ B₂) :
    WRel (w₁.append B₁) (w₂.append B₂) :=
  ⟨tensorHom φ ψ, extension φ ψ⟩

/-! ## Futures -/

/-- `(σ₁, σ₂, φ')` is a **future** of `φ`: the square of algebra maps
commutes, `φ' ∘ σ₁ = σ₂ ∘ φ`. -/
def Fut {w₁ w₂ v₁ v₂ : World k} (φ : WRel w₁ w₂) (σ₁ : Hom w₁ v₁) (σ₂ : Hom w₂ v₂)
    (φ' : WRel v₁ v₂) : Prop :=
  φ'.toAlgHom.comp (rename σ₁.toFun) = (rename σ₂.toFun).comp φ.toAlgHom

section futures

variable {w₁ w₂ v₁ v₂ u₁ u₂ : World k} {φ : WRel w₁ w₂} {φ' : WRel v₁ v₂}
  {σ₁ : Hom w₁ v₁} {σ₂ : Hom w₂ v₂}

theorem Fut.apply (h : Fut φ σ₁ σ₂ φ') (p : MvPolynomial (Fin w₁.size) k) :
    φ'.toAlgHom (rename σ₁.toFun p) = rename σ₂.toFun (φ.toAlgHom p) :=
  DFunLike.congr_fun h p

theorem Fut.apply_X (h : Fut φ σ₁ σ₂ φ') (x : Fin w₁.size) :
    φ'.toAlgHom (X (σ₁.toFun x)) = rename σ₂.toFun (φ.toAlgHom (X x)) := by
  rw [← h.apply, rename_X]

theorem Fut.refl (φ : WRel w₁ w₂) : Fut φ (Hom.id w₁) (Hom.id w₂) φ := by
  simp [Fut, Hom.id, MvPolynomial.rename_id]

theorem Fut.trans {φ'' : WRel u₁ u₂} {τ₁ : Hom v₁ u₁} {τ₂ : Hom v₂ u₂}
    (h : Fut φ σ₁ σ₂ φ') (h' : Fut φ' τ₁ τ₂ φ'') :
    Fut φ (σ₁.comp τ₁) (σ₂.comp τ₂) φ'' := by
  unfold Fut at *
  simp only [Hom.comp]
  rw [← MvPolynomial.rename_comp_rename, ← MvPolynomial.rename_comp_rename, ← AlgHom.comp_assoc,
    h', AlgHom.comp_assoc, h, AlgHom.comp_assoc]

theorem Fut.inl {B₁ B₂ : World k} (φ : WRel w₁ w₂) (ψ : WRel B₁ B₂) :
    Fut φ (Hom.inl w₁ B₁) (Hom.inl w₂ B₂) (φ.tensor ψ) :=
  tensorHom_comp_castAdd φ ψ

theorem Fut.ext {B₁ B₂ : World k} (ψ : WRel B₁ B₂) (h : Fut φ σ₁ σ₂ φ') :
    Fut (φ.tensor ψ) (σ₁.ext B₁) (σ₂.ext B₂) (φ'.tensor ψ) := by
  refine MvPolynomial.algHom_ext fun i => ?_
  simp only [AlgHom.comp_apply, rename_X, WRel.tensor, Hom.ext]
  induction i using Fin.addCases with
  | left a =>
    rw [Hom.extMap_castAdd, tensorHom_X_castAdd, tensorHom_X_castAdd, h.apply_X, rename_rename,
      rename_rename]
    exact congrArg (fun f => rename f _) (funext fun x => by simp)
  | right b =>
    rw [Hom.extMap_natAdd, tensorHom_X_natAdd, tensorHom_X_natAdd, rename_rename]
    exact congrArg (fun f => rename f _) (funext fun x => by simp)

theorem Fut.assoc {B₁ B₂ B₁' B₂' : World k} (φ : WRel w₁ w₂) (ψ : WRel B₁ B₂)
    (ψ' : WRel B₁' B₂') :
    Fut ((φ.tensor ψ).tensor ψ') (Hom.assoc w₁ B₁ B₁') (Hom.assoc w₂ B₂ B₂')
      (φ.tensor (ψ.tensor ψ')) := by
  refine MvPolynomial.algHom_ext fun i => ?_
  simp only [AlgHom.comp_apply, rename_X, WRel.tensor, Hom.assoc]
  induction i using Fin.addCases with
  | left j =>
    induction j using Fin.addCases with
    | left a =>
      have hc : Fin.cast (Nat.add_assoc _ _ _) (Fin.castAdd B₁'.size (Fin.castAdd B₁.size a))
          = Fin.castAdd (B₁.size + B₁'.size) a := Fin.ext rfl
      rw [hc, tensorHom_X_castAdd, tensorHom_X_castAdd, tensorHom_X_castAdd, rename_rename,
        rename_rename]
      exact congrArg (fun f => rename f _) (funext fun x => Fin.ext rfl)
    | right b =>
      have hc : Fin.cast (Nat.add_assoc _ _ _) (Fin.castAdd B₁'.size (Fin.natAdd w₁.size b))
          = Fin.natAdd w₁.size (Fin.castAdd B₁'.size b) := Fin.ext rfl
      rw [hc, tensorHom_X_natAdd, tensorHom_X_castAdd, tensorHom_X_castAdd, tensorHom_X_natAdd,
        rename_rename, rename_rename, rename_rename]
      exact congrArg (fun f => rename f _) (funext fun x => Fin.ext rfl)
  | right c =>
    have hc : Fin.cast (Nat.add_assoc _ _ _) (Fin.natAdd (w₁.size + B₁.size) c)
        = Fin.natAdd w₁.size (Fin.natAdd B₁.size c) := Fin.ext (Nat.add_assoc _ _ _)
    rw [hc, tensorHom_X_natAdd, tensorHom_X_natAdd, tensorHom_X_natAdd, rename_rename,
      rename_rename]
    exact congrArg (fun f => rename f _) (funext fun x => Fin.ext (Nat.add_assoc _ _ _).symm)

end futures

variable (k) in
/-- **The relational structure of moment worlds.** World relations are
evaluation-preserving algebra maps, block relations are world relations between
blocks, and the tensor is the extension lemma. -/
abbrev rel : RelStr (alloc k) where
  R := WRel
  Fut := Fut
  fut_refl := Fut.refl
  fut_trans := Fut.trans
  BR := WRel
  tensor := WRel.tensor
  fut_inl := Fut.inl
  fut_ext := fun ψ h => Fut.ext ψ h
  bempty := WRel.id World.empty
  bapp := WRel.tensor
  fut_assoc := Fut.assoc

/-! ## The relations at the three sorts

At the scalars the relation is equality. At the umbrae, `x` is related to `y`
when `φ` sends the name `x` to the name `y`: the name part of `φ`. At the
polynomials it is the graph of `φ`. Each is monotone along futures, because a
future is a commuting square. -/

/-- Equality at the scalars. -/
def relK : KRel (rel k) (base k) (base k) (.base .K) (.base .K) where
  rel := fun _ x y => x = y
  mono := fun h _ => h

/-- The name part of a world relation, at the umbrae. -/
def relU : KRel (rel k) (base k) (base k) (.base .U) (.base .U) where
  rel := fun φ x y => WRel.toAlgHom φ (X x) = X y
  mono := by
    intro (w₁ : World k) (w₂ : World k) (v₁ : World k) (v₂ : World k) (φ : WRel w₁ w₂)
      (φ' : WRel v₁ v₂) (h₁ : Hom w₁ v₁) (h₂ : Hom w₂ v₂) (x : Fin w₁.size) (y : Fin w₂.size)
      (hxy : φ.toAlgHom (X x) = X y) (hf : Fut φ h₁ h₂ φ')
    show φ'.toAlgHom (X (h₁.toFun x)) = X (h₂.toFun y)
    rw [Fut.apply_X hf x, hxy, rename_X]

/-- The graph of a world relation, at the polynomials. -/
def relA : KRel (rel k) (base k) (base k) (.base .A) (.base .A) where
  rel := fun φ p q => WRel.toAlgHom φ p = q
  mono := by
    intro (w₁ : World k) (w₂ : World k) (v₁ : World k) (v₂ : World k) (φ : WRel w₁ w₂)
      (φ' : WRel v₁ v₂) (h₁ : Hom w₁ v₁) (h₂ : Hom w₂ v₂) (p : MvPolynomial (Fin w₁.size) k)
      (q : MvPolynomial (Fin w₂.size) k) (hpq : φ.toAlgHom p = q) (hf : Fut φ h₁ h₂ φ')
    show φ'.toAlgHom (rename h₁.toFun p) = rename h₂.toFun q
    rw [Fut.apply hf p, hpq]

/-! ## The class `Umbral(K, U, A)` of the full language -/

open Kripke.QTy in
/-- The thirteen methods of the class `Umbral(K, U, A)` of the restricted language, as a curried
dictionary in front of a body. As in the restricted language, the de Bruijn indices are `K = 2`,
`U = 1`, `A = 0`. The embedding of the restricted language's `dictTy body` is definitionally
`methodsTy` of the embedded body. -/
def methodsTy (body : QTy 3) : QTy 3 :=
  tvar 2 ⇛ tvar 2 ⇛ (tvar 2 ⇛ tvar 2 ⇛ tvar 2) ⇛ (tvar 2 ⇛ tvar 2 ⇛ tvar 2) ⇛
    (tvar 2 ⇛ tvar 2) ⇛
  tvar 0 ⇛ tvar 0 ⇛ (tvar 0 ⇛ tvar 0 ⇛ tvar 0) ⇛ (tvar 0 ⇛ tvar 0 ⇛ tvar 0) ⇛
    (tvar 0 ⇛ tvar 0) ⇛
  (tvar 2 ⇛ tvar 0) ⇛ (tvar 1 ⇛ tvar 0) ⇛ (tvar 0 ⇛ tvar 2) ⇛ body

open Kripke.QTy in
/-- The type of `mk`, `(N → K) → T U`. -/
abbrev mkTy : QTy 3 := (nat ⇛ tvar 2) ⇛ comp (tvar 1)

/-- The class `Umbral(K, U, A)` of the full language, as a curried dictionary in front of a
body: the thirteen methods of the restricted language, in the same order, then `mk`. -/
def dictTy (body : QTy 3) : QTy 3 := methodsTy (mkTy ⇛ body)

/-- `∀K U A. Umbral(K, U, A) ⇒ body`, in the full language. -/
abbrev quantTy (body : QTy 3) : QTy 0 := .all (.all (.all (dictTy body)))

open Kripke.QTy in
/-- The body `U → ⋯ → U → T K` with `m` umbra arguments. -/
def umbraArrows : ℕ → QTy 3
  | 0 => comp (tvar 2)
  | m + 1 => tvar 1 ⇛ umbraArrows m

/-- An **expression of the full language in `m` umbrae**: a closed term of type
`∀K U A. Umbral(K, U, A) ⇒ U → ⋯ → U → T K`. -/
abbrev Expr (m : ℕ) : Type := QClosedTm (quantTy (umbraArrows m))

/-- The instantiation of `K`, `U` and `A` at the three sorts. -/
abbrev sortEnv : Fin 3 → STy Slot :=
  scons (.base .A) (scons (.base .U) (scons (.base .K) fun i => i.elim0))

/-- The relation environment carrying the three relations above. -/
def sortRel : KREnv (rel k) (base k) (base k) 3 :=
  KREnv.cons (KREnv.cons (KREnv.cons ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
    (.base .K) (.base .K) relK) (.base .U) (.base .U) relU) (.base .A) (.base .A) relA

/-- A value of a type under the three quantifiers, at the three sorts and a
world. -/
abbrev Val (τ : QTy 3) (w : World k) : Type := QTyD (base k) τ sortEnv w

/-! ## The moment dictionary

Each method is a Kripke function: it may be applied at any later world, after
transport along a morphism. A method of two arguments therefore transports its
first argument to the world of its second. -/

/-- The method `mk`: a block with one fresh name whose moments are the given
sequence, read at the identity, and that name. -/
def momentMk (w : World k) : (v : World k) → Hom w v → ((x : World k) → Hom v x → ℕ → k) →
    Σ B : World k, Fin (v.size + B.size) :=
  fun v _ f => ⟨World.single (f v (Hom.id v)), Fin.natAdd v.size 0⟩

/-- Apply a value of a type headed by the thirteen methods of the restricted language to the
moment dictionary at `w`, every method at the identity. -/
def applyMethods {body : QTy 3} (w : World k) (f : Val (methodsTy body) w) : Val body w :=
  f w (Hom.id w) (0 : k) w (Hom.id w) (1 : k)
    w (Hom.id w) (fun _ _ (x : k) _ _ (y : k) => x + y)
    w (Hom.id w) (fun _ _ (x : k) _ _ (y : k) => x * y)
    w (Hom.id w) (fun _ _ (x : k) => -x)
    w (Hom.id w) (0 : MvPolynomial (Fin w.size) k)
    w (Hom.id w) (1 : MvPolynomial (Fin w.size) k)
    w (Hom.id w) (fun _ _ (p : MvPolynomial _ k) _ (σ : Hom _ _) (q : MvPolynomial _ k) =>
      rename σ.toFun p + q)
    w (Hom.id w) (fun _ _ (p : MvPolynomial _ k) _ (σ : Hom _ _) (q : MvPolynomial _ k) =>
      rename σ.toFun p * q)
    w (Hom.id w) (fun _ _ (p : MvPolynomial _ k) => -p)
    w (Hom.id w) (fun _ _ (c : k) => (C c : MvPolynomial _ k))
    w (Hom.id w) (fun _ _ (x : Fin _) => (X x : MvPolynomial _ k))
    w (Hom.id w) (fun (v : World k) _ (p : MvPolynomial (Fin v.size) k) => (Umbral.eval v.mom p : k))

/-- Apply a value of the dictionary-headed type to the moment dictionary of
the full language at `w`, every method at the identity. -/
def applyDict {body : QTy 3} (w : World k) (f : Val (dictTy body) w) : Val body w :=
  applyMethods w f w (Hom.id w) (momentMk w)

/-- Apply a curried function of `m` umbrae, at the identity each time. -/
def apply (w : World k) : (m : ℕ) → Val (umbraArrows m) w → (Fin m → Fin w.size) →
    Σ _ : World k, k
  | 0, c, _ => c
  | m + 1, f, u => apply w m (f w (Hom.id w) (u 0)) (fun i => u i.succ)

/-- **The denotation of an expression of the full language** at the moment dictionary of a
world and a tuple of its names: a block of fresh names and a scalar. -/
def den (m : ℕ) (t : Expr m) (w : World k) (u : Fin m → Fin w.size) : Σ _ : World k, k :=
  apply w m (applyDict w (evalC (base k) t w (.base .K) (.base .U) (.base .A))) u

/-! ## The moment dictionary is related to itself -/

section dict

variable {w₁ w₂ : World k} (φ : WRel w₁ w₂)

/-- Shorthand for the logical relation under the three quantifiers. -/
abbrev Related (τ : QTy 3) {w₁ w₂ : World k} (φ : WRel w₁ w₂) (x : Val τ w₁) (y : Val τ w₂) :
    Prop :=
  QRel τ sortRel (A := alloc k) (RS := rel k) φ x y

/-- **The method `mk` is related to itself** at every world relation. Related
moment sequences are equal, so the two fresh blocks have the same moments, and
the identity of the one-name block preserves the evaluation. The two fresh names
then correspond under the tensor. -/
theorem mk_rel : Related ((.nat ⇛ .tvar 2) ⇛ .comp (.tvar 1)) φ (momentMk w₁) (momentMk w₂) := by
  intro (v₁ : World k) (v₂ : World k) _ _ (φ' : WRel v₁ v₂) _
    (f : (x : World k) → Hom v₁ x → ℕ → k) (g : (x : World k) → Hom v₂ x → ℕ → k) hfg
  have hs : f v₁ (Hom.id v₁) = g v₂ (Hom.id v₂) :=
    funext fun n => hfg v₁ v₂ (Hom.id v₁) (Hom.id v₂) φ' (Fut.refl φ') n n rfl
  let σ : Hom (World.single (f v₁ (Hom.id v₁))) (World.single (g v₂ (Hom.id v₂))) :=
    ⟨_root_.id, Function.injective_id, fun _ n _ => (congrFun hs n).symm⟩
  refine ⟨WRel.ofHom σ, ?_⟩
  show tensorHom φ' (WRel.ofHom σ) (X (Fin.natAdd v₁.size 0)) = X (Fin.natAdd v₂.size 0)
  rw [tensorHom_X_natAdd]
  show rename _ (rename _root_.id (X 0)) = _
  rw [rename_X, rename_X]
  rfl

/-- **The thirteen methods of the moment dictionary are related to themselves**
at every world relation. The ring operations are related because `φ` is an
algebra map and futures commute with renaming, `inj` by the definition of the
relation at the umbrae, and the evaluation because `φ` preserves it. -/
theorem applyMethods_rel {body : QTy 3} {f : Val (methodsTy body) w₁}
    {g : Val (methodsTy body) w₂} (h : Related (methodsTy body) φ f g) :
    Related body φ (applyMethods w₁ f) (applyMethods w₂ g) := by
  have r := Fut.refl φ
  refine h w₁ w₂ _ _ φ r _ _ rfl w₁ w₂ _ _ φ r _ _ rfl
    w₁ w₂ _ _ φ r _ _ ?addK w₁ w₂ _ _ φ r _ _ ?mulK w₁ w₂ _ _ φ r _ _ ?negK
    w₁ w₂ _ _ φ r _ _ (map_zero _) w₁ w₂ _ _ φ r _ _ (map_one _)
    w₁ w₂ _ _ φ r _ _ ?addA w₁ w₂ _ _ φ r _ _ ?mulA w₁ w₂ _ _ φ r _ _ ?negA
    w₁ w₂ _ _ φ r _ _ ?constA w₁ w₂ _ _ φ r _ _ ?injA w₁ w₂ _ _ φ r _ _ ?evalA
  case addK =>
    intro (v₁ : World k) (v₂ : World k) _ _ (φ' : WRel v₁ v₂) _ (x : k) (y : k) (hx : x = y)
      (u₁ : World k) (u₂ : World k) _ _ (φ'' : WRel u₁ u₂) _ (z : k) (z' : k) (hz : z = z')
    show x + z = y + z'
    rw [hx, hz]
  case mulK =>
    intro (v₁ : World k) (v₂ : World k) _ _ (φ' : WRel v₁ v₂) _ (x : k) (y : k) (hx : x = y)
      (u₁ : World k) (u₂ : World k) _ _ (φ'' : WRel u₁ u₂) _ (z : k) (z' : k) (hz : z = z')
    show x * z = y * z'
    rw [hx, hz]
  case negK =>
    intro (v₁ : World k) (v₂ : World k) _ _ (φ' : WRel v₁ v₂) _ (x : k) (y : k) (hx : x = y)
    show -x = -y
    rw [hx]
  case addA =>
    intro (v₁ : World k) (v₂ : World k) _ _ (φ' : WRel v₁ v₂) _
      (p : MvPolynomial (Fin v₁.size) k) (q : MvPolynomial (Fin v₂.size) k)
      (hpq : φ'.toAlgHom p = q) (u₁ : World k) (u₂ : World k) (j₁ : Hom v₁ u₁) (j₂ : Hom v₂ u₂)
      (φ'' : WRel u₁ u₂) (hf : Fut φ' j₁ j₂ φ'') (p' : MvPolynomial (Fin u₁.size) k)
      (q' : MvPolynomial (Fin u₂.size) k) (hpq' : φ''.toAlgHom p' = q')
    show φ''.toAlgHom (rename j₁.toFun p + p') = rename j₂.toFun q + q'
    rw [map_add, Fut.apply hf, hpq, hpq']
  case mulA =>
    intro (v₁ : World k) (v₂ : World k) _ _ (φ' : WRel v₁ v₂) _
      (p : MvPolynomial (Fin v₁.size) k) (q : MvPolynomial (Fin v₂.size) k)
      (hpq : φ'.toAlgHom p = q) (u₁ : World k) (u₂ : World k) (j₁ : Hom v₁ u₁) (j₂ : Hom v₂ u₂)
      (φ'' : WRel u₁ u₂) (hf : Fut φ' j₁ j₂ φ'') (p' : MvPolynomial (Fin u₁.size) k)
      (q' : MvPolynomial (Fin u₂.size) k) (hpq' : φ''.toAlgHom p' = q')
    show φ''.toAlgHom (rename j₁.toFun p * p') = rename j₂.toFun q * q'
    rw [map_mul, Fut.apply hf, hpq, hpq']
  case negA =>
    intro (v₁ : World k) (v₂ : World k) _ _ (φ' : WRel v₁ v₂) _
      (p : MvPolynomial (Fin v₁.size) k) (q : MvPolynomial (Fin v₂.size) k)
      (hpq : φ'.toAlgHom p = q)
    show φ'.toAlgHom (-p) = -q
    rw [map_neg, hpq]
  case constA =>
    intro (v₁ : World k) (v₂ : World k) _ _ (φ' : WRel v₁ v₂) _ (c : k) (c' : k) (hc : c = c')
    show φ'.toAlgHom (C c) = C c'
    rw [MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, hc]
  case injA =>
    intro (v₁ : World k) (v₂ : World k) _ _ (φ' : WRel v₁ v₂) _ (x : Fin v₁.size)
      (y : Fin v₂.size) (hxy : φ'.toAlgHom (X x) = X y)
    exact hxy
  case evalA =>
    intro (v₁ : World k) (v₂ : World k) _ _ (φ' : WRel v₁ v₂) _
      (p : MvPolynomial (Fin v₁.size) k) (q : MvPolynomial (Fin v₂.size) k)
      (hpq : φ'.toAlgHom p = q)
    show Umbral.eval v₁.mom p = Umbral.eval v₂.mom q
    rw [← hpq, φ'.eval_eq]

/-- **The moment dictionary of the full language is related to itself** at every world
relation: the thirteen methods by
`applyMethods_rel`, and `mk` by `mk_rel`. -/
theorem applyDict_rel {body : QTy 3} {f : Val (dictTy body) w₁}
    {g : Val (dictTy body) w₂} (h : Related (dictTy body) φ f g) :
    Related body φ (applyDict w₁ f) (applyDict w₂ g) :=
  applyMethods_rel φ h w₁ w₂ _ _ φ (Fut.refl φ) _ _ (mk_rel φ)

/-- Related curried functions give related results at pointwise related tuples
of umbrae. -/
theorem apply_rel : (m : ℕ) → {f : Val (umbraArrows m) w₁} → {g : Val (umbraArrows m) w₂} →
    Related (umbraArrows m) φ f g → (u₁ : Fin m → Fin w₁.size) → (u₂ : Fin m → Fin w₂.size) →
    (∀ i, φ.toAlgHom (X (u₁ i)) = X (u₂ i)) →
    Related (.comp (.tvar 2)) φ (apply w₁ m f u₁) (apply w₂ m g u₂)
  | 0, _, _, h, _, _, _ => h
  | m + 1, _, _, h, u₁, u₂, hu =>
      apply_rel m (h w₁ w₂ _ _ φ (Fut.refl φ) (u₁ 0) (u₂ 0) (hu 0))
        (fun i => u₁ i.succ) (fun i => u₂ i.succ) (fun i => hu i.succ)

end dict

/-- **The free theorem of `∀K U A. Umbral K U A ⇒ U → ⋯ → U → T K`.** Let
`φ : w₁ ⇸ w₂` be a world relation and let `φ` send the names `u₁ i` to the names
`u₂ i`. Then every expression of this type takes the same scalar value at `w₁` and `u₁` as at `w₂` and `u₂`,
whatever it allocates on the way.

The proof is the Kripke abstraction theorem at the relations `relK`, `relU`,
`relA`, with the dictionary related to itself by `applyDict_rel`. -/
theorem den_rel (m : ℕ) (t : Expr m) {w₁ w₂ : World k} (φ : WRel w₁ w₂)
    (u₁ : Fin m → Fin w₁.size) (u₂ : Fin m → Fin w₂.size)
    (hu : ∀ i, φ.toAlgHom (X (u₁ i)) = X (u₂ i)) :
    (den m t w₁ u₁).2 = (den m t w₂ u₂).2 := by
  have h := abstraction_closed (A := alloc k) (RS := rel k) (I₁ := base k) (I₂ := base k) t φ
  obtain ⟨_, hψ⟩ := apply_rel φ m
    (applyDict_rel φ (h (.base .K) (.base .K) relK (.base .U) (.base .U) relU
      (.base .A) (.base .A) relA)) u₁ u₂ hu
  exact hψ

/-! ## First instance: the substitution principle with allocation -/

/-- The transposition of two similar names is a morphism of a world to itself. -/
def swapHom (w : World k) {a b : Fin w.size} (hab : ∀ n, n ≠ 0 → w.mom a n = w.mom b n) :
    Hom w w where
  toFun := Equiv.swap a b
  inj := (Equiv.swap a b).injective
  mom := by
    intro c n hn
    rcases eq_or_ne c a with rfl | hca
    · rw [Equiv.swap_apply_left]; exact (hab n hn).symm
    · rcases eq_or_ne c b with rfl | hcb
      · rw [Equiv.swap_apply_right]; exact hab n hn
      · rw [Equiv.swap_apply_of_ne_of_ne hca hcb]

/--
**Rota's substitution principle, with allocation.** Let `a` and `b` be similar
names of a world, and `c₁, …, cₘ` names different from both. Replacing `a` by
`b` in the last argument of an expression of the full language does not change its value,
whatever the expression allocates.

This is the full-language form of `Restricted.substitution`: the world relation is the
renaming by the transposition of `a` and `b`, a world morphism. So this result,
like its form in the restricted language, is naturality.
-/
theorem substitution (w : World k) {a b : Fin w.size}
    (hab : ∀ n, n ≠ 0 → w.mom a n = w.mom b n) (m : ℕ) (t : Expr (m + 1))
    (c : Fin m → Fin w.size) (hca : ∀ i, c i ≠ a) (hcb : ∀ i, c i ≠ b) :
    (den (m + 1) t w (Fin.snoc c a)).2 = (den (m + 1) t w (Fin.snoc c b)).2 :=
  den_rel (m + 1) t (WRel.ofHom (swapHom w hab)) _ _ fun i => by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [WRel.ofHom, swapHom]
    · simp [WRel.ofHom, swapHom, Equiv.swap_apply_of_ne_of_ne (hca j) (hcb j)]

end

end FreeThms.Umbral.Full
