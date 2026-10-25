/-
# Separation from naturality

The free theorem of the type of contexts for the dot product, which gives
representation independence, is not an instance of naturality (write-up,
Chapter 3).

* A **`𝒲`-set** is a functor from the category of worlds to types, and
  `WSet.T` is the allocation monad on `𝒲`-sets.
* A **`𝒲`-dictionary** has `𝒲`-sets as carriers and natural transformations as
  methods, with `mk` valued in `T U`. Its homomorphisms commute with every
  method. The moment dictionary is one (`momentWDict`).
* A **pair** is a `𝒲`-dictionary with an implementation of the dot product at a
  world. A family of functions indexed by pairs is **natural** when it commutes
  with every homomorphism of pairs.
* **`separation`**: the block-size family is natural, and it takes different
  values at the symbolic and the constructed dot product, which the logical
  relation relates. So representation independence is not a consequence of
  naturality, and a natural family need not be parametric.
-/

import FreeThms.Umbral.RepIndependence

namespace FreeThms.Umbral.Full

open MvPolynomial (X C rename rename_X)

noncomputable section

variable {k : Type} [CommRing k]

/-! ## `𝒲`-sets and the allocation monad -/

omit [CommRing k] in
/-- Two morphisms with the same map on names are equal. -/
theorem Hom.toFun_inj {w v : World k} {σ τ : Hom w v} (h : σ.toFun = τ.toFun) : σ = τ := by
  cases σ
  cases τ
  cases h
  rfl

omit [CommRing k] in
theorem Hom.ext_id (w B : World k) : (Hom.id w).ext B = Hom.id (w.append B) :=
  Hom.toFun_inj (funext fun i => by
    induction i using Fin.addCases with
    | left a => simp [Hom.ext]
    | right b => simp [Hom.ext])

omit [CommRing k] in
theorem Hom.ext_comp {u v x : World k} (σ : Hom u v) (τ : Hom v x) (B : World k) :
    (σ.comp τ).ext B = (σ.ext B).comp (τ.ext B) :=
  Hom.toFun_inj (funext fun i => by
    induction i using Fin.addCases with
    | left a => simp [Hom.ext, Hom.comp]
    | right b => simp [Hom.ext, Hom.comp])

variable (k) in
/-- A **`𝒲`-set**: a functor from the category of worlds to types. -/
structure WSet where
  /-- The set at a world. -/
  obj : World k → Type
  /-- The action of a morphism. -/
  map : {w v : World k} → Hom w v → obj w → obj v
  map_id : ∀ w (x : obj w), map (Hom.id w) x = x
  map_comp : ∀ {u v w : World k} (σ : Hom u v) (τ : Hom v w) (x : obj u),
    map (σ.comp τ) x = map τ (map σ x)

/-- **The allocation monad** on `𝒲`-sets: `(T F)(w) = Σ_B F(w ⊕ B)`, on which a
morphism `σ` acts as `(B, s) ↦ (B, (σ ⊕ B) s)`. -/
def WSet.T (F : WSet k) : WSet k where
  obj w := Σ B : World k, F.obj (w.append B)
  map σ c := ⟨c.1, F.map (σ.ext c.1) c.2⟩
  map_id w c := by
    rw [Hom.ext_id, F.map_id]
  map_comp σ τ c := by
    rw [Hom.ext_comp, F.map_comp]

/-- A map of values acts on computations as `(B, s) ↦ (B, h s)`. -/
def WSet.tlift {F G : WSet k} (h : ∀ w, F.obj w → G.obj w) (w : World k) :
    F.T.obj w → G.T.obj w :=
  fun c => ⟨c.1, h (w.append c.1) c.2⟩

/-- The constant `𝒲`-set. -/
abbrev WSet.const (S : Type) : WSet k := ⟨fun _ => S, fun _ x => x, fun _ _ => rfl, fun _ _ _ => rfl⟩

/-- The names of a world. -/
abbrev WSet.names : WSet k :=
  ⟨fun w => Fin w.size, fun σ x => σ.toFun x, fun _ _ => rfl, fun _ _ _ => rfl⟩

/-- The polynomials in the names of a world, on which morphisms act by renaming. -/
abbrev WSet.polys : WSet k :=
  ⟨fun w => MvPolynomial (Fin w.size) k, fun σ p => rename σ.toFun p,
    fun _ p => MvPolynomial.rename_id_apply p, fun σ τ p => (MvPolynomial.rename_rename σ.toFun τ.toFun p).symm⟩

/-! ## `𝒲`-dictionaries and their homomorphisms -/

variable (k) in
/-- A **`𝒲`-dictionary**: the methods of the class `Umbral(K, U, A)` with
allocation, with `𝒲`-sets as carriers and natural transformations as methods;
`mk` is valued in `T U`. -/
structure WDict where
  K : WSet k
  U : WSet k
  A : WSet k
  zeroK : ∀ w, K.obj w
  oneK : ∀ w, K.obj w
  addK : ∀ w, K.obj w → K.obj w → K.obj w
  mulK : ∀ w, K.obj w → K.obj w → K.obj w
  negK : ∀ w, K.obj w → K.obj w
  zeroA : ∀ w, A.obj w
  oneA : ∀ w, A.obj w
  addA : ∀ w, A.obj w → A.obj w → A.obj w
  mulA : ∀ w, A.obj w → A.obj w → A.obj w
  negA : ∀ w, A.obj w → A.obj w
  const : ∀ w, K.obj w → A.obj w
  inj : ∀ w, U.obj w → A.obj w
  eval : ∀ w, A.obj w → K.obj w
  /-- The method `mk`, the allocation of a fresh umbra with the given moments. -/
  allocate : ∀ w, (ℕ → K.obj w) → U.T.obj w
  zeroK_nat : ∀ {w v} (σ : Hom w v), K.map σ (zeroK w) = zeroK v
  oneK_nat : ∀ {w v} (σ : Hom w v), K.map σ (oneK w) = oneK v
  addK_nat : ∀ {w v} (σ : Hom w v) x y, K.map σ (addK w x y) = addK v (K.map σ x) (K.map σ y)
  mulK_nat : ∀ {w v} (σ : Hom w v) x y, K.map σ (mulK w x y) = mulK v (K.map σ x) (K.map σ y)
  negK_nat : ∀ {w v} (σ : Hom w v) x, K.map σ (negK w x) = negK v (K.map σ x)
  zeroA_nat : ∀ {w v} (σ : Hom w v), A.map σ (zeroA w) = zeroA v
  oneA_nat : ∀ {w v} (σ : Hom w v), A.map σ (oneA w) = oneA v
  addA_nat : ∀ {w v} (σ : Hom w v) p q, A.map σ (addA w p q) = addA v (A.map σ p) (A.map σ q)
  mulA_nat : ∀ {w v} (σ : Hom w v) p q, A.map σ (mulA w p q) = mulA v (A.map σ p) (A.map σ q)
  negA_nat : ∀ {w v} (σ : Hom w v) p, A.map σ (negA w p) = negA v (A.map σ p)
  const_nat : ∀ {w v} (σ : Hom w v) c, A.map σ (const w c) = const v (K.map σ c)
  inj_nat : ∀ {w v} (σ : Hom w v) x, A.map σ (inj w x) = inj v (U.map σ x)
  eval_nat : ∀ {w v} (σ : Hom w v) p, K.map σ (eval w p) = eval v (A.map σ p)
  allocate_nat : ∀ {w v} (σ : Hom w v) f, U.T.map σ (allocate w f) = allocate v (K.map σ ∘ f)

/-- A **homomorphism of `𝒲`-dictionaries**: natural transformations `h_K`,
`h_U`, `h_A` that commute with every method. For `mk`, `h_{T U}(mk f) = mk'(h_K ∘ f)`,
where `h_{T U}` acts as `(B, s) ↦ (B, h_U s)`. -/
structure WDictHom (d d' : WDict k) where
  hK : ∀ w, d.K.obj w → d'.K.obj w
  hU : ∀ w, d.U.obj w → d'.U.obj w
  hA : ∀ w, d.A.obj w → d'.A.obj w
  hK_nat : ∀ {w v} (σ : Hom w v) x, d'.K.map σ (hK w x) = hK v (d.K.map σ x)
  hU_nat : ∀ {w v} (σ : Hom w v) x, d'.U.map σ (hU w x) = hU v (d.U.map σ x)
  hA_nat : ∀ {w v} (σ : Hom w v) x, d'.A.map σ (hA w x) = hA v (d.A.map σ x)
  zeroK : ∀ w, hK w (d.zeroK w) = d'.zeroK w
  oneK : ∀ w, hK w (d.oneK w) = d'.oneK w
  addK : ∀ w x y, hK w (d.addK w x y) = d'.addK w (hK w x) (hK w y)
  mulK : ∀ w x y, hK w (d.mulK w x y) = d'.mulK w (hK w x) (hK w y)
  negK : ∀ w x, hK w (d.negK w x) = d'.negK w (hK w x)
  zeroA : ∀ w, hA w (d.zeroA w) = d'.zeroA w
  oneA : ∀ w, hA w (d.oneA w) = d'.oneA w
  addA : ∀ w p q, hA w (d.addA w p q) = d'.addA w (hA w p) (hA w q)
  mulA : ∀ w p q, hA w (d.mulA w p q) = d'.mulA w (hA w p) (hA w q)
  negA : ∀ w p, hA w (d.negA w p) = d'.negA w (hA w p)
  const : ∀ w c, hA w (d.const w c) = d'.const w (hK w c)
  inj : ∀ w x, hA w (d.inj w x) = d'.inj w (hU w x)
  eval : ∀ w p, hK w (d.eval w p) = d'.eval w (hA w p)
  allocate : ∀ w f, WSet.tlift hU w (d.allocate w f) = d'.allocate w (hK w ∘ f)

/-- The numeral `n` of a `𝒲`-dictionary at a world, `0 + 1 + ⋯ + 1`. -/
def WDict.numeral (d : WDict k) (w : World k) : ℕ → d.K.obj w
  | 0 => d.zeroK w
  | n + 1 => d.addK w (d.numeral w n) (d.oneK w)

omit [CommRing k] in
/-- A homomorphism preserves numerals, because it commutes with `0`, `1` and `+`. -/
theorem WDictHom.map_numeral {d d' : WDict k} (h : WDictHom d d') (w : World k) :
    ∀ n, h.hK w (d.numeral w n) = d'.numeral w n
  | 0 => h.zeroK w
  | n + 1 => by rw [WDict.numeral, h.addK, h.map_numeral w n, h.oneK]; rfl

/-! ## The moment dictionary is a `𝒲`-dictionary -/

variable (k) in
/-- **The moment dictionary**, as a `𝒲`-dictionary: `K(w) = k`, `U(w)` the names
of `w`, `A(w)` the polynomials in them, the operations of the moment model of
`w`, and `mk f` a block with one name whose moments are `f`. -/
def momentWDict : WDict k where
  K := WSet.const k
  U := WSet.names
  A := WSet.polys
  zeroK _ := (0 : k)
  oneK _ := (1 : k)
  addK _ x y := (x + y : k)
  mulK _ x y := (x * y : k)
  negK _ x := (-x : k)
  zeroA _ := (0 : MvPolynomial _ k)
  oneA _ := (1 : MvPolynomial _ k)
  addA _ p q := (p + q : MvPolynomial _ k)
  mulA _ p q := (p * q : MvPolynomial _ k)
  negA _ p := (-p : MvPolynomial _ k)
  const _ c := (C c : MvPolynomial _ k)
  inj _ x := (X x : MvPolynomial _ k)
  eval w p := (Umbral.eval w.mom p : k)
  allocate w f := ⟨World.single f, Fin.natAdd w.size 0⟩
  zeroK_nat _ := rfl
  oneK_nat _ := rfl
  addK_nat _ _ _ := rfl
  mulK_nat _ _ _ := rfl
  negK_nat _ _ := rfl
  zeroA_nat _ := map_zero _
  oneA_nat _ := map_one _
  addA_nat _ p q := map_add _ p q
  mulA_nat _ p q := map_mul _ p q
  negA_nat _ p := map_neg _ p
  const_nat _ c := MvPolynomial.rename_C _ c
  inj_nat _ x := rename_X _ x
  eval_nat σ p := (eval_rename_hom σ p).symm
  allocate_nat σ f := by
    show (⟨World.single f, (σ.ext (World.single f)).toFun (Fin.natAdd _ 0)⟩ :
      Σ B : World k, Fin (_ + B.size)) = ⟨World.single f, Fin.natAdd _ 0⟩
    rw [show (σ.ext (World.single f)).toFun = σ.extMap (World.single f) from rfl,
      Hom.extMap_natAdd]

theorem numeral_momentWDict (w : World k) : ∀ n : ℕ, (momentWDict k).numeral w n = (n : k)
  | 0 => by rw [WDict.numeral, Nat.cast_zero]; rfl
  | n + 1 => by
    rw [WDict.numeral, numeral_momentWDict w n, Nat.cast_succ]
    rfl

/-! ## Pairs, natural families, and separation -/

variable (k) in
/-- A **pair** at a world `w`: a `𝒲`-dictionary and an implementation of the dot
product at `w`. -/
structure DotPair (w : World k) where
  d : WDict k
  dot : ℕ → d.U.obj w → d.A.T.obj w

/-- A **homomorphism of pairs**: a homomorphism of the dictionaries that
commutes with the dot products, `h_{T A} ∘ dot = dot' ∘ (id × h_U)`. -/
structure DotPairHom {w : World k} (P P' : DotPair k w) extends WDictHom P.d P'.d where
  dot : ∀ n x, WSet.tlift hA w (P.dot n x) = P'.dot n (hU w x)

variable (k) in
/-- A family of functions `ℕ × U → K`, one for each pair. -/
abbrev PairFamily : Type 1 := ∀ {w : World k} (P : DotPair k w), ℕ → P.d.U.obj w → P.d.K.obj w

/-- A family is **natural** if it commutes with every homomorphism of pairs. -/
def PairFamily.Natural (F : PairFamily k) : Prop :=
  ∀ {w : World k} {P P' : DotPair k w} (h : DotPairHom P P') (n : ℕ) (x : P.d.U.obj w),
    h.hK w (F P n x) = F P' n (h.hU w x)

/-- **The block-size family**: the number of names that the dot product
allocates, as a numeral of the dictionary. -/
def blockCount : PairFamily k := fun {w} P n x => P.d.numeral w (P.dot n x).1.size

omit [CommRing k] in
/-- **The block size is natural.** A homomorphism of pairs leaves the block
unchanged and commutes with `0`, `1` and `+`. -/
theorem blockCount_natural : PairFamily.Natural (blockCount (k := k)) := by
  intro w P P' h n x
  show h.hK w (P.d.numeral w (P.dot n x).1.size) = P'.d.numeral w (P'.dot n (h.hU w x)).1.size
  rw [← h.dot, h.map_numeral]
  rfl

/-- The symbolic dot product at the moment dictionary of `w`. -/
abbrev symbolicDot (w : World k) (n : ℕ) (x : Fin w.size) : Val (.comp tA) w :=
  (⟦dotSymbolicT⟧ w) w (Hom.id w) n w (Hom.id w) x

/-- The constructed dot product at the moment dictionary of `w`. -/
abbrev constructedDot (w : World k) (n : ℕ) (x : Fin w.size) : Val (.comp tA) w :=
  (⟦dotConstructedT⟧ w) w (Hom.id w) n w (Hom.id w) x

/-- The pair of the moment dictionary and the symbolic dot product. -/
def symbolicPair (w : World k) : DotPair k w := ⟨momentWDict k, symbolicDot w⟩

/-- The pair of the moment dictionary and the constructed dot product. -/
def constructedPair (w : World k) : DotPair k w := ⟨momentWDict k, constructedDot w⟩

/-- **Separation from naturality.** The block-size family is natural, the two
dot products are related by the logical relation, and for `n ≠ 1` the family
takes different values at them: one name against `n`. So representation
independence is not a consequence of naturality, and a natural family need not
be parametric. -/
theorem separation [CharZero k] (w : World k) (x : Fin w.size) {n : ℕ} (hn : n ≠ 1) :
    PairFamily.Natural (blockCount (k := k)) ∧
      Related dotTy (WRel.id w) (⟦dotSymbolicT⟧ w) (⟦dotConstructedT⟧ w) ∧
      blockCount (symbolicPair w) n x ≠ blockCount (constructedPair w) n x := by
  refine ⟨blockCount_natural, dot_rel _, ?_⟩
  have h₁ : (symbolicDot w n x).1.size = 1 := (sem_dotSymbolic (Hom.id w) n (Hom.id w) x).1
  have h₂ : (constructedDot w n x).1.size = n := (sem_dotConstructed (Hom.id w) n (Hom.id w) x).1
  show (momentWDict k).numeral w (symbolicDot w n x).1.size
    ≠ (momentWDict k).numeral w (constructedDot w n x).1.size
  rw [h₁, h₂, numeral_momentWDict, numeral_momentWDict]
  exact fun h => hn (Nat.cast_injective (R := k) h.symm)

end

end FreeThms.Umbral.Full
