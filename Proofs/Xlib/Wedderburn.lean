import Mathlib

/-!
# Wedderburn uniqueness over an algebraically closed field

This file supplies the **uniqueness half of the Artin–Wedderburn theorem** in the
algebraically closed case, which Mathlib currently lacks (explicit TODO in
`Mathlib.RingTheory.SimpleModule.Basic`: "Artin-Wedderburn Theory (uniqueness)").

The canonical, choice-free invariant is

  `isotypicLengthMultiset R : Multiset ℕ`,

the multiset of `(Module.length R c).toNat` over the isotypic components
`c ∈ isotypicComponents R R` of `R` as a module over itself.  The main theorem,

  `isotypicLengthMultiset_eq_of_algEquiv`,

identifies this multiset with the block-size multiset `{d i}` of **any** pi-matrix
decomposition `A ≃ₐ[F] Π i, Matrix (Fin (d i)) (Fin (d i)) F`.  In particular the
block sizes of such a decomposition are unique up to permutation.

## Proof architecture

* `mem_isotypicComponents_iff_minimal`: in a semisimple module, the isotypic
  components are exactly the minimal nonzero fully invariant submodules.  For a
  ring over itself, fully invariant = two-sided (`isFullyInvariant_iff_isTwoSided`),
  so membership in `isotypicComponents R R` is a purely ring-theoretic condition.
* `mapIdeal`: transport of left ideals along a ring equivalence; it preserves
  two-sidedness, `⊥`, `≤` and `Module.length` (the latter via a bijective
  semilinear map and `Order.krullDim_eq_of_orderIso`), hence maps isotypic
  components to isotypic components (`mapIdeal_mem_isotypicComponents`) and
  preserves the length multiset (`isotypicLengthMultiset_eq_of_ringEquiv`).
* `factorIdeal`: in a finite product `Π i, A i` of simple rings, the isotypic
  components are exactly the factor ideals (`factorIdeal_mem_isotypicComponents`,
  `eq_factorIdeal_of_mem_isotypicComponents`), and the `i`-th one has the length
  of `A i` over itself (`length_factorIdeal`).
* `colIdeal`: a square matrix ring over a division ring is, as a module over
  itself, the direct product of its (simple) column ideals, so
  `Module.length (Matrix m m K) (Matrix m m K) = Fintype.card m`
  (`length_matrix_self`).

Everything here is group-free generic ring theory; the application to group
algebras lives in `Xlib.CharDegrees`.

## Mathlib upstream candidate

`mem_isotypicComponents_iff_minimal`, `length_matrix_self` and
`isotypicLengthMultiset_eq_of_algEquiv` are natural upstream candidates: they
discharge the "uniqueness" TODO of `Mathlib.RingTheory.SimpleModule.Basic` for
algebras over algebraically closed fields.
-/

open Module

namespace Xlib.Wedderburn

/-! ### Length transport along bijective semilinear maps

`LinearEquiv.length_eq` is stated in Mathlib only for linear equivalences over a
fixed ring.  The same krull-dimension proof works verbatim for a bijective
semilinear map, which is exactly what transporting along a ring equivalence (or
along `Pi.evalRingHom`) requires. -/

/-- `Module.length` is invariant under bijective semilinear maps. -/
theorem length_eq_of_semilinear {R R' M M' : Type*} [Ring R] [Ring R']
    [AddCommGroup M] [AddCommGroup M'] [Module R M] [Module R' M']
    {σ : R →+* R'} [RingHomSurjective σ] (f : M →ₛₗ[σ] M') (hf : Function.Bijective f) :
    Module.length R M = Module.length R' M' := by
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f hf)]

/-! ### Isotypic components as minimal fully invariant submodules -/

/-- The infimum of two fully invariant submodules is fully invariant. -/
theorem isFullyInvariant_inf {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {N P : Submodule R M} (hN : N.IsFullyInvariant) (hP : P.IsFullyInvariant) :
    (N ⊓ P).IsFullyInvariant := fun f =>
  (inf_le_inf (hN f) (hP f)).trans_eq (Submodule.comap_inf ..).symm

/-- **Atom characterization of isotypic components.**  In a semisimple module, a
submodule is an isotypic component iff it is a minimal nonzero fully invariant
submodule.  This turns membership in `isotypicComponents R R` into a purely
lattice/ring-theoretic condition (fully invariant = two-sided for ideals), which
is what makes it transportable along ring equivalences. -/
theorem mem_isotypicComponents_iff_minimal {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [IsSemisimpleModule R M] {m : Submodule R M} :
    m ∈ isotypicComponents R M ↔
      m.IsFullyInvariant ∧ m ≠ ⊥ ∧ ∀ m' ≤ m, m'.IsFullyInvariant → m' = ⊥ ∨ m' = m := by
  constructor
  · intro hm
    refine ⟨.of_mem_isotypicComponents hm, (bot_lt_isotypicComponents hm).ne',
      fun m' hle hfi => ?_⟩
    obtain ⟨s, hs, rfl⟩ := isFullyInvariant_iff_sSup_isotypicComponents.mp hfi
    have hsub : s ⊆ {m} := by
      intro c hc
      rw [Set.mem_singleton_iff]
      by_contra hne
      have hc' : c ≤ sSup (isotypicComponents R M \ {c}) :=
        ((le_sSup hc).trans hle).trans
          (le_sSup ⟨hm, fun h => hne (Set.mem_singleton_iff.mp h).symm⟩)
      exact (bot_lt_isotypicComponents (hs hc)).ne'
        ((sSupIndep_isotypicComponents R M (hs hc)).eq_bot_of_le hc')
    rcases Set.subset_singleton_iff_eq.mp hsub with rfl | rfl
    · exact Or.inl sSup_empty
    · exact Or.inr sSup_singleton
  · rintro ⟨hfi, hne, hmin⟩
    obtain ⟨s, hs, rfl⟩ := isFullyInvariant_iff_sSup_isotypicComponents.mp hfi
    obtain ⟨c, hc⟩ : s.Nonempty :=
      Set.nonempty_iff_ne_empty.mpr fun h => hne (by rw [h, sSup_empty])
    rcases hmin c (le_sSup hc) (.of_mem_isotypicComponents (hs hc)) with h | h
    · exact absurd h (bot_lt_isotypicComponents (hs hc)).ne'
    · exact h ▸ hs hc

/-! ### The isotypic length multiset -/

/-- **The isotypic length multiset** of a ring: the multiset of
`(Module.length R c).toNat` over the isotypic components `c` of `R` as a module
over itself.  For a finite-dimensional semisimple algebra over an algebraically
closed field this is the multiset of matrix block sizes of any Wedderburn
decomposition (`isotypicLengthMultiset_eq_of_algEquiv`); for a group algebra
`ℂ[G]` it is the multiset of irreducible character degrees. -/
noncomputable def isotypicLengthMultiset (R : Type*) [Ring R]
    [Fintype ↥(isotypicComponents R R)] : Multiset ℕ :=
  (Finset.univ : Finset ↥(isotypicComponents R R)).val.map
    fun c => (Module.length R c.1).toNat

/-! ### Transport along a ring equivalence -/

section Transport

variable {R R' : Type*} [Ring R] [Ring R']

/-- Transport of a left ideal along a ring equivalence.  (A hand-rolled image
construction: keeping the membership definitional avoids all semilinear
typeclass bookkeeping in statements.) -/
def mapIdeal (e : R ≃+* R') (I : Ideal R) : Ideal R' where
  carrier := e '' I
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, I.add_mem hx hy, map_add e x y⟩
  zero_mem' := ⟨0, I.zero_mem, map_zero e⟩
  smul_mem' := by
    rintro c _ ⟨x, hx, rfl⟩
    exact ⟨e.symm c * x, I.mul_mem_left _ hx, by rw [map_mul, e.apply_symm_apply, smul_eq_mul]⟩

variable {e : R ≃+* R'} {I J : Ideal R}

lemma mem_mapIdeal {y : R'} : y ∈ mapIdeal e I ↔ e.symm y ∈ I := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    rwa [e.symm_apply_apply]
  · intro h
    exact ⟨e.symm y, h, e.apply_symm_apply y⟩

lemma mapIdeal_symm_mapIdeal (e : R ≃+* R') (I : Ideal R) :
    mapIdeal e.symm (mapIdeal e I) = I := by
  ext x
  rw [mem_mapIdeal, mem_mapIdeal, RingEquiv.symm_symm, e.symm_apply_apply]

lemma mapIdeal_mapIdeal_symm (e : R ≃+* R') (I' : Ideal R') :
    mapIdeal e (mapIdeal e.symm I') = I' := by
  ext x
  rw [mem_mapIdeal, mem_mapIdeal, RingEquiv.symm_symm, e.apply_symm_apply]

lemma mapIdeal_le_iff : mapIdeal e I ≤ mapIdeal e J ↔ I ≤ J := by
  constructor
  · intro h x hx
    have := h ⟨x, hx, rfl⟩
    rwa [mem_mapIdeal, e.symm_apply_apply] at this
  · rintro h _ ⟨x, hx, rfl⟩
    exact ⟨x, h hx, rfl⟩

lemma mapIdeal_bot (e : R ≃+* R') : mapIdeal e (⊥ : Ideal R) = ⊥ := by
  ext x
  rw [mem_mapIdeal, Submodule.mem_bot, Submodule.mem_bot, EmbeddingLike.map_eq_zero_iff]

lemma mapIdeal_eq_bot_iff : mapIdeal e I = ⊥ ↔ I = ⊥ := by
  constructor
  · intro h
    rw [← mapIdeal_symm_mapIdeal e I, h, mapIdeal_bot]
  · rintro rfl
    exact mapIdeal_bot e

lemma mapIdeal_isTwoSided (h : I.IsTwoSided) : (mapIdeal e I).IsTwoSided := by
  constructor
  rintro _ b ⟨x, hx, rfl⟩
  exact ⟨x * e.symm b, h.mul_mem_of_left _ hx, by rw [map_mul, e.apply_symm_apply]⟩

lemma mapIdeal_isFullyInvariant_iff :
    (mapIdeal e I).IsFullyInvariant ↔ I.IsFullyInvariant := by
  rw [isFullyInvariant_iff_isTwoSided, isFullyInvariant_iff_isTwoSided]
  constructor
  · intro h
    have := mapIdeal_isTwoSided (e := e.symm) h
    rwa [mapIdeal_symm_mapIdeal] at this
  · exact mapIdeal_isTwoSided

/-- `mapIdeal` preserves `Module.length`, via the bijective `e`-semilinear
equivalence `I → mapIdeal e I`. -/
lemma length_mapIdeal (e : R ≃+* R') (I : Ideal R) :
    Module.length R' (mapIdeal e I) = Module.length R I := by
  haveI : RingHomSurjective (e : R →+* R') := ⟨e.surjective⟩
  refine (length_eq_of_semilinear (σ := (e : R →+* R'))
    { toFun := fun x => ⟨e x.1, ⟨x.1, x.2, rfl⟩⟩
      map_add' := fun x y => Subtype.ext (map_add e x.1 y.1)
      map_smul' := fun r x => Subtype.ext (by
        show e (↑(r • x)) = e r * e x.1
        rw [Submodule.coe_smul, smul_eq_mul, map_mul]) }
    ⟨fun x y h => Subtype.ext (e.injective (congrArg Subtype.val h)),
     fun y => ⟨⟨e.symm y.1, by
        obtain ⟨_, x, hx, rfl⟩ := y
        rwa [e.symm_apply_apply]⟩, Subtype.ext (e.apply_symm_apply y.1)⟩⟩).symm

/-- Ring equivalences map isotypic components to isotypic components. -/
theorem mapIdeal_mem_isotypicComponents (e : R ≃+* R') [IsSemisimpleRing R] {c : Ideal R}
    (hc : c ∈ isotypicComponents R R) : mapIdeal e c ∈ isotypicComponents R' R' := by
  haveI : IsSemisimpleRing R' := e.isSemisimpleRing
  rw [mem_isotypicComponents_iff_minimal] at hc ⊢
  obtain ⟨h1, h2, h3⟩ := hc
  refine ⟨mapIdeal_isFullyInvariant_iff.mpr h1,
    fun h => h2 (mapIdeal_eq_bot_iff.mp h), fun m' hle hfi => ?_⟩
  have hm' : m' = mapIdeal e (mapIdeal e.symm m') := (mapIdeal_mapIdeal_symm e m').symm
  have hle' : mapIdeal e.symm m' ≤ c := by
    rw [← mapIdeal_le_iff (e := e), ← hm']
    exact hle
  rcases h3 _ hle' (mapIdeal_isFullyInvariant_iff.mpr hfi) with h | h
  · left
    rw [hm', h, mapIdeal_bot]
  · right
    rw [hm', h]

/-- **Invariance of the isotypic length multiset.**  Isomorphic (semisimple)
rings have equal isotypic length multisets. -/
theorem isotypicLengthMultiset_eq_of_ringEquiv (e : R ≃+* R') [IsSemisimpleRing R]
    [Fintype ↥(isotypicComponents R R)] [Fintype ↥(isotypicComponents R' R')] :
    isotypicLengthMultiset R = isotypicLengthMultiset R' := by
  haveI : IsSemisimpleRing R' := e.isSemisimpleRing
  let φ : ↥(isotypicComponents R R) ≃ ↥(isotypicComponents R' R') :=
    { toFun := fun c => ⟨mapIdeal e c.1, mapIdeal_mem_isotypicComponents e c.2⟩
      invFun := fun c => ⟨mapIdeal e.symm c.1, mapIdeal_mem_isotypicComponents e.symm c.2⟩
      left_inv := fun c => Subtype.ext (mapIdeal_symm_mapIdeal e c.1)
      right_inv := fun c => Subtype.ext (mapIdeal_mapIdeal_symm e c.1) }
  unfold isotypicLengthMultiset
  rw [← Multiset.map_univ_val_equiv φ, Multiset.map_map]
  exact Multiset.map_congr rfl fun c _ => (congrArg ENat.toNat (length_mapIdeal e c.1)).symm

end Transport

/-! ### Column ideals: the length of a matrix ring over itself -/

section MatrixColumns

variable {K : Type*} [DivisionRing K] {m : Type*} [Fintype m] [DecidableEq m]

/-- The left ideal of `Matrix m m K` of matrices supported on column `k`. -/
def colIdeal (K : Type*) [DivisionRing K] {m : Type*} [Fintype m] [DecidableEq m] (k : m) :
    Ideal (Matrix m m K) where
  carrier := {x | ∀ p q, q ≠ k → x p q = 0}
  add_mem' := fun {x y} hx hy p q hq => by
    rw [Matrix.add_apply, hx p q hq, hy p q hq, add_zero]
  zero_mem' := fun p q _ => rfl
  smul_mem' := fun c x hx => by
    intro p q hq
    rw [smul_eq_mul, Matrix.mul_apply]
    exact Finset.sum_eq_zero fun r _ => by rw [hx r q hq, mul_zero]

lemma mem_colIdeal {k : m} {x : Matrix m m K} :
    x ∈ colIdeal K k ↔ ∀ p q, q ≠ k → x p q = 0 := Iff.rfl

/-- Column ideals are simple modules: any nonzero column-supported matrix
generates the whole column ideal. -/
theorem isSimpleModule_colIdeal (k : m) :
    IsSimpleModule (Matrix m m K) (colIdeal K k) := by
  rw [isSimpleModule_iff_toSpanSingleton_surjective]
  constructor
  · refine (Submodule.nontrivial_iff_ne_bot).mpr ((Submodule.ne_bot_iff _).mpr
      ⟨Matrix.of fun p q => if q = k then 1 else 0, fun p q hq => if_neg hq, fun h => ?_⟩)
    have := congrFun (congrFun h k) k
    simp at this
  · rintro ⟨x, hx⟩ hx0
    have hxe : ∃ i₀, x i₀ k ≠ 0 := by
      by_contra h
      simp only [not_exists, not_ne_iff] at h
      refine hx0 (Subtype.ext ?_)
      funext p q
      rcases eq_or_ne q k with rfl | hq
      · exact h p
      · exact hx p q hq
    obtain ⟨i₀, hi₀⟩ := hxe
    rintro ⟨w, hw⟩
    refine ⟨Matrix.of fun p r => if r = i₀ then w p k * (x i₀ k)⁻¹ else 0, Subtype.ext ?_⟩
    rw [LinearMap.toSpanSingleton_apply, Submodule.coe_smul, smul_eq_mul]
    ext p q
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    rw [Finset.sum_eq_single i₀ (fun r _ hr => by rw [if_neg hr, zero_mul])
      (fun h => absurd (Finset.mem_univ i₀) h), if_pos rfl]
    rcases eq_or_ne q k with rfl | hq
    · rw [mul_assoc, inv_mul_cancel₀ hi₀, mul_one]
    · rw [hx i₀ q hq, mul_zero, hw p q hq]

/-- A square matrix ring, as a module over itself, is the direct product of its
column ideals. -/
def matrixColEquiv :
    Matrix m m K ≃ₗ[Matrix m m K] Π k : m, colIdeal K k where
  toFun x k := ⟨Matrix.of fun p q => if q = k then x p q else 0, fun p q hq => if_neg hq⟩
  map_add' x y := by
    funext k
    apply Subtype.ext
    show (Matrix.of fun p q => if q = k then (x + y) p q else 0) =
      (Matrix.of fun p q => if q = k then x p q else 0) +
        (Matrix.of fun p q => if q = k then y p q else 0)
    ext p q
    simp only [Matrix.of_apply, Matrix.add_apply]
    rcases eq_or_ne q k with rfl | hq
    · rw [if_pos rfl, if_pos rfl, if_pos rfl]
    · rw [if_neg hq, if_neg hq, if_neg hq, add_zero]
  map_smul' a x := by
    funext k
    apply Subtype.ext
    show (Matrix.of fun p q => if q = k then (a * x) p q else 0) =
      a * Matrix.of fun p q => if q = k then x p q else 0
    ext p q
    simp only [Matrix.of_apply, Matrix.mul_apply]
    rcases eq_or_ne q k with rfl | hq
    · rw [if_pos rfl]
      exact Finset.sum_congr rfl fun r _ => by rw [if_pos rfl]
    · rw [if_neg hq]
      exact (Finset.sum_eq_zero fun r _ => by rw [if_neg hq, mul_zero]).symm
  invFun c := ∑ k, (c k : Matrix m m K)
  left_inv x := by
    dsimp only
    ext p q
    rw [Matrix.sum_apply]
    simp only [Matrix.of_apply]
    rw [Finset.sum_ite_eq]
    exact if_pos (Finset.mem_univ q)
  right_inv c := by
    dsimp only
    funext k
    apply Subtype.ext
    show (Matrix.of fun p q => if q = k then (∑ j, ((c j : Matrix m m K))) p q else 0) =
      (c k : Matrix m m K)
    ext p q
    rw [Matrix.of_apply]
    rcases eq_or_ne q k with rfl | hq
    · rw [if_pos rfl, Matrix.sum_apply]
      exact Finset.sum_eq_single q (fun j _ hj => (c j).2 p q (Ne.symm hj))
        (fun h => absurd (Finset.mem_univ q) h)
    · rw [if_neg hq, ((c k).2 p q hq)]

/-- **The length of a matrix ring over itself** is the number of columns. -/
theorem length_matrix_self :
    Module.length (Matrix m m K) (Matrix m m K) = Fintype.card m := by
  rw [(matrixColEquiv (K := K) (m := m)).length_eq, Module.length_pi_of_fintype]
  have h : ∀ k : m, Module.length (Matrix m m K) (colIdeal K k) = 1 := fun k =>
    haveI := isSimpleModule_colIdeal (K := K) k
    Module.length_eq_one _ _
  rw [Finset.sum_congr rfl fun k _ => h k, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one]

end MatrixColumns

/-! ### Factor ideals: the isotypic components of a finite product of simple rings -/

section PiFactor

variable {ι : Type*} {A : ι → Type*} [∀ i, Ring (A i)]

/-- The `i`-th factor ideal of a finite product of rings: elements supported on
the `i`-th coordinate. -/
def factorIdeal (A : ι → Type*) [∀ i, Ring (A i)] (i : ι) : Ideal (Π j, A j) where
  carrier := {x | ∀ j, j ≠ i → x j = 0}
  add_mem' := fun {x y} hx hy j hj => by
    rw [Pi.add_apply, hx j hj, hy j hj, add_zero]
  zero_mem' := fun j _ => rfl
  smul_mem' := fun c x hx j hj => by
    rw [smul_eq_mul, Pi.mul_apply, hx j hj, mul_zero]

lemma mem_factorIdeal {i : ι} {x : Π j, A j} :
    x ∈ factorIdeal A i ↔ ∀ j, j ≠ i → x j = 0 := Iff.rfl

variable [DecidableEq ι]

lemma single_mem_factorIdeal (i : ι) (y : A i) : Pi.single i y ∈ factorIdeal A i :=
  fun _ hj => Pi.single_eq_of_ne hj y

lemma eq_single_of_mem_factorIdeal {i : ι} {x : Π j, A j} (hx : x ∈ factorIdeal A i) :
    x = Pi.single i (x i) := by
  funext j
  rcases eq_or_ne j i with rfl | hj
  · rw [Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hj, hx j hj]

lemma mul_single_one (x : Π j, A j) (i : ι) : x * Pi.single i 1 = Pi.single i (x i) := by
  funext j
  rcases eq_or_ne j i with rfl | hj
  · rw [Pi.mul_apply, Pi.single_eq_same, Pi.single_eq_same, mul_one]
  · rw [Pi.mul_apply, Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj, mul_zero]

omit [DecidableEq ι] in
lemma factorIdeal_isTwoSided (i : ι) : (factorIdeal A i).IsTwoSided := by
  constructor
  intro x b hx j hj
  rw [Pi.mul_apply, hx j hj, zero_mul]

lemma factorIdeal_ne_bot (i : ι) [Nontrivial (A i)] : factorIdeal A i ≠ ⊥ := by
  rw [Submodule.ne_bot_iff]
  refine ⟨Pi.single i 1, single_mem_factorIdeal i 1, fun h => ?_⟩
  have := congrFun h i
  rw [Pi.single_eq_same] at this
  exact one_ne_zero this

lemma factorIdeal_injective [∀ i, Nontrivial (A i)] :
    Function.Injective (factorIdeal A) := by
  intro i j h
  by_contra hij
  have h1 : Pi.single i (1 : A i) ∈ factorIdeal A j := h ▸ single_mem_factorIdeal i 1
  have := h1 i hij
  rw [Pi.single_eq_same] at this
  exact one_ne_zero this

/-- The restriction of an ideal of a product ring to the `i`-th coordinate. -/
private def factorRestrict (I : Ideal (Π j, A j)) (i : ι) : Ideal (A i) where
  carrier := {y | Pi.single i y ∈ I}
  add_mem' := fun {a b} ha hb => by
    show Pi.single i (a + b) ∈ I
    rw [Pi.single_add]
    exact I.add_mem ha hb
  zero_mem' := by
    show Pi.single i (0 : A i) ∈ I
    rw [Pi.single_zero]
    exact I.zero_mem
  smul_mem' := fun c y hy => by
    show Pi.single i (c • y) ∈ I
    rw [smul_eq_mul, Pi.single_mul]
    exact I.mul_mem_left _ hy

private lemma mem_factorRestrict {I : Ideal (Π j, A j)} {i : ι} {y : A i} :
    y ∈ factorRestrict I i ↔ Pi.single i y ∈ I := Iff.rfl

/-- Minimality of factor ideals over simple factors: a two-sided ideal below
`factorIdeal A i` is `⊥` or everything. -/
theorem eq_bot_or_eq_of_le_factorIdeal {i : ι} [IsSimpleRing (A i)]
    {I : Ideal (Π j, A j)} (hI : I.IsTwoSided) (hle : I ≤ factorIdeal A i) :
    I = ⊥ ∨ I = factorIdeal A i := by
  have hK : (factorRestrict I i).IsTwoSided := by
    constructor
    intro y b hy
    show Pi.single i (y * b) ∈ I
    rw [Pi.single_mul]
    exact hI.mul_mem_of_left _ hy
  rcases (isSimpleRing_iff_isTwoSided_imp.mp inferInstance).2 (factorRestrict I i) hK
    with hbot | htop
  · left
    rw [eq_bot_iff]
    intro z hz
    have hz' : z = Pi.single i (z i) := eq_single_of_mem_factorIdeal (hle hz)
    have hzK : z i ∈ factorRestrict I i := by
      rw [mem_factorRestrict, ← hz']
      exact hz
    rw [hbot, Submodule.mem_bot] at hzK
    rw [Submodule.mem_bot, hz', hzK, Pi.single_zero]
  · right
    refine le_antisymm hle fun z hz => ?_
    have hz' : z = Pi.single i (z i) := eq_single_of_mem_factorIdeal hz
    have hzK : z i ∈ factorRestrict I i := htop ▸ Submodule.mem_top
    rw [hz']
    exact hzK

/-- Every isotypic component of a finite product of simple rings is a factor ideal. -/
theorem eq_factorIdeal_of_mem_isotypicComponents [∀ i, IsSimpleRing (A i)]
    [IsSemisimpleRing (Π i, A i)] {c : Ideal (Π j, A j)}
    (hc : c ∈ isotypicComponents (Π j, A j) (Π j, A j)) : ∃ i, c = factorIdeal A i := by
  rw [mem_isotypicComponents_iff_minimal] at hc
  obtain ⟨hfi, hne, hmin⟩ := hc
  have htwo : c.IsTwoSided := isFullyInvariant_iff_isTwoSided.mp hfi
  obtain ⟨x, hxc, hx0⟩ := (Submodule.ne_bot_iff c).mp hne
  obtain ⟨i, hxi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    simp only [not_exists, not_ne_iff] at h
    exact hx0 (funext h)
  refine ⟨i, ?_⟩
  have hsx : Pi.single i (x i) ∈ c := by
    rw [← mul_single_one x i]
    exact htwo.mul_mem_of_left _ hxc
  have hinf : c ⊓ factorIdeal A i ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    refine ⟨Pi.single i (x i), ⟨hsx, single_mem_factorIdeal i (x i)⟩, fun h => hxi ?_⟩
    have := congrFun h i
    rwa [Pi.single_eq_same] at this
  rcases hmin (c ⊓ factorIdeal A i) inf_le_left
    (isFullyInvariant_inf hfi (isFullyInvariant_iff_isTwoSided.mpr (factorIdeal_isTwoSided i)))
    with h | h
  · exact absurd h hinf
  · have hle : c ≤ factorIdeal A i := inf_eq_left.mp h
    exact (eq_bot_or_eq_of_le_factorIdeal htwo hle).resolve_left hne

/-- Every factor ideal of a finite product of simple rings is an isotypic component. -/
theorem factorIdeal_mem_isotypicComponents [∀ i, IsSimpleRing (A i)]
    [IsSemisimpleRing (Π i, A i)] (i : ι) :
    factorIdeal A i ∈ isotypicComponents (Π j, A j) (Π j, A j) := by
  rw [mem_isotypicComponents_iff_minimal]
  exact ⟨isFullyInvariant_iff_isTwoSided.mpr (factorIdeal_isTwoSided i), factorIdeal_ne_bot i,
    fun m' h1 h2 =>
      eq_bot_or_eq_of_le_factorIdeal (isFullyInvariant_iff_isTwoSided.mp h2) h1⟩

/-- The length of the `i`-th factor ideal over the product ring is the length of
the `i`-th factor over itself, via the (bijective, `Pi.evalRingHom`-semilinear)
evaluation map. -/
theorem length_factorIdeal (i : ι) :
    Module.length (Π j, A j) (factorIdeal A i) = Module.length (A i) (A i) := by
  haveI : RingHomSurjective (Pi.evalRingHom A i) :=
    ⟨fun y => ⟨Pi.single i y, Pi.single_eq_same i y⟩⟩
  refine length_eq_of_semilinear (σ := Pi.evalRingHom A i)
    { toFun := fun x => x.1 i
      map_add' := fun x y => rfl
      map_smul' := fun r x => rfl } ⟨fun x y h => ?_, fun y => ?_⟩
  · apply Subtype.ext
    funext j
    rcases eq_or_ne j i with rfl | hj
    · exact h
    · rw [x.2 j hj, y.2 j hj]
  · exact ⟨⟨Pi.single i y, single_mem_factorIdeal i y⟩, Pi.single_eq_same i y⟩

/-- **The isotypic length multiset of a finite product of simple rings** is the
multiset of the factors' self-lengths. -/
theorem isotypicLengthMultiset_pi [Fintype ι] [∀ i, IsSimpleRing (A i)]
    [IsSemisimpleRing (Π i, A i)]
    [Fintype ↥(isotypicComponents (Π j, A j) (Π j, A j))] :
    isotypicLengthMultiset (Π j, A j) =
      Finset.univ.val.map fun i => (Module.length (A i) (A i)).toNat := by
  let ψ : ι ≃ ↥(isotypicComponents (Π j, A j) (Π j, A j)) :=
    Equiv.ofBijective (fun i => ⟨factorIdeal A i, factorIdeal_mem_isotypicComponents i⟩)
      ⟨fun i j h => factorIdeal_injective (congrArg Subtype.val h),
       fun c => (eq_factorIdeal_of_mem_isotypicComponents c.2).imp
         fun i hi => Subtype.ext hi.symm⟩
  unfold isotypicLengthMultiset
  rw [← Multiset.map_univ_val_equiv ψ, Multiset.map_map]
  exact Multiset.map_congr rfl fun i _ => congrArg ENat.toNat (length_factorIdeal i)

end PiFactor

/-! ### Center glue: products and transport along algebra equivalences

Small general lemmas about `Subalgebra.center` missing from Mathlib (which has
`Set.center_pi` and `Subalgebra.pi` but no bridge, and no transport of the
center along an `AlgEquiv`) — **upstream candidates**.  Consumed by the
`#irreps = #conjugacy classes` count in `Xlib.CharDegrees`. -/

section Center

variable {R : Type*} [CommSemiring R]

section Pi

variable {ι : Type*} {S : ι → Type*} [∀ i, Semiring (S i)] [∀ i, Algebra R (S i)]

/-- The center of a product algebra is the product of the centers
(`Set.center_pi` lifted to `Subalgebra`). -/
theorem center_pi :
    Subalgebra.center R (Π i, S i) = Subalgebra.pi Set.univ fun i => Subalgebra.center R (S i) :=
  SetLike.coe_injective Set.center_pi

/-- The center of a product algebra is `R`-linearly equivalent to the product
of the centers. -/
def centerPiEquiv :
    Subalgebra.center R (Π i, S i) ≃ₗ[R] Π i, Subalgebra.center R (S i) where
  toFun z i := ⟨z.1 i, by
    have hz : (z : Π i, S i) ∈ Set.center (Π i, S i) := z.2
    rw [Set.center_pi] at hz
    exact hz i (Set.mem_univ i)⟩
  invFun c := ⟨fun i => (c i).1, by
    show _ ∈ Set.center (Π i, S i)
    rw [Set.center_pi]
    exact fun i _ => (c i).2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

end Pi

variable {A B : Type*} [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

/-- An algebra equivalence maps the center onto the center. -/
theorem map_center (e : A ≃ₐ[R] B) :
    (Subalgebra.center R A).map (e : A →ₐ[R] B) = Subalgebra.center R B := by
  ext b
  simp only [Subalgebra.mem_map, Subalgebra.mem_center_iff]
  constructor
  · rintro ⟨a, ha, rfl⟩ c
    calc c * e a = e (e.symm c * a) := by rw [map_mul, e.apply_symm_apply]
      _ = e (a * e.symm c) := by rw [ha]
      _ = e a * c := by rw [map_mul, e.apply_symm_apply]
  · intro hb
    refine ⟨e.symm b, fun c => e.injective ?_, e.apply_symm_apply b⟩
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact hb (e c)

/-- Transport of the center of an algebra along an algebra equivalence. -/
def centerCongr (e : A ≃ₐ[R] B) :
    Subalgebra.center R A ≃ₐ[R] Subalgebra.center R B :=
  (e.subalgebraMap (Subalgebra.center R A)).trans
    (Subalgebra.equivOfEq _ _ (map_center e))

end Center

/-- **The center of a finite product of central algebras has dimension the
number of factors**: for nontrivial central algebras `A i` over a field `F`
(e.g. matrix algebras `Matrix (Fin dᵢ) (Fin dᵢ) F` with `dᵢ ≠ 0`),
`finrank F Z(Π i, A i) = card ι`. -/
theorem finrank_center_pi {F : Type*} [Field F] {ι : Type*} [Fintype ι] {A : ι → Type*}
    [∀ i, Semiring (A i)] [∀ i, Algebra F (A i)] [∀ i, Algebra.IsCentral F (A i)]
    [∀ i, Nontrivial (A i)] :
    Module.finrank F (Subalgebra.center F (Π i, A i)) = Fintype.card ι := by
  rw [LinearEquiv.finrank_eq (centerPiEquiv (R := F) (S := A)),
    LinearEquiv.finrank_eq (LinearEquiv.piCongrRight fun i =>
      ((Subalgebra.equivOfEq _ _ (Algebra.IsCentral.center_eq_bot F (A i))).trans
        (Algebra.botEquiv F (A i))).toLinearEquiv),
    Module.finrank_pi]

/-! ### The main theorem: Wedderburn uniqueness over an algebraically closed field -/

/-- **Wedderburn uniqueness (algebraically closed case).**  If
`A ≃ₐ[F] Π i, Matrix (Fin (d i)) (Fin (d i)) F` is **any** pi-matrix
decomposition of an `F`-algebra `A` (with nonzero blocks), then the isotypic
length multiset of `A` equals the multiset of block sizes `{d i}`.  In
particular the block sizes are determined by `A` up to permutation.

This is the uniqueness half of the Artin–Wedderburn theorem (over an
algebraically closed field the existence half is
`IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed`); it is stated as a
Mathlib TODO in `Mathlib.RingTheory.SimpleModule.Basic`. -/
theorem isotypicLengthMultiset_eq_of_algEquiv {F : Type*} [Field F] {A : Type*} [Ring A]
    [Algebra F A] {n : ℕ} {d : Fin n → ℕ} [∀ i, NeZero (d i)]
    [Fintype ↥(isotypicComponents A A)]
    (e : A ≃ₐ[F] Π i, Matrix (Fin (d i)) (Fin (d i)) F) :
    isotypicLengthMultiset A = Finset.univ.val.map d := by
  haveI : ∀ i, Nonempty (Fin (d i)) := fun i => ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (d i))⟩⟩
  haveI : IsSemisimpleRing A := e.symm.toRingEquiv.isSemisimpleRing
  haveI : Fintype ↥(isotypicComponents (Π i, Matrix (Fin (d i)) (Fin (d i)) F)
      (Π i, Matrix (Fin (d i)) (Fin (d i)) F)) := Fintype.ofFinite _
  rw [isotypicLengthMultiset_eq_of_ringEquiv e.toRingEquiv, isotypicLengthMultiset_pi]
  exact Multiset.map_congr rfl fun i _ => by
    rw [length_matrix_self, Fintype.card_fin, ENat.toNat_coe]

end Xlib.Wedderburn
