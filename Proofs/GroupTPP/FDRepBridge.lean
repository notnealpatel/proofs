import GroupTPP.CharDegrees

/-!
# Bridge: charDegrees equals the multiset of simple-module dimensions

**Packaging decision (Fd1):** module-side (`IsSimpleModule`) not `FDRep`.
See `charDegrees_eq_simpleModuleDims` docstring for rationale.
-/

open scoped BigOperators
open GroupTPP.CharDegrees GroupTPP.Wedderburn

namespace GroupTPP.FDRepBridge

/-! ### Column ideal dimension -/

section ColIdealFinrank

variable {K : Type*} [Field K] {m : Type*} [Fintype m] [DecidableEq m]

noncomputable def colIdealEquiv (k : m) : colIdeal K k ≃ₗ[K] (m → K) where
  toFun x := fun i => (x : Matrix m m K) i k
  map_add' x y := funext fun _ => by simp
  map_smul' r x := by ext; rfl
  invFun v := ⟨Matrix.of fun i j => if j = k then v i else 0,
    fun _ q hq => by simp [Matrix.of_apply, if_neg hq]⟩
  left_inv x := by
    apply Subtype.ext; ext i j; simp only [Matrix.of_apply]
    rcases eq_or_ne j k with rfl | hj
    · simp
    · rw [if_neg hj]; exact (x.2 i j hj).symm
  right_inv v := by ext i; simp [Matrix.of_apply]

theorem finrank_colIdeal (k : m) :
    Module.finrank K (colIdeal K k) = Fintype.card m := by
  rw [(colIdealEquiv k).finrank_eq, Module.finrank_fintype_fun_eq_card]

end ColIdealFinrank

/-! ### finrank preservation along algebra equivalences -/

section FinrankTransport

variable {K : Type*} [CommSemiring K]
  {R R' : Type*} [Ring R] [Ring R'] [Algebra K R] [Algebra K R']

noncomputable def idealLinearEquiv (e : R ≃ₐ[K] R') (I : Ideal R) :
    I ≃ₗ[K] mapIdeal e.toRingEquiv I where
  toFun x := ⟨e x, ⟨x, x.2, rfl⟩⟩
  map_add' x y := Subtype.ext (map_add e x.1 y.1)
  map_smul' r x := Subtype.ext (by
    show e (r • (x : R)) = r • (e (x : R))
    simp [Algebra.smul_def, map_mul, e.commutes])
  invFun y := ⟨e.symm y, mem_mapIdeal.mp y.2⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv y := Subtype.ext (e.apply_symm_apply y)

theorem finrank_mapIdeal (e : R ≃ₐ[K] R') (I : Ideal R) :
    Module.finrank K (mapIdeal e.toRingEquiv I) = Module.finrank K I :=
  (idealLinearEquiv e I).finrank_eq.symm

end FinrankTransport

/-! ### R-linear isos between ideals preserve K-dimension -/

section ScalarRestrict

variable {K : Type*} [CommSemiring K] {R : Type*} [Ring R] [Algebra K R]

theorem finrank_eq_of_linearEquiv_ideal {I J : Ideal R}
    (e : I ≃ₗ[R] J) : Module.finrank K I = Module.finrank K J :=
  (e.restrictScalars K).finrank_eq

end ScalarRestrict

/-! ### Simple ideals of Mat_n(K) have K-dimension n -/

section MatrixSimple

variable {K : Type*} [Field K] {n : ℕ} [NeZero n]

theorem finrank_simple_ideal_matrix
    (I : Ideal (Matrix (Fin n) (Fin n) K))
    [IsSimpleModule (Matrix (Fin n) (Fin n) K) I] :
    Module.finrank K I = n := by
  haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩
  set k : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
  haveI : IsSimpleModule (Matrix (Fin n) (Fin n) K) (colIdeal K k) :=
    isSimpleModule_colIdeal k
  have hiso := IsSimpleRing.isIsotypic (Matrix (Fin n) (Fin n) K)
    (Matrix (Fin n) (Fin n) K)
  obtain ⟨e⟩ := (hiso I) (colIdeal K k)
  rw [← finrank_eq_of_linearEquiv_ideal (K := K) e, finrank_colIdeal, Fintype.card_fin]

end MatrixSimple

/-! ### The bridge: isotypic length = finrank of simple submodule

The proof uses a dimensional argument. Given a Wedderburn decomposition
`e : A ≃ₐ[F] Π Mat_{d_i}(F)`:

1. The isotypic component `c` maps to the `j`-th factor ideal, with
   `length A c = d_j` (from `length_factorIdeal` + `length_matrix_self`).

2. The factor ideal has `finrank F = (d_j)²` (matrix algebra dimension).

3. `c` is isotypic of type `S`, so `c ≃ₗ[A] Fin m → S` where
   `m = length A c = d_j`, giving `finrank F c = d_j · finrank F S`.

4. Since `finrank F c = (d_j)² = d_j · finrank F S` and `d_j ≠ 0`,
   we get `finrank F S = d_j = length A c`. -/

section Bridge

/-- The `F`-dimension of a factor ideal of `Π Mat_{d_i}(F)` is `(d j)²`. -/
theorem finrank_factorIdeal_matrix {F : Type*} [Field F]
    {n : ℕ} {d : Fin n → ℕ} [∀ i, NeZero (d i)] (j : Fin n) :
    Module.finrank F (factorIdeal (fun i => Matrix (Fin (d i)) (Fin (d i)) F) j) =
      d j * d j := by
  haveI : ∀ i, Nonempty (Fin (d i)) := fun i =>
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (d i))⟩⟩
  set A := fun i => Matrix (Fin (d i)) (Fin (d i)) F
  -- Build the linear equivalence with more explicit typing
  have φ : factorIdeal A j ≃ₗ[F] A j :=
  { toFun := fun x => (x : Π i, A i) j
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    invFun := fun M => ⟨Pi.single j M, single_mem_factorIdeal j M⟩
    left_inv := fun x => Subtype.ext
      (eq_single_of_mem_factorIdeal (show (x : Π i, A i) ∈ factorIdeal A j from x.2)).symm
    right_inv := fun M => Pi.single_eq_same j M }
  rw [φ.finrank_eq, Module.finrank_matrix, Module.finrank_self, Fintype.card_fin]
  ring

/-- **Bridge theorem.** In a f.d. semisimple algebra over an alg-closed field,
the isotypic length of a component equals the `F`-dimension of any simple
submodule in it. -/
theorem isotypicLength_eq_finrank_simple
    {F : Type*} [Field F] [IsAlgClosed F]
    {A : Type*} [Ring A] [Algebra F A] [FiniteDimensional F A] [IsSemisimpleRing A]
    (c : ↥(isotypicComponents A A)) (S : Submodule A A)
    [IsSimpleModule A S] (hS : S ≤ c.1) :
    (Module.length A c.1).toNat = Module.finrank F S := by
  -- Extract a Wedderburn decomposition
  obtain ⟨n, d, hd, ⟨e⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed F A
  haveI := hd
  haveI : ∀ i, Nonempty (Fin (d i)) := fun i =>
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (d i))⟩⟩
  haveI : Fintype ↥(isotypicComponents A A) := Fintype.ofFinite _
  haveI : IsSemisimpleRing (Π i, Matrix (Fin (d i)) (Fin (d i)) F) :=
    e.toRingEquiv.isSemisimpleRing
  haveI : Fintype ↥(isotypicComponents
      (Π i, Matrix (Fin (d i)) (Fin (d i)) F)
      (Π i, Matrix (Fin (d i)) (Fin (d i)) F)) := Fintype.ofFinite _
  -- c maps to a factor ideal j
  have hcmap : mapIdeal e.toRingEquiv c.1 ∈ isotypicComponents _ _ :=
    mapIdeal_mem_isotypicComponents e.toRingEquiv c.2
  obtain ⟨j, hj⟩ := eq_factorIdeal_of_mem_isotypicComponents hcmap
  -- Step 1: length A c = d j
  have hlength : (Module.length A c.1).toNat = d j := by
    have h1 := (length_mapIdeal e.toRingEquiv c.1).symm
    rw [h1, hj, length_factorIdeal, length_matrix_self, Fintype.card_fin, ENat.toNat_coe]
  -- Step 2: finrank F c = (d j)²
  have hfr_c : Module.finrank F c.1 = d j * d j := by
    rw [← finrank_mapIdeal e c.1, hj, finrank_factorIdeal_matrix]
  -- Step 3: c is isotypic of type S, so c ≃ₗ[A] Fin m → S
  have hiso_type : IsIsotypicOfType A c.1 S := by
    have h := eq_isotypicComponent_of_le c.2 hS
    rw [h]; exact IsIsotypicOfType.isotypicComponent A A S
  -- The isotypic decomposition gives c ≃ₗ[A] Fin m → S for some m
  haveI : Module.Finite A c.1 := inferInstance
  obtain ⟨m, ⟨φ⟩⟩ := hiso_type.linearEquiv_fun
  -- finrank F c = m * finrank F S
  have hfr_decomp : Module.finrank F c.1 = m * Module.finrank F S := by
    rw [(φ.restrictScalars F).finrank_eq, Module.finrank_pi_fintype, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  -- m = length A c = d j
  have hm : m = d j := by
    have hlen_c : Module.length A c.1 = (m : ℕ∞) := by
      rw [φ.length_eq, Module.length_pi_of_fintype]
      simp [Module.length_eq_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one]
    have := congrArg ENat.toNat hlen_c
    simp [ENat.toNat_coe] at this
    linarith [hlength]
  -- Step 4: (d j)² = (d j) * finrank F S, so finrank F S = d j
  have hpos : 0 < d j := Nat.pos_of_ne_zero (NeZero.ne (d j))
  rw [hlength]
  nlinarith [hfr_c, hfr_decomp, hm]

end Bridge

/-! ### The headline theorem -/

/-- **`charDegrees` equals the multiset of simple-module dimensions.**

`charDegrees G` maps each isotypic component `c` of `ℂ[G]` to
`(Module.length ℂ[G] c).toNat`. By `isotypicLength_eq_finrank_simple`, this
equals `Module.finrank ℂ S` for any simple `ℂ[G]`-submodule `S ≤ c`.

**Packaging decision:** module-side (`IsSimpleModule (MonoidAlgebra ℂ G)`)
rather than `FDRep ℂ G`. -/
theorem charDegrees_eq_simpleModuleDims (G : Type*) [Group G] [Fintype G]
    (c : ↥(isotypicComponents (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)))
    (S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))
    [IsSimpleModule (MonoidAlgebra ℂ G) S] (hS : S ≤ c.1) :
    (Module.length (MonoidAlgebra ℂ G) c.1).toNat = Module.finrank ℂ S := by
  haveI : NeZero (Nat.card G : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  exact isotypicLength_eq_finrank_simple c S hS

end GroupTPP.FDRepBridge
