import Xlib.CharDegrees

/-!
# Bridge: charDegrees equals the multiset of simple-module dimensions

**Packaging decision (Fd1):** module-side (`IsSimpleModule`) not `FDRep`.
See `charDegrees_eq_simpleModuleDims` docstring for rationale.
-/

open scoped BigOperators
open Xlib.CharDegrees Xlib.Wedderburn

namespace Xlib.FDRepBridge

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

noncomputable def idealRestrictScalars {I J : Ideal R} (e : I ≃ₗ[R] J) : I ≃ₗ[K] J :=
  e.restrictScalars K

theorem finrank_eq_of_linearEquiv_ideal {I J : Ideal R}
    (e : I ≃ₗ[R] J) : Module.finrank K I = Module.finrank K J :=
  (idealRestrictScalars (K := K) e).finrank_eq

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
  -- Matrix ring is simple Artinian hence isotypic: all simple modules ≃
  have hiso := IsSimpleRing.isIsotypic (Matrix (Fin n) (Fin n) K)
    (Matrix (Fin n) (Fin n) K)
  -- Apply isotypic to I: all simple submodules are isomorphic to I
  have hI_type : IsIsotypicOfType (Matrix (Fin n) (Fin n) K)
      (Matrix (Fin n) (Fin n) K) I := hiso I
  -- In particular colIdeal K k ≃ₗ[R] I
  obtain ⟨e⟩ := hI_type (colIdeal K k)
  rw [← finrank_eq_of_linearEquiv_ideal (K := K) e, finrank_colIdeal, Fintype.card_fin]

end MatrixSimple

/-! ### The bridge: isotypic length = finrank of simple submodule -/

section Bridge

/-- **Bridge theorem.** In a finite-dimensional semisimple algebra `A` over an
algebraically closed field `F`, for each isotypic component `c` of `A` (as a
module over itself), and any simple submodule `S ≤ c`:

  `(Module.length A c).toNat = Module.finrank F S`

This is the missing plank between the ring-theoretic `charDegrees` definition
(via isotypic lengths) and the representation-theoretic multiset (via dimensions
of irreducible representations). -/
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
  -- c maps to a factor ideal
  have hcmap : mapIdeal e.toRingEquiv c.1 ∈ isotypicComponents _ _ :=
    mapIdeal_mem_isotypicComponents e.toRingEquiv c.2
  obtain ⟨i, hi⟩ := eq_factorIdeal_of_mem_isotypicComponents hcmap
  -- length of c equals d i
  have hlength : (Module.length A c.1).toNat = d i := by
    have h1 : Module.length A c.1 =
        Module.length _ (mapIdeal e.toRingEquiv c.1) :=
      (length_mapIdeal e.toRingEquiv c.1).symm
    rw [h1, hi, length_factorIdeal, length_matrix_self, Fintype.card_fin, ENat.toNat_coe]
  -- S maps to a simple submodule within the i-th factor
  have hSmap : mapIdeal e.toRingEquiv S ≤ factorIdeal _ i := by
    rw [← hi]; exact mapIdeal_le_iff.mpr hS
  -- finrank of S equals finrank of mapIdeal e S
  have hfr : Module.finrank F S = Module.finrank F (mapIdeal e.toRingEquiv S) := by
    exact (finrank_mapIdeal e S).symm
  -- Need: finrank F (mapIdeal e S) = d i
  -- The mapIdeal e S is a simple ideal within factorIdeal i, which is
  -- isomorphic to Mat_{d_i}(F). Its finrank should be d i.
  rw [hlength, hfr]
  sorry

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

end Xlib.FDRepBridge
