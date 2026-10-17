import Combinatorics.TreeClusterIrreducibility
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

set_option autoImplicit false

open Polynomial IntermediateField

namespace TreeCluster

/-- A root of the irreducible tree-cluster polynomial has minimal degree exactly `q`. -/
theorem root_minpoly_natDegree {K : Type*} [Field K] [Algebra (RatFunc ℚ) K]
    (q : ℕ) (hq : 2 ≤ q) (v : K)
    (hv : algebraMap (RatFunc ℚ) K RatFunc.X * v ^ q + v -
      algebraMap (RatFunc ℚ) K RatFunc.X = 0) :
    (minpoly (RatFunc ℚ) v).natDegree = q := by
  let p : (RatFunc ℚ)[X] := C RatFunc.X * X ^ q + X - C RatFunc.X
  have hp : Irreducible p := irreducible q hq
  have he : aeval v p = 0 := by simpa [p] using hv
  have hd : p.natDegree = q := by
    have hlead : (C (RatFunc.X : RatFunc ℚ) * X ^ q).natDegree = q := by
      rw [natDegree_C_mul RatFunc.X_ne_zero, natDegree_X_pow]
    have hadd : (C (RatFunc.X : RatFunc ℚ) * X ^ q + X).natDegree = q := by
      rw [natDegree_add_eq_left_of_natDegree_lt, hlead]
      rw [hlead, natDegree_X]
      omega
    change (C (RatFunc.X : RatFunc ℚ) * X ^ q + X - C RatFunc.X).natDegree = q
    rw [natDegree_sub_eq_left_of_natDegree_lt, hadd]
    rw [hadd, natDegree_C]
    omega
  rw [← minpoly.eq_of_irreducible hp he, natDegree_mul_C
    (inv_ne_zero (leadingCoeff_ne_zero.mpr hp.ne_zero))]
  exact hd

/-- The Möbius transform of a tree-cluster root has minimal degree `q` over `ℚ(X)`.
No integrality assumptions on either element are needed. -/
theorem minpoly_natDegree {K : Type*} [Field K] [Algebra (RatFunc ℚ) K]
    (q : ℕ) (hq : 2 ≤ q) (v y : K)
    (hv : algebraMap (RatFunc ℚ) K RatFunc.X * v ^ q + v -
      algebraMap (RatFunc ℚ) K RatFunc.X = 0)
    (hy : (1 + algebraMap (RatFunc ℚ) K RatFunc.X - v) * y =
      algebraMap (RatFunc ℚ) K RatFunc.X) :
    (minpoly (RatFunc ℚ) y).natDegree = q := by
  let x : K := algebraMap (RatFunc ℚ) K RatFunc.X
  have hx : x ≠ 0 := by
    simpa only [map_zero] using
      (algebraMap (RatFunc ℚ) K).injective.ne RatFunc.X_ne_zero
  have hy0 : y ≠ 0 := by
    intro h
    have : x = 0 := by simpa [h, x] using hy.symm
    exact hx this
  have hd0 : 1 + x - v ≠ 0 := by
    intro h
    have : x = 0 := by simpa [x, h] using hy.symm
    exact hx this
  have hyform : y = x / (1 + x - v) := (eq_div_iff hd0).mpr (by simpa [mul_comm, x] using hy)
  have hvform : v = 1 + x - x / y := by
    have hdiv : x / y = 1 + x - v := (div_eq_iff hy0).mpr (by simpa [x] using hy.symm)
    rw [hdiv]
    ring
  have hy_mem : y ∈ (RatFunc ℚ)⟮v⟯ := by
    rw [hyform]
    exact div_mem (IntermediateField.algebraMap_mem _ _) (sub_mem (add_mem (one_mem _) (IntermediateField.algebraMap_mem _ _))
      (mem_adjoin_simple_self _ _))
  have hv_mem : v ∈ (RatFunc ℚ)⟮y⟯ := by
    rw [hvform]
    exact sub_mem (add_mem (one_mem _) (IntermediateField.algebraMap_mem _ _))
      (div_mem (IntermediateField.algebraMap_mem _ _) (mem_adjoin_simple_self _ _))
  have hfields : (RatFunc ℚ)⟮v⟯ = (RatFunc ℚ)⟮y⟯ :=
    le_antisymm (adjoin_simple_le_iff.mpr hv_mem) (adjoin_simple_le_iff.mpr hy_mem)
  have hiv : IsIntegral (RatFunc ℚ) v := by
    apply IsAlgebraic.isIntegral
    exact ⟨C RatFunc.X * X ^ q + X - C RatFunc.X, (irreducible q hq).ne_zero,
      by simpa using hv⟩
  letI := adjoin.finiteDimensional hiv
  have hiy : IsIntegral (RatFunc ℚ) y := by
    exact (IsIntegral.of_finite (RatFunc ℚ) (⟨y, hy_mem⟩ : (RatFunc ℚ)⟮v⟯)).map
      ((RatFunc ℚ)⟮v⟯.val)
  calc
    (minpoly (RatFunc ℚ) y).natDegree = Module.finrank (RatFunc ℚ) (RatFunc ℚ)⟮y⟯ :=
      (adjoin.finrank hiy).symm
    _ = Module.finrank (RatFunc ℚ) (RatFunc ℚ)⟮v⟯ := by rw [hfields]
    _ = (minpoly (RatFunc ℚ) v).natDegree := adjoin.finrank hiv
    _ = q := root_minpoly_natDegree q hq v hv

end TreeCluster
