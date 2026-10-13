import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace BilinearComplexity

open scoped Matrix

private theorem right_kernel {K : Type*} [Field K]
    (M : Matrix (Fin 3) (Fin 3) K) (hM : ¬ IsUnit M) :
    ∃ x : Fin 3 → K, x ≠ 0 ∧ M *ᵥ x = 0 := by
  have hn : ¬ Function.Injective M.mulVec :=
    fun h => hM (Matrix.mulVec_injective_iff_isUnit.mp h)
  obtain ⟨x, y, hxy, hne⟩ := Function.not_injective_iff.mp hn
  exact ⟨x - y, sub_ne_zero.mpr hne, by rw [Matrix.mulVec_sub, hxy, sub_self]⟩

private theorem left_kernel {K : Type*} [Field K]
    (M : Matrix (Fin 3) (Fin 3) K) (hM : ¬ IsUnit M) :
    ∃ x : Fin 3 → K, x ≠ 0 ∧ x ᵥ* M = 0 := by
  obtain ⟨x, hx, hMx⟩ := right_kernel M.transpose (by simpa using hM)
  exact ⟨x, hx, by simpa only [Matrix.mulVec_transpose] using hMx⟩

private theorem outer_nonscalar {K : Type*} [Field K]
    (x y : Fin 3 → K) (hx : x ≠ 0) (hy : y ≠ 0) :
    ¬ ∃ a : K, Matrix.vecMulVec x y = a • (1 : Matrix (Fin 3) (Fin 3) K) := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    apply hx
    ext i
    simpa using not_exists.mp h i
  obtain ⟨j, hj⟩ : ∃ j, y j ≠ 0 := by
    by_contra h
    apply hy
    ext j
    simpa using not_exists.mp h j
  rintro ⟨a, ha⟩
  have ha0 : a ≠ 0 := by
    intro hz
    have hij := congrArg (fun M => M i j) ha
    simp only [Matrix.vecMulVec_apply, hz, zero_smul, Matrix.zero_apply] at hij
    exact mul_ne_zero hi hj hij
  have h00 := congrArg (fun M => M 0 0) ha
  have h11 := congrArg (fun M => M 1 1) ha
  have h01 := congrArg (fun M => M 0 1) ha
  have h10 := congrArg (fun M => M 1 0) ha
  simp only [Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, ite_true, mul_one] at h00 h11
  simp only [Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, show (0 : Fin 3) ≠ 1 by decide, show (1 : Fin 3) ≠ 0 by decide,
    ite_false, mul_zero] at h01 h10
  have heq : (x 0 * y 0) * (x 1 * y 1) = (x 0 * y 1) * (x 1 * y 0) := by ring
  rw [h00, h11, h01, h10, mul_zero] at heq
  exact mul_ne_zero ha0 ha0 heq

private theorem singular_pair {K : Type*} [Field K]
    (U V W : Matrix (Fin 3) (Fin 3) K) (hU : ¬ IsUnit U) (hW : ¬ IsUnit W) :
    ∃ A B C : Matrix (Fin 3) (Fin 3) K,
      A * U = U * B ∧ B * V = V * C ∧ C * W = W * A ∧
      ¬ (∃ a b c : K, A = a • 1 ∧ B = b • 1 ∧ C = c • 1) := by
  obtain ⟨x, hx, hWx⟩ := right_kernel W hW
  obtain ⟨y, hy, hyU⟩ := left_kernel U hU
  refine ⟨Matrix.vecMulVec x y, 0, 0, ?_, by simp, ?_, ?_⟩
  · simp [Matrix.vecMulVec_mul, hyU]
  · simp [Matrix.mul_vecMulVec, hWx]
  · rintro ⟨a, b, c, ha, hb, hc⟩
    exact outer_nonscalar x y hx hy ⟨a, ha⟩

private theorem commuting_nonscalar {K : Type*} [Field K]
    (D : Matrix (Fin 3) (Fin 3) K) :
    ∃ A : Matrix (Fin 3) (Fin 3) K,
      A * D = D * A ∧ ¬ ∃ a : K, A = a • 1 := by
  by_cases hD : ∃ d : K, D = d • 1
  · obtain ⟨d, hd⟩ := hD
    let E : Matrix (Fin 3) (Fin 3) K := Matrix.vecMulVec (Pi.single 0 1) (Pi.single 1 1)
    refine ⟨E, ?_, ?_⟩
    · rw [hd, Matrix.mul_smul, Matrix.smul_mul, mul_one, one_mul]
    · apply outer_nonscalar
      · intro h
        have hh := congrFun h 0
        simp at hh
      · intro h
        have hh := congrFun h 1
        simp at hh
  · exact ⟨D, rfl, hD⟩

private theorem invertible_pair {K : Type*} [Field K]
    (U V W : Matrix (Fin 3) (Fin 3) K) (hV : IsUnit V) (hW : IsUnit W) :
    ∃ A B C : Matrix (Fin 3) (Fin 3) K,
      A * U = U * B ∧ B * V = V * C ∧ C * W = W * A ∧
      ¬ (∃ a b c : K, A = a • 1 ∧ B = b • 1 ∧ C = c • 1) := by
  have hVi : V⁻¹ * V = 1 := Matrix.nonsing_inv_mul V ((Matrix.isUnit_iff_isUnit_det V).mp hV)
  have hWi : W⁻¹ * W = 1 := Matrix.nonsing_inv_mul W ((Matrix.isUnit_iff_isUnit_det W).mp hW)
  have hVr : V * V⁻¹ = 1 := Matrix.mul_nonsing_inv V ((Matrix.isUnit_iff_isUnit_det V).mp hV)
  have hWr : W * W⁻¹ = 1 := Matrix.mul_nonsing_inv W ((Matrix.isUnit_iff_isUnit_det W).mp hW)
  obtain ⟨A, hAD, hA⟩ := commuting_nonscalar (U * V * W)
  let C := W * A * W⁻¹
  let B := V * C * V⁻¹
  have hCW : C * W = W * A := by simp only [C, mul_assoc, hWi, mul_one]
  have hBV : B * V = V * C := by simp only [B, mul_assoc, hVi, mul_one]
  refine ⟨A, B, C, ?_, hBV, hCW, ?_⟩
  · have heq : (A * U) * (V * W) = (U * B) * (V * W) := by
      calc
        (A * U) * (V * W) = A * (U * V * W) := by simp only [mul_assoc]
        _ = (U * V * W) * A := hAD
        _ = (U * B) * (V * W) := by
          rw [mul_assoc U B, ← mul_assoc B V, hBV, mul_assoc V C, hCW]
          simp only [mul_assoc]
    have hc := congrArg (fun M => M * (W⁻¹ * V⁻¹)) heq
    have hinv : (V * W) * (W⁻¹ * V⁻¹) = 1 := by
      calc
        (V * W) * (W⁻¹ * V⁻¹) = V * (W * W⁻¹) * V⁻¹ := by simp only [mul_assoc]
        _ = 1 := by rw [hWr, mul_one, hVr]
    calc
      A * U = ((A * U) * (V * W)) * (W⁻¹ * V⁻¹) := by
        rw [mul_assoc (A * U) (V * W), hinv, mul_one]
      _ = ((U * B) * (V * W)) * (W⁻¹ * V⁻¹) := hc
      _ = U * B := by rw [mul_assoc (U * B) (V * W), hinv, mul_one]
  · rintro ⟨a, b, c, ha, hb, hc⟩
    exact hA ⟨a, ha⟩

private theorem rotate {K : Type*} [Field K]
    (U V W : Matrix (Fin 3) (Fin 3) K)
    (h : ∃ A B C : Matrix (Fin 3) (Fin 3) K,
      A * V = V * B ∧ B * W = W * C ∧ C * U = U * A ∧
      ¬ (∃ a b c : K, A = a • 1 ∧ B = b • 1 ∧ C = c • 1)) :
    ∃ A B C : Matrix (Fin 3) (Fin 3) K,
      A * U = U * B ∧ B * V = V * C ∧ C * W = W * A ∧
      ¬ (∃ a b c : K, A = a • 1 ∧ B = b • 1 ∧ C = c • 1) := by
  obtain ⟨A, B, C, hAV, hBW, hCU, hn⟩ := h
  refine ⟨C, A, B, hCU, hAV, hBW, ?_⟩
  rintro ⟨c, a, b, hc, ha, hb⟩
  exact hn ⟨a, b, c, ha, hb, hc⟩

/-- Every cyclic triple of three-by-three matrices over a field has intertwiners
that are not all scalar matrices. No invertibility assumptions are required. -/
theorem exists_nonscalar_cyclic_intertwiners_field {K : Type*} [Field K]
    (U V W : Matrix (Fin 3) (Fin 3) K) :
    ∃ A B C : Matrix (Fin 3) (Fin 3) K,
      A * U = U * B ∧ B * V = V * C ∧ C * W = W * A ∧
      ¬ (∃ a b c : K, A = a • 1 ∧ B = b • 1 ∧ C = c • 1) := by
  by_cases hU : IsUnit U <;> by_cases hV : IsUnit V <;> by_cases hW : IsUnit W
  all_goals first
    | exact invertible_pair U V W hV hW
    | exact rotate U V W (invertible_pair V W U hW hU)
    | exact rotate U V W (rotate V W U (invertible_pair W U V hU hV))
    | exact singular_pair U V W hU hW
    | exact rotate U V W (singular_pair V W U hV hU)
    | exact rotate U V W (rotate V W U (singular_pair W U V hW hV))

/-- Every cyclic triple of three-by-three binary matrices admits cyclic
intertwiners that are not simultaneously scalar. This includes zero matrices. -/
theorem exists_nonscalar_cyclic_intertwiners
    (U V W : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    ∃ A B C : Matrix (Fin 3) (Fin 3) (ZMod 2),
      A * U = U * B ∧ B * V = V * C ∧ C * W = W * A ∧
      ¬ (∃ a b c : ZMod 2, A = a • 1 ∧ B = b • 1 ∧ C = c • 1) :=
  exists_nonscalar_cyclic_intertwiners_field U V W

example : Nonempty (Fin 3) := ⟨0⟩

example : ∃ A B C : Matrix (Fin 3) (Fin 3) (ZMod 2),
    A * 0 = 0 * B ∧ B * 0 = 0 * C ∧ C * 0 = 0 * A ∧
    ¬ (∃ a b c : ZMod 2, A = a • 1 ∧ B = b • 1 ∧ C = c • 1) :=
  exists_nonscalar_cyclic_intertwiners 0 0 0

example : ∃ A B C : Matrix (Fin 3) (Fin 3) (ZMod 2),
    A * 1 = 1 * B ∧ B * 1 = 1 * C ∧ C * 1 = 1 * A ∧
    ¬ (∃ a b c : ZMod 2, A = a • 1 ∧ B = b • 1 ∧ C = c • 1) :=
  exists_nonscalar_cyclic_intertwiners 1 1 1

end BilinearComplexity
