import BilinearComplexity.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases

set_option autoImplicit false

namespace BilinearComplexity.CyclicLadermanCounterexample

-- Data from Programs/BilinearComplexity/laderman_matrices.sage, reduced modulo two,
-- with the output transposed for cyclic packing, then sandwiched by
-- P = I, Q = swap01, R = I. The third factor below is already cyclically packed.

/-- Explicit u-factor coordinates of the cyclic binary Laderman witness. -/
def u : Fin 23 → Fin (3 * 3) → ZMod 2 :=
  ![![1, 1, 1, 1, 1, 0, 1, 0, 1],
    ![0, 1, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 1, 0, 1, 1, 0, 0, 0, 0],
    ![0, 0, 0, 1, 1, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 1, 1, 0],
    ![0, 1, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 1, 1, 0],
    ![1, 1, 1, 1, 0, 1, 1, 1, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 1, 0, 0, 0, 1, 0, 1],
    ![0, 0, 1, 0, 0, 0, 0, 0, 1],
    ![0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 1],
    ![0, 0, 1, 1, 0, 1, 0, 0, 0],
    ![0, 0, 1, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 1, 0, 1, 0, 0, 0],
    ![1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1]]

example : u 0 0 = 1 := rfl

/-- Explicit v-factor coordinates of the cyclic binary Laderman witness. -/
def v : Fin 23 → Fin (3 * 3) → ZMod 2 :=
  ![![0, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 1, 0, 0, 0, 0],
    ![1, 1, 1, 1, 1, 0, 1, 0, 1],
    ![0, 1, 0, 1, 1, 0, 0, 0, 0],
    ![0, 0, 0, 1, 1, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 1, 1, 0, 1, 0, 0, 0],
    ![0, 0, 1, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 1, 0, 1, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![1, 1, 1, 1, 0, 1, 1, 1, 0],
    ![0, 1, 0, 0, 0, 0, 1, 1, 0],
    ![0, 1, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 1, 0],
    ![0, 0, 1, 0, 0, 0, 1, 0, 1],
    ![0, 0, 1, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1, 0, 1],
    ![1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1]]

example : v 0 0 = 0 := rfl

/-- Explicit w-factor coordinates of the cyclic binary Laderman witness. -/
def w : Fin 23 → Fin (3 * 3) → ZMod 2 :=
  ![![0, 0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 1, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 1, 1, 0, 0, 0, 0],
    ![0, 0, 0, 1, 1, 0, 0, 0, 0],
    ![1, 1, 1, 1, 1, 0, 1, 0, 1],
    ![0, 0, 1, 0, 0, 0, 1, 0, 1],
    ![0, 0, 1, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 1, 0, 1, 0, 0, 0],
    ![0, 0, 1, 0, 0, 1, 0, 0, 0],
    ![1, 1, 1, 1, 0, 1, 1, 1, 0],
    ![0, 0, 0, 1, 0, 1, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 1, 1, 0],
    ![0, 1, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 1, 1, 0],
    ![1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1]]

example : w 0 0 = 0 := rfl

/-- The cyclic permutation of the 23 summands. -/
def cycle : Fin 23 → Fin 23 :=
  ![5, 1, 0, 3, 4, 2, 15, 16, 17, 13, 9, 6, 7, 10, 8, 11, 12, 14, 18, 21, 19, 20, 22]

example : cycle 0 = 5 := rfl

/-- The cyclic action as a permutation, with its square as explicit inverse. -/
def π : Equiv.Perm (Fin 23) where
  toFun := cycle
  invFun := cycle ∘ cycle
  left_inv := by decide
  right_inv := by decide

example : π 0 = 5 := rfl

/-- Row-major unpacking, exactly the archived claim's matrix conversion. -/
def unpack (x : Fin (3 * 3) → ZMod 2) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  fun i j => x (finProdFinEquiv (i, j))

example (x : Fin (3 * 3) → ZMod 2) (i j : Fin 3) :
    unpack x i j = x (finProdFinEquiv (i, j)) := rfl

/-- The permutation has cube equal to the identity. -/
theorem cube_eq_one : π ^ 3 = 1 := by
  apply Equiv.ext
  intro s
  change cycle (cycle (cycle s)) = s
  exact (by decide : ∀ s, cycle (cycle (cycle s)) = s) s

set_option maxHeartbeats 2000000 in
/-- Cyclic rotation of the three factors agrees with the summand permutation. -/
theorem cyclic_symmetry : ∀ s, u (π s) = v s ∧ v (π s) = w s ∧ w (π s) = u s := by
  decide

/-- All 729 entries agree with the actual cyclically packed multiplication tensor. -/
theorem decomposition : matMulTensor (ZMod 2) 3 3 3 =
    fun i j l => ∑ s, u s i * v s j * w s l := by
  funext i j l
  exact (by decide : ∀ i j l, matMulTensor (ZMod 2) 3 3 3 i j l =
    ∑ s, u s i * v s j * w s l) i j l

/-- The fixed summands are precisely the five listed indices. -/
theorem fixed_iff (s : Fin 23) : π s = s ↔
    s = 1 ∨ s = 3 ∨ s = 4 ∨ s = 18 ∨ s = 22 := by
  exact (by decide : ∀ s : Fin 23, π s = s ↔
    s = 1 ∨ s = 3 ∨ s = 4 ∨ s = 18 ∨ s = 22) s

/-- Each fixed first-factor matrix has zero determinant. -/
theorem det_eq_zero_of_fixed (s : Fin 23) (hs : π s = s) :
    (unpack (u s)).det = 0 := by
  rcases (fixed_iff s).mp hs with h | h | h | h | h
  all_goals subst s; rw [Matrix.det_fin_three]; decide

/-- No fixed summand has an invertible first-factor matrix. -/
theorem not_isUnit_of_fixed (s : Fin 23) (hs : π s = s) :
    ¬ IsUnit (unpack (u s)) := by
  intro hunit
  have hdet := (Matrix.isUnit_iff_isUnit_det (unpack (u s))).mp hunit
  rw [det_eq_zero_of_fixed s hs] at hdet
  exact not_isUnit_zero hdet

/-- The exact existential conclusion of the archived p2_c10 fails for this witness. -/
theorem not_archived_conclusion : ¬ ∃ s t, s ≠ t ∧ π s = s ∧ π t = t ∧
    (IsUnit (unpack (u s)) ∨ IsUnit (unpack (u t))) := by
  rintro ⟨s, t, _hne, hs, ht, hunit⟩
  rcases hunit with hu | hu
  · exact not_isUnit_of_fixed s hs hu
  · exact not_isUnit_of_fixed t ht hu

/-- A concrete counterexample to the exact archived p2_c10, without importing it. -/
theorem counterexample :
    ∃ (u v w : Fin 23 → Fin (3 * 3) → ZMod 2) (π : Equiv.Perm (Fin 23)),
      π ^ 3 = 1 ∧
      matMulTensor (ZMod 2) 3 3 3 = (fun i j l => ∑ s, u s i * v s j * w s l) ∧
      (∀ s, u (π s) = v s ∧ v (π s) = w s ∧ w (π s) = u s) ∧
      ¬ (∃ s t, s ≠ t ∧ π s = s ∧ π t = t ∧
        (IsUnit (unpack (u s)) ∨ IsUnit (unpack (u t)))) := by
  exact ⟨u, v, w, π, cube_eq_one, decomposition, cyclic_symmetry,
    not_archived_conclusion⟩

example : (1 : Fin 23) ≠ 3 ∧ π 1 = 1 ∧ π 3 = 3 := by decide

example : π ^ 3 = 1 ∧
    matMulTensor (ZMod 2) 3 3 3 = (fun i j l => ∑ s, u s i * v s j * w s l) ∧
    (∀ s, u (π s) = v s ∧ v (π s) = w s ∧ w (π s) = u s) :=
  ⟨cube_eq_one, decomposition, cyclic_symmetry⟩

example : Nonempty (Fin 23) ∧ Nonempty (Fin (3 * 3)) ∧ Nonempty (Fin 3) :=
  ⟨⟨0⟩, ⟨0⟩, ⟨0⟩⟩

end BilinearComplexity.CyclicLadermanCounterexample
