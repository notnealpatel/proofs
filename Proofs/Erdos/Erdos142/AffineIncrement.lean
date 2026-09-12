/-
  Erdős Problem #142 — conditional affine density increment.

  A large balanced correlation with an additive complex character, together
  with a supplied positive step on which the character is nearly constant,
  yields a density increment on a genuine finite affine progression. The
  theorem also returns the affine pullback and transports three-AP-freeness.

  This is a conditional reduction: it does not select the step or establish
  the correlation, and it makes no asymptotic claim about Roth's theorem.
-/

import Erdos.Erdos142.CorrelationIncrement
import Erdos.Erdos142.PhasePartition
import Mathlib.Combinatorics.Additive.AP.Three.Defs

set_option autoImplicit false

open scoped BigOperators

namespace Erdos142

/-- A balanced correlation with a unit-norm additive character that is almost
fixed by a supplied positive step yields a density increment on an explicit
positive-step affine progression. The returned pullback has the same number
of selected points and inherits three-AP-freeness from the ambient set. -/
theorem exists_affine_density_increment_of_correlation
    (A : Finset ℕ) (N d K : ℕ) (χ : ℕ → ℂ) (δ η : ℝ)
    (hAU : A ⊆ Finset.range N) (hd : 0 < d) (hK : 0 < K)
    (hdK : d * K ≤ N) (hadd : ∀ m n, χ (m + n) = χ m * χ n)
    (hnorm : ∀ n, ‖χ n‖ = 1) (hδ : 0 ≤ δ)
    (hphase : ‖χ d - 1‖ ≤ δ) (hη : 0 < η)
    (hhalf : ((2 * K : ℕ) : ℝ) * δ ≤ η / 2)
    (hcorr : η * (N : ℝ) ≤
      ‖∑ x ∈ Finset.range N,
        (balancedIndicator (Finset.range N) A x : ℂ) * χ x‖) :
    ∃ a m : ℕ, ∃ P B : Finset ℕ,
      P = (Finset.range m).image (fun i => a + d * i) ∧
      B = (Finset.range m).filter (fun i => a + d * i ∈ A) ∧
      P ⊆ Finset.range N ∧ B ⊆ Finset.range m ∧
      K ≤ m ∧ m < 2 * K ∧ P.card = m ∧
      (A.card : ℝ) / N + η / 4 ≤ ((A ∩ P).card : ℝ) / P.card ∧
      B.card = (A ∩ P).card ∧
      (ThreeAPFree (A : Set ℕ) → ThreeAPFree (B : Set ℕ)) := by
  classical
  let J := phasePartition N d K
  have hcell : ∀ C ∈ J, C.Nonempty := by
    intro C hC
    obtain ⟨r, hr, j, hj, hform, hbounds⟩ :=
      phasePartition_cell_structure hd hK hdK hC
    exact Finset.card_pos.mp (lt_of_lt_of_le hK hbounds.1)
  let ζ : Finset ℕ → ℂ := fun C =>
    if hC : C.Nonempty then χ (C.min' hC) else 0
  have hζ : ∀ C ∈ J, ‖ζ C‖ ≤ 1 := by
    intro C hC
    rw [show ζ C = χ (C.min' (hcell C hC)) by simp [ζ, hcell C hC]]
    rw [hnorm]
  have happrox : ∀ C ∈ J, ∀ x ∈ C,
      ‖χ x - ζ C‖ ≤ ((2 * K : ℕ) : ℝ) * δ := by
    intro C hC x hx
    rw [show ζ C = χ (C.min' (hcell C hC)) by simp [ζ, hcell C hC]]
    exact norm_sub_le_of_mem_phasePartition_additiveCharacter χ hd hK hδ hdK
      hadd hnorm hphase hC hx (C.min'_mem (hcell C hC))
  have hsize : ∀ C ∈ J, K ≤ C.card := by
    intro C hC
    obtain ⟨r, hr, j, hj, hform, hbounds⟩ :=
      phasePartition_cell_structure hd hK hdK hC
    exact hbounds.1
  have hdisjoint : (↑J : Set (Finset ℕ)).PairwiseDisjoint id := by
    intro C hCJ D hDJ hCD
    exact phasePartition_pairwiseDisjoint hd hCJ hDJ hCD
  obtain ⟨P, hPJ, hPne, hKP, hinc⟩ :=
    exists_density_increment_quarter_of_correlation
      (Finset.range N) A J id χ ζ K (((2 * K : ℕ) : ℝ) * δ) η
      (⟨0, Finset.mem_range.mpr (by nlinarith)⟩) hAU hcell hsize hdisjoint
      (by simpa only [J] using biUnion_phasePartition hd hK hdK)
      hζ happrox (mul_nonneg (by positivity) hδ) hη hhalf (by simpa using hcorr)
  obtain ⟨r, hr, j, hj, hPform0, hbounds⟩ :=
    phasePartition_cell_structure hd hK hdK hPJ
  let m := mergedBlockLength (residueLength N d r) K j
  let a := r + d * (j * K)
  have hPform : P = (Finset.range m).image (fun i => a + d * i) := by
    rw [hPform0]
    congr 1
    funext i
    dsimp only [a, m]
    ring
  have hcardP : P.card = m := by
    rw [hPform, Finset.card_image_of_injective]
    · exact Finset.card_range m
    · intro x y hxy
      have hmul : d * x = d * y := Nat.add_left_cancel hxy
      exact Nat.mul_left_cancel hd hmul
  let B := (Finset.range m).filter (fun i => a + d * i ∈ A)
  have hBsub : B ⊆ Finset.range m := by
    intro i hi
    exact (Finset.mem_filter.mp hi).1
  have hPsub : P ⊆ Finset.range N := by
    intro x hx
    rw [← biUnion_phasePartition hd hK hdK]
    exact Finset.mem_biUnion.mpr ⟨P, hPJ, hx⟩
  have himage : B.image (fun i => a + d * i) = A ∩ P := by
    ext x
    simp only [Finset.mem_image, Finset.mem_inter]
    constructor
    · rintro ⟨i, hiB, rfl⟩
      have hi := Finset.mem_filter.mp hiB
      exact ⟨hi.2, by rw [hPform]; exact Finset.mem_image.mpr ⟨i, hi.1, rfl⟩⟩
    · rintro ⟨hxA, hxP⟩
      rw [hPform] at hxP
      obtain ⟨i, him, rfl⟩ := Finset.mem_image.mp hxP
      exact ⟨i, Finset.mem_filter.mpr ⟨him, hxA⟩, rfl⟩
  have hcardB : B.card = (A ∩ P).card := by
    rw [← himage, Finset.card_image_of_injective]
    intro x y hxy
    have hmul : d * x = d * y := Nat.add_left_cancel hxy
    exact Nat.mul_left_cancel hd hmul
  have hfreeB : ThreeAPFree (A : Set ℕ) → ThreeAPFree (B : Set ℕ) := by
    intro hfree x hxB y hyB z hzB hxyz
    have hxA : a + d * x ∈ A := (Finset.mem_filter.mp hxB).2
    have hyA : a + d * y ∈ A := (Finset.mem_filter.mp hyB).2
    have hzA : a + d * z ∈ A := (Finset.mem_filter.mp hzB).2
    have haffine : (a + d * x) + (a + d * z) =
        (a + d * y) + (a + d * y) := by
      calc
        (a + d * x) + (a + d * z) = 2 * a + d * (x + z) := by ring
        _ = 2 * a + d * (y + y) := by rw [hxyz]
        _ = (a + d * y) + (a + d * y) := by ring
    have hxy := hfree hxA hyA hzA haffine
    have hmul : d * x = d * y := Nat.add_left_cancel hxy
    exact Nat.mul_left_cancel hd hmul
  refine ⟨a, m, P, B, hPform, rfl, hPsub, hBsub, ?_, ?_, hcardP, ?_,
    hcardB, hfreeB⟩
  · rw [← hcardP]
    exact hbounds.1
  · rw [← hcardP]
    exact hbounds.2
  · simpa only [Finset.card_range, id_eq] using hinc

/-- Joint satisfiability check with `K = 2`: parity is a nonconstant unit
character and the even points have balanced correlation exactly `N / 2`. -/
example :
    let A : Finset ℕ := {0, 2}
    let χ : ℕ → ℂ := fun n => (-1 : ℂ) ^ n
    A ⊆ Finset.range 4 ∧ 0 < 2 ∧ 0 < 2 ∧ 2 * 2 ≤ 4 ∧
      (∀ m n, χ (m + n) = χ m * χ n) ∧
      (∀ n, ‖χ n‖ = 1) ∧ 0 ≤ (0 : ℝ) ∧
      ‖χ 2 - 1‖ ≤ (0 : ℝ) ∧ 0 < (1 / 2 : ℝ) ∧
      (((2 * 2 : ℕ) : ℝ) * 0 ≤ (1 / 2 : ℝ) / 2) ∧
      (1 / 2 : ℝ) * 4 ≤
        ‖∑ x ∈ Finset.range 4,
          (balancedIndicator (Finset.range 4) A x : ℂ) * χ x‖ := by
  dsimp only
  refine ⟨by decide, by norm_num, by norm_num, by norm_num, ?_, ?_, by norm_num,
    by norm_num, by norm_num, by norm_num, ?_⟩
  · intro m n
    exact pow_add (-1 : ℂ) m n
  · intro n
    rw [norm_pow]
    norm_num
  · norm_num [Finset.sum_range_succ, balancedIndicator, Complex.norm_real,
      Real.norm_eq_abs]

#check @exists_affine_density_increment_of_correlation
#print axioms exists_affine_density_increment_of_correlation

end Erdos142
