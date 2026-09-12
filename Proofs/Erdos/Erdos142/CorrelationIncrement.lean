/-
  Erdos142/CorrelationIncrement — a finite deterministic density increment.

  A large correlation of a balanced indicator with a character that is
  nearly constant on the cells of a finite partition forces increased
  density on one cell. The reduction is conditional: it constructs neither
  the correlation nor the partition.
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace Erdos142

/-- The balanced indicator of `A` relative to `U`. -/
noncomputable def balancedIndicator {α : Type*} [DecidableEq α]
    (U A : Finset α) (x : α) : ℝ :=
  (if x ∈ A then 1 else 0) - (A.card : ℝ) / U.card

example : balancedIndicator ({0, 1} : Finset ℕ) {0} 0 = 1 / 2 := by
  norm_num [balancedIndicator]

example : balancedIndicator (∅ : Finset ℕ) ∅ 4 = 0 := by
  norm_num [balancedIndicator]

/-- The balanced indicator sums to zero on its nonempty ambient set. -/
theorem sum_balancedIndicator_eq_zero {α : Type*} [DecidableEq α]
    (U A : Finset α) (hU : U.Nonempty) (hAU : A ⊆ U) :
    ∑ x ∈ U, balancedIndicator U A x = 0 := by
  have hfilter : U.filter (fun x => x ∈ A) = A := by
    ext x
    simp only [Finset.mem_filter]
    constructor
    · exact fun hx => hx.2
    · exact fun hx => ⟨hAU hx, hx⟩
  have hcard_pos : (0 : ℝ) < U.card := by
    exact_mod_cast Finset.card_pos.mpr hU
  simp only [balancedIndicator, Finset.sum_sub_distrib, Finset.sum_boole,
    hfilter, Finset.sum_const, nsmul_eq_mul]
  field_simp
  ring

/-- The `L¹` mass of a balanced indicator is at most the size of its ambient
set. -/
theorem sum_abs_balancedIndicator_le_card {α : Type*} [DecidableEq α]
    (U A : Finset α) (hU : U.Nonempty) (hAU : A ⊆ U) :
    (∑ x ∈ U, |balancedIndicator U A x|) ≤ (U.card : ℝ) := by
  let d : ℝ := (A.card : ℝ) / U.card
  have hcard_pos : (0 : ℝ) < U.card := by
    exact_mod_cast Finset.card_pos.mpr hU
  have hcard_le : (A.card : ℝ) ≤ U.card := by
    exact_mod_cast Finset.card_le_card hAU
  have hd0 : 0 ≤ d := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hd1 : d ≤ 1 := (div_le_one₀ hcard_pos).mpr hcard_le
  calc
    (∑ x ∈ U, |balancedIndicator U A x|) ≤ ∑ _x ∈ U, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      by_cases hxA : x ∈ A
      · rw [balancedIndicator, if_pos hxA]
        dsimp only [d] at hd0 hd1 ⊢
        rw [abs_of_nonneg (sub_nonneg.mpr hd1)]
        linarith
      · rw [balancedIndicator, if_neg hxA, zero_sub]
        dsimp only [d] at hd0 hd1 ⊢
        rw [abs_neg, abs_of_nonneg hd0]
        exact hd1
    _ = (U.card : ℝ) := by simp

/-- A zero-sum real function with large `L¹` mass across positive finite
weights has a cell on which its value dominates the corresponding weight. -/
theorem exists_large_of_sum_eq_zero {ι : Type*} [DecidableEq ι]
    (J : Finset ι) (w g : ι → ℝ) (δ : ℝ)
    (hJ : J.Nonempty) (hw : ∀ j ∈ J, 0 < w j) (hδ : 0 < δ)
    (hzero : ∑ j ∈ J, g j = 0)
    (hmass : 2 * δ * (∑ j ∈ J, w j) ≤ ∑ j ∈ J, |g j|) :
    ∃ j ∈ J, δ * w j ≤ g j := by
  by_contra hnot
  simp only [not_exists, not_and, not_le] at hnot
  have hmaxlt : ∀ j ∈ J, max (g j) 0 < δ * w j := by
    intro j hj
    rw [max_lt_iff]
    exact ⟨hnot j hj, mul_pos hδ (hw j hj)⟩
  have hsumlt : (∑ j ∈ J, max (g j) 0) < ∑ j ∈ J, δ * w j := by
    apply Finset.sum_lt_sum
    · intro j hj
      exact (hmaxlt j hj).le
    · obtain ⟨j, hj⟩ := hJ
      exact ⟨j, hj, hmaxlt j hj⟩
  have habs_point : ∀ j ∈ J, |g j| = 2 * max (g j) 0 - g j := by
    intro j hj
    by_cases hg : 0 ≤ g j
    · rw [abs_of_nonneg hg, max_eq_left hg]
      ring
    · have hg' : g j ≤ 0 := le_of_not_ge hg
      rw [abs_of_nonpos hg', max_eq_right hg']
      ring
  have habs_eq : (∑ j ∈ J, |g j|) = 2 * ∑ j ∈ J, max (g j) 0 := by
    calc
      (∑ j ∈ J, |g j|) = ∑ j ∈ J, (2 * max (g j) 0 - g j) :=
        Finset.sum_congr rfl habs_point
      _ = (∑ j ∈ J, 2 * max (g j) 0) - ∑ j ∈ J, g j :=
        Finset.sum_sub_distrib _ _
      _ = 2 * ∑ j ∈ J, max (g j) 0 := by rw [hzero, sub_zero, Finset.mul_sum]
  have hscaled : 2 * (∑ j ∈ J, max (g j) 0) <
      2 * (∑ j ∈ J, δ * w j) := mul_lt_mul_of_pos_left hsumlt (by norm_num)
  have hstrict : (∑ j ∈ J, |g j|) < 2 * δ * (∑ j ∈ J, w j) := by
    rw [habs_eq]
    calc
      2 * (∑ j ∈ J, max (g j) 0) < 2 * (∑ j ∈ J, δ * w j) := hscaled
      _ = 2 * δ * (∑ j ∈ J, w j) := by rw [← Finset.mul_sum]; ring
  exact (not_lt_of_ge hmass) hstrict

/-- An explicit bound on the summed phase-approximation error converts a
large complex correlation of a zero-sum real function into a positive cell
sum. -/
theorem exists_cell_sum_ge_of_correlation_with_error
    {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (U : Finset α) (J : Finset ι) (C : ι → Finset α)
    (f : α → ℝ) (χ : α → ℂ) (ζ : ι → ℂ) (ε η E : ℝ)
    (hU : U.Nonempty) (hC : ∀ j ∈ J, (C j).Nonempty)
    (hdisjoint : (↑J : Set ι).PairwiseDisjoint C)
    (hcover : J.biUnion C = U)
    (hzero : ∑ x ∈ U, f x = 0)
    (hζ : ∀ j ∈ J, ‖ζ j‖ ≤ 1)
    (herror : (∑ j ∈ J, ∑ x ∈ C j, |f x| * ‖χ x - ζ j‖) ≤ E)
    (hE : E ≤ ε * (U.card : ℝ)) (hgap : ε < η)
    (hcorr : η * (U.card : ℝ) ≤
      ‖∑ x ∈ U, (f x : ℂ) * χ x‖) :
    ∃ j ∈ J, ((η - ε) / 2) * (C j).card ≤ ∑ x ∈ C j, f x := by
  let s : ι → ℝ := fun j => ∑ x ∈ C j, f x
  have hJ : J.Nonempty := by
    obtain ⟨x, hxU⟩ := hU
    have hx : x ∈ J.biUnion C := by rwa [hcover]
    simp only [Finset.mem_biUnion] at hx
    obtain ⟨j, hj, hxC⟩ := hx
    exact ⟨j, hj⟩
  have hzero_cells : ∑ j ∈ J, s j = 0 := by
    have hpartition := Finset.sum_biUnion (M := ℝ) (f := f) hdisjoint
    rw [hcover] at hpartition
    exact hpartition.symm.trans hzero
  have hcards : (∑ j ∈ J, ((C j).card : ℝ)) = (U.card : ℝ) := by
    have hpartition := Finset.sum_biUnion (M := ℝ) (f := fun _ : α => 1) hdisjoint
    rw [hcover] at hpartition
    simpa using hpartition.symm
  have hdecomp :
      (∑ x ∈ U, (f x : ℂ) * χ x) =
        (∑ j ∈ J, (s j : ℂ) * ζ j) +
          ∑ j ∈ J, ∑ x ∈ C j, (f x : ℂ) * (χ x - ζ j) := by
    rw [← hcover, Finset.sum_biUnion hdisjoint]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    calc
      (∑ x ∈ C j, (f x : ℂ) * χ x) =
          ∑ x ∈ C j, ((f x : ℂ) * ζ j + (f x : ℂ) * (χ x - ζ j)) := by
        apply Finset.sum_congr rfl
        intro x hx
        ring
      _ = (∑ x ∈ C j, (f x : ℂ) * ζ j) +
          ∑ x ∈ C j, (f x : ℂ) * (χ x - ζ j) :=
        Finset.sum_add_distrib
      _ = (s j : ℂ) * ζ j +
          ∑ x ∈ C j, (f x : ℂ) * (χ x - ζ j) := by
        congr 1
        rw [← Finset.sum_mul]
        simp only [s, Complex.ofReal_sum]
  have herrnorm :
      ‖∑ j ∈ J, ∑ x ∈ C j, (f x : ℂ) * (χ x - ζ j)‖ ≤ E := by
    calc
      ‖∑ j ∈ J, ∑ x ∈ C j, (f x : ℂ) * (χ x - ζ j)‖ ≤
          ∑ j ∈ J, ‖∑ x ∈ C j, (f x : ℂ) * (χ x - ζ j)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ j ∈ J, ∑ x ∈ C j, ‖(f x : ℂ) * (χ x - ζ j)‖ := by
        apply Finset.sum_le_sum
        intro j hj
        exact norm_sum_le _ _
      _ = ∑ j ∈ J, ∑ x ∈ C j, |f x| * ‖χ x - ζ j‖ := by
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro x hx
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ E := herror
  have hcenternorm : ‖∑ j ∈ J, (s j : ℂ) * ζ j‖ ≤ ∑ j ∈ J, |s j| := by
    calc
      ‖∑ j ∈ J, (s j : ℂ) * ζ j‖ ≤ ∑ j ∈ J, ‖(s j : ℂ) * ζ j‖ :=
        norm_sum_le _ _
      _ ≤ ∑ j ∈ J, |s j| := by
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_of_le_one_right (abs_nonneg (s j)) (hζ j hj)
  have hmass : (η - ε) * (U.card : ℝ) ≤ ∑ j ∈ J, |s j| := by
    have htriangle : ‖∑ x ∈ U, (f x : ℂ) * χ x‖ ≤
        ‖∑ j ∈ J, (s j : ℂ) * ζ j‖ +
          ‖∑ j ∈ J, ∑ x ∈ C j, (f x : ℂ) * (χ x - ζ j)‖ := by
      rw [hdecomp]
      exact norm_add_le _ _
    have htotal : η * (U.card : ℝ) ≤ (∑ j ∈ J, |s j|) + E :=
      hcorr.trans (htriangle.trans (add_le_add hcenternorm herrnorm))
    have hcard_nonneg : (0 : ℝ) ≤ U.card := Nat.cast_nonneg _
    linarith
  apply exists_large_of_sum_eq_zero J (fun j => ((C j).card : ℝ)) s
      ((η - ε) / 2) hJ
  · intro j hj
    exact_mod_cast Finset.card_pos.mpr (hC j hj)
  · linarith
  · exact hzero_cells
  · rw [hcards]
    convert hmass using 1
    ring

/-- Pointwise phase approximation and an `L¹` bound imply the explicit phase
error estimate needed for the finite correlation reduction. -/
theorem exists_cell_sum_ge_of_correlation
    {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (U : Finset α) (J : Finset ι) (C : ι → Finset α)
    (f : α → ℝ) (χ : α → ℂ) (ζ : ι → ℂ) (ε η : ℝ)
    (hU : U.Nonempty) (hC : ∀ j ∈ J, (C j).Nonempty)
    (hdisjoint : (↑J : Set ι).PairwiseDisjoint C)
    (hcover : J.biUnion C = U)
    (hzero : ∑ x ∈ U, f x = 0)
    (hLone : (∑ x ∈ U, |f x|) ≤ (U.card : ℝ))
    (hζ : ∀ j ∈ J, ‖ζ j‖ ≤ 1)
    (happrox : ∀ j ∈ J, ∀ x ∈ C j, ‖χ x - ζ j‖ ≤ ε)
    (hε : 0 ≤ ε) (hgap : ε < η)
    (hcorr : η * (U.card : ℝ) ≤
      ‖∑ x ∈ U, (f x : ℂ) * χ x‖) :
    ∃ j ∈ J, ((η - ε) / 2) * (C j).card ≤ ∑ x ∈ C j, f x := by
  apply exists_cell_sum_ge_of_correlation_with_error U J C f χ ζ ε η
      (ε * (U.card : ℝ)) hU hC hdisjoint hcover hzero hζ
  · calc
      (∑ j ∈ J, ∑ x ∈ C j, |f x| * ‖χ x - ζ j‖) ≤
          ∑ j ∈ J, ∑ x ∈ C j, |f x| * ε := by
        apply Finset.sum_le_sum
        intro j hj
        apply Finset.sum_le_sum
        intro x hx
        exact mul_le_mul_of_nonneg_left (happrox j hj x hx) (abs_nonneg (f x))
      _ = ε * ∑ x ∈ U, |f x| := by
        have hpartition :=
          Finset.sum_biUnion (M := ℝ) (f := fun x : α => |f x|) hdisjoint
        rw [hcover] at hpartition
        simp_rw [← Finset.sum_mul]
        rw [← hpartition]
        ring
      _ ≤ ε * (U.card : ℝ) := mul_le_mul_of_nonneg_left hLone hε
  · exact le_rfl
  · exact hgap
  · exact hcorr

/-- The sum of the balanced indicator on a cell is its excess count over the
ambient density prediction. -/
theorem sum_balancedIndicator_on_cell {α : Type*} [DecidableEq α]
    (U A C : Finset α) :
    (∑ x ∈ C, balancedIndicator U A x) =
      ((A ∩ C).card : ℝ) -
        ((A.card : ℝ) / U.card) * (C.card : ℝ) := by
  have hfilter : C.filter (fun x => x ∈ A) = A ∩ C := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_inter]
    tauto
  simp only [balancedIndicator, Finset.sum_sub_distrib, Finset.sum_boole,
    hfilter, Finset.sum_const, nsmul_eq_mul]
  ring

/-- A supplied bound `E` on the summed phase approximation error turns a
large balanced-indicator correlation into a density increment. The error is
required to be at most `ε * U.card`, and the selected cell retains the size
floor `L`. -/
theorem exists_density_increment_of_correlation_with_error
    {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (U A : Finset α) (J : Finset ι) (C : ι → Finset α)
    (χ : α → ℂ) (ζ : ι → ℂ) (L : ℕ) (ε η E : ℝ)
    (hU : U.Nonempty) (hAU : A ⊆ U)
    (hC : ∀ j ∈ J, (C j).Nonempty)
    (hsize : ∀ j ∈ J, L ≤ (C j).card)
    (hdisjoint : (↑J : Set ι).PairwiseDisjoint C)
    (hcover : J.biUnion C = U)
    (hζ : ∀ j ∈ J, ‖ζ j‖ ≤ 1)
    (herror :
      (∑ j ∈ J, ∑ x ∈ C j,
        |balancedIndicator U A x| * ‖χ x - ζ j‖) ≤ E)
    (hE : E ≤ ε * (U.card : ℝ)) (hgap : ε < η)
    (hcorr : η * (U.card : ℝ) ≤
      ‖∑ x ∈ U, (balancedIndicator U A x : ℂ) * χ x‖) :
    ∃ j ∈ J, (C j).Nonempty ∧ L ≤ (C j).card ∧
      (A.card : ℝ) / U.card + (η - ε) / 2 ≤
        ((A ∩ C j).card : ℝ) / (C j).card := by
  obtain ⟨j, hj, hsum⟩ :=
    exists_cell_sum_ge_of_correlation_with_error U J C
      (balancedIndicator U A) χ ζ ε η E hU hC hdisjoint hcover
      (sum_balancedIndicator_eq_zero U A hU hAU) hζ herror hE hgap hcorr
  refine ⟨j, hj, hC j hj, hsize j hj, ?_⟩
  rw [sum_balancedIndicator_on_cell] at hsum
  have hcard_pos : (0 : ℝ) < (C j).card := by
    exact_mod_cast Finset.card_pos.mpr (hC j hj)
  rw [le_div_iff₀ hcard_pos]
  nlinarith

/-- A character that is nearly constant on each cell of a finite partition
and has large correlation with the balanced indicator forces a density
increment on a cell. The selected cell retains the supplied size floor `L`. -/
theorem exists_density_increment_of_correlation
    {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (U A : Finset α) (J : Finset ι) (C : ι → Finset α)
    (χ : α → ℂ) (ζ : ι → ℂ) (L : ℕ) (ε η : ℝ)
    (hU : U.Nonempty) (hAU : A ⊆ U)
    (hC : ∀ j ∈ J, (C j).Nonempty)
    (hsize : ∀ j ∈ J, L ≤ (C j).card)
    (hdisjoint : (↑J : Set ι).PairwiseDisjoint C)
    (hcover : J.biUnion C = U)
    (hζ : ∀ j ∈ J, ‖ζ j‖ ≤ 1)
    (happrox : ∀ j ∈ J, ∀ x ∈ C j, ‖χ x - ζ j‖ ≤ ε)
    (hε : 0 ≤ ε) (hgap : ε < η)
    (hcorr : η * (U.card : ℝ) ≤
      ‖∑ x ∈ U, (balancedIndicator U A x : ℂ) * χ x‖) :
    ∃ j ∈ J, (C j).Nonempty ∧ L ≤ (C j).card ∧
      (A.card : ℝ) / U.card + (η - ε) / 2 ≤
        ((A ∩ C j).card : ℝ) / (C j).card := by
  obtain ⟨j, hj, hsum⟩ := exists_cell_sum_ge_of_correlation U J C
    (balancedIndicator U A) χ ζ ε η hU hC hdisjoint hcover
    (sum_balancedIndicator_eq_zero U A hU hAU)
    (sum_abs_balancedIndicator_le_card U A hU hAU) hζ happrox hε hgap hcorr
  refine ⟨j, hj, hC j hj, hsize j hj, ?_⟩
  rw [sum_balancedIndicator_on_cell] at hsum
  have hcard_pos : (0 : ℝ) < (C j).card := by
    exact_mod_cast Finset.card_pos.mpr (hC j hj)
  rw [le_div_iff₀ hcard_pos]
  nlinarith

/-- If the phase error is at most half the correlation threshold, the finite
reduction supplies the simpler density gain `η / 4`, while preserving the
cell-size floor. -/
theorem exists_density_increment_quarter_of_correlation
    {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (U A : Finset α) (J : Finset ι) (C : ι → Finset α)
    (χ : α → ℂ) (ζ : ι → ℂ) (L : ℕ) (ε η : ℝ)
    (hU : U.Nonempty) (hAU : A ⊆ U)
    (hC : ∀ j ∈ J, (C j).Nonempty)
    (hsize : ∀ j ∈ J, L ≤ (C j).card)
    (hdisjoint : (↑J : Set ι).PairwiseDisjoint C)
    (hcover : J.biUnion C = U)
    (hζ : ∀ j ∈ J, ‖ζ j‖ ≤ 1)
    (happrox : ∀ j ∈ J, ∀ x ∈ C j, ‖χ x - ζ j‖ ≤ ε)
    (hε : 0 ≤ ε) (hη : 0 < η) (hhalf : ε ≤ η / 2)
    (hcorr : η * (U.card : ℝ) ≤
      ‖∑ x ∈ U, (balancedIndicator U A x : ℂ) * χ x‖) :
    ∃ j ∈ J, (C j).Nonempty ∧ L ≤ (C j).card ∧
      (A.card : ℝ) / U.card + η / 4 ≤
        ((A ∩ C j).card : ℝ) / (C j).card := by
  have hgap : ε < η := by linarith
  obtain ⟨j, hj, hCj, hLj, hincrement⟩ :=
    exists_density_increment_of_correlation U A J C χ ζ L ε η hU hAU hC hsize
      hdisjoint hcover hζ happrox hε hgap hcorr
  refine ⟨j, hj, hCj, hLj, ?_⟩
  calc
    (A.card : ℝ) / U.card + η / 4 ≤
        (A.card : ℝ) / U.card + (η - ε) / 2 := by linarith
    _ ≤ ((A ∩ C j).card : ℝ) / (C j).card := hincrement

/-- Joint satisfiability check on a two-point partition: the balanced
indicator correlates perfectly with the sign that is constant on each
singleton cell. -/
example :
    let U : Finset ℕ := {0, 1}
    let A : Finset ℕ := {0}
    let J : Finset Bool := Finset.univ
    let C : Bool → Finset ℕ := fun j => if j then {1} else {0}
    ∃ j ∈ J, (C j).Nonempty ∧ 1 ≤ (C j).card ∧
      (A.card : ℝ) / U.card + (((1 : ℝ) / 2) - 0) / 2 ≤
        ((A ∩ C j).card : ℝ) / (C j).card := by
  dsimp only
  apply exists_density_increment_of_correlation
    ({0, 1} : Finset ℕ) ({0} : Finset ℕ) Finset.univ
    (fun j : Bool => if j then {1} else {0})
    (fun x : ℕ => if x = 0 then 1 else -1)
    (fun j : Bool => if j then -1 else 1) 1 0 (1 / 2)
  · simp
  · simp
  · intro j hj
    cases j <;> simp
  · intro j hj
    cases j <;> simp
  · intro i hi j hj hij
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro x hxi hxj
    cases i <;> cases j <;> simp_all
  · ext x
    simp
    omega
  · intro j hj
    cases j <;> norm_num
  · intro j hj x hx
    cases j <;> simp_all
  · norm_num
  · norm_num
  · norm_num [balancedIndicator, Complex.norm_real, Real.norm_eq_abs]

#check @balancedIndicator
#check @sum_balancedIndicator_eq_zero
#check @sum_abs_balancedIndicator_le_card
#check @exists_large_of_sum_eq_zero
#check @exists_cell_sum_ge_of_correlation_with_error
#check @exists_cell_sum_ge_of_correlation
#check @sum_balancedIndicator_on_cell
#check @exists_density_increment_of_correlation_with_error
#check @exists_density_increment_of_correlation
#check @exists_density_increment_quarter_of_correlation

#print axioms sum_balancedIndicator_eq_zero
#print axioms sum_abs_balancedIndicator_le_card
#print axioms exists_large_of_sum_eq_zero
#print axioms exists_cell_sum_ge_of_correlation_with_error
#print axioms exists_cell_sum_ge_of_correlation
#print axioms sum_balancedIndicator_on_cell
#print axioms exists_density_increment_of_correlation_with_error
#print axioms exists_density_increment_of_correlation
#print axioms exists_density_increment_quarter_of_correlation

end Erdos142
