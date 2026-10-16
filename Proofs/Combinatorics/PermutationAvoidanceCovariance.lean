import Combinatorics.PermutationEndpointReflection

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace PermutationAvoidanceCovariance

open PermutationOverlapBound PermutationEndpointReflection

attribute [local instance] Classical.propDecidable

/-- The actual permutations avoiding all proper overlaps of length at least two. -/
def avoiding (n : ℕ) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter fun π => ∀ k, 2 ≤ k → ∀ hkn : k < n, ¬ Overlap hkn π

example : Equiv.refl (Fin 1) ∈ avoiding 1 := by
  simp only [avoiding, Finset.mem_filter, Finset.mem_univ, true_and]
  intro k hk hkn
  omega

/-- Membership in the actual avoidance event is precisely absence of each overlap. -/
theorem mem_avoiding {n : ℕ} (π : Equiv.Perm (Fin n)) :
    π ∈ avoiding n ↔ ∀ k, 2 ≤ k → ∀ hkn : k < n, ¬ Overlap hkn π := by
  simp [avoiding]

/-- Complementing labels preserves the actual avoidance event. -/
theorem complement_mem_avoiding {n : ℕ} (π : Equiv.Perm (Fin n)) :
    complement π ∈ avoiding n ↔ π ∈ avoiding n := by
  simp only [mem_avoiding, overlap_complement_iff]

/-- Complementation as an equivalence of actual avoiding permutations. -/
def reflection (n : ℕ) : {π // π ∈ avoiding n} ≃ {π // π ∈ avoiding n} where
  toFun π := ⟨complement π.val, (complement_mem_avoiding π.val).mpr π.property⟩
  invFun π := ⟨complement π.val, (complement_mem_avoiding π.val).mpr π.property⟩
  left_inv π := Subtype.ext (complement_involutive π.val)
  right_inv π := Subtype.ext (complement_involutive π.val)

example {n : ℕ} (π : {π // π ∈ avoiding n}) :
    (reflection n π).val = complement π.val := rfl

/-- A label at a specified position, normalized by the nonzero range length. -/
def coordinate {n : ℕ} (i : Fin n) (π : Equiv.Perm (Fin n)) : ℝ :=
  (π i).val / ((n : ℝ) - 1)

example : coordinate (0 : Fin 2) (Equiv.refl _) = 0 := by
  norm_num [coordinate]

/-- Finite uniform mean over the actual avoidance event (used only when it is nonempty). -/
def mean {n : ℕ} (f : Equiv.Perm (Fin n) → ℝ) : ℝ :=
  (∑ π ∈ avoiding n, f π) / (avoiding n).card

example : @mean 1 (fun _ => 1) = 1 := by
  have hA : avoiding 1 = Finset.univ := by
    ext π
    simp only [mem_avoiding, Finset.mem_univ, iff_true]
    intro k hk hkn
    omega
  norm_num [mean, hA, Fintype.card_perm]

/-- The actual covariance subtracts both actual conditional means. -/
def covariance {n : ℕ} (i j : Fin n) : ℝ :=
  mean (fun π => (coordinate i π - mean (coordinate i)) *
    (coordinate j π - mean (coordinate j)))

example : covariance (0 : Fin 1) 0 = 0 := by
  simp [covariance, coordinate, mean]

/-- Complementation sends every normalized coordinate to its complement about one half. -/
theorem coordinate_complement {n : ℕ} (hn : 2 ≤ n) (i : Fin n)
    (π : Equiv.Perm (Fin n)) : coordinate i (complement π) = 1 - coordinate i π := by
  have hv : (π i).val ≤ n - 1 := by have hi := (π i).isLt; omega
  have hn0 : n ≠ 0 := by omega
  have hden : (n : ℝ) - 1 ≠ 0 := by exact_mod_cast (show (n : ℤ) - 1 ≠ 0 by omega)
  simp only [coordinate, complement, Equiv.trans_apply, Fin.revPerm_apply, Fin.val_rev]
  rw [Nat.cast_sub (by have hi := (π i).isLt; omega : (π i).val + 1 ≤ n)]
  push_cast
  field_simp
  ring

/-- Summation over actual avoiding permutations is invariant under label complementation. -/
theorem sum_complement {n : ℕ} (f : Equiv.Perm (Fin n) → ℝ) :
    (∑ π ∈ avoiding n, f (complement π)) = ∑ π ∈ avoiding n, f π := by
  apply Finset.sum_bij (fun π _ => complement π)
  · intro π hπ
    exact (complement_mem_avoiding π).mpr hπ
  · intro π hπ ρ hρ he
    exact complement_involutive.injective he
  · intro ρ hρ
    exact ⟨complement ρ, (complement_mem_avoiding ρ).mpr hρ,
      complement_involutive ρ⟩
  · intro π hπ
    rfl

/-- Reflection forces every actual conditional coordinate mean to be one half. -/
theorem mean_coordinate {n : ℕ} (hn : 2 ≤ n) (hH : (avoiding n).Nonempty)
    (i : Fin n) : mean (coordinate i) = 1 / 2 := by
  have hc : (avoiding n).card ≠ 0 := Finset.card_ne_zero.mpr hH
  have hcR : ((avoiding n).card : ℝ) ≠ 0 := by exact_mod_cast hc
  have hs := sum_complement (coordinate i)
  simp_rw [coordinate_complement hn] at hs
  rw [Finset.sum_sub_distrib] at hs
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hs
  unfold mean
  apply (div_eq_iff hcR).mpr
  linarith

/-- Actual covariance equals the half-centered conditional moment, after proving the means. -/
theorem covariance_eq_centered {n : ℕ} (hn : 2 ≤ n)
    (hH : (avoiding n).Nonempty) (i j : Fin n) :
    covariance i j = mean (fun π => (coordinate i π - 1 / 2) *
      (coordinate j π - 1 / 2)) := by
  rw [covariance, mean_coordinate hn hH i, mean_coordinate hn hH j]

example : 2 ≤ 2 ∧ (avoiding 2).Nonempty ∧ Nonempty (Fin 2) := by
  refine ⟨by omega, ?_, ⟨0⟩⟩
  refine ⟨Equiv.refl _, (mem_avoiding _).mpr ?_⟩
  intro k hk hkn
  omega

/-- The actual short avoidance event excludes lengths two and three only. -/
def shortAvoiding (n : ℕ) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter fun π => ∀ k, 2 ≤ k → k ≤ 3 → ∀ hkn : k < n, ¬ Overlap hkn π

example : shortAvoiding 2 = avoiding 2 := by
  ext π
  simp only [shortAvoiding, Finset.mem_filter, Finset.mem_univ, true_and, mem_avoiding]
  constructor <;> intro h k hk <;> intros <;> omega

/-- A positive actual-event sum ensures that the event is inhabited. -/
theorem avoiding_nonempty_of_sum_pos {n : ℕ} (f : Equiv.Perm (Fin n) → ℝ)
    (h : 0 < ∑ π ∈ avoiding n, f π) : (avoiding n).Nonempty := by
  by_contra he
  have hempty := Finset.not_nonempty_iff_eq_empty.mp he
  simp only [hempty, Finset.sum_empty, lt_self_iff_false] at h

/-- Dividing a positive actual-event sum by its own cardinality is at least
its unconditional normalization over all permutations. -/
theorem unconditional_le_mean {n : ℕ} (f : Equiv.Perm (Fin n) → ℝ)
    (h : 0 < ∑ π ∈ avoiding n, f π) :
    (∑ π ∈ avoiding n, f π) / Fintype.card (Equiv.Perm (Fin n)) ≤ mean f := by
  have hH := avoiding_nonempty_of_sum_pos f h
  have hc : (0 : ℝ) < (avoiding n).card := by exact_mod_cast Finset.card_pos.mpr hH
  have hle : ((avoiding n).card : ℝ) ≤ Fintype.card (Equiv.Perm (Fin n)) := by
    exact_mod_cast Finset.card_le_univ (avoiding n)
  exact div_le_div_of_nonneg_left h.le hc hle

/-- Staged transfer from a positive unconditional actual centered moment to actual
covariance. The centered-moment premise remains an explicit unpaid input. -/
theorem covariance_lower_of_centered_lower {n : ℕ} (hn : 2 ≤ n)
    (i j : Fin n) (c : ℝ) (hc : 0 < c)
    (h : c ≤ (∑ π ∈ avoiding n, (coordinate i π - 1 / 2) *
      (coordinate j π - 1 / 2)) / Fintype.card (Equiv.Perm (Fin n))) :
    (avoiding n).Nonempty ∧ c ≤ covariance i j := by
  have hp : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin n)) := by
    exact_mod_cast Fintype.card_pos
  have hs : 0 < ∑ π ∈ avoiding n, (coordinate i π - 1 / 2) *
      (coordinate j π - 1 / 2) := ((div_pos_iff.mp (lt_of_lt_of_le hc h)).resolve_right
        (by intro hh; exact (not_lt_of_ge hp.le) hh.2)).1
  have hH := avoiding_nonempty_of_sum_pos _ hs
  refine ⟨hH, ?_⟩
  rw [covariance_eq_centered hn hH]
  exact h.trans (unconditional_le_mean _ hs)

/-- Each normalized actual coordinate lies in the unit interval when its denominator is positive. -/
theorem coordinate_bounds {n : ℕ} (hn : 2 ≤ n) (i : Fin n)
    (π : Equiv.Perm (Fin n)) : 0 ≤ coordinate i π ∧ coordinate i π ≤ 1 := by
  have hd : (0 : ℝ) < (n : ℝ) - 1 := by exact_mod_cast (show (0 : ℤ) < (n : ℤ)-1 by omega)
  have hv : ((π i).val : ℝ) ≤ (n : ℝ)-1 := by
    exact_mod_cast (show ((π i).val : ℤ) ≤ (n : ℤ)-1 by have hi := (π i).isLt; omega)
  exact ⟨div_nonneg (Nat.cast_nonneg _) hd.le, (div_le_one hd).mpr hv⟩

end PermutationAvoidanceCovariance
