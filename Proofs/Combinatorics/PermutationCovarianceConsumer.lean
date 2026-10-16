import Combinatorics.PermutationCovarianceShortMoment
import Combinatorics.PermutationAvoidanceCovarianceTail
import Combinatorics.PermutationSubsetMoments

set_option autoImplicit false

noncomputable section
open scoped BigOperators

namespace PermutationCovarianceConsumer

open PermutationOverlapBound PermutationAvoidanceCovariance
open PermutationCovarianceShortMoment PermutationCovarianceRanks

attribute [local instance] Classical.propDecidable

/-- For at least six positions, the actual short event excludes exactly overlaps two and three. -/
theorem mem_shortAvoiding_iff {n : ℕ} (hn : 6 ≤ n) (π : Equiv.Perm (Fin n)) :
    π ∈ shortAvoiding n ↔
      ¬ Overlap (show 2 < n by omega) π ∧ ¬ Overlap (show 3 < n by omega) π := by
  simp only [shortAvoiding, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    exact ⟨h 2 (by omega) (by omega) _, h 3 (by omega) (by omega) _⟩
  · intro h k hk hk3 hkn
    have hk23 : k = 2 ∨ k = 3 := by omega
    rcases hk23 with rfl | rfl
    · exact h.1
    · exact h.2

/-- The actual short-event endpoint moment is the sorted-subset accepted-rank expression.
No sorted-subset moment evaluation is assumed or asserted here. -/
theorem short_endpoint_moment_decomposition {n : ℕ} (hn : 6 ≤ n) :
    (∑ π ∈ shortAvoiding n,
      (coordinate (⟨0, by omega⟩ : Fin n) π - 1 / 2) *
        (coordinate (⟨n - 1, by omega⟩ : Fin n) π - 1 / 2)) /
      Fintype.card (Equiv.Perm (Fin n)) =
    (∑ s : {s : Finset (Fin n) // s.card = 6},
      ∑ p ∈ Finset.univ.filter Accepted,
        (((s.val.orderEmbOfFin s.property (p 0)).val : ℝ) / ((n : ℝ) - 1) - 1 / 2) *
        (((s.val.orderEmbOfFin s.property (p 5)).val : ℝ) / ((n : ℝ) - 1) - 1 / 2)) /
      ((Fintype.card {s : Finset (Fin n) // s.card = 6} : ℝ) * 720) := by
  have he : shortAvoiding n = Finset.univ.filter (fun π : Equiv.Perm (Fin n) =>
      ¬ Overlap (show 2 < n by omega) π ∧ ¬ Overlap (show 3 < n by omega) π) := by
    ext π
    simp only [mem_shortAvoiding_iff hn, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [he, Fintype.card_perm, Fintype.card_fin]
  exact short_moment_decomposition hn

/-- Algebraic simplification of the audited rank coefficients, with a nonzero denominator. -/
theorem rank_average_identity {n : ℕ} (hn : 6 ≤ n) :
    (1264 * ((n : ℝ) + 1)^2 / (196 * ((n : ℝ) - 1)^2) +
      1392 * ((n : ℝ) + 1) * ((n : ℝ) - 6) / (392 * ((n : ℝ) - 1)^2)) / 720 =
      ((n : ℝ) + 1) * (35 * (n : ℝ) - 52) / (2520 * ((n : ℝ) - 1)^2) := by
  have hnR : (6 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : (n : ℝ) - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- The simplified rank average is at least one seventy-second for every size at least six. -/
theorem rank_average_lower {n : ℕ} (hn : 6 ≤ n) :
    (1 / 72 : ℝ) ≤
      ((n : ℝ) + 1) * (35 * (n : ℝ) - 52) / (2520 * ((n : ℝ) - 1)^2) := by
  have hnR : (6 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < (n : ℝ) - 1 := by linarith
  apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2520) (sq_pos_of_pos hd))).mpr
  nlinarith

/-- The actual sorted-subset expression is at most the full-event endpoint moment
plus the proved unconditional tail loss. This is structural transfer, not a moment evaluation. -/
theorem sorted_moment_le_full_add_tail {n : ℕ} (hn : 30 ≤ n) :
    (∑ s : {s : Finset (Fin n) // s.card = 6},
      ∑ p ∈ Finset.univ.filter Accepted,
        (((s.val.orderEmbOfFin s.property (p 0)).val : ℝ) / ((n : ℝ) - 1) - 1 / 2) *
        (((s.val.orderEmbOfFin s.property (p 5)).val : ℝ) / ((n : ℝ) - 1) - 1 / 2)) /
      ((Fintype.card {s : Finset (Fin n) // s.card = 6} : ℝ) * 720) ≤
    (∑ π ∈ avoiding n,
      (coordinate (⟨0, by omega⟩ : Fin n) π - 1 / 2) *
        (coordinate (⟨n - 1, by omega⟩ : Fin n) π - 1 / 2)) /
      Fintype.card (Equiv.Perm (Fin n)) + 2609 / 201600 := by
  rw [← short_endpoint_moment_decomposition (by omega : 6 ≤ n)]
  have hp : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin n)) := by
    exact_mod_cast Fintype.card_pos
  have hsum := centered_short_le_full_add_tail (by omega : 2 ≤ n)
    (⟨0, by omega⟩ : Fin n) (⟨n - 1, by omega⟩ : Fin n)
  have hdiv := div_le_div_of_nonneg_right hsum hp.le
  rw [add_div, mul_div_assoc] at hdiv
  have htail := all_tail_fraction_le hn
  linarith

example : 6 ≤ 6 ∧ Nonempty (Fin 6) ∧
    Equiv.swap (0 : Fin 6) 1 ∈ shortAvoiding 6 := by
  refine ⟨by omega, ⟨0⟩, (mem_shortAvoiding_iff (by decide) _).mpr ?_⟩
  rw [short_avoidance_iff (by decide : 6 ≤ 6)]
  have he : PermutationSixMarginal.sixPositions (by decide : 6 ≤ 6) =
      Function.Embedding.refl (Fin 6) := by
    ext i
    simp [PermutationSixMarginal.sixPositions]
  rw [he]
  change Accepted (Equiv.swap (0 : Fin 6) 1)
  exact of_decide_eq_true rfl

/-- The actual rational subset moment transports to real coordinates. -/
theorem sum_sorted6_scaled_centered_real {n : ℕ} (hn : 6 ≤ n) (i j : Fin 6) :
    (∑ s : PermutationSubsetMoments.SixSubset n,
      (((PermutationSubsetMoments.sorted6 s i).val : ℝ) / ((n : ℝ) - 1) - 1 / 2) *
      (((PermutationSubsetMoments.sorted6 s j).val : ℝ) / ((n : ℝ) - 1) - 1 / 2)) =
      (Fintype.card (PermutationSubsetMoments.SixSubset n) : ℝ) *
        (((n : ℝ) + 1)^2 * (2 * (i.val + 1) - 7) * (2 * (j.val + 1) - 7) /
            (196 * ((n : ℝ) - 1)^2) +
          (min i.val j.val + 1) * (7 - ((max i.val j.val : ℕ) + 1 : ℝ)) *
            ((n : ℝ) + 1) * (n - 6) / (392 * ((n : ℝ) - 1)^2)) := by
  have h := congrArg (fun q : ℚ => (q : ℝ))
    (PermutationSubsetMoments.sum_sorted6_scaled_centered hn i j)
  push_cast at h
  simpa only [Nat.cast_min, Nat.cast_max] using h

/-- The actual accepted short-event moment equals the evaluated rank average. -/
theorem short_endpoint_moment_evaluation {n : ℕ} (hn : 6 ≤ n) :
    (∑ π ∈ shortAvoiding n,
      (coordinate (⟨0, by omega⟩ : Fin n) π - 1 / 2) *
        (coordinate (⟨n - 1, by omega⟩ : Fin n) π - 1 / 2)) /
      Fintype.card (Equiv.Perm (Fin n)) =
      ((n : ℝ) + 1) * (35 * (n : ℝ) - 52) / (2520 * ((n : ℝ) - 1)^2) := by
  obtain ⟨s, _, hs⟩ := Finset.exists_subset_card_eq
    (show 6 ≤ (Finset.univ : Finset (Fin n)).card by simpa using hn)
  letI : Nonempty (PermutationSubsetMoments.SixSubset n) := ⟨⟨s, hs⟩⟩
  have hc : (Fintype.card (PermutationSubsetMoments.SixSubset n) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt Fintype.card_pos)
  rw [short_endpoint_moment_decomposition hn, Finset.sum_comm]
  have hp (p : Equiv.Perm (Fin 6)) :
      (∑ s : PermutationSubsetMoments.SixSubset n,
        (((s.val.orderEmbOfFin s.property (p 0)).val : ℝ) / ((n : ℝ) - 1) - 1 / 2) *
        (((s.val.orderEmbOfFin s.property (p 5)).val : ℝ) / ((n : ℝ) - 1) - 1 / 2)) =
      (Fintype.card (PermutationSubsetMoments.SixSubset n) : ℝ) *
        ((((n : ℝ) + 1)^2 / (196 * ((n : ℝ) - 1)^2)) *
            (2 * (endpointA p : ℝ) - 7) * (2 * (endpointB p : ℝ) - 7) +
          (((n : ℝ) + 1) * (n - 6) / (392 * ((n : ℝ) - 1)^2)) *
            (min (endpointA p) (endpointB p) : ℝ) *
            (7 - (max (endpointA p) (endpointB p) : ℝ))) := by
    have h := sum_sorted6_scaled_centered_real hn (p 0) (p 5)
    simp only [PermutationSubsetMoments.sorted6] at h
    rw [h]
    simp only [endpointA, endpointB, min_add_add_right, max_add_add_right,
      Nat.cast_add, Nat.cast_one, Nat.cast_min, Nat.cast_max]
    ring
  simp_rw [hp]
  rw [← Finset.mul_sum, accepted_linear_kernel]
  rw [mul_div_mul_left _ _ hc]
  simpa only [mul_div_assoc, mul_assoc] using rank_average_identity hn

/-- The actual endpoint short-event moment is at least one seventy-second. -/
theorem short_endpoint_moment_lower {n : ℕ} (hn : 6 ≤ n) :
    (1 / 72 : ℝ) ≤
      (∑ π ∈ shortAvoiding n,
        (coordinate (⟨0, by omega⟩ : Fin n) π - 1 / 2) *
          (coordinate (⟨n - 1, by omega⟩ : Fin n) π - 1 / 2)) /
        Fintype.card (Equiv.Perm (Fin n)) := by
  rw [short_endpoint_moment_evaluation hn]
  exact rank_average_lower hn

/-- For every size at least thirty, actual avoidance is nonempty and actual endpoint
covariance is at least `191/201600`, strictly exceeding `1/1152`, with no moment premise. -/
theorem actual_endpoint_covariance_lower {n : ℕ} (hn : 30 ≤ n) :
    (avoiding n).Nonempty ∧
      (191 / 201600 : ℝ) ≤
        covariance (⟨0, by omega⟩ : Fin n) (⟨n - 1, by omega⟩ : Fin n) ∧
      (1 / 1152 : ℝ) <
        covariance (⟨0, by omega⟩ : Fin n) (⟨n - 1, by omega⟩ : Fin n) := by
  obtain ⟨hne, hcov⟩ := covariance_lower_of_short_lower hn
    (⟨0, by omega⟩ : Fin n) (⟨n - 1, by omega⟩ : Fin n)
    (short_endpoint_moment_lower (by omega : 6 ≤ n))
  exact ⟨hne, hcov, lt_of_lt_of_le target_constant_strict hcov⟩

example : 30 ≤ 30 ∧ Nonempty (Fin 30) ∧
    (⟨0, by omega⟩ : Fin 30) ≠ ⟨30 - 1, by omega⟩ := by
  exact ⟨by omega, ⟨0⟩, by decide⟩

end PermutationCovarianceConsumer
