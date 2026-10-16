import Combinatorics.PermutationSixMarginal
import Combinatorics.PermutationCovarianceRanks
import Combinatorics.PermutationAvoidanceCovariance

set_option autoImplicit false

noncomputable section
open scoped BigOperators

namespace PermutationCovarianceShortMoment

open PermutationSixMarginal PermutationCovarianceRanks
open PermutationOverlapBound PermutationAvoidanceCovariance

attribute [local instance] Classical.propDecidable

/-- Avoidance of the pair and triple comparison events on six boundary labels. -/
def BoundaryAccepted {n : ℕ} (b : Fin 6 → Fin n) : Prop :=
  ¬ ((b 0 < b 1) ↔ (b 4 < b 5)) ∧
  ¬ (∀ i j : Fin 3,
    b ⟨i.val, by omega⟩ < b ⟨j.val, by omega⟩ ↔
    b ⟨i.val + 3, by omega⟩ < b ⟨j.val + 3, by omega⟩)

example : BoundaryAccepted (Equiv.swap (0 : Fin 6) 1) := by
  change Accepted (Equiv.swap (0 : Fin 6) 1)
  exact of_decide_eq_true rfl

/-- Increasing sorted-label embeddings preserve exactly the accepted rank patterns. -/
theorem boundaryAccepted_sorted_iff {n : ℕ}
    (s : {s : Finset (Fin n) // s.card = 6}) (p : Equiv.Perm (Fin 6)) :
    BoundaryAccepted (fun i => s.val.orderEmbOfFin s.property (p i)) ↔ Accepted p := by
  simp only [BoundaryAccepted, Accepted, E2, E3, OrderEmbedding.lt_iff_lt]

private theorem overlap_two_iff {n : ℕ} (hn : 6 ≤ n) (π : Equiv.Perm (Fin n)) :
    Overlap (show 2 < n by omega) π ↔
      (π (sixPositions hn 0) < π (sixPositions hn 1) ↔
        π (sixPositions hn 4) < π (sixPositions hn 5)) := by
  have hpos (i : Fin 2) :
      (⟨i.val, by omega⟩ : Fin n) = sixPositions hn ⟨i.val, by omega⟩ := by
    apply Fin.ext
    simp only [sixPositions_apply]
    have hi := i.isLt
    split_ifs <;> omega
  have hlast (i : Fin 2) :
      (⟨i.val + (n - 2), by omega⟩ : Fin n) =
        sixPositions hn ⟨i.val + 4, by omega⟩ := by
    apply Fin.ext
    simp only [sixPositions_apply]
    have hi := i.isLt
    split_ifs <;> omega
  simp only [Overlap, hpos, hlast]
  constructor
  · intro h
    exact h 0 1
  · intro h i j
    fin_cases i <;> fin_cases j
    · simp
    · exact h
    · change (π (sixPositions hn 1) < π (sixPositions hn 0) ↔
        π (sixPositions hn 5) < π (sixPositions hn 4))
      simpa only [not_lt, le_iff_lt_or_eq, π.injective.eq_iff,
        (sixPositions hn).injective.eq_iff,
        show (1 : Fin 6) ≠ 0 by decide, show (5 : Fin 6) ≠ 4 by decide,
        or_false] using (not_congr h)
    · simp

private theorem overlap_three_iff {n : ℕ} (hn : 6 ≤ n) (π : Equiv.Perm (Fin n)) :
    Overlap (show 3 < n by omega) π ↔
      ∀ i j : Fin 3,
        π (sixPositions hn ⟨i.val, by omega⟩) <
          π (sixPositions hn ⟨j.val, by omega⟩) ↔
        π (sixPositions hn ⟨i.val + 3, by omega⟩) <
          π (sixPositions hn ⟨j.val + 3, by omega⟩) := by
  have hpos (i : Fin 3) :
      (⟨i.val, by omega⟩ : Fin n) = sixPositions hn ⟨i.val, by omega⟩ := by
    apply Fin.ext
    simp only [sixPositions_apply]
    have hi := i.isLt
    split_ifs <;> omega
  have hlast (i : Fin 3) :
      (⟨i.val + (n - 3), by omega⟩ : Fin n) =
        sixPositions hn ⟨i.val + 3, by omega⟩ := by
    apply Fin.ext
    simp only [sixPositions_apply]
    have hi := i.isLt
    split_ifs <;> omega
  simp only [Overlap, hpos, hlast]

/-- Actual short avoidance is precisely boundary comparison avoidance. -/
theorem short_avoidance_iff {n : ℕ} (hn : 6 ≤ n) (π : Equiv.Perm (Fin n)) :
    (¬ Overlap (show 2 < n by omega) π ∧ ¬ Overlap (show 3 < n by omega) π) ↔
      BoundaryAccepted (fun i => π (sixPositions hn i)) := by
  rw [overlap_two_iff hn, overlap_three_iff hn]
  rfl

/-- If actual boundary labels are a sorted subset with pattern `p`, short avoidance is `Accepted p`. -/
theorem short_avoidance_sorted_iff {n : ℕ} (hn : 6 ≤ n) (π : Equiv.Perm (Fin n))
    (s : {s : Finset (Fin n) // s.card = 6}) (p : Equiv.Perm (Fin 6))
    (hlabels : ∀ i, π (sixPositions hn i) = s.val.orderEmbOfFin s.property (p i)) :
    (¬ Overlap (show 2 < n by omega) π ∧ ¬ Overlap (show 3 < n by omega) π) ↔
      Accepted p := by
  rw [short_avoidance_iff hn]
  simp_rw [hlabels]
  exact boundaryAccepted_sorted_iff s p

/-- The two audited integer kernels give their real linear combination, without moment assumptions. -/
theorem accepted_linear_kernel (u v : ℝ) :
    (∑ p ∈ Finset.univ.filter Accepted,
      (u * (2 * (endpointA p : ℝ) - 7) * (2 * (endpointB p : ℝ) - 7) +
       v * (min (endpointA p) (endpointB p) : ℝ) *
         (7 - (max (endpointA p) (endpointB p) : ℝ)))) = 1264 * u + 1392 * v := by
  have hs : (∑ p ∈ Finset.univ.filter Accepted,
      (2 * (endpointA p : ℝ) - 7) * (2 * (endpointB p : ℝ) - 7)) = 1264 := by
    exact_mod_cast accepted_signed_sum
  have hm : (∑ p ∈ Finset.univ.filter Accepted,
      (min (endpointA p) (endpointB p) : ℝ) *
        (7 - (max (endpointA p) (endpointB p) : ℝ))) = 1392 := by
    exact_mod_cast accepted_minmax_sum
  simp_rw [mul_assoc]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hs, hm]
  ring

/-- The actual normalized short-avoidance endpoint moment splits into sorted subsets and accepted patterns. -/
theorem short_moment_decomposition {n : ℕ} (hn : 6 ≤ n) :
    (∑ π ∈ Finset.univ.filter (fun π : Equiv.Perm (Fin n) =>
        ¬ Overlap (show 2 < n by omega) π ∧ ¬ Overlap (show 3 < n by omega) π),
      (coordinate (⟨0, by omega⟩ : Fin n) π - 1 / 2) *
        (coordinate (⟨n - 1, by omega⟩ : Fin n) π - 1 / 2)) /
      (Nat.factorial n : ℝ) =
    (∑ s : {s : Finset (Fin n) // s.card = 6},
      ∑ p ∈ Finset.univ.filter Accepted,
        (((s.val.orderEmbOfFin s.property (p 0)).val : ℝ) / ((n : ℝ) - 1) - 1 / 2) *
        (((s.val.orderEmbOfFin s.property (p 5)).val : ℝ) / ((n : ℝ) - 1) - 1 / 2)) /
      ((Fintype.card {s : Finset (Fin n) // s.card = 6} : ℝ) * 720) := by
  let f : (Fin 6 → Fin n) → ℝ := fun b =>
    if BoundaryAccepted b then
      ((b 0).val / ((n : ℝ) - 1) - 1 / 2) *
      ((b 5).val / ((n : ℝ) - 1) - 1 / 2) else 0
  have hzero : sixPositions hn 0 = (⟨0, by omega⟩ : Fin n) := by
    apply Fin.ext
    exact (sixPositions_values hn).1
  have hfive : sixPositions hn 5 = (⟨n - 1, by omega⟩ : Fin n) := by
    apply Fin.ext
    exact (sixPositions_values hn).2.2.2.2.2
  have hleft : (∑ π : Equiv.Perm (Fin n), f (fun i => π (sixPositions hn i))) =
      ∑ π ∈ Finset.univ.filter (fun π : Equiv.Perm (Fin n) =>
        ¬ Overlap (show 2 < n by omega) π ∧ ¬ Overlap (show 3 < n by omega) π),
      (coordinate (⟨0, by omega⟩ : Fin n) π - 1 / 2) *
        (coordinate (⟨n - 1, by omega⟩ : Fin n) π - 1 / 2) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro π _
    simp only [f, ← short_avoidance_iff hn, hzero, hfive, coordinate]
  have hright (s : {s : Finset (Fin n) // s.card = 6}) :
      (∑ p : Equiv.Perm (Fin 6), f (fun i => s.val.orderEmbOfFin s.property (p i))) =
      ∑ p ∈ Finset.univ.filter Accepted,
        (((s.val.orderEmbOfFin s.property (p 0)).val : ℝ) / ((n : ℝ) - 1) - 1 / 2) *
        (((s.val.orderEmbOfFin s.property (p 5)).val : ℝ) / ((n : ℝ) - 1) - 1 / 2) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    simp only [f, boundaryAccepted_sorted_iff]
  have huniform := six_boundary_uniform hn f
  rw [hleft] at huniform
  simp_rw [hright] at huniform
  exact huniform

example : 6 ≤ 6 ∧ Nonempty (Fin 6) ∧
    Accepted (Equiv.swap (0 : Fin 6) 1) := by
  exact ⟨by omega, ⟨0⟩, by decide⟩

example : Nonempty {s : Finset (Fin 6) // s.card = 6} :=
  ⟨⟨Finset.univ, by decide⟩⟩

example : ¬ Overlap (by decide : 2 < 6) (Equiv.swap (0 : Fin 6) 1) ∧
    ¬ Overlap (by decide : 3 < 6) (Equiv.swap (0 : Fin 6) 1) := by
  rw [short_avoidance_iff (by decide : 6 ≤ 6)]
  have he : sixPositions (by decide : 6 ≤ 6) = Function.Embedding.refl (Fin 6) := by
    ext i
    simp [sixPositions]
  rw [he]
  change Accepted (Equiv.swap (0 : Fin 6) 1)
  exact of_decide_eq_true rfl

end PermutationCovarianceShortMoment
