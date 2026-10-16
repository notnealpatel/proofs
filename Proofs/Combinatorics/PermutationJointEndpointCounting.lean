import Combinatorics.PermutationSameEdgeLimit
import Combinatorics.PermutationTwoAnchorFraction
import Combinatorics.PermutationCovarianceConsumer

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace PermutationJointEndpointCounting

open PermutationAvoidanceCovariance PermutationCovarianceConsumer
open PermutationCovarianceShortMoment PermutationCovarianceRanks PermutationSixMarginal
open PermutationOverlapBound
attribute [local instance] Classical.propDecidable

/-- Actual avoidance of the pair and triple overlap events has probability seven eighteenths. -/
theorem short_probability {n : ℕ} (hn : 6 ≤ n) :
    ((shortAvoiding n).card : ℝ) / Fintype.card (Equiv.Perm (Fin n)) = 7 / 18 := by
  let f : (Fin 6 → Fin n) → ℝ := fun b => if BoundaryAccepted b then 1 else 0
  have hleft : (∑ π : Equiv.Perm (Fin n), f (fun i => π (sixPositions hn i))) =
      ((shortAvoiding n).card : ℝ) := by
    simp only [f, ← short_avoidance_iff hn, ← mem_shortAvoiding_iff hn]
    simp
  have hright (s : {s : Finset (Fin n) // s.card = 6}) :
      (∑ p : Equiv.Perm (Fin 6), f (fun i => s.val.orderEmbOfFin s.property (p i))) = 280 := by
    simp only [f, boundaryAccepted_sorted_iff]
    have hi : (∑ p : Equiv.Perm (Fin 6), if Accepted p then (1 : ℝ) else 0) =
        ((Finset.univ.filter Accepted).card : ℝ) := by simp
    rw [hi, accepted_count]
    norm_num
  obtain ⟨s, _, hs⟩ := Finset.exists_subset_card_eq
    (show 6 ≤ (Finset.univ : Finset (Fin n)).card by simpa using hn)
  letI : Nonempty {s : Finset (Fin n) // s.card = 6} := ⟨⟨s, hs⟩⟩
  have hc : (Fintype.card {s : Finset (Fin n) // s.card = 6} : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt Fintype.card_pos)
  have hu := six_boundary_uniform hn f
  rw [hleft] at hu
  simp_rw [hright] at hu
  rw [Fintype.card_perm, Fintype.card_fin]
  rw [hu]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
  ring

/-- Removing the actual long-overlap tail from short avoidance loses at most its cardinality. -/
theorem short_card_le_avoiding_add_tail (n : ℕ) :
    (shortAvoiding n).card ≤ (avoiding n).card + (longOverlaps n 4).card := by
  have hsub : shortAvoiding n ⊆ avoiding n ∪ longOverlaps n 4 := by
    intro π hπ
    by_cases hH : π ∈ avoiding n
    · exact Finset.mem_union_left _ hH
    · have hA : ∀ k, 2 ≤ k → k ≤ 3 → ∀ hkn : k < n, ¬ Overlap hkn π := by
        simpa only [shortAvoiding, Finset.mem_filter, Finset.mem_univ, true_and] using hπ
      have hnot : ¬ (∀ k, 2 ≤ k → ∀ hkn : k < n, ¬ Overlap hkn π) := by
        simpa only [mem_avoiding] using hH
      push Not at hnot
      obtain ⟨k, hk, hkn, hO⟩ := hnot
      have hk4 : 4 ≤ k := by
        by_contra he
        exact hA k hk (by omega) hkn hO
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨Finset.mem_univ π, k, hk4, hkn, hO⟩)
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

/-- Actual full avoidance has uniform probability at least `16991/50400` for all sizes at least thirty. -/
theorem avoiding_probability_lower {n : ℕ} (hn : 30 ≤ n) :
    (16991 / 50400 : ℝ) ≤
      ((avoiding n).card : ℝ) / Fintype.card (Equiv.Perm (Fin n)) := by
  have hp : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin n)) := by
    exact_mod_cast Fintype.card_pos
  have hc : ((shortAvoiding n).card : ℝ) ≤
      (avoiding n).card + (longOverlaps n 4).card := by
    exact_mod_cast short_card_le_avoiding_add_tail n
  have hd := div_le_div_of_nonneg_right hc hp.le
  rw [add_div, short_probability (by omega : 6 ≤ n)] at hd
  have ht := all_tail_fraction_le hn
  linarith

/-- Partition actual avoidance by its ordered, distinct endpoint labels, with arbitrary weights. -/
theorem sum_avoiding_endpoints {n : ℕ} [NeZero n] (q : Fin n) (hq : (0 : Fin n) ≠ q)
    (w : Fin n → Fin n → ℝ) :
    (∑ π ∈ avoiding n, w (π 0) (π q)) =
      ∑ a : Fin n, ∑ b : Fin n with a ≠ b,
        w a b * (Fintype.card (PermutationMixedEndpointBound.AvoidTwo q a b) : ℝ) := by
  classical
  let W : Equiv.Perm (Fin n) → ℝ := fun π => w (π 0) (π q)
  change (∑ π ∈ avoiding n, W π) = _
  rw [← Finset.sum_fiberwise (avoiding n) (fun π => π 0) W]
  apply Finset.sum_congr rfl
  intro a _
  have hm : ∀ π ∈ (avoiding n).filter (fun π => π 0 = a),
      π q ∈ Finset.univ.filter (fun b => a ≠ b) := by
    intro π hπ
    have ha := (Finset.mem_filter.mp hπ).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro he
    exact hq (π.injective (ha.trans he))
  rw [← Finset.sum_fiberwise_of_maps_to hm W]
  apply Finset.sum_congr rfl
  intro b hb
  let S := ((avoiding n).filter (fun π => π 0 = a)).filter (fun π => π q = b)
  have hcard : S.card = Fintype.card (PermutationMixedEndpointBound.AvoidTwo q a b) := by
    symm
    apply Fintype.card_of_subtype
    intro π
    simp only [S, Finset.mem_filter, mem_avoiding]
    tauto
  have hW : (∑ π ∈ S, W π) = ∑ _π ∈ S, w a b := by
    apply Finset.sum_congr rfl
    intro π hπ
    have hmem := Finset.mem_filter.mp hπ
    have ha := (Finset.mem_filter.mp hmem.1).2
    simp only [W, ha, hmem.2]
  change (∑ π ∈ S, W π) = _
  rw [hW]
  simp only [Finset.sum_const, nsmul_eq_mul, hcard, mul_comm]

private theorem factorial_two {n : ℕ} (hn : 2 ≤ n) :
    (n.factorial : ℝ) = (n : ℝ) * ((n : ℝ) - 1) * ((n - 2).factorial : ℝ) := by
  have he : n = (n - 2) + 1 + 1 := by omega
  have hnat : n.factorial = n * (n - 1) * (n - 2).factorial := by
    conv_lhs => rw [he, Nat.factorial_succ, Nat.factorial_succ]
    have he1 : n - 2 + 1 = n - 1 := by omega
    rw [← he, he1]
    ring
  rw [hnat, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ n)]
  norm_num

/-- Exact disintegration of any actual endpoint weight into the actual two-endpoint
avoidance fractions; endpoints are distinct and all denominators are positive for `2 ≤ n`. -/
theorem weighted_actual_disintegration {n : ℕ} (hn : 2 ≤ n) (phi : ℝ → ℝ → ℝ) :
    (∑ π ∈ avoiding n,
      phi (coordinate (⟨0, by omega⟩ : Fin n) π)
        (coordinate (⟨n - 1, by omega⟩ : Fin n) π)) /
        (Fintype.card (Equiv.Perm (Fin n)) : ℝ) =
      (∑ a : Fin n, ∑ b : Fin n with a ≠ b,
        phi ((a.val : ℝ) / ((n : ℝ) - 1)) ((b.val : ℝ) / ((n : ℝ) - 1)) *
          PermutationSameEdgeLimit.F n a.val b.val) / ((n : ℝ) * ((n : ℝ) - 1)) := by
  letI : NeZero n := ⟨by omega⟩
  let q : Fin n := ⟨n - 1, by omega⟩
  have hq : (0 : Fin n) ≠ q := by
    intro he
    have hv := congrArg Fin.val he
    change 0 = n - 1 at hv
    omega
  let w : Fin n → Fin n → ℝ := fun a b =>
    phi ((a.val : ℝ) / ((n : ℝ) - 1)) ((b.val : ℝ) / ((n : ℝ) - 1))
  have hsum := sum_avoiding_endpoints q hq w
  change (∑ π ∈ avoiding n, w (π 0) (π q)) /
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ) = _
  rw [hsum, Fintype.card_perm, Fintype.card_fin, factorial_two hn]
  have hf : ((n - 2).factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n - 2)
  have hterm (a b : Fin n) (hab : a ≠ b) :
      w a b * (Fintype.card (PermutationMixedEndpointBound.AvoidTwo q a b) : ℝ) =
        (w a b * PermutationSameEdgeLimit.F n a.val b.val) * ((n - 2).factorial : ℝ) := by
    have hv : a.val ≠ b.val := fun he => hab (Fin.ext he)
    rw [PermutationSameEdgeLimit.F_eq_actual hn a.isLt b.isLt hv]
    rw [PermutationTwoAnchorKernel.card_fixedTwo (0 : Fin n) q a b hq hab]
    change w a b * _ = (w a b * (_ / ((n - 2).factorial : ℝ))) * ((n - 2).factorial : ℝ)
    field_simp
    rfl
  have hs : (∑ a : Fin n, ∑ b : Fin n with a ≠ b,
      w a b * (Fintype.card (PermutationMixedEndpointBound.AvoidTwo q a b) : ℝ)) =
      (∑ a : Fin n, ∑ b : Fin n with a ≠ b,
        w a b * PermutationSameEdgeLimit.F n a.val b.val) * ((n - 2).factorial : ℝ) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b hb
    exact hterm a b (Finset.mem_filter.mp hb).2
  rw [hs, mul_div_mul_right _ _ hf]

example : 2 ≤ 2 ∧ (0 : Fin 2) ≠ 1 ∧ (avoiding 2).Nonempty := by
  refine ⟨by decide, by decide, Equiv.refl _, ?_⟩
  rw [mem_avoiding]
  intro k hk hkn
  omega

example : 6 ≤ 6 ∧ Nonempty {s : Finset (Fin 6) // s.card = 6} :=
  ⟨by decide, ⟨⟨Finset.univ, by decide⟩⟩⟩

example : 30 ≤ 30 ∧ Nonempty (Fin 30) := ⟨by decide, ⟨0⟩⟩

end PermutationJointEndpointCounting
