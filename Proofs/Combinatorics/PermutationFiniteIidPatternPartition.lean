import Combinatorics.PermutationFiniteIidCore

set_option autoImplicit false

noncomputable section
namespace FiniteIidPatternRepair
open PermutationFiniteWordPartition PermutationFiniteIidEndpointLaw
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- A common pattern is unique, including for words with cross-block ties. -/
theorem common_unique {m n k : ℕ} (L R : Fin m → Fin n) (hk : k ≤ m)
    (σ τ : Equiv.Perm (Fin k)) (hs : Common L R hk σ) (ht : Common L R hk τ) :
    σ = τ := by
  obtain ⟨hl, hr, hsl, hsr⟩ := (common_iff_rank L R hk σ).mp hs
  obtain ⟨hl', hr', htl, htr⟩ := (common_iff_rank L R hk τ).mp ht
  exact hsl.symm.trans htl

/-- Nonavoidance is the disjoint union of earliest length cells, without Good. -/
theorem card_nonavoid {m n : ℕ} (hm : 0 < m) (a b : Fin n) :
    (Finset.univ.filter (fun z => ¬ SampleAvoid hm a b z)).card =
      ∑ k ∈ Finset.Icc 2 m,
        (Finset.univ.filter (fun z => ∃ hk : k ≤ m,
          A (sampledLeft hm a z) (sampledRight hm b z) hk)).card := by
  let C := fun k => Finset.univ.filter (fun z : Fin (2 * (m - 1)) → Fin n =>
    ∃ hk : k ≤ m, A (sampledLeft hm a z) (sampledRight hm b z) hk)
  have he : Finset.univ.filter (fun z => ¬ SampleAvoid hm a b z) =
      (Finset.Icc 2 m).biUnion C := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_Icc, C]
    rw [sampleAvoid_iff_no_earliest]
    push Not
    constructor
    · rintro ⟨k, hk, htwo, ha⟩
      exact ⟨k, ⟨htwo, hk⟩, hk, ha⟩
    · rintro ⟨k, ⟨htwo, hk⟩, hk', ha⟩
      exact ⟨k, hk, htwo, ha⟩
  rw [he]
  apply Finset.card_biUnion
  intro j hj k hk hne
  apply Finset.disjoint_left.mpr
  intro z hzj hzk
  obtain ⟨hj', haj⟩ := (Finset.mem_filter.mp hzj).2
  obtain ⟨hk', hak⟩ := (Finset.mem_filter.mp hzk).2
  have hjtwo := (Finset.mem_Icc.mp hj).1
  have hktwo := (Finset.mem_Icc.mp hk).1
  rcases lt_or_gt_of_ne hne with hjk | hkj
  · exact A_disjoint _ _ hjtwo hjk hk' ⟨haj, hak⟩
  · exact A_disjoint _ _ hktwo hkj hj' ⟨hak, haj⟩

/-- Each earliest cell splits disjointly into actual avoiding common patterns. -/
theorem card_earliest_patterns {m n k : ℕ} (hm : 0 < m) (a b : Fin n)
    (hk : k ≤ m) :
    (Finset.univ.filter (fun z => A (sampledLeft hm a z)
      (sampledRight hm b z) hk)).card =
      ∑ σ ∈ PermutationAvoidanceCovariance.avoiding k,
        (Finset.univ.filter (fun z => Common (sampledLeft hm a z)
          (sampledRight hm b z) hk σ)).card := by
  let C := fun σ => Finset.univ.filter (fun z : Fin (2 * (m - 1)) → Fin n =>
    Common (sampledLeft hm a z) (sampledRight hm b z) hk σ)
  have he : Finset.univ.filter (fun z => A (sampledLeft hm a z)
      (sampledRight hm b z) hk) =
      (PermutationAvoidanceCovariance.avoiding k).biUnion C := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    constructor
    · rintro ⟨σ, hc, ha⟩
      refine ⟨σ, ?_, Finset.mem_filter.mpr ⟨Finset.mem_univ z, hc⟩⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ σ, fun j hj hjk => ha j hj hjk hjk⟩
    · rintro ⟨σ, ha, hc⟩
      refine ⟨σ, (Finset.mem_filter.mp hc).2, ?_⟩
      intro j hj hjk _
      exact (Finset.mem_filter.mp ha).2 j hj hjk
  rw [he]
  apply Finset.card_biUnion
  intro σ hσ τ hτ hne
  apply Finset.disjoint_left.mpr
  intro z hzσ hzτ
  exact hne (common_unique _ _ hk σ τ
    (Finset.mem_filter.mp hzσ).2 (Finset.mem_filter.mp hzτ).2)

/-- The iid space is partitioned into avoidance and the actual avoiding-pattern
cells, even when free coordinates coincide with each other or the anchors. -/
theorem card_sample_partition {m n : ℕ} (hm : 0 < m) (a b : Fin n) :
    (Finset.univ.filter (SampleAvoid hm a b)).card +
      (∑ k ∈ Finset.Icc 2 m, ∑ σ ∈ PermutationAvoidanceCovariance.avoiding k,
        (Finset.univ.filter (fun z => ∃ hk : k ≤ m,
          Common (sampledLeft hm a z) (sampledRight hm b z) hk σ)).card) =
      n ^ (2 * (m - 1)) := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (2 * (m - 1)) → Fin n)))
    (p := SampleAvoid hm a b)
  rw [card_nonavoid hm a b] at hsplit
  have hcells : (∑ k ∈ Finset.Icc 2 m,
      (Finset.univ.filter (fun z => ∃ hk : k ≤ m,
        A (sampledLeft hm a z) (sampledRight hm b z) hk)).card) =
      ∑ k ∈ Finset.Icc 2 m, ∑ σ ∈ PermutationAvoidanceCovariance.avoiding k,
        (Finset.univ.filter (fun z => ∃ hk : k ≤ m,
          Common (sampledLeft hm a z) (sampledRight hm b z) hk σ)).card := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkm := (Finset.mem_Icc.mp hk).2
    simp only [exists_prop_of_true hkm]
    exact card_earliest_patterns hm a b hkm
  rw [hcells] at hsplit
  simpa using hsplit

/-- Independent left and right anchored assignments have the product of the
paid binomial counts; no distinctness between the two words is imposed. -/
theorem card_independent_anchors {n k : ℕ} (i j : Fin k) (a b : Fin n)
    (σ : Equiv.Perm (Fin k)) :
    Nat.card ({f : Fin k ↪ Fin n // f i = a ∧
      PermutationBoundaryStandardization.rank f = σ} ×
      {g : Fin k ↪ Fin n // g j = b ∧
        PermutationBoundaryStandardization.rank g = σ}) =
      (Nat.choose a.val (σ i).val *
        Nat.choose (n - 1 - a.val) (k - 1 - (σ i).val)) *
      (Nat.choose b.val (σ j).val *
        Nat.choose (n - 1 - b.val) (k - 1 - (σ j).val)) := by
  rw [Nat.card_prod, card_anchored_pattern, card_anchored_pattern]

/-- The normalized iid avoidance mass is one minus the disjoint common-pattern
cell masses. This is the exact reduction before free-coordinate counting. -/
theorem normalized_sample_partition {m n : ℕ} (hm : 2 ≤ m) (hn : 2 * m ≤ n)
    (a b : Fin n) :
    ((Finset.univ.filter (SampleAvoid (by omega : 0 < m) a b)).card : ℝ) /
        (n : ℝ) ^ (2 * (m - 1)) =
      1 - ((∑ k ∈ Finset.Icc 2 m,
        ∑ σ ∈ PermutationAvoidanceCovariance.avoiding k,
          (Finset.univ.filter (fun z => ∃ hk : k ≤ m,
            Common (sampledLeft (by omega : 0 < m) a z)
              (sampledRight (by omega : 0 < m) b z) hk σ)).card : ℕ) : ℝ) /
        (n : ℝ) ^ (2 * (m - 1)) := by
  have hpart := card_sample_partition (by omega : 0 < m) a b
  have hcast := congrArg (fun x : ℕ => (x : ℝ)) hpart
  push_cast at hcast ⊢
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hpow : (n : ℝ) ^ (2 * (m - 1)) ≠ 0 := ne_of_gt (pow_pos hnpos _)
  apply (div_eq_iff hpow).mpr
  field_simp
  nlinarith [hcast]

example : 2 ≤ (2 : ℕ) ∧ 2 * 2 ≤ (4 : ℕ) ∧
    Nonempty (Fin (2 * (2 - 1)) → Fin 4) := by
  exact ⟨by decide, by decide, ⟨fun _ => 0⟩⟩

end FiniteIidPatternRepair
