import Combinatorics.PermutationFiniteWordPartition
import Combinatorics.PermutationFirstRankRenewal
import Combinatorics.PermutationEndpointProfileTail
import Combinatorics.PermutationAvoidanceCovariance

set_option autoImplicit false

noncomputable section

namespace PermutationFiniteIidEndpointLaw

open scoped BigOperators
open PermutationFiniteWordPartition

attribute [local instance] Classical.propDecidable

/-- The two binomial counts for an anchored injective word, normalized by the
number of iid assignments to its other positions. -/
def anchorWeight {n k : ℕ} (a : Fin n) (r : Fin k) : ℝ :=
  ((Nat.choose a.val r.val : ℝ) *
    Nat.choose (n - 1 - a.val) (k - 1 - r.val)) / (n : ℝ) ^ (k - 1)

example : anchorWeight (0 : Fin 100) (0 : Fin 2) = 99 / 100 := by
  norm_num [anchorWeight, Nat.choose_one_right]

/-- The iid weight of a specified common boundary pattern, with the right
anchor at the last physical position. The empty pattern has weight zero. -/
def patternWeight {n k : ℕ} (a b : Fin n) (σ : Equiv.Perm (Fin k)) : ℝ :=
  if hk : 0 < k then
    anchorWeight a (σ ⟨0, hk⟩) * anchorWeight b (σ ⟨k - 1, by omega⟩)
  else 0

example : patternWeight (0 : Fin 100) (99 : Fin 100) (Equiv.refl (Fin 2)) =
    (99 / 100 : ℝ) ^ 2 := by
  norm_num [patternWeight, anchorWeight, Nat.choose_one_right]

/-- The explicit sum over actual fully avoiding permutation patterns; no
alternative abstract survival event is used in this definition. -/
def patternSum {n : ℕ} (m : ℕ) (a b : Fin n) : ℝ :=
  1 - ∑ k ∈ Finset.Icc 2 m,
    ∑ σ ∈ PermutationAvoidanceCovariance.avoiding k, patternWeight a b σ

example (a b : Fin 100) : patternSum 1 a b = 1 := by
  simp [patternSum]

/-- The iid sample is good when all its free labels are distinct and avoid
both prescribed endpoint labels. -/
def Good {m n : ℕ} (a b : Fin n) (z : Fin (2 * (m - 1)) → Fin n) : Prop :=
  Function.Injective z ∧ ∀ i, z i ≠ a ∧ z i ≠ b

example : Good (m := 2) (0 : Fin 4) (3 : Fin 4)
    (fun i => ⟨i.val + 1, by omega⟩) := by
  constructor
  · intro i j h
    apply Fin.ext
    have hv := congrArg Fin.val h
    dsimp at hv
    omega
  · intro i
    constructor <;> intro h <;> have hv := congrArg Fin.val h <;> dsimp at hv <;> omega

/-- No nontrivial common pattern occurs in the sampled anchored words. -/
def SampleAvoid {m n : ℕ} (hm : 0 < m) (a b : Fin n)
    (z : Fin (2 * (m - 1)) → Fin n) : Prop :=
  ¬ ∃ k, ∃ hk : k ≤ m, 2 ≤ k ∧
    B (sampledLeft hm a z) (sampledRight hm b z) hk

example (a b : Fin 100) (z : Fin 0 → Fin 100) :
    SampleAvoid (m := 1) (by decide) a b z := by
  rintro ⟨k, hk, htwo, _⟩
  omega

/-- The finite-word partition identifies the complement of sampled avoidance
with the disjoint earliest-agreement cells, without assuming `Good`. -/
theorem sampleAvoid_iff_no_earliest {m n : ℕ} (hm : 0 < m) (a b : Fin n)
    (z : Fin (2 * (m - 1)) → Fin n) :
    SampleAvoid hm a b z ↔ ¬ ∃ k, ∃ hk : k ≤ m, 2 ≤ k ∧
      A (sampledLeft hm a z) (sampledRight hm b z) hk := by
  exact not_congr (sampled_partition hm a b z)

/-- Elementary conditioning comparison with no reciprocal-good-probability
loss. Here `x` and `y` are the masses inside and outside the good event. -/
theorem conditioning_comparison (x y g N : ℝ) (hg : 0 < g) (hgN : g ≤ N)
    (hx : 0 ≤ x) (hxg : x ≤ g) (hy : 0 ≤ y) (hyN : y ≤ N - g) :
    |x / g - (x + y) / N| ≤ 1 - g / N := by
  have hN : 0 < N := lt_of_lt_of_le hg hgN
  have hNg : 0 ≤ N - g := sub_nonneg.mpr hgN
  apply abs_le.mpr
  constructor
  · have hxy : 0 ≤ x * (N - g) := mul_nonneg hx hNg
    have hyg : y * g ≤ (N - g) * g := mul_le_mul_of_nonneg_right hyN hg.le
    apply (mul_le_mul_iff_right₀ (mul_pos hg hN)).mp
    field_simp
    nlinarith
  · have hxmul : x * (N - g) ≤ g * (N - g) :=
      mul_le_mul_of_nonneg_right hxg hNg
    have hymul : 0 ≤ y * g := mul_nonneg hy hg.le
    apply (mul_le_mul_iff_right₀ (mul_pos hg hN)).mp
    field_simp
    nlinarith

example : 0 < (1 : ℝ) ∧ (1 : ℝ) ≤ 2 ∧
    0 ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ 1 ∧ 0 ≤ (1 : ℝ) ∧ (1 : ℝ) ≤ 2 - 1 := by
  norm_num

example : ((Finset.univ : Finset (Fin 1)).Nonempty) := by
  exact ⟨0, Finset.mem_univ 0⟩

/-- For any finite event and nonempty good event, conditioning changes its
uniform frequency by at most the frequency of the bad event. -/
theorem finite_conditioning_comparison {α : Type*} [Fintype α] [DecidableEq α]
    (E G : Finset α) (hG : G.Nonempty) :
    |((E ∩ G).card : ℝ) / G.card - (E.card : ℝ) / Fintype.card α| ≤
      1 - (G.card : ℝ) / Fintype.card α := by
  have hg : (0 : ℝ) < G.card := by exact_mod_cast Finset.card_pos.mpr hG
  have hgN : (G.card : ℝ) ≤ Fintype.card α := by
    exact_mod_cast Finset.card_le_univ G
  have hxg : ((E ∩ G).card : ℝ) ≤ G.card := by
    exact_mod_cast Finset.card_le_card Finset.inter_subset_right
  have hyN : ((E \ G).card : ℝ) ≤ (Fintype.card α : ℝ) - G.card := by
    have hs : E \ G ⊆ Finset.univ \ G := by
      intro x hx
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, (Finset.mem_sdiff.mp hx).2⟩
    have hc := Finset.card_le_card hs
    have he := Finset.card_sdiff_add_card_inter (Finset.univ : Finset α) G
    simp only [Finset.univ_inter, Finset.card_univ] at he
    have hr : ((Finset.univ \ G).card : ℝ) + G.card = Fintype.card α := by
      exact_mod_cast he
    have hl : ((E \ G).card : ℝ) ≤ (Finset.univ \ G).card := by
      exact_mod_cast hc
    linarith
  have he := Finset.card_sdiff_add_card_inter E G
  have heR : ((E \ G).card : ℝ) + (E ∩ G).card = E.card := by
    exact_mod_cast he
  have h := conditioning_comparison ((E ∩ G).card : ℝ) ((E \ G).card : ℝ)
    G.card (Fintype.card α) hg hgN (Nat.cast_nonneg _) hxg (Nat.cast_nonneg _) hyN
  rw [add_comm, heR] at h
  exact h

/-- The existing actual short-avoidance event is the complement of earliest
agreement on its two physical boundary words. -/
theorem actual_short_iff_no_earliest {m n : ℕ} [NeZero n]
    (hm : 2 ≤ m) (hn : 2 * m ≤ n) (q a b : Fin n)
    (π : PermutationEndpointCounting.FixedTwo (0 : Fin n) q a b) :
    π ∈ PermutationEndpointProfile.shortAvoidFinset (m + 1) q a b ↔
      ¬ ∃ k, ∃ hk : k ≤ m, 2 ≤ k ∧
        A (fun i => π.val (prefixEmbedding (by omega : m ≤ n) i))
          (fun i => π.val (suffix (by omega : m ≤ n) i)) hk := by
  rw [← not_congr (exists_B_iff_exists_A
    (fun i => π.val (prefixEmbedding (by omega : m ≤ n) i))
    (fun i => π.val (suffix (by omega : m ≤ n) i)))]
  simp only [PermutationEndpointProfile.shortAvoidFinset, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro h ⟨k, hk, htwo, hb⟩
    exact h k htwo (by omega) (by omega)
      ((B_boundary_permutation_iff π.val (by omega) hk (by omega)).mp hb)
  · intro h k htwo hkm hkn ho
    apply h
    refine ⟨k, by omega, htwo, ?_⟩
    exact (B_boundary_permutation_iff π.val (by omega) (by omega) hkn).mpr ho

/-- The adopted fixed-pattern count applies at either physical anchor position. -/
theorem card_anchored_pattern {n k : ℕ} (z : Fin k) (a : Fin n)
    (σ : Equiv.Perm (Fin k)) :
    Nat.card {f : Fin k ↪ Fin n // f z = a ∧
      PermutationBoundaryStandardization.rank f = σ} =
      Nat.choose a.val (σ z).val *
        Nat.choose (n - 1 - a.val) (k - 1 - (σ z).val) := by
  rw [PermutationFirstRankRenewal.card_fixed_pattern,
    PermutationFirstRankRenewal.card_ranked_subset]

end PermutationFiniteIidEndpointLaw
