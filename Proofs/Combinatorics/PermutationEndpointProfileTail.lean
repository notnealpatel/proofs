import Combinatorics.PermutationEndpointProfileReversal

set_option autoImplicit false

namespace PermutationEndpointProfile

open PermutationOverlapBound PermutationEndpointCounting PermutationEndpointOverlapTail

attribute [local instance] Classical.propDecidable

/-- Actual permutations avoiding exactly lengths from two up to the cutoff. -/
noncomputable def shortAvoidFinset {n : ℕ} [NeZero n] (K : ℕ) (q a b : Fin n) :
    Finset (FixedTwo (0 : Fin n) q a b) :=
  Finset.univ.filter (fun π => ∀ k, 2 ≤ k → k < K → ∀ hkn : k < n, ¬ Overlap hkn π.val)

example {n : ℕ} [NeZero n] (q a b : Fin n) :
    shortAvoidFinset 2 q a b = Finset.univ := by
  ext π
  simp only [shortAvoidFinset, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  intro k hk hk2
  omega

/-- The full actual avoidance event inside its conditioning fiber. -/
noncomputable def fullAvoidFinset {n : ℕ} [NeZero n] (q a b : Fin n) :
    Finset (FixedTwo (0 : Fin n) q a b) :=
  Finset.univ.filter (fun π => ∀ k, 2 ≤ k → ∀ hkn : k < n, ¬ Overlap hkn π.val)

example {n : ℕ} [NeZero n] (q a b : Fin n) :
    fullAvoidFinset q a b = shortAvoidFinset n q a b := by
  ext π
  simp only [fullAvoidFinset, shortAvoidFinset, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · intro h k hk _ hkn
    exact h k hk hkn
  · intro h k hk hkn
    exact h k hk hkn hkn

/-- Counting the full finite event gives exactly the established actual event count. -/
theorem card_fullAvoidFinset {n : ℕ} [NeZero n] (q a b : Fin n) :
    (fullAvoidFinset q a b).card =
      Fintype.card (PermutationMixedEndpointBound.AvoidTwo q a b) := by
  classical
  let e : ↥(fullAvoidFinset q a b) ≃ PermutationMixedEndpointBound.AvoidTwo q a b :=
    { toFun := fun π => ⟨π.val.val, π.val.property, by
        simpa only [fullAvoidFinset, Finset.mem_filter, Finset.mem_univ, true_and]
          using π.property⟩
      invFun := fun π => ⟨⟨π.val, π.property.1⟩, by
        simpa only [fullAvoidFinset, Finset.mem_filter, Finset.mem_univ, true_and]
          using π.property.2⟩
      left_inv := by intro π; rfl
      right_inv := by intro π; rfl }
  exact (Fintype.card_coe _).symm.trans (Fintype.card_congr e)

/-- Every fully avoiding permutation avoids each truncated collection of lengths. -/
theorem fullAvoidFinset_subset_short {n : ℕ} [NeZero n] (K : ℕ) (q a b : Fin n) :
    fullAvoidFinset q a b ⊆ shortAvoidFinset K q a b := by
  intro π hπ
  simp only [fullAvoidFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hπ
  simp only [shortAvoidFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  intro k hk _ hkn
  exact hπ k hk hkn

/-- A permutation surviving truncation but not full avoidance has an actual
long overlap, with precisely the existing `[K,n)` tail convention. -/
theorem short_sdiff_full_subset_long {n : ℕ} [NeZero n] (K : ℕ) (q a b : Fin n) :
    shortAvoidFinset K q a b \ fullAvoidFinset q a b ⊆ longOverlapTwoFinset K q a b := by
  intro π hπ
  obtain ⟨hs, hf⟩ := Finset.mem_sdiff.mp hπ
  simp only [shortAvoidFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hs
  simp only [fullAvoidFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hf
  push Not at hf
  obtain ⟨k, hk, hkn, hov⟩ := hf
  apply (mem_longOverlapTwoFinset K q a b π).mpr
  refine ⟨k, ?_, hkn, hov⟩
  by_contra h
  exact hs k hk (by omega) hkn hov

/-- Actual truncated conditional avoidance fraction. No equal-label or invalid
input extension is used in this fiber-based definition. -/
noncomputable def shortFraction {n : ℕ} [NeZero n] (K : ℕ) (q a b : Fin n) : ℝ :=
  (shortAvoidFinset K q a b).card / Fintype.card (FixedTwo (0 : Fin n) q a b)

example {n : ℕ} [NeZero n] (K : ℕ) (q a b : Fin n) :
    shortFraction K q a b =
      (shortAvoidFinset K q a b).card / (Fintype.card (FixedTwo (0 : Fin n) q a b) : ℝ) := rfl

/-- The actual truncated-minus-full fraction lies between zero and the uniform
factorial tail. Distinct prescribed labels keep the denominator nonzero. -/
theorem shortFraction_sub_actual_bounds {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    (K : ℕ) (hK : 3 ≤ K) (q : Fin n) (hq : q.val + 1 = n)
    (a b : Fin n) (hab : a ≠ b) :
    0 ≤ shortFraction K q a b -
      (Fintype.card (PermutationMixedEndpointBound.AvoidTwo q a b) : ℝ) /
        Fintype.card (FixedTwo (0 : Fin n) q a b) ∧
    shortFraction K q a b -
      (Fintype.card (PermutationMixedEndpointBound.AvoidTwo q a b) : ℝ) /
        Fintype.card (FixedTwo (0 : Fin n) q a b) ≤ 6 / (K / 3).factorial := by
  classical
  have hsub := fullAvoidFinset_subset_short K q a b
  have hc := Finset.card_sdiff_add_card_eq_card hsub
  have hle := Finset.card_le_card (short_sdiff_full_subset_long K q a b)
  have hreal : ((shortAvoidFinset K q a b).card : ℝ) -
      (fullAvoidFinset q a b).card =
      ((shortAvoidFinset K q a b \ fullAvoidFinset q a b).card : ℝ) := by
    have hcR : ((shortAvoidFinset K q a b \ fullAvoidFinset q a b).card : ℝ) +
        (fullAvoidFinset q a b).card = (shortAvoidFinset K q a b).card := by
      exact_mod_cast hc
    linarith
  rw [shortFraction, ← card_fullAvoidFinset, ← sub_div, hreal]
  constructor
  · positivity
  · calc
      _ ≤ (longOverlapTwoFinset K q a b).card /
          (Fintype.card (FixedTwo (0 : Fin n) q a b) : ℝ) :=
        div_le_div_of_nonneg_right (by exact_mod_cast hle) (by positivity)
      _ ≤ _ := longOverlapTwo_fraction_le hn K hK q hq a b hab

/-- Actual truncation fractions are nonnegative. -/
theorem shortFraction_nonneg {n : ℕ} [NeZero n] (K : ℕ) (q a b : Fin n) :
    0 ≤ shortFraction K q a b := by
  unfold shortFraction
  positivity

/-- Every truncated conditional avoidance fraction is at most one. -/
theorem shortFraction_le_one {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (K : ℕ) (q : Fin n) (hq : q.val + 1 = n) (a b : Fin n) (hab : a ≠ b) :
    shortFraction K q a b ≤ 1 := by
  have hpq : (0 : Fin n) ≠ q := by
    intro he
    have hv := congrArg Fin.val he
    change 0 = q.val at hv
    omega
  letI := fixedTwo_nonempty 0 q a b hpq hab
  have hd : (0 : ℝ) < Fintype.card (FixedTwo (0 : Fin n) q a b) := by
    exact_mod_cast Fintype.card_pos
  apply (div_le_one hd).mpr
  exact_mod_cast (Finset.card_le_card (Finset.subset_univ (shortAvoidFinset K q a b)))

/-- Increasing the cutoff only removes actual permutations. -/
theorem shortFraction_antitone {n : ℕ} [NeZero n] {K J : ℕ} (hKJ : K ≤ J)
    (q a b : Fin n) : shortFraction J q a b ≤ shortFraction K q a b := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro π hπ
  simp only [shortAvoidFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hπ ⊢
  intro k hk hkK hkn
  exact hπ k hk (lt_of_lt_of_le hkK hKJ) hkn

/-- Position reversal gives an equivalence of actual truncated terminal events. -/
noncomputable def shortReverseEquiv {n : ℕ} [NeZero n] (K : ℕ) (a b : Fin n) :
    ↥(shortAvoidFinset K (0 : Fin n).rev a b) ≃
      ↥(shortAvoidFinset K (0 : Fin n).rev b a) where
  toFun π := ⟨fixedTwoReverseEquiv a b π.val, by
    have hπ := π.property
    simp only [shortAvoidFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hπ ⊢
    intro k hk hkK hkn hov
    exact hπ k hk hkK hkn ((overlap_reversePositions_iff hkn π.val.val).mp hov)⟩
  invFun π := ⟨fixedTwoReverseEquiv b a π.val, by
    have hπ := π.property
    simp only [shortAvoidFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hπ ⊢
    intro k hk hkK hkn hov
    exact hπ k hk hkK hkn ((overlap_reversePositions_iff hkn π.val.val).mp hov)⟩
  left_inv π := by
    apply Subtype.ext
    apply Subtype.ext
    exact reversePositions_involutive π.val.val
  right_inv π := by
    apply Subtype.ext
    apply Subtype.ext
    exact reversePositions_involutive π.val.val

example (π : ↥(shortAvoidFinset 2 (1 : Fin 2) 0 1)) :
    (shortReverseEquiv 2 0 1 π).val.val = reversePositions π.val.val := rfl

/-- Actual truncated conditional fractions are symmetric in the two labels. -/
theorem shortFraction_symm {n : ℕ} [NeZero n] (K : ℕ) (a b : Fin n) :
    shortFraction K (0 : Fin n).rev a b = shortFraction K (0 : Fin n).rev b a := by
  have hc : (shortAvoidFinset K (0 : Fin n).rev a b).card =
      (shortAvoidFinset K (0 : Fin n).rev b a).card := by
    simpa only [Fintype.card_coe] using Fintype.card_congr (shortReverseEquiv K a b)
  unfold shortFraction
  rw [hc, Fintype.card_congr (fixedTwoReverseEquiv a b)]

/-- On every valid input the actual totalized fraction has the same uniform
truncated-minus-full bound; invalid and equal labels are not used. -/
theorem shortFraction_sub_F_bounds {n a b : ℕ} [NeZero n] (hn : 3 ≤ n)
    (K : ℕ) (hK : 3 ≤ K) (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    0 ≤ shortFraction K ⟨n - 1, by omega⟩ ⟨a, ha⟩ ⟨b, hb⟩ -
      PermutationSameEdgeLimit.F n a b ∧
    shortFraction K ⟨n - 1, by omega⟩ ⟨a, ha⟩ ⟨b, hb⟩ -
      PermutationSameEdgeLimit.F n a b ≤ 6 / (K / 3).factorial := by
  rw [PermutationSameEdgeLimit.F_eq_actual (by omega) ha hb hab]
  exact shortFraction_sub_actual_bounds hn K hK _ (by dsimp; omega) _ _
    (fun he => hab (congrArg Fin.val he))

end PermutationEndpointProfile
