import Combinatorics.PermutationOppositeTripleLongTail

/-!
# Actual-event truncation on an opposite-corner triple

This module bounds the difference between actual all-overlap avoidance and
avoidance of lengths `2 ≤ k < K`, uniformly over the low triple
`π 0 = a`, `π 1 = r < a`, `π (n - 1) = h > a`. In particular length two is
NOT discarded: the prescribed triple does not rule it out.

The intended research target remains the UNPROVED first-order law
`n * PermutationSameEdgeLimit.F n a (n - 1 - b) → (a + b) * C`.
No convergence is assumed or proved here. The unpaid bridge is the precise
finite-window anchored standardization / `C_K` law, followed by its connection
to the fixed-corner first-order normalization. This theorem only discharges
the uniform conditional tail obligation, using actual finite permutation events.
-/

set_option autoImplicit false

namespace PermutationOppositeCornerTruncation

open PermutationOrderCounting PermutationOverlapBound PermutationEndpointCounting
open PermutationEndpointZeroTwoExact PermutationOppositeTripleBounds
open PermutationOppositeTripleLongTail

attribute [local instance] Classical.propDecidable

/-- In the actual three-anchor fiber, all avoidance is at most truncated
avoidance, and the difference of their cardinal fractions is bounded by the
short factorial tail plus the whole long-overlap bound. Both fractions use
the positive cardinality of the same fiber, not independent surrogate events. -/
theorem actual_avoidance_truncation_bound {n K D : ℕ}
    (hK : 4 ≤ K) (hKn : 2 * K ≤ n) (hD : 2 ≤ D) (hDn : 2 * D < n)
    (a r h : Fin n) (hra : r < a) (hah : a < h) :
    let T := FixedThree (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩
      ⟨n - 1, by omega⟩ a r h
    let A : Finset T := Finset.univ.filter (fun π =>
      ∀ k, 2 ≤ k → ∀ hk : k < n, ¬ Overlap hk π.val)
    let W : Finset T := Finset.univ.filter (fun π =>
      ∀ k, 2 ≤ k → k < K → ∀ hk : k < n, ¬ Overlap hk π.val)
    (A.card : ℝ) / Fintype.card T ≤ (W.card : ℝ) / Fintype.card T ∧
      (W.card : ℝ) / Fintype.card T - (A.card : ℝ) / Fintype.card T ≤
        2 / ((K - 1).factorial : ℝ) +
          ((2 * (D - 1) : ℝ) / (((n - 3) / D).factorial : ℝ) +
            2 / ((D + 1).factorial : ℝ)) := by
  classical
  dsimp only
  let T := FixedThree (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩
    ⟨n - 1, by omega⟩ a r h
  let A : Finset T := Finset.univ.filter (fun π =>
    ∀ k, 2 ≤ k → ∀ hk : k < n, ¬ Overlap hk π.val)
  let W : Finset T := Finset.univ.filter (fun π =>
    ∀ k, 2 ≤ k → k < K → ∀ hk : k < n, ¬ Overlap hk π.val)
  change (A.card : ℝ) / Fintype.card T ≤ (W.card : ℝ) / Fintype.card T ∧ _
  let E (j : ℕ) : Finset T := Finset.univ.filter (fun π =>
    ∃ hs : 2 * (j + 1) ≤ n, Overlap (by omega : j + 1 < n) π.val)
  let S := (Finset.Ico (K - 1) (n - 1)).biUnion E
  let L : Finset T := Finset.univ.filter (fun π =>
    ∃ d : ℕ, ∃ hd : 1 ≤ d, ∃ hl : 2 * d < n,
      Overlap (by omega : n - d < n) π.val)
  have hT : 0 < Fintype.card T := card_triple_pos (by omega) a r h hra hah
  have hTR : (0 : ℝ) < Fintype.card T := by exact_mod_cast hT
  have hAW : A ⊆ W := by
    intro π hπ
    simp only [A, W, Finset.mem_filter, Finset.mem_univ, true_and] at *
    intro k hk _ hkn
    exact hπ k hk hkn
  have hcover : W ⊆ A ∪ (S ∪ L) := by
    intro π hπ
    by_cases hall : π ∈ A
    · exact Finset.mem_union_left _ hall
    · have hw : ∀ k, 2 ≤ k → k < K → ∀ hk : k < n, ¬ Overlap hk π.val := by
        simpa only [W, Finset.mem_filter, Finset.mem_univ, true_and] using hπ
      have hnall : ¬ ∀ k, 2 ≤ k → ∀ hk : k < n, ¬ Overlap hk π.val := by
        simpa only [A, Finset.mem_filter, Finset.mem_univ, true_and] using hall
      push Not at hnall
      obtain ⟨k, hk2, hkn, hov⟩ := hnall
      have hkK : K ≤ k := by
        by_contra hh
        exact hw k hk2 (by omega) hkn hov
      apply Finset.mem_union_right
      by_cases hs : 2 * k ≤ n
      · apply Finset.mem_union_left
        apply Finset.mem_biUnion.mpr
        refine ⟨k - 1, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
        have he : k - 1 + 1 = k := by omega
        simp only [E, Finset.mem_filter, Finset.mem_univ, true_and, he]
        exact ⟨hs, hov⟩
      · apply Finset.mem_union_right
        have hd : 1 ≤ n - k := by omega
        have hl : 2 * (n - k) < n := by omega
        have he : n - (n - k) = k := by omega
        simp only [L, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨n - k, hd, hl, ?_⟩
        simpa only [he] using hov
  have hE (j : ℕ) (hj : j ∈ Finset.Ico (K - 1) (n - 1)) :
      ((E j).card : ℝ) / Fintype.card T ≤ 1 / (j.factorial : ℝ) := by
    by_cases hs : 2 * (j + 1) ≤ n
    · have hj3 : 3 ≤ j + 1 := by have hh := (Finset.mem_Ico.mp hj).1; omega
      have he : (E j).card =
          Fintype.card {π : T // Overlap (by omega : j + 1 < n) π.val} := by
        rw [Fintype.card_subtype]
        congr 1
        ext π
        simp only [E, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun hh => hh.choose_spec, fun hh => ⟨hs, hh⟩⟩
      have hc := card_short_overlap_mul_factorial_le hj3 hs a r h
      have hjsub : j + 1 - 1 = j := by omega
      rw [hjsub, ← he] at hc
      have hc' : (E j).card * j.factorial ≤ 1 * Fintype.card T := by simpa using hc
      simpa only [Nat.cast_one] using
        fraction_le_of_mul_le hT (Nat.factorial_pos _) hc'
    · have he : E j = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro π hπ
        exact hs ((Finset.mem_filter.mp hπ).2.choose)
      rw [he, Finset.card_empty, Nat.cast_zero, zero_div]
      positivity
  have hS : (S.card : ℝ) / Fintype.card T ≤ 2 / ((K - 1).factorial : ℝ) := by
    have hc : (S.card : ℝ) ≤ ∑ j ∈ Finset.Ico (K - 1) (n - 1), ((E j).card : ℝ) := by
      exact_mod_cast (show S.card ≤ ∑ j ∈ Finset.Ico (K - 1) (n - 1), (E j).card from
        Finset.card_biUnion_le)
    calc
      _ ≤ (∑ j ∈ Finset.Ico (K - 1) (n - 1), ((E j).card : ℝ)) /
          Fintype.card T := div_le_div_of_nonneg_right hc (le_of_lt hTR)
      _ = ∑ j ∈ Finset.Ico (K - 1) (n - 1), ((E j).card : ℝ) / Fintype.card T := by
        rw [Finset.sum_div]
      _ ≤ ∑ j ∈ Finset.Ico (K - 1) (n - 1), 1 / (j.factorial : ℝ) :=
        Finset.sum_le_sum hE
      _ ≤ 2 / ((K - 1).factorial : ℝ) := by
        have ht := sum_reciprocal_factorial_tail (K - 2) (n - 1) (by omega)
        have he : K - 2 + 1 = K - 1 := by omega
        simpa only [he] using ht
  have hL : (L.card : ℝ) / Fintype.card T ≤
      (2 * (D - 1) : ℝ) / (((n - 3) / D).factorial : ℝ) +
        2 / ((D + 1).factorial : ℝ) := by
    have ht := whole_long_overlap_ratio_le hD hDn a r h hra hah
    rw [Fintype.card_subtype] at ht
    exact ht
  have hc : W.card ≤ A.card + (S.card + L.card) :=
    (Finset.card_le_card hcover).trans
      ((Finset.card_union_le A (S ∪ L)).trans
        (Nat.add_le_add_left (Finset.card_union_le S L) _))
  have hcR : (W.card : ℝ) ≤ (A.card : ℝ) + ((S.card : ℝ) + (L.card : ℝ)) := by
    exact_mod_cast hc
  have hfrac := div_le_div_of_nonneg_right hcR (le_of_lt hTR)
  rw [add_div, add_div] at hfrac
  constructor
  · exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hAW)
      (le_of_lt hTR)
  · linarith

/-- On the concrete low triple `(1,0,n-1)`, length two is impossible:
the prefix descends, whereas a suffix ending at the maximal label ascends. -/
theorem not_overlap_two_max_last {n : ℕ} (hn : 4 ≤ n)
    (π : FixedThree (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩
      ⟨n - 1, by omega⟩ ⟨1, by omega⟩ ⟨0, by omega⟩ ⟨n - 1, by omega⟩) :
    ¬ Overlap (by omega : 2 < n) π.val := by
  intro hov
  have hne : π.val ⟨n - 2, by omega⟩ ≠ π.val ⟨n - 1, by omega⟩ := by
    intro he
    have he' := congrArg Fin.val (π.val.injective he)
    change n - 2 = n - 1 at he'
    omega
  have hlt : π.val ⟨n - 2, by omega⟩ < π.val ⟨n - 1, by omega⟩ := by
    rw [π.property.2] at *
    have hb := (π.val ⟨n - 2, by omega⟩).isLt
    change (π.val ⟨n - 2, by omega⟩).val < n - 1
    have hv : (π.val ⟨n - 2, by omega⟩).val ≠ n - 1 := by
      intro he
      exact hne (Fin.ext he)
    omega
  have hshift : 1 + (n - 2) = n - 1 := by omega
  have hp := (hov (0 : Fin 2) 1).mpr (by simpa only [Fin.val_zero, Fin.val_one, Nat.zero_add, hshift] using hlt)
  change π.val ⟨0, by omega⟩ < π.val ⟨1, by omega⟩ at hp
  rw [π.property.1.1, π.property.1.2] at hp
  change 1 < 0 at hp
  omega

/-- The fixed corner `(1,n-1)` has a genuinely nonzero first-order lower
bound. This is an actual avoidance fraction, not a surrogate survival law;
it does not assert the unpaid universal constant limit. -/
theorem one_div_eight_mul_sub_le_F {n : ℕ} (hn : 24 ≤ n) :
    1 / (8 * ((n : ℝ) - 2)) ≤ PermutationSameEdgeLimit.F n 1 (n - 1) := by
  classical
  letI : NeZero n := ⟨by omega⟩
  let a : Fin n := ⟨1, by omega⟩
  let r : Fin n := ⟨0, by omega⟩
  let h : Fin n := ⟨n - 1, by omega⟩
  let T := FixedThree (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ ⟨n - 1, by omega⟩ a r h
  let A : Finset T := Finset.univ.filter (fun π =>
    ∀ k, 2 ≤ k → ∀ hk : k < n, ¬ Overlap hk π.val)
  let W : Finset T := Finset.univ.filter (fun π =>
    ∀ k, 2 ≤ k → k < 5 → ∀ hk : k < n, ¬ Overlap hk π.val)
  let B (k : ℕ) (hk : k < n) : Finset T :=
    Finset.univ.filter (fun π => Overlap hk π.val)
  have hT : 0 < Fintype.card T := card_triple_pos (by omega) a r h (by change 0 < 1; omega) (by change 1 < n - 1; omega)
  have hTR : (0 : ℝ) < Fintype.card T := by exact_mod_cast hT
  have hB (k : ℕ) (hk : 3 ≤ k) (hs : 2 * k ≤ n) :
      ((B k (by omega)).card : ℝ) / Fintype.card T ≤ 1 / ((k - 1).factorial : ℝ) := by
    have hc := card_short_overlap_mul_factorial_le hk hs a r h
    rw [Fintype.card_subtype] at hc
    have hc' : (B k (by omega)).card * (k - 1).factorial ≤ 1 * Fintype.card T := by
      simpa only [one_mul] using hc
    simpa only [Nat.cast_one] using fraction_le_of_mul_le hT (Nat.factorial_pos _) hc'
  have hcover : (Finset.univ : Finset T) ⊆ W ∪ (B 3 (by omega) ∪ B 4 (by omega)) := by
    intro π _
    by_cases hw : π ∈ W
    · exact Finset.mem_union_left _ hw
    · have hb : ¬ ∀ k, 2 ≤ k → k < 5 → ∀ hk : k < n, ¬ Overlap hk π.val := by
        simpa only [W, Finset.mem_filter, Finset.mem_univ, true_and] using hw
      push Not at hb
      obtain ⟨k, hk, hk5, hkn, hov⟩ := hb
      have hkne : k ≠ 2 := by
        intro he
        subst k
        exact not_overlap_two_max_last (n := n) (by omega) π hov
      have hcases : k = 3 ∨ k = 4 := by omega
      apply Finset.mem_union_right
      rcases hcases with he | he <;> subst k
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hov⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hov⟩)
  have hc : Fintype.card T ≤ W.card + ((B 3 (by omega)).card + (B 4 (by omega)).card) := by
    have hc0 := (Finset.card_le_card hcover).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_left (Finset.card_union_le _ _) _))
    simpa only [Finset.card_univ] using hc0
  have hcR : (Fintype.card T : ℝ) ≤ (W.card : ℝ) +
      ((B 3 (by omega)).card : ℝ) + ((B 4 (by omega)).card : ℝ) := by exact_mod_cast (by simpa only [Nat.add_assoc] using hc : Fintype.card T ≤ W.card + (B 3 (by omega)).card + (B 4 (by omega)).card)
  have hwdiv := div_le_div_of_nonneg_right hcR (le_of_lt hTR)
  rw [div_self (ne_of_gt hTR), add_div, add_div] at hwdiv
  have hb3 := hB 3 (by omega) (by omega)
  have hb4 := hB 4 (by omega) (by omega)
  norm_num at hb3 hb4
  have hW : (1 : ℝ) / 3 ≤ (W.card : ℝ) / Fintype.card T := by linarith
  have htail := (actual_avoidance_truncation_bound (n := n) (K := 5) (D := 3)
    (by omega) (by omega) (by omega) (by omega) a r h (by change 0 < 1; omega) (by change 1 < n - 1; omega)).2
  change (W.card : ℝ) / Fintype.card T - (A.card : ℝ) / Fintype.card T ≤ _ at htail
  have hfacN : 7 ≤ (n - 3) / 3 := (Nat.le_div_iff_mul_le (by decide)).mpr (by omega)
  have hfac : (5040 : ℝ) ≤ (((n - 3) / 3).factorial : ℝ) := by
    exact_mod_cast (show 5040 ≤ ((n - 3) / 3).factorial from Nat.factorial_le hfacN)
  have hsmall : (4 : ℝ) / (((n - 3) / 3).factorial : ℝ) ≤ 1 / 100 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (((n - 3) / 3).factorial : ℝ))).mpr
    linarith
  norm_num at htail
  have hA : (1 : ℝ) / 8 ≤ (A.card : ℝ) / Fintype.card T := by linarith
  let U := PermutationMixedEndpointBound.AvoidTwo (⟨n - 1, by omega⟩ : Fin n) a h
  let f : {π // π ∈ A} → U := fun π =>
    ⟨π.val.val, ⟨π.val.property.1.1, π.val.property.2⟩,
      (Finset.mem_filter.mp π.property).2⟩
  have hf : Function.Injective f := by
    intro π ρ he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : U => z.val) he
  have hAU : A.card ≤ Fintype.card U := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf
  have heq : Fintype.card T * (n - 2) =
      Fintype.card (FixedTwo (0 : Fin n) ⟨n - 1, by omega⟩ a h) := by
    have ht := card_fixedThree_mul (0 : Fin n) ⟨n - 1, by omega⟩ ⟨1, by omega⟩ a h r
      (by intro he; have hv := congrArg Fin.val he; simp at hv)
      (by intro he; have hv := congrArg Fin.val he; change 1 = n - 1 at hv; omega)
      (by dsimp [a, h]; intro he; have hv := congrArg Fin.val he; dsimp at hv; omega)
      (by intro he; have hv := congrArg Fin.val he; change 0 = 1 at hv; omega) (by dsimp [r, h]; intro he; have hv := congrArg Fin.val he; dsimp at hv; omega)
    have hcT : Fintype.card T = Fintype.card
        (FixedThree (0 : Fin n) ⟨n - 1, by omega⟩ ⟨1, by omega⟩ a h r) := by
      apply Fintype.card_congr
      exact {
        toFun := fun π => ⟨π.val, ⟨π.property.1.1, π.property.2⟩, π.property.1.2⟩
        invFun := fun π => ⟨π.val, ⟨π.property.1.1, π.property.2⟩, π.property.1.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [hcT]
    exact ht
  rw [PermutationSameEdgeLimit.F_eq_actual (by omega) (by omega) (by omega) (by omega)]
  change 1 / (8 * ((n : ℝ) - 2)) ≤ (Fintype.card U : ℝ) / _
  rw [← heq, Nat.cast_mul, Nat.cast_sub (by omega : 2 ≤ n), Nat.cast_ofNat]
  have hnR : (0 : ℝ) < (n : ℝ) - 2 := by
    have hh : (24 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hAU_R : (A.card : ℝ) ≤ Fintype.card U := by exact_mod_cast hAU
  have hAcount : (Fintype.card T : ℝ) / 8 ≤ A.card := by
    have hc := (le_div_iff₀ hTR).mp hA
    linarith
  apply (div_le_div_iff₀ (by positivity) (mul_pos hTR hnR)).mpr
  nlinarith

example : Nonempty (FixedThree (0 : Fin 24) 1 23 1 0 23) := by
  exact ⟨⟨Equiv.swap 0 1, by decide, by decide⟩⟩

example : 24 ≤ 24 := by decide

example : Nonempty (FixedThree (0 : Fin 8) 1 7 1 0 7) := by
  exact ⟨⟨Equiv.swap 0 1, by decide, by decide⟩⟩

example : 4 ≤ 4 ∧ 2 * 4 ≤ 8 ∧ 2 ≤ 2 ∧ 2 * 2 < 8 ∧
    (0 : Fin 8) < 1 ∧ (1 : Fin 8) < 7 := by decide

end PermutationOppositeCornerTruncation
