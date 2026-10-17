import Sorry.PermutationOppositeTripleBounds

set_option autoImplicit false

namespace PermutationOppositeTripleLongTail

open PermutationOrderCounting PermutationOverlapBound PermutationEndpointCounting
open PermutationEndpointZeroTwoExact PermutationOppositeTripleBounds

attribute [local instance] Classical.propDecidable

/-- A deficit-one overlap cannot have the prescribed down-then-up triple. -/
theorem not_overlap_deficit_one {n : ℕ} (hn : 3 ≤ n) (a r b : Fin n)
    (hra : r < a) (hab : a < b)
    (π : FixedThree (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩
      ⟨n - 1, by omega⟩ a r b) :
    ¬ Overlap (by omega : n - 1 < n) π.val := by
  intro hov
  have hadj : ∀ j (hj : j + 1 < n),
      π.val ⟨j + 1, hj⟩ < π.val ⟨j, by omega⟩ := by
    intro j
    induction j with
    | zero =>
      intro hj
      simpa only [Nat.zero_add, π.property.1.1, π.property.1.2] using hra
    | succ j ih =>
      intro hj
      have hp := ih (by omega)
      have hc := (hov ⟨j + 1, by omega⟩ ⟨j, by omega⟩).mp hp
      have hs : n - (n - 1) = 1 := by omega
      simpa only [hs, Nat.succ_eq_add_one] using hc
  have hdec : ∀ j (hj : j < n), 1 ≤ j →
      π.val ⟨j, hj⟩ < π.val ⟨0, by omega⟩ := by
    intro j
    induction j with
    | zero => omega
    | succ j ih =>
      intro hj hjpos
      by_cases hz : j = 0
      · subst j
        exact hadj 0 hj
      · exact lt_trans (hadj j hj) (ih (by omega) (by omega))
  have hlast := hdec (n - 1) (by omega) (by omega)
  rw [π.property.1.1, π.property.2] at hlast
  exact (not_lt_of_gt hab) hlast

/-- Every finite reciprocal-factorial tail has the uniform bound used in the
long-overlap union estimate. -/
theorem sum_reciprocal_factorial_tail (D N : ℕ) (hD : 1 ≤ D) :
    (∑ d ∈ Finset.Ico (D + 1) N, (1 / (d.factorial : ℝ))) ≤
      2 / ((D + 1).factorial : ℝ) := by
  have step (d : ℕ) (hd : 1 ≤ d) :
      (1 / (d.factorial : ℝ)) ≤
        2 / (d.factorial : ℝ) - 2 / ((d + 1).factorial : ℝ) := by
    have hf : (0 : ℝ) < d.factorial := by exact_mod_cast Nat.factorial_pos d
    have hdR : (2 : ℝ) ≤ d + 1 := by exact_mod_cast (show 2 ≤ d + 1 by omega)
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp
    nlinarith
  have telescope : ∀ N, D + 1 ≤ N →
      (∑ d ∈ Finset.Ico (D + 1) N, (1 / (d.factorial : ℝ))) ≤
        2 / ((D + 1).factorial : ℝ) - 2 / (N.factorial : ℝ) := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => simp
    | succ N hN ih =>
      rw [Finset.sum_Ico_succ_top hN]
      have hs := step N (by omega)
      linarith
  by_cases hN : D + 1 ≤ N
  · have ht := telescope N hN
    have hz : (0 : ℝ) ≤ 2 / (N.factorial : ℝ) := by positivity
    linarith
  · have he : Finset.Ico (D + 1) N = ∅ := Finset.Ico_eq_empty_of_le (by omega)
    rw [he, Finset.sum_empty]
    positivity

/-- Three distinct labels at three distinct positions give a nonempty actual fiber. -/
theorem fixedThree_nonempty {n : ℕ} (p q s a r b : Fin n)
    (hpq : p ≠ q) (hsp : s ≠ p) (hsq : s ≠ q)
    (har : a ≠ r) (hba : b ≠ a) (hbr : b ≠ r) :
    Nonempty (FixedThree p q s a r b) := by
  obtain ⟨σ, hσp, hσq⟩ := fixedTwo_nonempty p q a r hpq har
  have hsa : σ s ≠ a := by
    intro he
    exact hsp (σ.injective (he.trans hσp.symm))
  have hsr : σ s ≠ r := by
    intro he
    exact hsq (σ.injective (he.trans hσq.symm))
  refine ⟨⟨σ.trans (Equiv.swap (σ s) b), ⟨?_, ?_⟩, ?_⟩⟩
  · change Equiv.swap (σ s) b (σ p) = a
    rw [hσp]
    exact Equiv.swap_apply_of_ne_of_ne hsa.symm hba.symm
  · change Equiv.swap (σ s) b (σ q) = r
    rw [hσq]
    exact Equiv.swap_apply_of_ne_of_ne hsr.symm hbr.symm
  · exact Equiv.swap_apply_left (σ s) b

/-- The actual opposite triple fiber has positive cardinality. -/
theorem card_triple_pos {n : ℕ} (hn : 3 ≤ n) (a r b : Fin n)
    (hra : r < a) (hab : a < b) :
    0 < Fintype.card (FixedThree (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩
      ⟨n - 1, by omega⟩ a r b) := by
  apply Fintype.card_pos_iff.mpr
  apply fixedThree_nonempty
  · intro he; have hv := congrArg Fin.val he; simp at hv
  · intro he; have hv := congrArg Fin.val he; simp only [Fin.mk.injEq] at he; omega
  · intro he; have hv := congrArg Fin.val he; simp only [Fin.mk.injEq] at he; omega
  · exact ne_of_gt hra
  · exact ne_of_gt hab
  · exact ne_of_gt (lt_trans hra hab)

/-- Residue-chain count in the actual three-anchor fiber. Remaining formal gap:
uniform relative-order counting for the free residue-chain positions, together
with the overlap-to-chain monotonicity bridge. -/
theorem card_residue_overlap_mul_factorial_le {n d : ℕ} (hd : 2 ≤ d)
    (hlong : 2 * d < n) (a r b : Fin n) :
    Fintype.card {π : FixedThree (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩
      ⟨n - 1, by omega⟩ a r b // Overlap (by omega : n - d < n) π.val} *
        ((n - 3) / d).factorial ≤
      2 * Fintype.card (FixedThree (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩
        ⟨n - 1, by omega⟩ a r b) := by
  sorry

/-- A cross-multiplied finite count bound gives a bound on its actual fraction
when the fiber and the factorial denominator are positive. -/
theorem fraction_le_of_mul_le {e t f c : ℕ} (ht : 0 < t) (hf : 0 < f)
    (hc : e * f ≤ c * t) : (e : ℝ) / t ≤ (c : ℝ) / f := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hfR : (0 : ℝ) < f := by exact_mod_cast hf
  apply (div_le_div_iff₀ htR hfR).mpr
  exact_mod_cast hc

/-- Whole long-overlap union in the actual opposite-triple fiber. The finite
union aggregation is explicit; the remaining dependency gap is precisely the
residue-chain counting lemma above. -/
theorem whole_long_overlap_ratio_le {n D : ℕ} (hD : 2 ≤ D)
    (hDn : 2 * D < n) (a r b : Fin n) (hra : r < a) (hab : a < b) :
    (Fintype.card {π : FixedThree (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩
      ⟨n - 1, by omega⟩ a r b //
        ∃ d : ℕ, ∃ hd : 1 ≤ d, ∃ hlong : 2 * d < n,
          Overlap (by omega : n - d < n) π.val} : ℝ) /
      (Fintype.card (FixedThree (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩
        ⟨n - 1, by omega⟩ a r b) : ℝ) ≤
      (2 * (D - 1) : ℝ) / (((n - 3) / D).factorial : ℝ) +
        2 / ((D + 1).factorial : ℝ) := by
  let T := FixedThree (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩
    ⟨n - 1, by omega⟩ a r b
  let E (d : ℕ) : Finset T := Finset.univ.filter (fun π =>
    ∃ hd : 2 ≤ d, ∃ hlong : 2 * d < n,
      Overlap (by omega : n - d < n) π.val)
  have hmem (d : ℕ) (π : T) : π ∈ E d ↔
      ∃ hd : 2 ≤ d, ∃ hlong : 2 * d < n,
        Overlap (by omega : n - d < n) π.val := by
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and]
  have hcard (d : ℕ) (hd : 2 ≤ d) (hlong : 2 * d < n) :
      (E d).card = Fintype.card {π : T // Overlap (by omega : n - d < n) π.val} := by
    rw [← Fintype.card_coe]
    apply Fintype.card_congr
    exact {
      toFun := fun π => ⟨π.val, (hmem d π.val).mp π.property |>.choose_spec.choose_spec⟩
      invFun := fun π => ⟨π.val, (hmem d π.val).mpr ⟨hd, hlong, π.property⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hzero (d : ℕ) (hnot : ¬ 2 * d < n) : E d = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro π hπ
    exact hnot ((hmem d π).mp hπ).choose_spec.choose
  have hT : 0 < Fintype.card T := card_triple_pos (by omega) a r b hra hab
  have hTR : (0 : ℝ) < Fintype.card T := by exact_mod_cast hT
  have hlow (d : ℕ) (hd : d ∈ Finset.Ico 2 (D + 1)) :
      ((E d).card : ℝ) / Fintype.card T ≤
        (2 : ℝ) / (((n - 3) / D).factorial : ℝ) := by
    have hd2 : 2 ≤ d := (Finset.mem_Ico.mp hd).1
    have hdD : d ≤ D := by have h := (Finset.mem_Ico.mp hd).2; omega
    have hlong : 2 * d < n := by omega
    have hc := card_residue_overlap_mul_factorial_le hd2 hlong a r b
    rw [← hcard d hd2 hlong] at hc
    have hfac : ((n - 3) / D).factorial ≤ ((n - 3) / d).factorial :=
      Nat.factorial_le (Nat.div_le_div_left hdD (by omega))
    apply fraction_le_of_mul_le hT (Nat.factorial_pos _)
    exact (Nat.mul_le_mul_left (E d).card hfac).trans hc
  have hhigh (d : ℕ) (hd : d ∈ Finset.Ico (D + 1) n) :
      ((E d).card : ℝ) / Fintype.card T ≤ 1 / (d.factorial : ℝ) := by
    by_cases hlong : 2 * d < n
    · have hd2 : 2 ≤ d := by have h := (Finset.mem_Ico.mp hd).1; omega
      have hc := card_long_overlap_mul_factorial_le hd2 hlong a r b
      rw [← hcard d hd2 hlong] at hc
      have hc' : (E d).card * d.factorial ≤ 1 * Fintype.card T := by simpa using hc
      simpa only [Nat.cast_one] using
        (fraction_le_of_mul_le hT (Nat.factorial_pos _) hc')
    · rw [hzero d hlong, Finset.card_empty, Nat.cast_zero, zero_div]
      positivity
  let B := (Finset.Ico 2 n).biUnion E
  have hU : Fintype.card {π : T //
      ∃ d : ℕ, ∃ hd : 1 ≤ d, ∃ hlong : 2 * d < n,
        Overlap (by omega : n - d < n) π.val} = B.card := by
    rw [← Fintype.card_coe B]
    apply Fintype.card_congr
    refine {
      toFun := fun π => ⟨π.val, ?_⟩
      invFun := fun π => ⟨π.val, ?_⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    · obtain ⟨d, hd, hlong, hov⟩ := π.property
      have hd2 : 2 ≤ d := by
        by_contra h
        have he : d = 1 := by omega
        subst d
        exact not_overlap_deficit_one (by omega) a r b hra hab π.val hov
      exact Finset.mem_biUnion.mpr ⟨d, Finset.mem_Ico.mpr ⟨hd2, by omega⟩,
        (hmem d π.val).mpr ⟨hd2, hlong, hov⟩⟩
    · obtain ⟨d, hd, hπ⟩ := Finset.mem_biUnion.mp π.property
      obtain ⟨hd2, hlong, hov⟩ := (hmem d π.val).mp hπ
      exact ⟨d, by omega, hlong, hov⟩
  change (Fintype.card {π : T //
      ∃ d : ℕ, ∃ hd : 1 ≤ d, ∃ hlong : 2 * d < n,
        Overlap (by omega : n - d < n) π.val} : ℝ) / Fintype.card T ≤ _
  rw [hU]
  have hcount : (B.card : ℝ) ≤ ∑ d ∈ Finset.Ico 2 n, ((E d).card : ℝ) := by
    exact_mod_cast (show B.card ≤ ∑ d ∈ Finset.Ico 2 n, (E d).card from
      Finset.card_biUnion_le)
  calc
    _ ≤ (∑ d ∈ Finset.Ico 2 n, ((E d).card : ℝ)) / Fintype.card T :=
      div_le_div_of_nonneg_right hcount (le_of_lt hTR)
    _ = (∑ d ∈ Finset.Ico 2 (D + 1), ((E d).card : ℝ) / Fintype.card T) +
        (∑ d ∈ Finset.Ico (D + 1) n, ((E d).card : ℝ) / Fintype.card T) := by
      rw [Finset.sum_div]
      exact (Finset.sum_Ico_consecutive
        (fun d => ((E d).card : ℝ) / Fintype.card T)
        (by omega : 2 ≤ D + 1) (by omega : D + 1 ≤ n)).symm
    _ ≤ (∑ d ∈ Finset.Ico 2 (D + 1),
          (2 : ℝ) / (((n - 3) / D).factorial : ℝ)) +
        (∑ d ∈ Finset.Ico (D + 1) n, 1 / (d.factorial : ℝ)) :=
      add_le_add (Finset.sum_le_sum hlow) (Finset.sum_le_sum hhigh)
    _ ≤ (2 * (D - 1) : ℝ) / (((n - 3) / D).factorial : ℝ) +
        2 / ((D + 1).factorial : ℝ) := by
      have hconst : (∑ d ∈ Finset.Ico 2 (D + 1),
          (2 : ℝ) / (((n - 3) / D).factorial : ℝ)) =
          (2 * (D - 1) : ℝ) / (((n - 3) / D).factorial : ℝ) := by
        simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
        have hsub : D + 1 - 2 = D - 1 := by omega
        rw [hsub]
        have hcast : ((D - 1 : ℕ) : ℝ) = (D : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ D), Nat.cast_one]
        rw [hcast]
        ring
      rw [hconst]
      exact add_le_add le_rfl (sum_reciprocal_factorial_tail D n (by omega))

example : Nonempty (FixedThree (0 : Fin 6) 1 5 1 0 5) := by
  exact ⟨⟨Equiv.swap 0 1, by decide, by decide⟩⟩

example : (0 : Fin 6) < 1 ∧ (1 : Fin 6) < 5 ∧ 2 ≤ 2 ∧ 2 * 2 < 6 := by decide

end PermutationOppositeTripleLongTail
