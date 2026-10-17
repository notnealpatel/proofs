import Combinatorics.RetainedMoment
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

open scoped BigOperators

noncomputable section

namespace AffineRetainedVariance

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The real indicator of a finite subset of the field. -/
def indicator (C : Finset F) (x : F) : ℝ := if x ∈ C then 1 else 0

example (C : Finset F) (x : F) : indicator C x = if x ∈ C then 1 else 0 := rfl

/-- Nonzero affine directions. -/
def directions (F : Type*) [Field F] [Fintype F] [DecidableEq F] : Finset F :=
  Finset.univ.erase 0

example : directions F = Finset.univ.erase (0 : F) := rfl

/-- Number of points of the affine copy of `J` lying in `C`, valued in the reals. -/
def Y (C J : Finset F) (a b : F) : ℝ := ∑ j ∈ J, indicator C (a * j + b)

example (C : Finset F) (a b : F) : Y C ∅ a b = 0 := by simp [Y]

/-- The translation mean of the affine count. -/
def mean (C J : Finset F) : ℝ := (C.card : ℝ) * J.card / Fintype.card F

example (C : Finset F) : mean C ∅ = 0 := by simp [mean]

/-- Translation-averaged centered square in a fixed direction. -/
def S (C J : Finset F) (a : F) : ℝ :=
  (∑ b : F, (Y C J a b - mean C J) ^ 2) / Fintype.card F

example (C : Finset F) (a : F) : S C ∅ a = 0 := by simp [S, Y, mean]

/-- Average variance over all nonzero directions. -/
def avgS (C J : Finset F) : ℝ :=
  (∑ a ∈ directions F, S C J a) / ((Fintype.card F : ℝ) - 1)

example (C : Finset F) : avgS C ∅ = 0 := by simp [avgS, S, Y, mean]

/-- The full variance filter, retaining directions at most twice the average. -/
def retained (C J : Finset F) : Finset F :=
  (directions F).filter (fun a ↦ S C J a ≤ 2 * avgS C J)

example (C : Finset F) : retained C ∅ = directions F := by
  simp [retained, S, Y, mean, avgS]

omit [Field F] in
private theorem sum_indicator (C : Finset F) : ∑ x : F, indicator C x = C.card := by
  simp [indicator]

omit [Field F] [Fintype F] in
private theorem indicator_sq (C : Finset F) (x : F) :
    indicator C x * indicator C x = indicator C x := by
  simp [indicator]

omit [DecidableEq F] in
private theorem sum_translate (f : F → ℝ) (t : F) :
    ∑ b : F, f (t + b) = ∑ b : F, f b := by
  exact Equiv.sum_comp (Equiv.addLeft t) f

/-- Summing the count over translations gives exactly `|C| |J|`. -/
theorem sum_Y (C J : Finset F) (a : F) :
    ∑ b : F, Y C J a b = (C.card : ℝ) * J.card := by
  unfold Y
  rw [Finset.sum_comm]
  simp_rw [sum_translate, sum_indicator]
  simp [mul_comm]

private theorem pair_sum (C : Finset F) (j k : F) (hjk : j ≠ k) :
    (∑ a : F, ∑ b : F,
      indicator C (a * j + b) * indicator C (a * k + b)) = (C.card : ℝ) ^ 2 := by
  have hd : k - j ≠ 0 := sub_ne_zero.mpr (Ne.symm hjk)
  have hshift (a : F) :
      (∑ b : F, indicator C (a * j + b) * indicator C (a * k + b)) =
        ∑ x : F, indicator C x * indicator C (a * (k - j) + x) := by
    apply Fintype.sum_equiv (Equiv.addLeft (a * j))
    intro b
    simp only [Equiv.coe_addLeft]
    congr 2
    ring
  simp_rw [hshift]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have hinner (x : F) : (∑ a : F, indicator C (a * (k - j) + x)) = C.card := by
    calc
      _ = ∑ y : F, indicator C (y + x) :=
        Equiv.sum_comp (Equiv.mulRight₀ (k - j) hd) _
      _ = ∑ y : F, indicator C y := Equiv.sum_comp (Equiv.addRight x) _
      _ = _ := sum_indicator C
  simp_rw [hinner]
  rw [← Finset.sum_mul, sum_indicator]
  ring

private theorem pair_sum_eq (C : Finset F) (j k : F) :
    (∑ a : F, ∑ b : F,
      indicator C (a * j + b) * indicator C (a * k + b)) =
      (C.card : ℝ) ^ 2 + if j = k then
        (Fintype.card F : ℝ) * C.card - (C.card : ℝ) ^ 2 else 0 := by
  by_cases hjk : j = k
  · subst k
    simp_rw [indicator_sq, sum_translate, sum_indicator]
    simp
  · rw [pair_sum C j k hjk, if_neg hjk, add_zero]

private theorem sum_Y_sq_all (C J : Finset F) :
    (∑ a : F, ∑ b : F, Y C J a b ^ 2) =
      (J.card : ℝ) * ((J.card : ℝ) * (C.card : ℝ) ^ 2 +
        ((Fintype.card F : ℝ) * C.card - (C.card : ℝ) ^ 2)) := by
  have hexpand (a b : F) : Y C J a b ^ 2 =
      ∑ j ∈ J, ∑ k ∈ J, indicator C (a * j + b) * indicator C (a * k + b) := by
    simp_rw [Y, pow_two, Finset.sum_mul, Finset.mul_sum]
  simp_rw [hexpand, Finset.sum_comm (s := Finset.univ) (t := J), pair_sum_eq]
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  simp [mul_add, mul_sub]

/-- Unnormalized centered square over nonzero directions and all translations. -/
theorem centered_square_sum (C J : Finset F) :
    (∑ a ∈ directions F, ∑ b : F, (Y C J a b - mean C J) ^ 2) =
      (C.card : ℝ) * J.card * ((Fintype.card F : ℝ) - C.card) *
        ((Fintype.card F : ℝ) - J.card) / Fintype.card F := by
  have hp : (Fintype.card F : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hzero : (∑ b : F, Y C J 0 b ^ 2) = (C.card : ℝ) * (J.card : ℝ) ^ 2 := by
    simp only [Y, zero_mul, zero_add, Finset.sum_const, nsmul_eq_mul, mul_pow]
    simp_rw [pow_two (indicator C _), indicator_sq]
    rw [← Finset.mul_sum, sum_indicator]
    ring
  have hsecond := Finset.sum_erase_add Finset.univ
    (fun a : F ↦ ∑ b : F, Y C J a b ^ 2) (Finset.mem_univ (0 : F))
  rw [sum_Y_sq_all, hzero] at hsecond
  have hfirst : (∑ a ∈ directions F, ∑ b : F, Y C J a b) =
      ((Fintype.card F : ℝ) - 1) * ((C.card : ℝ) * J.card) := by
    simp_rw [sum_Y]
    simp [directions, Finset.card_erase_of_mem, Nat.cast_sub (show 1 ≤ Fintype.card F from Fintype.card_pos)]
  have hcard : ((directions F).card : ℝ) = (Fintype.card F : ℝ) - 1 := by
    simp [directions, Finset.card_erase_of_mem, Nat.cast_sub (show 1 ≤ Fintype.card F from Fintype.card_pos)]
  have hexpand (a b : F) : (Y C J a b - mean C J) ^ 2 =
      Y C J a b ^ 2 - 2 * mean C J * Y C J a b + mean C J ^ 2 := by ring
  simp_rw [hexpand, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  rw [hfirst, hcard]
  change (∑ a ∈ Finset.univ.erase 0, ∑ b : F, Y C J a b ^ 2) - _ + _ = _
  rw [eq_sub_of_add_eq hsecond]
  simp only [mean, Finset.card_univ]
  field_simp
  ring

omit [DecidableEq F] in
/-- A finite field has at least two elements; every variance denominator is positive. -/
theorem card_two_le : 2 ≤ Fintype.card F := Fintype.one_lt_card

/-- Real cardinality of the set of nonzero directions. -/
theorem card_directions : ((directions F).card : ℝ) = (Fintype.card F : ℝ) - 1 := by
  simp [directions, Finset.card_erase_of_mem,
    Nat.cast_sub (show 1 ≤ Fintype.card F from Fintype.card_pos)]

/-- Exact affine variance, with no energy or counting assumptions. -/
theorem avgS_eq (C J : Finset F) :
    avgS C J = (C.card : ℝ) * ((Fintype.card F : ℝ) - C.card) *
      J.card * ((Fintype.card F : ℝ) - J.card) /
        ((Fintype.card F : ℝ) ^ 2 * ((Fintype.card F : ℝ) - 1)) := by
  unfold avgS S
  rw [← Finset.sum_div, centered_square_sum]
  simp only [div_div, pow_two]
  congr 1
  ring

/-- Variance is nonnegative in every direction, including the zero direction. -/
theorem S_nonneg (C J : Finset F) (a : F) : 0 ≤ S C J a := by
  unfold S
  positivity

/-- The average variance is nonnegative. -/
theorem avgS_nonneg (C J : Finset F) : 0 ≤ avgS C J := by
  have hp : (1 : ℝ) < Fintype.card F := by exact_mod_cast (card_two_le (F := F))
  exact div_nonneg (Finset.sum_nonneg (fun a _ ↦ S_nonneg C J a)) (by linarith)

/-- Summing variances recovers the average times the number of directions. -/
theorem sum_S (C J : Finset F) :
    ∑ a ∈ directions F, S C J a = ((Fintype.card F : ℝ) - 1) * avgS C J := by
  have hp : (1 : ℝ) < Fintype.card F := by exact_mod_cast (card_two_le (F := F))
  unfold avgS
  rw [mul_div_cancel₀ _ (ne_of_gt (sub_pos.mpr hp))]

/-- Retention selects only nonzero directions. -/
theorem retained_subset (C J : Finset F) : retained C J ⊆ directions F :=
  Finset.filter_subset _ _

/-- The concrete variance filter holds at every retained direction. -/
theorem S_le_two_avgS (C J : Finset F) (a : F) (ha : a ∈ retained C J) :
    S C J a ≤ 2 * avgS C J := (Finset.mem_filter.mp ha).2

/-- Zero average variance means zero variance in every nonzero direction. -/
theorem S_eq_zero_of_avgS_eq_zero (C J : Finset F) (havg : avgS C J = 0)
    (a : F) (ha : a ∈ directions F) : S C J a = 0 := by
  have hsum : ∑ a ∈ directions F, S C J a = 0 := by rw [sum_S, havg, mul_zero]
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun a _ ↦ S_nonneg C J a)).mp hsum a ha

/-- All directions are retained when the average variance is zero; no division by
that average is used. -/
theorem retained_eq_directions_of_avgS_eq_zero (C J : Finset F)
    (havg : avgS C J = 0) : retained C J = directions F := by
  apply Finset.Subset.antisymm (retained_subset C J)
  intro a ha
  exact Finset.mem_filter.mpr ⟨ha, by
    rw [S_eq_zero_of_avgS_eq_zero C J havg a ha, havg]; norm_num⟩

/-- At least half of the nonzero directions pass the full variance filter. -/
theorem half_le_card_retained (C J : Finset F) :
    ((Fintype.card F : ℝ) - 1) / 2 ≤ ((retained C J).card : ℝ) := by
  by_cases havg : avgS C J = 0
  · rw [retained_eq_directions_of_avgS_eq_zero C J havg, card_directions]
    have hp : (1 : ℝ) < Fintype.card F := by exact_mod_cast (card_two_le (F := F))
    linarith
  · have havgpos : 0 < avgS C J := lt_of_le_of_ne (avgS_nonneg C J) (Ne.symm havg)
    let B := directions F \ retained C J
    have hB : B ⊆ directions F := Finset.sdiff_subset
    have hlower : (2 * avgS C J) * (B.card : ℝ) ≤ ∑ a ∈ B, S C J a := by
      calc
        _ = ∑ _a ∈ B, 2 * avgS C J := by simp [mul_comm]
        _ ≤ _ := Finset.sum_le_sum (fun a ha ↦ by
          have hamem := Finset.mem_sdiff.mp ha
          have hbad : ¬ S C J a ≤ 2 * avgS C J := by
            intro hle
            exact hamem.2 (Finset.mem_filter.mpr ⟨hamem.1, hle⟩)
          exact (lt_of_not_ge hbad).le)
    have hupper : (∑ a ∈ B, S C J a) ≤
        ((Fintype.card F : ℝ) - 1) * avgS C J := by
      rw [← sum_S]
      exact Finset.sum_le_sum_of_subset_of_nonneg hB (fun a _ _ ↦ S_nonneg C J a)
    have hcards : (B.card : ℝ) + (retained C J).card = (Fintype.card F : ℝ) - 1 := by
      rw [← card_directions]
      exact_mod_cast Finset.card_sdiff_add_card_eq_card (retained_subset C J)
    have hbadcard : 2 * (B.card : ℝ) ≤ (Fintype.card F : ℝ) - 1 := by
      nlinarith [hlower.trans hupper]
    linarith

/-- The natural-cardinality form of the half-retention bound. -/
theorem card_sub_one_le_two_mul_card_retained (C J : Finset F) :
    Fintype.card F - 1 ≤ 2 * (retained C J).card := by
  have h := half_le_card_retained C J
  have hnat : ((Fintype.card F - 1 : ℕ) : ℝ) = (Fintype.card F : ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ Fintype.card F from Fintype.card_pos), Nat.cast_one]
  have hreal : ((Fintype.card F - 1 : ℕ) : ℝ) ≤ 2 * ((retained C J).card : ℝ) := by
    rw [hnat]
    linarith
  exact_mod_cast hreal

/-- The retained set is nonempty, even at zero variance. -/
theorem retained_nonempty (C J : Finset F) : (retained C J).Nonempty := by
  have hp : (1 : ℝ) < Fintype.card F := by exact_mod_cast (card_two_le (F := F))
  have hpos : 0 < ((retained C J).card : ℝ) := by
    linarith [half_le_card_retained C J]
  exact Finset.card_pos.mp (by exact_mod_cast hpos)

/-- A full translation window has zero average variance. -/
theorem avgS_univ (C : Finset F) : avgS C Finset.univ = 0 := by
  rw [avgS_eq]
  simp

/-- For a full window all nonzero directions are retained. -/
theorem retained_univ (C : Finset F) : retained C Finset.univ = directions F :=
  retained_eq_directions_of_avgS_eq_zero C Finset.univ (avgS_univ C)

/-- For a set of half-interval cardinality, twice the exact average variance is
precisely the coefficient required by the numerical fourth-moment consumer. -/
theorem two_mul_avgS_eq (C J : Finset F)
    (hm : 2 * (C.card : ℝ) = (Fintype.card F : ℝ) + 1) :
    2 * avgS C J = ((Fintype.card F : ℝ) + 1) * J.card *
      ((Fintype.card F : ℝ) - J.card) / (2 * (Fintype.card F : ℝ) ^ 2) := by
  have hp : (1 : ℝ) < Fintype.card F := by exact_mod_cast (card_two_le (F := F))
  have hm' : (C.card : ℝ) = ((Fintype.card F : ℝ) + 1) / 2 := by linarith
  rw [avgS_eq, hm']
  field_simp [ne_of_gt (lt_trans zero_lt_one hp), ne_of_gt (sub_pos.mpr hp)]
  ring

/-- Concrete affine variance and retention discharge the variance and cardinality
inputs of the half-interval consumer. The Fourier energy, total weight, and
pointwise fourth-moment bridge remain explicit inputs, not proved Fourier facts. -/
theorem half_interval_fourth_mean_le {κ : Type*} (C J : Finset F) (K : Finset κ)
    (c : κ → ℝ) (d : F → κ → ℝ) (F4 : F → ℝ) (H : ℝ)
    (hp : 3 ≤ Fintype.card F) (hq : 1 ≤ J.card)
    (hm : 2 * (C.card : ℝ) = (Fintype.card F : ℝ) + 1)
    (hc : ∀ k ∈ K, 0 ≤ c k)
    (henergy : ∀ k ∈ K, ∑ a ∈ directions F, d a k ^ 2 ≤
      (J.card : ℝ) * ((Fintype.card F : ℝ) - J.card))
    (hpoint : ∀ a ∈ retained C J, F4 a ≤ S C J a * (∑ k ∈ K, c k * d a k) ^ 2)
    (hweight : ∑ k ∈ K, c k ≤ H) :
    (∑ a ∈ retained C J, F4 a) / ((retained C J).card : ℝ) ≤ (J.card : ℝ) ^ 2 * H ^ 2 := by
  apply RetainedMoment.half_interval_fourth_mean_le (directions F) (retained C J)
    K c d F4 (Fintype.card F) J.card H
    (by exact_mod_cast hp) (by exact_mod_cast hq)
    (by exact_mod_cast Finset.card_le_univ J)
    (retained_subset C J) hc (half_le_card_retained C J) henergy _ hweight
  intro a ha
  calc
    F4 a ≤ S C J a * (∑ k ∈ K, c k * d a k) ^ 2 := hpoint a ha
    _ ≤ (2 * avgS C J) * (∑ k ∈ K, c k * d a k) ^ 2 :=
      mul_le_mul_of_nonneg_right (S_le_two_avgS C J a ha) (sq_nonneg _)
    _ = _ := by rw [two_mul_avgS_eq C J hm]

example : avgS ({0, 1} : Finset (ZMod 3)) {0} = 2 / 9 := by
  rw [avgS_eq]
  norm_num

example : retained ({0, 1} : Finset (ZMod 3)) Finset.univ = directions (ZMod 3) :=
  retained_univ _

example : (retained ({0, 1} : Finset (ZMod 3)) {0}).Nonempty := retained_nonempty _ _

example : 2 * (({0, 1} : Finset (ZMod 3)).card : ℝ) =
    (Fintype.card (ZMod 3) : ℝ) + 1 := by norm_num

example : (∑ _a ∈ retained ({0, 1} : Finset (ZMod 3)) {0}, (0 : ℝ)) /
    ((retained ({0, 1} : Finset (ZMod 3)) {0}).card : ℝ) ≤ (1 : ℝ) ^ 2 * 1 ^ 2 := by
  have hresult := half_interval_fourth_mean_le ({0, 1} : Finset (ZMod 3)) {0}
    ({0} : Finset ℕ) (fun _ ↦ 1) (fun _ _ ↦ 0) (fun _ ↦ 0) 1
    (by norm_num) (by norm_num) (by norm_num) (by simp)
    (by simp) (by intro a ha; simp) (by simp)
  simpa only [Finset.card_singleton, Nat.cast_one] using hresult

end AffineRetainedVariance
