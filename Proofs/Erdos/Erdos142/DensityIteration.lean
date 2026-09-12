import Mathlib

set_option autoImplicit false

namespace Erdos142

/-- The size threshold obtained by repeatedly reversing a square-root size loss. -/
def densityIterationThreshold (B : ℝ) : ℕ → ℝ
  | 0 => B
  | n + 1 => B * densityIterationThreshold B n ^ 2

example : densityIterationThreshold 2 0 = 2 := rfl
example : densityIterationThreshold 2 1 = 8 := by norm_num [densityIterationThreshold]
example : densityIterationThreshold 2 2 = 128 := by norm_num [densityIterationThreshold]

private theorem densityIterationThreshold_pos {B : ℝ} (hB : 0 < B) (n : ℕ) :
    0 < densityIterationThreshold B n := by
  induction n with
  | zero => simpa [densityIterationThreshold] using hB
  | succ n ih =>
      simp only [densityIterationThreshold]
      positivity

private theorem densityIterationThreshold_ge {B : ℝ} (hB : 1 ≤ B) (n : ℕ) :
    B ≤ densityIterationThreshold B n := by
  induction n with
  | zero => simp [densityIterationThreshold]
  | succ n ih =>
      rw [densityIterationThreshold]
      have hthreshold : 1 ≤ densityIterationThreshold B n := hB.trans ih
      nlinarith [sq_nonneg (densityIterationThreshold B n)]

private theorem densityIterationThreshold_closed (B : ℝ) (n : ℕ) :
    densityIterationThreshold B n = B ^ (2 ^ (n + 1) - 1) := by
  induction n with
  | zero => simp [densityIterationThreshold]
  | succ n ih =>
      rw [densityIterationThreshold, ih, pow_two, ← pow_add]
      have hpow : 2 ^ (n + 1 + 1) = 2 ^ (n + 1) * 2 := by
        rw [pow_succ]
      have hexponent :
          2 ^ (n + 1 + 1) - 1 =
            (2 ^ (n + 1) - 1 + (2 ^ (n + 1) - 1)) + 1 := by
        rw [hpow]
        have hpositive : 0 < 2 ^ (n + 1) := pow_pos (by norm_num) _
        omega
      rw [hexponent, pow_succ]
      ring

private theorem densityIterationThreshold_le_explicit {B : ℝ} (hB : 1 ≤ B) (n : ℕ) :
    densityIterationThreshold B n ≤ B ^ (2 ^ (n + 1)) := by
  rw [densityIterationThreshold_closed]
  exact pow_le_pow_right₀ hB (Nat.sub_le _ _)

private theorem reciprocal_decrement {a b : ℝ} (ha : 0 < a) (ha_one : a ≤ 1)
    (hab : a + a ^ 2 / 48 ≤ b) :
    1 / b ≤ 1 / a - 1 / 49 := by
  have hb : 0 < b := by nlinarith [sq_nonneg a]
  have ha49 : 0 < 49 * a := mul_pos (by norm_num) ha
  have hcoefficient : 0 ≤ 1 / a - 1 / 49 := by
    rw [sub_nonneg, one_div_le_one_div (by norm_num) ha]
    exact ha_one.trans (by norm_num)
  apply (div_le_iff₀ hb).2
  calc
    1 ≤ (1 / a - 1 / 49) * (a + a ^ 2 / 48) := by
      field_simp
      nlinarith [mul_nonneg ha.le (sub_nonneg.mpr ha_one)]
    _ ≤ (1 / a - 1 / 49) * b :=
      mul_le_mul_of_nonneg_left hab hcoefficient

private theorem iterate_reciprocal
    {State : Type*} (size density : State → ℝ) {δ B : ℝ}
    (hdensity : ∀ s, 0 < density s ∧ density s ≤ 1)
    (hsize : ∀ s, 0 ≤ size s)
    (hB : 1 < B)
    (hstep : ∀ s, δ ≤ density s → B ≤ size s →
      ∃ s', density s + density s ^ 2 / 48 ≤ density s' ∧
        Real.sqrt (size s / B) ≤ size s') :
    ∀ (n : ℕ) (s : State), δ ≤ density s →
      densityIterationThreshold B n ≤ size s →
      ∃ s', 1 / density s' ≤ 1 / density s - n / 49 := by
  intro n
  induction n with
  | zero =>
      intro s _ _
      refine ⟨s, ?_⟩
      norm_num
  | succ n ih =>
      intro s hδ hs
      have hBone : 1 ≤ B := hB.le
      have hBpos : 0 < B := lt_trans zero_lt_one hB
      have hthreshold_nonneg : 0 ≤ densityIterationThreshold B n :=
        (densityIterationThreshold_pos hBpos (n := n)).le
      have hlarge : B ≤ size s :=
        (densityIterationThreshold_ge hBone (n + 1)).trans hs
      obtain ⟨s₁, hdensity_step, hsize_step⟩ := hstep s hδ hlarge
      have hs_div_nonneg : 0 ≤ size s / B := div_nonneg (hsize s) hBpos.le
      have hthreshold_sq : densityIterationThreshold B n ^ 2 ≤ size s / B := by
        apply (le_div_iff₀ hBpos).2
        simpa [densityIterationThreshold, mul_comm] using hs
      have hthreshold_sqrt : densityIterationThreshold B n ≤ Real.sqrt (size s / B) :=
        (Real.le_sqrt hthreshold_nonneg hs_div_nonneg).2 hthreshold_sq
      have hs₁ : densityIterationThreshold B n ≤ size s₁ := hthreshold_sqrt.trans hsize_step
      have hδ₁ : δ ≤ density s₁ := by
        have hdensity_mono : density s ≤ density s₁ := by
          nlinarith [sq_nonneg (density s)]
        exact hδ.trans hdensity_mono
      obtain ⟨s₂, hs₂⟩ := ih s₁ hδ₁ hs₁
      refine ⟨s₂, ?_⟩
      have hreciprocal := reciprocal_decrement (hdensity s).1 (hdensity s).2 hdensity_step
      calc
        1 / density s₂ ≤ 1 / density s₁ - n / 49 := hs₂
        _ ≤ (1 / density s - 1 / 49) - n / 49 := sub_le_sub_right hreciprocal _
        _ = 1 / density s - ((n + 1 : ℕ) : ℝ) / 49 := by
          push_cast
          ring

example :
    (0 : ℝ) < 1 ∧ (1 : ℝ) ≤ 1 ∧ (1 : ℝ) < 2 ∧
      (∀ _ : Unit, 0 < (1 : ℝ) ∧ (1 : ℝ) ≤ 1) ∧
      (∀ _ : Unit, 0 ≤ (0 : ℝ)) ∧
      (1 : ℝ) ≤ 1 ∧
      (∀ _s : Unit, (1 : ℝ) ≤ 1 → (2 : ℝ) ≤ 0 →
        ∃ _s' : Unit, 1 + 1 ^ 2 / 48 ≤ 1 ∧ Real.sqrt (0 / 2) ≤ 0) := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_, by norm_num, ?_⟩
  · intro s
    exact ⟨by norm_num, by norm_num⟩
  · intro s
    norm_num
  · intro s hδ hlarge
    norm_num at hlarge

/-- If every sufficiently large state admits the stated density increment and square-root
size transition, then a state of density at least `δ` has size strictly below the explicit
double-exponential threshold with `⌈49 / δ⌉₊` iterations. -/
theorem size_lt_explicit_threshold
    {State : Type*} (size density : State → ℝ) {δ B : ℝ}
    (hδpos : 0 < δ) (hδone : δ ≤ 1) (hB : 1 < B)
    (hdensity : ∀ s, 0 < density s ∧ density s ≤ 1)
    (hsize : ∀ s, 0 ≤ size s)
    (hstep : ∀ s, δ ≤ density s → B ≤ size s →
      ∃ s', density s + density s ^ 2 / 48 ≤ density s' ∧
        Real.sqrt (size s / B) ≤ size s')
    (s₀ : State) (hδ₀ : δ ≤ density s₀) :
    size s₀ < B ^ (2 ^ (Nat.ceil (49 / δ) + 1)) := by
  let t := Nat.ceil (49 / δ)
  by_contra hnot
  have hlarge : B ^ (2 ^ (t + 1)) ≤ size s₀ := le_of_not_gt hnot
  have hthreshold : densityIterationThreshold B t ≤ size s₀ :=
    (densityIterationThreshold_le_explicit hB.le t).trans hlarge
  obtain ⟨s, hs⟩ := iterate_reciprocal size density hdensity hsize hB hstep t s₀ hδ₀ hthreshold
  have ht : 49 / δ ≤ (t : ℝ) := by
    exact_mod_cast Nat.le_ceil (49 / δ)
  have hone_le_ratio : 1 ≤ 49 / δ := by
    apply (le_div_iff₀ hδpos).2
    nlinarith
  have ht_pos : 0 < (t : ℝ) := zero_lt_one.trans_le (hone_le_ratio.trans ht)
  have hdensity₀_reciprocal : 1 / density s₀ ≤ 1 / δ := by
    exact one_div_le_one_div_of_le hδpos hδ₀
  have ht_div : 1 / δ ≤ (t : ℝ) / 49 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 49)).2
    calc
      1 / δ * 49 = 49 / δ := by ring
      _ ≤ t := ht
  have ht_div_nonneg : 0 ≤ (t : ℝ) / 49 := div_nonneg ht_pos.le (by norm_num)
  have hnonpos : 1 / density s₀ - (t : ℝ) / 49 ≤ 0 := by linarith
  have hpositive : 0 < 1 / density s := one_div_pos.mpr (hdensity s).1
  linarith

#check @size_lt_explicit_threshold
#print axioms size_lt_explicit_threshold

end Erdos142
