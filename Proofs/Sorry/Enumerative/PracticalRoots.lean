import Mathlib
import Sorry.Enumerative.MelfiPracticalSum

set_option autoImplicit false

namespace Enumerative.PracticalRoots

/-- The practical numbers in increasing order, indexed starting at zero. -/
noncomputable def pract (k : ℕ) : ℕ := Nat.nth Nat.Practical k

/-- Powers of two give infinitely many practical numbers. -/
theorem practical_infinite : {n : ℕ | n.Practical}.Infinite := by
  apply (Set.infinite_range_of_injective (Nat.pow_right_injective (a := 2) (by norm_num))).mono
  rintro n ⟨j, rfl⟩
  exact Nat.practical_two_pow j

/-- Every enumerated practical number is positive. -/
theorem pract_pos (k : ℕ) : 0 < pract k :=
  (Nat.nth_mem_of_infinite practical_infinite k).pos

example : pract 0 = Nat.nth Nat.Practical 0 := rfl
example : (1 : ℕ).Practical ∧ 0 < (1 : ℕ) := by decide

/-- The first practical number is one (zero-index convention). -/
theorem pract_zero : pract 0 = 1 := by
  have h := Nat.nth_count (by decide : (1 : ℕ).Practical)
  have hc : Nat.count Nat.Practical 1 = 0 := by decide
  simpa only [pract, hc] using h

/-- The second practical number is two. -/
theorem pract_one : pract 1 = 2 := by
  have h := Nat.nth_count (by decide : (2 : ℕ).Practical)
  have hc : Nat.count Nat.Practical 2 = 1 := by decide
  simpa only [pract, hc] using h

/-- The third practical number is four. -/
theorem pract_two : pract 2 = 4 := by
  have h := Nat.nth_count (by decide : (4 : ℕ).Practical)
  have hc : Nat.count Nat.Practical 4 = 2 := by decide
  simpa only [pract, hc] using h

/-- The fourth practical number is six. -/
theorem pract_three : pract 3 = 6 := by
  have h := Nat.nth_count (by decide : (6 : ℕ).Practical)
  have hc : Nat.count Nat.Practical 6 = 3 := by decide
  simpa only [pract, hc] using h

/-- An elementary quadratic bound from distinct practical multiples of a power of two. -/
theorem pract_le_quadratic (k : ℕ) : pract k ≤ 2 * (k + 1) ^ 2 := by
  classical
  let n := k + 1
  let P := 2 ^ (Nat.log 2 n + 1)
  have hn : 0 < n := by dsimp [n]; omega
  have hnP : n ≤ P := Nat.le_of_lt (Nat.lt_pow_succ_log_self (by norm_num) n)
  have hP : P ≤ 2 * n := by
    dsimp [P]
    rw [pow_succ]
    have h := Nat.pow_log_le_self 2 hn.ne'
    omega
  have hPpos : 0 < P := lt_of_lt_of_le hn hnP
  let s := (Finset.range n).image (fun i => P * (i + 1))
  have hcard : s.card = n := by
    dsimp [s]
    rw [Finset.card_image_of_injective]
    · exact Finset.card_range n
    · intro i j hij
      have hij' := Nat.eq_of_mul_eq_mul_left hPpos hij
      omega
  have hsub : s ⊆ (Finset.range (2 * n ^ 2 + 1)).filter Nat.Practical := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hi' : i + 1 ≤ n := by simpa using Nat.succ_le_of_lt (Finset.mem_range.mp hi)
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_range.mpr
      have hmul := Nat.mul_le_mul hP hi'
      nlinarith
    · exact (Nat.practical_two_pow _).mul_of_le_two_mul (by omega) (by omega)
  have hc : n ≤ Nat.count Nat.Practical (2 * n ^ 2 + 1) := by
    rw [Nat.count_eq_card_filter_range]
    calc
      n = s.card := hcard.symm
      _ ≤ _ := Finset.card_le_card hsub
  have hlt : pract k < 2 * n ^ 2 + 1 := by
    by_contra h
    have hc' := (Nat.count_le_iff_le_nth practical_infinite).mpr (Nat.le_of_not_gt h)
    change Nat.count Nat.Practical (2 * n ^ 2 + 1) ≤ k at hc'
    have hnk : n = k + 1 := rfl
    omega
  exact Nat.le_of_lt_succ hlt

/-- The consecutive root comparison is exactly an integer power comparison. -/
theorem root_strictAnti_iff_pow (k : ℕ) (hp : 0 < pract k) (hq : 0 < pract (k + 1)) :
    ((pract (k + 1) : ℝ)) ^ ((k + 2 : ℝ)⁻¹) < ((pract k : ℝ)) ^ ((k + 1 : ℝ)⁻¹)
      ↔ pract (k + 1) ^ (k + 1) < pract k ^ (k + 2) := by
  have ha : 0 < (pract k : ℝ) := by exact_mod_cast hp
  have hb : 0 < (pract (k + 1) : ℝ) := by exact_mod_cast hq
  have hn : 0 < (k + 1 : ℝ) := by positivity
  have hm : 0 < (k + 2 : ℝ) := by positivity
  rw [← Real.log_lt_log_iff (Real.rpow_pos_of_pos hb _) (Real.rpow_pos_of_pos ha _),
    Real.log_rpow hb, Real.log_rpow ha]
  have hcast : pract (k + 1) ^ (k + 1) < pract k ^ (k + 2) ↔
      (pract (k + 1) : ℝ) ^ (k + 1) < (pract k : ℝ) ^ (k + 2) := by
    exact_mod_cast Iff.rfl
  rw [hcast, ← Real.log_lt_log_iff (pow_pos hb _) (pow_pos ha _),
    Real.log_pow, Real.log_pow]
  push_cast
  constructor <;> intro h
  · have h' := (mul_lt_mul_iff_of_pos_right (mul_pos hn hm)).mpr h
    field_simp at h'
    nlinarith
  · apply (mul_lt_mul_iff_of_pos_right (mul_pos hn hm)).mp
    field_simp
    nlinarith

example : 0 < pract 0 ∧ 0 < pract (0 + 1) := by
  rw [pract_zero, pract_one]
  norm_num

/-- The practical-number roots tend to one, using only the quadratic bound. -/
theorem sun_root_tendsto_one :
    Filter.Tendsto (fun k : ℕ => ((pract k : ℝ)) ^ ((k + 1 : ℝ)⁻¹))
      Filter.atTop (nhds 1) := by
  have hn : Filter.Tendsto (fun k : ℕ => (k + 1 : ℝ)) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right Filter.atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  have hlog : Filter.Tendsto (fun k : ℕ => Real.log (k + 1 : ℝ) / (k + 1 : ℝ))
      Filter.atTop (nhds 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)).comp hn
    simpa [Function.comp_def] using h
  have hconst : Filter.Tendsto (fun k : ℕ => Real.log 2 / (k + 1 : ℝ))
      Filter.atTop (nhds 0) := tendsto_const_nhds.div_atTop hn
  have hupper : Filter.Tendsto
      (fun k : ℕ => (Real.log 2 + 2 * Real.log (k + 1 : ℝ)) / (k + 1 : ℝ))
      Filter.atTop (nhds 0) := by
    have h := hconst.add (hlog.const_mul 2)
    simpa [add_div, mul_div_assoc] using h
  have hsqueeze : Filter.Tendsto
      (fun k : ℕ => Real.log (pract k : ℝ) / (k + 1 : ℝ)) Filter.atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    · intro k
      have h1 : 1 ≤ (pract k : ℝ) := by exact_mod_cast pract_pos k
      exact div_nonneg (Real.log_nonneg h1) (by positivity)
    · intro k
      have hpos : 0 < (pract k : ℝ) := by exact_mod_cast pract_pos k
      have hb : (pract k : ℝ) ≤ 2 * (k + 1 : ℝ) ^ 2 := by
        exact_mod_cast pract_le_quadratic k
      have hl := Real.log_le_log hpos hb
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hl
      norm_num at hl
      exact div_le_div_of_nonneg_right hl (by positivity)
  have he := Real.continuous_exp.continuousAt.tendsto.comp hsqueeze
  simpa only [Real.exp_zero] using he.congr (fun k => by
    have hpos : 0 < (pract k : ℝ) := by exact_mod_cast pract_pos k
    simp only [Function.comp_apply, Real.rpow_def_of_pos hpos, div_eq_mul_inv])

end Enumerative.PracticalRoots
