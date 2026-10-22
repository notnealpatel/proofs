/-
# A189786: Mathar's counterexample to Dale's conjecture

OEIS A189786 defines `a(n) = n + ⌊nr/t⌋ + ⌊ns/t⌋`, where
`r = π/2`, `s = arcsin(5/13)`, and `t = arcsin(12/13)`.
Harvey P. Dale's conjecture (2018-12-07) says its values at positive
indices are exactly the positive even integers not congruent to `6 mod 8`.
R. J. Mathar's comment (2025-08-25) records the counterexample `a(143) = 382`.

Here `r = s+t` gives `a(n) = 2n + 2⌊ns/t⌋`. With
`A = arctan(1/5)` and `B = arctan(1/239)`, the identities `s = 2A` and
`t = 6A-2B` and rational arctangent bounds give `⌊143s/t⌋ = 48`.
Thus `a(143) = 382 = 8·47+6`, refuting the conjecture.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A189786Refutation

open Real

/-- The OEIS constant `r = π/2`. -/
noncomputable def r : ℝ := π / 2

/-- The OEIS constant `s = arcsin(5/13)`. -/
noncomputable def s : ℝ := arcsin (5 / 13)

/-- The OEIS constant `t = arcsin(12/13)`. -/
noncomputable def t : ℝ := arcsin (12 / 13)

/-- A189786: `a(n) = n + ⌊n r / t⌋ + ⌊n s / t⌋` (offset 1). -/
noncomputable def seq (n : ℕ) : ℤ := n + ⌊n * r / t⌋ + ⌊n * s / t⌋

/-- Dale's conjecture (Dec 07 2018): the values `a(n)`, `n ≥ 1`, are exactly
the positive even integers not of the form `8x + 6`. -/
def Conjecture : Prop :=
  ∀ m : ℤ, (∃ n : ℕ, 0 < n ∧ seq n = m) ↔ (0 < m ∧ Even m ∧ m % 8 ≠ 6)

/-! ## Elementary arctan bounds -/

/-- `arctan x < x` for `0 < x`. -/
theorem arctan_lt_self {x : ℝ} (hx : 0 < x) : arctan x < x := by
  have h := lt_tan (arctan_pos.2 hx) (arctan_lt_pi_div_two x)
  rwa [tan_arctan] at h

/-- If `0 < y ≤ 1` and `y / (1 - y²/2) ≤ x`, then `y < arctan x`
(from `sin y < y` and `1 - y²/2 ≤ cos y`). -/
theorem lt_arctan_of_le {x y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1)
    (h : y / (1 - y ^ 2 / 2) ≤ x) : y < arctan x := by
  have hpi : y < π / 2 := by linarith [pi_gt_three]
  have hden : 0 < 1 - y ^ 2 / 2 := by nlinarith
  have hcos : 1 - y ^ 2 / 2 ≤ cos y := one_sub_sq_div_two_le_cos
  have hcos0 : 0 < cos y := hden.trans_le hcos
  have htan : tan y < x := by
    rw [tan_eq_sin_div_cos]
    calc sin y / cos y < y / cos y := div_lt_div_of_pos_right (sin_lt hy0) hcos0
      _ ≤ y / (1 - y ^ 2 / 2) := div_le_div_of_nonneg_left hy0.le hden hcos
      _ ≤ x := h
  have := arctan_strictMono htan
  rwa [arctan_tan (by linarith) hpi] at this

/-! ## Closed forms of the constants -/

/-- `arcsin(5/13) = 2 arctan(1/5)`. -/
theorem s_eq : s = 2 * arctan (1 / 5) := by
  have hsq : √(1 - (5 / 13 : ℝ) ^ 2) = 12 / 13 := by
    rw [show (1 : ℝ) - (5 / 13) ^ 2 = (12 / 13) ^ 2 by norm_num]
    exact sqrt_sq (by norm_num)
  have hadd := arctan_add (x := 1 / 5) (y := 1 / 5) (by norm_num)
  rw [s, arcsin_eq_arctan (by constructor <;> norm_num), hsq, two_mul, hadd]
  norm_num

/-- `arcsin(12/13) = π/2 - arcsin(5/13)`. -/
theorem t_eq : t = π / 2 - s := by
  have hsq : √(1 - (12 / 13 : ℝ) ^ 2) = 5 / 13 := by
    rw [show (1 : ℝ) - (12 / 13) ^ 2 = (5 / 13) ^ 2 by norm_num]
    exact sqrt_sq (by norm_num)
  rw [t, s, arcsin_eq_pi_div_two_sub_arccos, arccos_eq_arcsin (by norm_num), hsq]

/-- `π/2 = 8 arctan(1/5) - 2 arctan(1/239)` (Machin's formula). -/
theorem pi_div_two_eq : π / 2 = 8 * arctan (1 / 5) - 2 * arctan (1 / 239) := by
  have h := four_mul_arctan_inv_5_sub_arctan_inv_239
  rw [inv_eq_one_div, inv_eq_one_div] at h
  linarith

/-- `arctan(1/5) < 1/5`. -/
theorem arctan_five_lt : arctan (1 / 5) < 1 / 5 := arctan_lt_self (by norm_num)

/-- `1/10 < arctan(1/5)`. -/
theorem lt_arctan_five : 1 / 10 < arctan (1 / 5) :=
  lt_arctan_of_le (by norm_num) (by norm_num) (by norm_num)

/-- `arctan(1/239) < 1/239`. -/
theorem arctan_239_lt : arctan (1 / 239) < 1 / 239 := arctan_lt_self (by norm_num)

/-- `1/240 < arctan(1/239)`. -/
theorem lt_arctan_239 : 1 / 240 < arctan (1 / 239) :=
  lt_arctan_of_le (by norm_num) (by norm_num) (by norm_num)

/-- `t = 6 arctan(1/5) - 2 arctan(1/239)`. -/
theorem t_eq' : t = 6 * arctan (1 / 5) - 2 * arctan (1 / 239) := by
  rw [t_eq, pi_div_two_eq, s_eq]
  ring

/-- `t > 0`, so the divisions by `t` in `seq` are genuine. -/
theorem t_pos : 0 < t := by
  rw [t_eq']
  linarith [lt_arctan_five, arctan_239_lt]

/-- Since `r = s + t`, `a(n) = 2n + 2⌊n s / t⌋`. -/
theorem seq_eq (n : ℕ) : seq n = 2 * n + 2 * ⌊n * s / t⌋ := by
  have hr : r = s + t := by rw [r, t_eq]; ring
  have hdiv : (n : ℝ) * r / t = ((n : ℤ) : ℝ) + n * s / t := by
    rw [hr]
    field_simp [t_pos.ne']
    push_cast
    ring
  rw [seq, hdiv, Int.floor_intCast_add]
  ring

/-- If `k t ≤ n s < (k+1) t` then `⌊n s / t⌋ = k`. -/
theorem floor_eq_of_bounds (n : ℕ) (k : ℤ)
    (hlo : (k : ℝ) * t ≤ n * s) (hhi : (n : ℝ) * s < (k + 1) * t) :
    ⌊(n : ℝ) * s / t⌋ = k := by
  rw [Int.floor_eq_iff, le_div_iff₀ t_pos, div_lt_iff₀ t_pos]
  exact ⟨hlo, hhi⟩

/-! ## Examples: the first listed terms `2, 4, 8` -/

example : seq 1 = 2 := by
  have hfl : ⌊((1 : ℕ) : ℝ) * s / t⌋ = 0 := by
    apply floor_eq_of_bounds
    · rw [s_eq, t_eq']; push_cast
      linarith [lt_arctan_five, arctan_239_lt]
    · rw [s_eq, t_eq']; push_cast
      linarith [lt_arctan_five, arctan_239_lt]
  rw [seq_eq, hfl]
  norm_num

example : seq 2 = 4 := by
  have hfl : ⌊((2 : ℕ) : ℝ) * s / t⌋ = 0 := by
    apply floor_eq_of_bounds
    · rw [s_eq, t_eq']; push_cast
      linarith [lt_arctan_five, arctan_239_lt]
    · rw [s_eq, t_eq']; push_cast
      linarith [lt_arctan_five, arctan_239_lt, lt_arctan_239]
  rw [seq_eq, hfl]
  norm_num

example : seq 3 = 8 := by
  have hfl : ⌊((3 : ℕ) : ℝ) * s / t⌋ = 1 := by
    apply floor_eq_of_bounds
    · rw [s_eq, t_eq']; push_cast
      linarith [lt_arctan_five, lt_arctan_239]
    · rw [s_eq, t_eq']; push_cast
      linarith [lt_arctan_five, arctan_239_lt]
  rw [seq_eq, hfl]
  norm_num

/-- `a(143) = 382`. -/
theorem seq_143 : seq 143 = 382 := by
  have hfl : ⌊((143 : ℕ) : ℝ) * s / t⌋ = 48 := by
    apply floor_eq_of_bounds
    · rw [s_eq, t_eq']; push_cast
      linarith [arctan_five_lt, lt_arctan_239]
    · rw [s_eq, t_eq']; push_cast
      linarith [lt_arctan_five, arctan_239_lt]
  rw [seq_eq, hfl]
  norm_num

/-- Dale's conjecture is false: `a(143) = 382 = 8·47+6` is a sequence value
excluded by the conjecture (Mathar, August 2025). -/
theorem conjecture_false : ¬ Conjecture := by
  intro h
  have hmem := (h 382).1 ⟨143, by norm_num, seq_143⟩
  exact hmem.2.2 (by norm_num)

end Candidates.A189786Refutation
