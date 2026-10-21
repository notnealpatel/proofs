/-
# A341249 — Kimberling: `1 < r*s*n - a(n) < 2` (refuted)

## OEIS source (retrieved 2026-10-21 with `oeis show A341249` and the live
## entry https://oeis.org/A341249)

```
NAME:     a(n) = floor(r*floor(s*n)), where r = 2 + sqrt(2) and s = sqrt(2).
TERMS:    3,6,13,17,23,27,30,37,40,47,51,54,61,64,71,75,81,85,88,95,...
COMMENT:  Conjecture:  1 < r*s*n - a(n) < 2 for n >= 1.
AUTHOR:   _Clark Kimberling_, Feb 13 2021
```

The conjecture comment carries no separate signature; it belongs to the
entry's author, Clark Kimberling (Feb 13 2021).  No later comment
retracts or corrects it.

## Status

This module **refutes** the conjecture.  At `n = 2` we have
`floor(2 * sqrt 2) = 2` and `a(2) = floor(2 * (2 + sqrt 2)) = 6`, while
`r * s * 2 = 4 + 4 * sqrt 2 ≈ 9.657`, so `r*s*n - a(n) = 4 * sqrt 2 - 2 ≈
3.657`, which is not `< 2`.  (A float check finds 19 violations among
`n ≤ 40`: `n = 2, 4, 7, 9, 11, 12, ...`.)

With `e = frac(n * sqrt 2)` one has `r*s*n - a(n) = 2e - floor(-sqrt 2 * e)`,
which lies in `(1, 1 + sqrt 2)` or in `(2 + sqrt 2, 4)`.  The corrected
bound `1 < r*s*n - a(n) < 4` is proved below as `corrected_bounds`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A341249Refutation

/-- The entry's `r = 2 + sqrt 2`. -/
noncomputable def r : ℝ := 2 + √2

/-- The entry's `s = sqrt 2`. -/
noncomputable def s : ℝ := √2

/-- A341249: `a(n) = floor(r * floor(s * n))` with `r = 2 + sqrt 2`, `s = sqrt 2`. -/
noncomputable def a (n : ℕ) : ℤ := ⌊r * ⌊s * n⌋⌋

/-- Rational bounds `1.41 < sqrt 2 < 1.42` used for the ground-truth checks. -/
theorem sqrt_two_bounds : (141 / 100 : ℝ) < √2 ∧ √2 < 142 / 100 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]
    norm_num
  · rw [Real.sqrt_lt' (by norm_num)]
    norm_num

/-! ## Ground truth: the first listed terms `3, 6, 13`. -/

example : a 1 = 3 := by
  obtain ⟨hlo, hhi⟩ := sqrt_two_bounds
  have hinner : ⌊s * ((1 : ℕ) : ℝ)⌋ = 1 := by
    rw [Int.floor_eq_iff]
    simp only [s, Nat.cast_one, mul_one, Int.cast_one]
    constructor <;> linarith
  rw [a, hinner, Int.floor_eq_iff]
  simp only [r, Int.cast_one, mul_one]
  push_cast
  constructor <;> linarith

example : a 2 = 6 := by
  obtain ⟨hlo, hhi⟩ := sqrt_two_bounds
  have hinner : ⌊s * ((2 : ℕ) : ℝ)⌋ = 2 := by
    rw [Int.floor_eq_iff]
    simp only [s]
    push_cast
    constructor <;> linarith
  rw [a, hinner, Int.floor_eq_iff]
  simp only [r]
  push_cast
  constructor <;> linarith

example : a 3 = 13 := by
  obtain ⟨hlo, hhi⟩ := sqrt_two_bounds
  have hinner : ⌊s * ((3 : ℕ) : ℝ)⌋ = 4 := by
    rw [Int.floor_eq_iff]
    simp only [s]
    push_cast
    constructor <;> linarith
  rw [a, hinner, Int.floor_eq_iff]
  simp only [r]
  push_cast
  constructor <;> linarith

/-! ## The conjecture and its refutation -/

/-- **Kimberling's conjecture (A341249, Feb 13 2021).**
Verbatim: "Conjecture:  1 < r*s*n - a(n) < 2 for n >= 1."
Here `r*s*n - a(n)` is computed in `ℝ`, with `a(n)` cast from `ℤ`. -/
def Conjecture : Prop :=
  ∀ n : ℕ, 1 ≤ n → 1 < r * s * n - a n ∧ r * s * n - a n < 2

/-- **The conjecture is false**, with counterexample `n = 2`: `a(2) = 6` and
`r * s * 2 - a(2) = 4 * sqrt 2 - 2 ≈ 3.657`, which is not `< 2`.  The
correct upper bound is `4` (see `corrected_bounds`). -/
theorem conjecture_false : ¬ Conjecture := by
  intro h
  obtain ⟨hlo, hhi⟩ := sqrt_two_bounds
  have ha2 : a 2 = 6 := by
    have hinner : ⌊s * ((2 : ℕ) : ℝ)⌋ = 2 := by
      rw [Int.floor_eq_iff]
      simp only [s]
      push_cast
      constructor <;> linarith
    rw [a, hinner, Int.floor_eq_iff]
    simp only [r]
    push_cast
    constructor <;> linarith
  have hsq : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hdiff : r * s * ((2 : ℕ) : ℝ) - ((a 2 : ℤ) : ℝ) = 4 * √2 - 2 := by
    rw [ha2]
    simp only [r, s]
    push_cast
    linear_combination 2 * hsq
  have hupper := (h 2 (by norm_num)).2
  rw [hdiff] at hupper
  linarith

/-- **Corrected form.** For every `n ≥ 1`, `1 < r*s*n - a(n) < 4`.  Writing
`m = floor(sqrt 2 * n)` and `e = sqrt 2 * n - m ∈ (0, 1)` (positive because
`sqrt 2` is irrational), one has `r * m = 2m + 2n - sqrt 2 * e`, hence
`r*s*n - a(n) = 2e - floor(-sqrt 2 * e)` with `floor(-sqrt 2 * e) ∈ {-2, -1}`. -/
theorem corrected_bounds (n : ℕ) (hn : 1 ≤ n) :
    1 < r * s * n - a n ∧ r * s * n - a n < 4 := by
  obtain ⟨hlo, hhi⟩ := sqrt_two_bounds
  have hsq : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  set m : ℤ := ⌊√2 * (n : ℝ)⌋ with hm
  set e : ℝ := √2 * n - m with he
  have he_lt : e < 1 := by
    have h := Int.lt_floor_add_one (√2 * (n : ℝ))
    rw [he]
    linarith
  have he_pos : 0 < e := by
    have hle : (m : ℝ) ≤ √2 * n := Int.floor_le _
    rcases hle.lt_or_eq with hlt | heq
    · rw [he]
      linarith
    · exfalso
      have hn0 : (n : ℝ) ≠ 0 := by
        have : (0 : ℝ) < n := by exact_mod_cast hn
        exact this.ne'
      have hrat : √2 = ((m : ℚ) / (n : ℚ) : ℚ) := by
        push_cast
        rw [heq]
        field_simp
      exact irrational_sqrt_two ⟨(m : ℚ) / (n : ℚ), hrat.symm⟩
  set k : ℤ := ⌊-(√2 * e)⌋ with hk
  have hrm : r * (m : ℝ) = ((2 * m + 2 * n : ℤ) : ℝ) + -(√2 * e) := by
    simp only [r, he]
    push_cast
    linear_combination (n : ℝ) * hsq
  have ha : a n = 2 * m + 2 * n + k := by
    simp only [a, s]
    rw [← hm, hrm, Int.floor_intCast_add]
  have hk_le : k ≤ -1 := by
    rw [hk, Int.floor_le_iff]
    push_cast
    have : 0 < √2 * e := mul_pos (by linarith) he_pos
    linarith
  have hk_ge : -2 ≤ k := by
    rw [hk, Int.le_floor]
    push_cast
    have : √2 * e < 2 := by nlinarith
    linarith
  have hkR_le : (k : ℝ) ≤ -1 := by exact_mod_cast hk_le
  have hkR_ge : (-2 : ℝ) ≤ k := by exact_mod_cast hk_ge
  have hdiff : r * s * n - a n = 2 * e - k := by
    rw [ha]
    simp only [r, s, he]
    push_cast
    linear_combination (n : ℝ) * hsq
  rw [hdiff]
  constructor <;> linarith

end Candidates.A341249Refutation
