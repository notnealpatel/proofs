/-
# A246396 — Dale: every term has a neighbouring term

## OEIS source (retrieved with `oeis show A246396`, 2026-10-21)

```
NAME:     Nonnegative integers k satisfying cos(k) <= 0 and cos(k+1) <= 0.
TERMS:    2,3,8,9,15,16,21,22,27,28,33,34,35,40,41,46,47,52,53,59,60,65,66,
          71,72,77,78,79,84,85,90,91,96,97,103,104,109,110,115,116,121,122,
          123,128,129,134,135,140,141,147,148,153,154,159,160,165,166,167,172
COMMENT (the conjecture):
  Conjecture: every term t has at least one neighbor which is equal to t plus
  or minus one. - _Harvey P. Dale_, Jul 11 2023
```

## Status

Triage status: open (no proof in the entry; none found in the literature by
the triage).  The triage judged it elementary: the closed arcs where
`cos ≤ 0` have length `π > 3`, so the terms come in runs of length at least
two.  Numerically re-validated for every `k < 2·10⁶` (681691 terms, no
isolated term) before formalization.

## Formalization

`IsTerm k` is the entry's defining predicate for `k : ℕ`.  "A neighbour equal
to `t ± 1`" is rendered as `IsTerm (k + 1)` or the existence of a natural
`j` with `j + 1 = k` and `IsTerm j` (this avoids truncated `ℕ` subtraction;
for `k = 0` the left neighbour does not exist).

The proof reduces to a statement about real numbers: if `cos x ≤ 0` and
`cos (x + 1) ≤ 0` then `cos (x + 2) ≤ 0` or `cos (x - 1) ≤ 0`, which uses only
`1 < π` and `3 < π`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A246396CosSameProperty

open Real

/-- The defining predicate of A246396: `k` is a term iff `cos k ≤ 0` and
`cos (k + 1) ≤ 0`. -/
def IsTerm (k : ℕ) : Prop :=
  Real.cos (k : ℝ) ≤ 0 ∧ Real.cos ((k : ℝ) + 1) ≤ 0

/-- Every real `x` is congruent modulo `2π` to a point of `(-π/2, 3π/2]`. -/
theorem exists_int_reduce (x : ℝ) :
    ∃ n : ℤ, -(π / 2) < x - n * (2 * π) ∧ x - n * (2 * π) ≤ π + π / 2 := by
  have hp : (0 : ℝ) < 2 * π := Real.two_pi_pos
  refine ⟨toIocDiv hp (-(π / 2)) x, ?_⟩
  have hmem := toIocMod_mem_Ioc hp (-(π / 2)) x
  have heq : x - (toIocDiv hp (-(π / 2)) x : ℝ) * (2 * π) = toIocMod hp (-(π / 2)) x := by
    rw [← self_sub_toIocDiv_zsmul hp (-(π / 2)) x, zsmul_eq_mul]
  rw [heq]
  refine ⟨hmem.1, ?_⟩
  linarith [hmem.2]

/-- If `cos x ≤ 0`, some translate `x - 2πn` lies in `[π/2, 3π/2]`. -/
theorem exists_int_reduce_of_cos_nonpos {x : ℝ} (hx : Real.cos x ≤ 0) :
    ∃ n : ℤ, π / 2 ≤ x - n * (2 * π) ∧ x - n * (2 * π) ≤ π + π / 2 := by
  obtain ⟨n, hlo, hhi⟩ := exists_int_reduce x
  refine ⟨n, ?_, hhi⟩
  by_contra hlt
  have hpos : 0 < Real.cos (x - n * (2 * π)) :=
    Real.cos_pos_of_mem_Ioo ⟨hlo, not_le.mp hlt⟩
  rw [Real.cos_sub_int_mul_two_pi] at hpos
  linarith

/-- The real-variable core: if `cos x ≤ 0` and `cos (x + 1) ≤ 0`, then
`cos (x + 2) ≤ 0` or `cos (x - 1) ≤ 0`. -/
theorem cos_add_two_nonpos_or_cos_sub_one_nonpos {x : ℝ} (h0 : Real.cos x ≤ 0)
    (h1 : Real.cos (x + 1) ≤ 0) : Real.cos (x + 2) ≤ 0 ∨ Real.cos (x - 1) ≤ 0 := by
  obtain ⟨n, hlo, hhi⟩ := exists_int_reduce_of_cos_nonpos h0
  have hpi3 : 3 < π := Real.pi_gt_three
  -- `x + 1` stays in the same arc `[π/2 + 2πn, 3π/2 + 2πn]`.
  have hstay : x + 1 - n * (2 * π) ≤ π + π / 2 := by
    by_contra hgt
    have hgt' : π + π / 2 < x + 1 - n * (2 * π) := not_le.mp hgt
    have hmem : x + 1 - ((n + 1 : ℤ) : ℝ) * (2 * π) ∈ Set.Ioo (-(π / 2)) (π / 2) := by
      push_cast
      constructor <;> nlinarith
    have hpos := Real.cos_pos_of_mem_Ioo hmem
    rw [Real.cos_sub_int_mul_two_pi] at hpos
    linarith
  by_cases h2 : x + 2 - n * (2 * π) ≤ π + π / 2
  · left
    have hc := Real.cos_nonpos_of_pi_div_two_le_of_le (x := x + 2 - n * (2 * π))
      (by linarith) h2
    rwa [Real.cos_sub_int_mul_two_pi] at hc
  · right
    have h2' : π + π / 2 < x + 2 - n * (2 * π) := not_le.mp h2
    have hc := Real.cos_nonpos_of_pi_div_two_le_of_le (x := x - 1 - n * (2 * π))
      (by linarith) (by linarith)
    rwa [Real.cos_sub_int_mul_two_pi] at hc

/-- `0` is not a term of A246396, since `cos 0 = 1`. -/
theorem not_isTerm_zero : ¬ IsTerm 0 := by
  rintro ⟨h0, -⟩
  norm_num at h0

/-- **Dale's conjecture (A246396, Harvey P. Dale, Jul 11 2023).**
Every term `k` of A246396 (a nonnegative integer with `cos k ≤ 0` and
`cos (k + 1) ≤ 0`) has a neighbour `k + 1` or `k - 1` that is also a term. -/
theorem isTerm_succ_or_exists_pred (k : ℕ) (hk : IsTerm k) :
    IsTerm (k + 1) ∨ ∃ j : ℕ, j + 1 = k ∧ IsTerm j := by
  obtain ⟨h0, h1⟩ := hk
  rcases cos_add_two_nonpos_or_cos_sub_one_nonpos h0 h1 with h2 | hm
  · left
    have hcast0 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    have hcast1 : ((k + 1 : ℕ) : ℝ) + 1 = (k : ℝ) + 2 := by push_cast; ring
    refine ⟨?_, ?_⟩
    · rw [hcast0]
      exact h1
    · rw [hcast1]
      exact h2
  · right
    rcases Nat.eq_zero_or_eq_succ_pred k with hz | hs
    · subst hz
      exact absurd ⟨h0, h1⟩ not_isTerm_zero
    · refine ⟨k - 1, by omega, ?_, ?_⟩
      · have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega), Nat.cast_one]
        rw [hcast]
        exact hm
      · have hcast : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by
          rw [Nat.cast_sub (by omega), Nat.cast_one]
          ring
        rw [hcast]
        exact h0

/-! ## Ground truth: the first listed terms -/

/-- `2` is a term (first listed term): `cos 2 ≤ 0` and `cos 3 ≤ 0`. -/
example : IsTerm 2 := by
  have h3 := Real.pi_gt_three
  have h4 := Real.pi_lt_four
  constructor
  · exact Real.cos_nonpos_of_pi_div_two_le_of_le (by push_cast; linarith)
      (by push_cast; linarith)
  · exact Real.cos_nonpos_of_pi_div_two_le_of_le (by push_cast; linarith)
      (by push_cast; linarith)

/-- `1` is not a term: `cos 1 > 0`. -/
example : ¬ IsTerm 1 := by
  rintro ⟨h1, -⟩
  have h3 := Real.pi_gt_three
  have hpos : 0 < Real.cos ((1 : ℕ) : ℝ) :=
    Real.cos_pos_of_mem_Ioo ⟨by push_cast; linarith, by push_cast; linarith⟩
  linarith

/-- Satisfiability of the hypothesis of the main theorem: the term `2` has the
neighbour `3`. -/
example : IsTerm 2 ∧ IsTerm 3 := by
  have h3 := Real.pi_gt_three
  have h4 := Real.pi_lt_four
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    exact Real.cos_nonpos_of_pi_div_two_le_of_le (by push_cast; linarith)
      (by push_cast; linarith)

end Candidates.A246396CosSameProperty
