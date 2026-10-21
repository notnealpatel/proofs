/-
# A113254 — family form: odd-indexed terms are perfect squares

## OEIS source (retrieved with `oeis show A113254`, 2026-10-21)

```
NAME:     Corresponds to m = 8 in a family of 4th-order linear recurrence
          sequences given by a(n) = m^4*a(n-4) + (2*m)^2*a(n-3) - 4*a(n-1),
          a(0) = -1, a(1) = 4, a(2) = -13 + 6*(m-1) + 3*(m-1)^2,
          a(3) = (-8+m^2)^2.
TERMS:    -1,4,176,3136,-15616,123904,1028096,4734976,-51183616,...
COMMENT:  Conjecture: a(m, 2*n+1) is a perfect square for all m,n
          (see A113249).
COMMENT:  This was proved in the case m = 8 (this sequence) by an autonomous
          AI agent, see the Lean file. ... - _Ralf Stephan_, May 25 2026
```

The conjecture line is unattributed and undated in the entry; it is the
family conjecture shared by A113249 through A113256 (A113249: "Conjecture:
a(m, 2*n+1) is a perfect square for all m, n.").  Sibling A113249 (m = 3)
carries Robert Israel's (Oct 23 2017) explicit square root for m = 3.

## Status (triage)

Open for general `m`: only the cases m = 8 (AlphaProof Nexus Lean file cited
in A113254, May 2026) and m = 3 (Israel's formula) are addressed in the
entries.  No general proof was found in the entries.

## Proof (this file)

The characteristic polynomial factors as
`x^4 + 4x^3 - 4m^2 x - m^4 = (x^2 - m^2)(x^2 + 4x + m^2)`.  With `B` the
sequence of `x^2 + 4x + m^2` (`B 0 = 1`, `B 1 = -2`), one has
`4 a(n) = m^(n+1) (1 - (-1)^n) + 2 B(n+1)` and the "double angle" identity
`B(2j) = 2 B(j)^2 - m^(2j)`; at odd `n = 2k+1` these give
`a(2k+1) = B(k+1)^2`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A113254FamilyFormPerfect

/-- The family `a_m` of A113249–A113256, verbatim from the entry:
`a(0) = -1`, `a(1) = 4`, `a(2) = -13 + 6(m-1) + 3(m-1)^2`, `a(3) = (-8+m^2)^2`,
`a(n) = m^4 a(n-4) + (2m)^2 a(n-3) - 4 a(n-1)` for `n ≥ 4`. -/
def a (m : ℤ) : ℕ → ℤ
  | 0 => -1
  | 1 => 4
  | 2 => -13 + 6 * (m - 1) + 3 * (m - 1) ^ 2
  | 3 => (-8 + m ^ 2) ^ 2
  | n + 4 => m ^ 4 * a m n + (2 * m) ^ 2 * a m (n + 1) - 4 * a m (n + 3)

/-- The auxiliary second-order sequence `B_m(0) = 1`, `B_m(1) = -2`,
`B_m(j) = -4 B_m(j-1) - m^2 B_m(j-2)` (the sequence of `x^2 + 4x + m^2`). -/
def B (m : ℤ) : ℕ → ℤ
  | 0 => 1
  | 1 => -2
  | j + 2 => -4 * B m (j + 1) - m ^ 2 * B m j

/-! ## Ground truth -/

/-- `m = 8` reproduces the first listed terms of A113254. -/
example : (List.range 8).map (a 8) =
    [-1, 4, 176, 3136, -15616, 123904, 1028096, 4734976] := by decide

/-- `m = 3` reproduces the first listed terms of A113249. -/
example : (List.range 10).map (a 3) =
    [-1, 4, 11, 1, 59, 484, -1009, 6241, -2761, 13924] := by decide

/-- `a_m(2) = 3m^2 - 16`, as in the conjecture's restatement. -/
example (m : ℤ) : a m 2 = 3 * m ^ 2 - 16 := by
  simp only [a]
  ring

/-! ## Proof -/

/-- The recurrence of `B`, as an equation. -/
theorem B_succ_succ (m : ℤ) (j : ℕ) :
    B m (j + 2) = -4 * B m (j + 1) - m ^ 2 * B m j := by
  rw [B]

/-- Addition law for `B` (the analogue of `cos(x+y) + cos(x-y) = 2 cos x cos y`):
`B(i + 2j) + m^(2j) B(i) = 2 B(i+j) B(j)`. -/
theorem B_add_law (m : ℤ) : ∀ j i : ℕ,
    B m (i + j + j) + m ^ (2 * j) * B m i = 2 * B m (i + j) * B m j
  | 0, i => by
    simp only [add_zero, mul_zero, pow_zero, one_mul, B, mul_one]
    ring
  | 1, i => by
    simp only [B, mul_one]
    ring
  | j + 2, i => by
    have h1 := B_add_law m (j + 1) (i + 1)
    have h0 := B_add_law m j (i + 2)
    have e1 := B_succ_succ m j
    have e2 := B_succ_succ m (i + 2 * j + 2)
    have e3 := B_succ_succ m i
    have r1 : i + 1 + (j + 1) + (j + 1) = i + 2 * j + 3 := by ring
    have r2 : i + 1 + (j + 1) = i + j + 2 := by ring
    have r3 : i + 2 + j + j = i + 2 * j + 2 := by ring
    have r4 : i + 2 + j = i + j + 2 := by ring
    have r5 : i + (j + 2) + (j + 2) = i + 2 * j + 2 + 2 := by ring
    have r6 : i + (j + 2) = i + j + 2 := by ring
    rw [r1, r2] at h1
    rw [r3, r4] at h0
    rw [r5, r6, e1, e2]
    rw [show i + 2 * j + 2 + 1 = i + 2 * j + 3 from rfl]
    linear_combination (-4) * h1 - m ^ 2 * h0 + m ^ (2 * j + 2) * e3

/-- Double-angle identity: `B(2j) = 2 B(j)^2 - m^(2j)`. -/
theorem B_two_mul (m : ℤ) (j : ℕ) : B m (2 * j) = 2 * B m j ^ 2 - m ^ (2 * j) := by
  have h := B_add_law m j 0
  simp only [Nat.zero_add, B, mul_one] at h
  rw [show 2 * j = j + j by ring]
  rw [show 2 * j = j + j by ring] at h
  linear_combination h

/-- Closed form: `4 a_m(n) = m^(n+1) (1 - (-1)^n) + 2 B_m(n+1)`. -/
theorem four_mul_a (m : ℤ) : ∀ n : ℕ,
    4 * a m n = m ^ (n + 1) * (1 - (-1) ^ n) + 2 * B m (n + 1)
  | 0 => by simp [a, B]
  | 1 => by
    simp only [a, Int.reduceMul, Nat.reduceAdd, Int.reduceNeg, pow_one, sub_neg_eq_add,
      Int.reduceAdd, B, mul_neg, neg_mul, neg_neg, mul_one]
    ring
  | 2 => by
    simp only [a, Int.reduceNeg, Nat.reduceAdd, even_two, Even.neg_pow, one_pow, sub_self,
      mul_zero, B, mul_neg, neg_mul, Int.reduceMul, neg_neg, mul_one, sub_neg_eq_add, zero_add]
    ring
  | 3 => by
    simp only [a, Int.reduceNeg, Nat.reduceAdd, Int.reducePow, sub_neg_eq_add, Int.reduceAdd, B,
      mul_neg, neg_mul, Int.reduceMul, neg_neg, mul_one]
    ring
  | n + 4 => by
    have h0 := four_mul_a m n
    have h1 : 4 * a m (n + 1) = m ^ (n + 2) * (1 - (-1) ^ (n + 1)) + 2 * B m (n + 2) :=
      four_mul_a m (n + 1)
    have h3 : 4 * a m (n + 3) = m ^ (n + 4) * (1 - (-1) ^ (n + 3)) + 2 * B m (n + 4) :=
      four_mul_a m (n + 3)
    have e1 : B m (n + 3) = -4 * B m (n + 2) - m ^ 2 * B m (n + 1) := B_succ_succ m (n + 1)
    have e3 : B m (n + 4 + 1) = -4 * B m (n + 4) - m ^ 2 * B m (n + 3) := B_succ_succ m (n + 3)
    rw [a]
    linear_combination m ^ 4 * h0 + (2 * m) ^ 2 * h1 - 4 * h3 - 2 * e3 + 2 * m ^ 2 * e1

/-! ## The conjecture -/

/-- **Explicit form (A113249–A113256 family).** For every integer `m` and every
`n ≥ 0`, `a_m(2n+1) = B_m(n+1)^2`. -/
theorem a_odd_eq_sq (m : ℤ) (n : ℕ) : a m (2 * n + 1) = B m (n + 1) ^ 2 := by
  have h4 := four_mul_a m (2 * n + 1)
  have hB : B m (2 * (n + 1)) = 2 * B m (n + 1) ^ 2 - m ^ (2 * (n + 1)) := B_two_mul m (n + 1)
  have hidx : 2 * n + 1 + 1 = 2 * (n + 1) := by ring
  have hsign : ((-1 : ℤ)) ^ (2 * n + 1) = -1 := by
    rw [pow_succ, pow_mul]
    norm_num
  rw [hidx, hB, hsign] at h4
  have h4' : 4 * a m (2 * n + 1) = 4 * B m (n + 1) ^ 2 := by linear_combination h4
  exact mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) h4'

/-- **Conjecture (OEIS A113254, family form; also A113249–A113256).**
"Conjecture: a(m, 2*n+1) is a perfect square for all m,n (see A113249)."
For every integer `m` and every `n ≥ 0`, the term `a_m(2n+1)` of the family
`a_m(0) = -1`, `a_m(1) = 4`, `a_m(2) = -13 + 6(m-1) + 3(m-1)^2`,
`a_m(3) = (-8+m^2)^2`, `a_m(n) = m^4 a_m(n-4) + (2m)^2 a_m(n-3) - 4 a_m(n-1)` is a
perfect square. -/
theorem a_odd_isSquare (m : ℤ) (n : ℕ) : IsSquare (a m (2 * n + 1)) :=
  ⟨B m (n + 1), by rw [a_odd_eq_sq, sq]⟩

end Candidates.A113254FamilyFormPerfect
