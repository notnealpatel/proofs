/-
# A011848 — Kagey: floor(C(n,2)/2) as a greatest index below a triangular number

## OEIS source (retrieved with `oeis show A011848`, 2026-10-21)

```
NAME:     a(n) = floor(binomial(n, 2)/2).
TERMS:    0,0,0,1,3,5,7,10,14,18,22,27,33,39,45,52,60,68,76,85,95,105,115,...
          (offset 0)
COMMENT (the conjecture):
  Conjecture: For n = 2, a(n) is the greatest k such that A123663(k) <
  A000217(n - 2). - _Peter Kagey_, Nov 18 2016
```

Auxiliary entries used verbatim:

```
A123663  NAME:    Number of shared edges in a spiral of n unit squares.
         FORMULA: a(n) = 2n - ceiling(2*sqrt(n)). - _Julian F. Fleron_, Nov 29 2016
         TERMS:   0,1,2,4,5,7,8,10,12,13,15,17,18,20,22,24,25,...  (offset 1)
A000217  NAME:    Triangular numbers: a(n) = binomial(n+1,2) = n*(n+1)/2.
```

## Status

Triage: open (no proof in the entry or the literature found).  "For n = 2" is
presumably a typo; the triage read it as "for n >= 2".

**Finding of this module.**  The reading "n >= 2" is false at its boundary
`n = 2`: `A000217(0) = 0` and `A123663(k) >= 0` for every `k`, so no `k`
satisfies `A123663(k) < A000217(0)` and there is no greatest one
(`not_isGreatest_two`).  The literal reading "n = 2" is false for the same
reason.  The repaired reading "n >= 3" (equivalently "n > 2") is proved in
full (`kagey_conjecture`).  Numerically (Python, exact integer arithmetic),
`n = 2` is the only failure for `2 <= n <= 20000`.

## Proof outline

Write `c(k) = ceil(2 sqrt k)`; for an integer `m >= 0`, `c(k) <= m` iff
`4k <= m^2`.  With `a = floor(C(n,2)/2)`, `e = C(n,2) mod 2` and
`T = A000217(n-2) = C(n-1,2)` one has `2a - T = n - 1 - e`, and the two
polynomial inequalities `(n-1-e)^2 < 4a` (needs `n >= 3` when `e = 1`) and
`4k <= (2k - T)^2` for every `k > a` give membership and maximality.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A011848EntryPresumablyTypo

/-! ## Definition layer -/

/-- A011848: `a(n) = floor(binomial(n, 2) / 2)`. -/
def a011848 (n : ℕ) : ℕ := n.choose 2 / 2

/-- A000217: the triangular numbers `a(n) = n * (n + 1) / 2`. -/
def a000217 (n : ℕ) : ℕ := n * (n + 1) / 2

/-- A123663 via Fleron's closed form `a(n) = 2n - ceiling(2 * sqrt(n))`,
computed in `ℤ` so that no truncated subtraction occurs. -/
noncomputable def a123663 (k : ℕ) : ℤ := 2 * (k : ℤ) - ⌈2 * Real.sqrt (k : ℝ)⌉

/-! ## Ground truth -/

example : (List.range 12).map a011848 = [0, 0, 0, 1, 3, 5, 7, 10, 14, 18, 22, 27] := by
  decide

example : (List.range 8).map a000217 = [0, 1, 3, 6, 10, 15, 21, 28] := by
  decide

/-- The ceiling of `2 * sqrt k` is at most a nonnegative integer `m` exactly when
`4k ≤ m ^ 2`. -/
theorem ceil_two_mul_sqrt_le_iff (k : ℕ) (m : ℤ) (hm : 0 ≤ m) :
    ⌈2 * Real.sqrt (k : ℝ)⌉ ≤ m ↔ 4 * (k : ℤ) ≤ m ^ 2 := by
  rw [Int.ceil_le]
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hsq : Real.sqrt (k : ℝ) ^ 2 = (k : ℝ) := Real.sq_sqrt hk
  have hs0 : 0 ≤ Real.sqrt (k : ℝ) := Real.sqrt_nonneg _
  have hmR : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  constructor
  · intro h
    have hR : 4 * (k : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
    exact_mod_cast hR
  · intro h
    have hR : 4 * (k : ℝ) ≤ (m : ℝ) ^ 2 := by exact_mod_cast h
    by_contra hlt
    rw [not_le] at hlt
    nlinarith

/-- Pinning `⌈2 * sqrt k⌉` by the integer square-root bracket `(m-1)^2 < 4k ≤ m^2`. -/
theorem ceil_two_mul_sqrt_eq (k : ℕ) (m : ℤ) (hm : 0 < m)
    (hlo : (m - 1) ^ 2 < 4 * (k : ℤ)) (hhi : 4 * (k : ℤ) ≤ m ^ 2) :
    ⌈2 * Real.sqrt (k : ℝ)⌉ = m := by
  have hle : ⌈2 * Real.sqrt (k : ℝ)⌉ ≤ m := (ceil_two_mul_sqrt_le_iff k m hm.le).mpr hhi
  have hnle : ¬ ⌈2 * Real.sqrt (k : ℝ)⌉ ≤ m - 1 := by
    rw [ceil_two_mul_sqrt_le_iff k (m - 1) (by omega)]
    exact not_le.mpr hlo
  omega

-- Ground truth for A123663 against its DATA line `0, 1, 2, 4, 5, 7, 8, 10`
-- (offset 1), via the bracket lemma.
example : (a123663 1, a123663 2, a123663 3, a123663 4) = (0, 1, 2, 4) := by
  simp only [a123663, ceil_two_mul_sqrt_eq 1 2 (by norm_num) (by norm_num) (by norm_num),
    ceil_two_mul_sqrt_eq 2 3 (by norm_num) (by norm_num) (by norm_num),
    ceil_two_mul_sqrt_eq 3 4 (by norm_num) (by norm_num) (by norm_num),
    ceil_two_mul_sqrt_eq 4 4 (by norm_num) (by norm_num) (by norm_num)]
  norm_num

example : (a123663 5, a123663 6, a123663 7, a123663 8) = (5, 7, 8, 10) := by
  simp only [a123663, ceil_two_mul_sqrt_eq 5 5 (by norm_num) (by norm_num) (by norm_num),
    ceil_two_mul_sqrt_eq 6 5 (by norm_num) (by norm_num) (by norm_num),
    ceil_two_mul_sqrt_eq 7 6 (by norm_num) (by norm_num) (by norm_num),
    ceil_two_mul_sqrt_eq 8 6 (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-! ## Core lemmas -/

/-- `A123663(k) < t` iff either `2k - t` is negative or `(2k - t)^2 < 4k`. -/
theorem a123663_lt_iff (k : ℕ) (t : ℤ) :
    a123663 k < t ↔ 2 * (k : ℤ) - t < 0 ∨ (2 * (k : ℤ) - t) ^ 2 < 4 * (k : ℤ) := by
  have hrw : a123663 k < t ↔ ¬ ⌈2 * Real.sqrt (k : ℝ)⌉ ≤ 2 * (k : ℤ) - t := by
    unfold a123663; omega
  rw [hrw]
  rcases lt_or_ge (2 * (k : ℤ) - t) 0 with hneg | hnn
  · have hc : 0 ≤ ⌈2 * Real.sqrt (k : ℝ)⌉ := Int.ceil_nonneg (by positivity)
    constructor
    · intro _; exact Or.inl hneg
    · intro _; omega
  · rw [ceil_two_mul_sqrt_le_iff k _ hnn, not_le]
    constructor
    · intro h; exact Or.inr h
    · rintro (h | h)
      · omega
      · exact h

/-- `A123663` takes nonnegative values, so nothing lies below `A000217(0) = 0`. -/
theorem a123663_nonneg (k : ℕ) : 0 ≤ a123663 k := by
  by_contra hlt
  rw [not_le, a123663_lt_iff] at hlt
  rcases hlt with h | h
  · omega
  · have hk0 : (0 : ℤ) ≤ (k : ℤ) := Nat.cast_nonneg k
    rcases eq_or_lt_of_le hk0 with h0 | hpos
    · rw [← h0] at h; norm_num at h
    · nlinarith

/-! ## The conjecture -/

/-- **The boundary `n = 2` is a counterexample** to the "n ≥ 2" reading (and to the
literal "n = 2" reading) of Kagey's conjecture: `A000217(0) = 0` and
`A123663 ≥ 0`, so the set of `k` with `A123663(k) < A000217(2 - 2)` is empty and
`a(2) = 0` is not its greatest element. -/
theorem not_isGreatest_two :
    ¬ IsGreatest {k : ℕ | a123663 k < (a000217 (2 - 2) : ℤ)} (a011848 2) := by
  rintro ⟨hmem, -⟩
  have h0 : (a000217 (2 - 2) : ℤ) = 0 := by decide
  have hlt : a123663 (a011848 2) < 0 := by
    rw [← h0]; exact hmem
  exact absurd (a123663_nonneg _) (not_le.mpr hlt)

/-- **Kagey's conjecture (A011848, Peter Kagey, Nov 18 2016), repaired to `n ≥ 3`.**

Verbatim: "Conjecture: For n = 2, a(n) is the greatest k such that A123663(k) <
A000217(n - 2)."  Read with `n ≥ 3` (the reading `n ≥ 2` fails at `n = 2`, see
`not_isGreatest_two`): `floor(C(n,2)/2)` is the greatest `k` with
`2k - ceil(2 sqrt k) < (n-2)(n-1)/2`. -/
theorem kagey_conjecture (n : ℕ) (hn : 3 ≤ n) :
    IsGreatest {k : ℕ | a123663 k < (a000217 (n - 2) : ℤ)} (a011848 n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  -- `2 * A000217(m+1) = (m+1)(m+2)` and `2 * C(m+3,2) = (m+3)(m+2)`.
  have hT : 2 * a000217 (m + 3 - 2) = (m + 1) * (m + 2) := by
    have hsub : m + 3 - 2 = m + 1 := by omega
    rw [hsub, a000217]
    exact Nat.mul_div_cancel' (Nat.even_mul_succ_self (m + 1)).two_dvd
  have hC : 2 * (m + 3).choose 2 = (m + 3) * (m + 2) := by
    rw [Nat.choose_two_right]
    have hsub : m + 3 - 1 = m + 2 := by omega
    rw [hsub]
    exact Nat.mul_div_cancel' (by
      have := Nat.even_mul_pred_self (m + 3)
      rw [hsub] at this
      exact this.two_dvd)
  have hA : 2 * a011848 (m + 3) + (m + 3).choose 2 % 2 = (m + 3).choose 2 := by
    unfold a011848; omega
  have he : (m + 3).choose 2 % 2 < 2 := Nat.mod_lt _ (by norm_num)
  set T := a000217 (m + 3 - 2) with hTdef
  set a := a011848 (m + 3) with hadef
  set e := (m + 3).choose 2 % 2 with hedef
  set C := (m + 3).choose 2 with hCdef
  have hTz : 2 * (T : ℤ) = ((m : ℤ) + 1) * ((m : ℤ) + 2) := by exact_mod_cast hT
  have hAz : 4 * (a : ℤ) + 2 * (e : ℤ) = ((m : ℤ) + 3) * ((m : ℤ) + 2) := by
    have h1 : 2 * (C : ℤ) = ((m : ℤ) + 3) * ((m : ℤ) + 2) := by exact_mod_cast hC
    have h2 : 2 * (a : ℤ) + (e : ℤ) = (C : ℤ) := by exact_mod_cast hA
    linarith
  have he01 : (e : ℤ) = 0 ∨ (e : ℤ) = 1 := by omega
  -- `2a - T = n - 1 - e = m + 2 - e`.
  have hdiff : 2 * (a : ℤ) - (T : ℤ) = (m : ℤ) + 2 - (e : ℤ) := by nlinarith
  refine ⟨?_, ?_⟩
  · show a123663 a < (T : ℤ)
    rw [a123663_lt_iff]
    right
    rw [hdiff]
    rcases he01 with h0 | h1
    · rw [h0]; nlinarith
    · rw [h1]; nlinarith
  · intro k hk
    change a123663 k < (T : ℤ) at hk
    rw [a123663_lt_iff] at hk
    by_contra hka
    rw [not_le] at hka
    have hkz : (a : ℤ) + 1 ≤ (k : ℤ) := by exact_mod_cast hka
    -- `d = 2k - T ≥ m + 4 - e ≥ 3`, and `4k = 2d + 2T ≤ d^2`.
    have hd : (m : ℤ) + 4 - (e : ℤ) ≤ 2 * (k : ℤ) - (T : ℤ) := by linarith
    rcases hk with hneg | hsq
    · omega
    · rcases he01 with h0 | h1
      · rw [h0] at hd hAz; nlinarith
      · rw [h1] at hd hAz; nlinarith

/-- Satisfiability at the first admissible `n`: for `n = 3` the set is nonempty
(it contains `a(3) = 1`). -/
example : (a011848 3) ∈ {k : ℕ | a123663 k < (a000217 (3 - 2) : ℤ)} :=
  (kagey_conjecture 3 le_rfl).1

end Candidates.A011848EntryPresumablyTypo
