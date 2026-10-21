/-
# A086845 — Bose-Nelson comparator counts are partial sums of A087808

## OEIS source (retrieved with `oeis show A086845`, 2026-10-21)

```
NAME:     a(1) = 0, a(n) = a(floor(n/2)) + 2*a(ceiling(n/2)) + floor(n/2).
TERMS:    0,1,3,5,9,12,16,19,27,32,38,42,50,55,61,65,81,90,100,106,118,125,
          133,138,154,163,173,179,191,198,206,211,243,260,278,288,308,319,...
COMMENT:  Number of comparators used in Bose-Nelson networks.
COMMENT (the conjecture):
  Conjecture: partial sums of A087808. - _Sean A. Irvine_, Jul 14 2022
```

A087808 (retrieved with `oeis show A087808`, 2026-10-21):

```
NAME:     a(0) = 0; a(2n) = 2a(n), a(2n+1) = a(n) + 1.
TERMS:    0,1,2,2,4,3,4,3,8,5,6,4,8,5,6,4,16,9,10,6,12,7,8,5,16,...
```

Precise reading (fixed by the triage and re-checked numerically for
`1 ≤ n < 5000`): `A086845(n) = ∑_{k=0}^{n-1} A087808(k)` for `n ≥ 1`.

## Status

Triage: open (no proof in the entry or the literature as far as the triage
could tell).  This module proves it.

## Proof idea

Writing `S n = ∑_{k<n} g k`, pairing `g (2j) + g (2j+1) = 3 g j + 1` gives
`S (2m) = 3 S m + m`, and `S (2m+1) = S (2m) + 2 g m = S m + 2 S (m+1) + m`.
So `S` satisfies the same recursion as `h` with the same initial value, and
strong induction concludes.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A086845BoseNelsonComparator

/-- A087808: `g 0 = 0`, `g (2n) = 2 g n`, `g (2n+1) = g n + 1`. -/
def g : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
    if (n + 1) % 2 = 0 then 2 * g ((n + 1) / 2) else g ((n + 1) / 2) + 1
decreasing_by all_goals omega

/-- A086845: `h 1 = 0` and, for `n ≥ 2`,
`h n = h ⌊n/2⌋ + 2 h ⌈n/2⌉ + ⌊n/2⌋` (with `⌈n/2⌉ = (n+1)/2`).
The value at `0` is outside the entry's domain and set to `0`. -/
def h : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | n + 2 => h ((n + 2) / 2) + 2 * h ((n + 3) / 2) + (n + 2) / 2
decreasing_by all_goals omega

/-! ## Ground truth -/

example : (List.range 17).map g = [0,1,2,2,4,3,4,3,8,5,6,4,8,5,6,4,16] := by
  decide +kernel

example : (List.range' 1 19).map h =
    [0,1,3,5,9,12,16,19,27,32,38,42,50,55,61,65,81,90,100] := by
  decide +kernel

/-! ## Recursion lemmas -/

/-- `g (2n) = 2 g n`. -/
theorem g_two_mul (n : ℕ) : g (2 * n) = 2 * g n := by
  rcases n with _ | n
  · simp [g]
  · rw [show 2 * (n + 1) = (2 * n + 1) + 1 by ring, g]
    have hmod : (2 * n + 1 + 1) % 2 = 0 := by omega
    have hdiv : (2 * n + 1 + 1) / 2 = n + 1 := by omega
    rw [if_pos hmod, hdiv]

/-- `g (2n+1) = g n + 1`. -/
theorem g_two_mul_add_one (n : ℕ) : g (2 * n + 1) = g n + 1 := by
  rw [g]
  have hmod : ¬ (2 * n + 1) % 2 = 0 := by omega
  have hdiv : (2 * n + 1) / 2 = n := by omega
  rw [if_neg hmod, hdiv]

/-- The defining recursion of `h` for `n ≥ 2`. -/
theorem h_rec (n : ℕ) (hn : 2 ≤ n) :
    h n = h (n / 2) + 2 * h ((n + 1) / 2) + n / 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [h]

/-- Pairing `g (2j) + g (2j+1) = 3 g j + 1`: `∑_{k<2m} g k = 3 ∑_{k<m} g k + m`. -/
theorem sum_range_two_mul (m : ℕ) :
    ∑ k ∈ Finset.range (2 * m), g k = 3 * ∑ k ∈ Finset.range m, g k + m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ, g_two_mul, g_two_mul_add_one]
    ring

/-- The partial sums satisfy the `h`-recursion at every `n ≥ 1`. -/
theorem sum_range_rec (n : ℕ) :
    ∑ k ∈ Finset.range n, g k = ∑ k ∈ Finset.range (n / 2), g k
      + 2 * ∑ k ∈ Finset.range ((n + 1) / 2), g k + n / 2 := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · have h1 : 2 * m / 2 = m := by omega
    have h2 : (2 * m + 1) / 2 = m := by omega
    rw [h1, h2, sum_range_two_mul]
    ring
  · have h1 : (2 * m + 1) / 2 = m := by omega
    have h2 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
    rw [h1, h2, Finset.sum_range_succ, sum_range_two_mul, Finset.sum_range_succ,
      g_two_mul]
    ring

/-! ## The conjecture -/

/-- **A086845 conjecture (Sean A. Irvine, Jul 14 2022), proved.**
For `n ≥ 1`, the Bose-Nelson comparator count `h n`
(`h 1 = 0`, `h n = h ⌊n/2⌋ + 2 h ⌈n/2⌉ + ⌊n/2⌋`) equals the partial sum
`∑_{k=0}^{n-1} A087808(k)`, where A087808 is `g 0 = 0`, `g (2k) = 2 g k`,
`g (2k+1) = g k + 1`. -/
theorem h_eq_sum_range (n : ℕ) (hn : 1 ≤ n) :
    h n = ∑ k ∈ Finset.range n, g k := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · obtain rfl : n = 1 := by omega
      simp [h, g]
    · have hhalf : 1 ≤ n / 2 := by omega
      have hceil : 1 ≤ (n + 1) / 2 := by omega
      rw [h_rec n hge, sum_range_rec n, ih (n / 2) (by omega) hhalf,
        ih ((n + 1) / 2) (by omega) hceil]

end Candidates.A086845BoseNelsonComparator
