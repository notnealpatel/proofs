/-
# A334166 — numbers `k` with a divisor `d` such that `d * k` is Zumkeller: gaps ≤ 6

## OEIS source (retrieved 2026-10-21 with `oeis show A334166`; author line from
## `https://oeis.org/A334166/internal`)

```
NAME:     Numbers k having a divisor d, such that d*k is a Zumkeller number (A083207).
TERMS:    6,10,12,14,18,20,24,28,30,36,40,42,44,48,50,52,54,56,60,66,68,70,72,76,
          78,80,84,88,90,92,96,98,100,102,104,105,108,110,112,114,116,120,...
KEYWORDS: nonn
AUTHOR:   Ivan N. Ianakiev, Apr 17 2020
COMMENT (the conjecture, unattributed, hence the entry author's, Apr 17 2020):
  Conjecture: The difference between two consecutive terms is 6 at most.
XREFS:    Supersequence of A083207.
```

## Status

Triage: open — no proof in the entry or found in the literature.  This module
proves it.  The argument is elementary: every positive multiple of `6` is a term,
so consecutive terms differ by at most `6`.  For `6 ∣ k` write
`k = 2 ^ a * 3 ^ b * r` with `a, b ≥ 1` and `gcd(r, 6) = 1`; take `d = 1` when `b`
is odd and `d = 3` when `b` is even.  Then `d * k = (2 ^ a * 3 ^ (2t+1)) * r`, the
first factor is Zumkeller by an explicit 2-adic weighting of the divisors of
`3 ^ (2t+1)`, and the coprime closure of Zumkeller numbers finishes.  The bound
`6` is sharp: `30` and `36` are consecutive terms.

## Definition layer

* `IsZumkeller` — `Proofs/Enumerative/IsZumkeller.lean` (repo, production):
  `0 < n ∧ ∃ A ∈ n.divisors.powerset, ∑ a ∈ A, a = ∑ d ∈ n.divisors \ A, d`,
  i.e. OEIS A083207, with `decide` ground truth there.
* `IsZumkeller.mul_of_coprime` — coprime closure (same file).
* `ZumkellerTauSigma.isZumkeller_two_pow_mul_of_coeff` — 2-adic coefficient
  criterion (`Proofs/Enumerative/ZumkellerTauSigma.lean`, production).
-/
import Mathlib
import Enumerative.IsZumkeller
import Sorry.Quarantine.Enumerative.ZumkellerTauSigma

set_option autoImplicit false

open Finset

namespace Candidates.A334166SetDivisorZumkeller

/-- **A334166**: `k` has a divisor `d` such that `d * k` is a Zumkeller number
(A083207).  The divisor ranges over `k.divisors`, which is empty at `k = 0`, so
`0` is excluded automatically, matching the entry's range `k ≥ 1`. -/
def IsA334166 (k : ℕ) : Prop :=
  ∃ d ∈ k.divisors, IsZumkeller (d * k)

/-- Membership in A334166 is decidable: the divisor ranges over a finite set and
`IsZumkeller` is decidable. -/
instance : DecidablePred IsA334166 := fun k =>
  inferInstanceAs (Decidable (∃ d ∈ k.divisors, IsZumkeller (d * k)))

/-! ## Ground truth -/

-- The first listed terms `6, 10, 12, 14` are members.
example : IsA334166 6 := by decide +kernel
example : IsA334166 10 := by decide +kernel
example : IsA334166 12 := by decide +kernel
example : IsA334166 14 := by decide +kernel

-- Non-members below `14`, as the entry lists no other term there.
example : ¬ IsA334166 1 := by decide +kernel
example : ¬ IsA334166 7 := by decide +kernel
example : ¬ IsA334166 8 := by decide +kernel
example : ¬ IsA334166 9 := by decide +kernel
example : ¬ IsA334166 11 := by decide +kernel
example : ¬ IsA334166 13 := by decide

/-! ## Arithmetic core -/

/-- Weighted geometric identity behind the `2 ^ a * 3 ^ (2t+1)` partition: weighting
`3 ^ j` by `y` for even `j` and by `y + 2` for odd `j` gives exactly half of
`(2y + 3) · (1 + 3 + ⋯ + 3 ^ (2t+1))`.  With `y = 2 ^ a - 2` the factor `2y + 3`
is `σ(2 ^ a) = 2 ^ (a+1) - 1`. -/
theorem two_mul_sum_weighted_three_pow (y t : ℕ) :
    2 * ∑ j ∈ range (2 * t + 2), (if Even j then y else y + 2) * 3 ^ j
      = (2 * y + 3) * ∑ j ∈ range (2 * t + 2), 3 ^ j := by
  induction t with
  | zero =>
    simp only [mul_zero, zero_add, ite_mul, sum_range_succ, range_one, sum_singleton,
      Even.zero, ↓reduceIte, pow_zero, mul_one, Nat.not_even_one, pow_one, Nat.reduceAdd]
    ring
  | succ t ih =>
    rw [show 2 * (t + 1) + 2 = (2 * t + 2) + 1 + 1 by ring, sum_range_succ,
      sum_range_succ, sum_range_succ (fun j => 3 ^ j), sum_range_succ (fun j => 3 ^ j)]
    have he : Even (2 * t + 2) := ⟨t + 1, by ring⟩
    have ho : ¬ Even (2 * t + 2 + 1) := by
      rw [Nat.not_even_iff_odd]
      exact ⟨t + 1, by ring⟩
    rw [if_pos he, if_neg ho, mul_add, mul_add, ih, mul_add, mul_add,
      pow_succ 3 (2 * t + 2)]
    ring

/-- `2 ^ a * 3 ^ (2t+1)` is a Zumkeller number for every `a ≥ 1`. -/
theorem isZumkeller_two_pow_mul_three_pow_odd {a : ℕ} (ha : 1 ≤ a) (t : ℕ) :
    IsZumkeller (2 ^ a * 3 ^ (2 * t + 1)) := by
  have h2a : 2 ≤ 2 ^ a :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  obtain ⟨y, hy⟩ : ∃ y, 2 ^ a = y + 2 := ⟨2 ^ a - 2, by omega⟩
  have hσ : ∑ d ∈ (2 ^ a).divisors, d = 2 * y + 3 := by
    have h := ZumkellerTauSigma.sum_divisors_two_pow_add_one a
    generalize (∑ d ∈ (2 ^ a).divisors, d) = M at h ⊢
    rw [pow_succ, hy] at h
    omega
  have hodd : Odd (3 ^ (2 * t + 1)) := Odd.pow (by decide)
  let c : ℕ → ℕ := fun e => if Even (Nat.log 3 e) then y else y + 2
  refine ZumkellerTauSigma.isZumkeller_two_pow_mul_of_coeff hodd c ?_ ?_
  · intro e _
    have hlt : y + 2 < 2 ^ (a + 1) := by rw [pow_succ]; omega
    by_cases he : Even (Nat.log 3 e)
    · simp only [c, if_pos he]; omega
    · simp only [c, if_neg he]; exact hlt
  · rw [hσ, Nat.sum_divisors_prime_pow (f := fun e => c e * e) Nat.prime_three,
      Nat.sum_divisors_prime_pow (f := fun e => e) Nat.prime_three]
    simp only [c, Nat.log_pow (by norm_num : 1 < 3)]
    rw [show 2 * t + 1 + 1 = 2 * t + 2 by ring]
    exact two_mul_sum_weighted_three_pow y t

/-- `2 ^ a * 3 ^ (2t+1) * r` is Zumkeller whenever `a ≥ 1` and `r` is coprime to `6`
(odd and not divisible by `3`). -/
theorem isZumkeller_two_pow_mul_three_pow_odd_mul {a r : ℕ} (ha : 1 ≤ a) (t : ℕ)
    (hr2 : ¬ 2 ∣ r) (hr3 : ¬ 3 ∣ r) :
    IsZumkeller (2 ^ a * 3 ^ (2 * t + 1) * r) := by
  have hcop : (2 ^ a * 3 ^ (2 * t + 1)).Coprime r :=
    Nat.Coprime.mul_left
      (Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hr2))
      (Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hr3))
  exact (isZumkeller_two_pow_mul_three_pow_odd ha t).mul_of_coprime hcop

/-- **Every positive multiple of `6` lies in A334166**, with divisor `d = 1` or
`d = 3`. -/
theorem isA334166_of_six_dvd {k : ℕ} (hk : 0 < k) (h6 : 6 ∣ k) : IsA334166 k := by
  obtain ⟨a, u, hu, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hk.ne'
  have hu0 : u ≠ 0 := by rintro rfl; exact absurd hu (by decide)
  obtain ⟨b, r, hr3, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hu0 3 (by norm_num)
  -- `r` is odd, as a factor of the odd number `3 ^ b * r`
  have hr2 : ¬ 2 ∣ r := fun h2 =>
    (Nat.not_even_iff_odd.mpr hu) (even_iff_two_dvd.mpr (dvd_mul_of_dvd_right h2 _))
  -- the `2`-adic exponent is positive
  have ha : 1 ≤ a := by
    by_contra hlt
    have ha0 : a = 0 := by omega
    subst ha0
    have h2 : 2 ∣ 3 ^ b * r := by simpa using dvd_trans (by norm_num : (2 : ℕ) ∣ 6) h6
    exact (Nat.not_even_iff_odd.mpr hu) (even_iff_two_dvd.mpr h2)
  -- the `3`-adic exponent is positive
  have hb : 1 ≤ b := by
    by_contra hlt
    have hb0 : b = 0 := by omega
    subst hb0
    have h3 : 3 ∣ 2 ^ a * r := by simpa using dvd_trans (by norm_num : (3 : ℕ) ∣ 6) h6
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h32 | h3r
    · exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h32) (by norm_num)
    · exact hr3 h3r
  have hk0 : 2 ^ a * (3 ^ b * r) ≠ 0 := by
    rintro h0; rw [h0] at hk; exact lt_irrefl 0 hk
  rcases Nat.even_or_odd b with ⟨s, hs⟩ | ⟨t, ht⟩
  · -- `b = 2s` even (so `s ≥ 1`): take `d = 3`, so `d * k = 2 ^ a * 3 ^ (2s + 1) * r`
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    refine ⟨3, Nat.mem_divisors.mpr ⟨?_, hk0⟩, ?_⟩
    · exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (dvd_pow_self 3 (by omega)) r) _
    · have hN : 3 * (2 ^ a * (3 ^ b * r)) = 2 ^ a * 3 ^ (2 * (t + 1) + 1) * r := by
        rw [hs]; ring
      rw [hN]
      exact isZumkeller_two_pow_mul_three_pow_odd_mul ha (t + 1) hr2 hr3
  · -- `b = 2t + 1` odd: take `d = 1`
    refine ⟨1, Nat.one_mem_divisors.mpr hk0, ?_⟩
    rw [one_mul, ht, ← mul_assoc]
    exact isZumkeller_two_pow_mul_three_pow_odd_mul ha t hr2 hr3

/-- For every `n` there is a term of A334166 in the window `(n, n + 6]`: the next
multiple of `6`. -/
theorem exists_isA334166_gt_le_add_six (n : ℕ) :
    ∃ k, IsA334166 k ∧ n < k ∧ k ≤ n + 6 := by
  refine ⟨6 * (n / 6 + 1), isA334166_of_six_dvd (by omega) (dvd_mul_right 6 _), ?_, ?_⟩ <;>
    omega

/-- A334166 is infinite (so `Nat.nth IsA334166` enumerates genuine terms). -/
theorem infinite_setOf_isA334166 : {k : ℕ | IsA334166 k}.Infinite :=
  Set.infinite_of_forall_exists_gt fun n => by
    obtain ⟨k, hk, hnk, -⟩ := exists_isA334166_gt_le_add_six n
    exact ⟨k, hk, hnk⟩

/-- Successor form of the conjecture: every term `k` of A334166 is followed by a
term `k'` with `k < k' ≤ k + 6`. -/
theorem exists_succ_isA334166_le_add_six {k : ℕ} (_hk : IsA334166 k) :
    ∃ k', IsA334166 k' ∧ k < k' ∧ k' ≤ k + 6 :=
  exists_isA334166_gt_le_add_six k

/-- **Ianakiev's conjecture (A334166, Ivan N. Ianakiev, Apr 17 2020).**

Verbatim: "Conjecture: The difference between two consecutive terms is 6 at most."

With `Nat.nth IsA334166 n` the `n`-th term (0-indexed; the set is infinite by
`infinite_setOf_isA334166`, so no junk value occurs), the `(n+1)`-st term exceeds the
`n`-th by at most `6`. -/
theorem nth_succ_le_nth_add_six (n : ℕ) :
    Nat.nth IsA334166 (n + 1) ≤ Nat.nth IsA334166 n + 6 := by
  obtain ⟨k, hk, hlt, hle⟩ := exists_isA334166_gt_le_add_six (Nat.nth IsA334166 n)
  by_contra hcon
  have hk_lt : k < Nat.nth IsA334166 (n + 1) := by omega
  have hk_le : k ≤ Nat.nth IsA334166 n := Nat.le_nth_of_lt_nth_succ hk_lt hk
  omega

/-- Sharpness: `30` and `36` are consecutive terms of A334166, so the bound `6`
cannot be lowered. -/
theorem sharp_thirty_thirtySix :
    IsA334166 30 ∧ IsA334166 36 ∧ ∀ k, 30 < k → k < 36 → ¬ IsA334166 k := by
  refine ⟨isA334166_of_six_dvd (by norm_num) (by norm_num),
    isA334166_of_six_dvd (by norm_num) (by norm_num), fun k h30 h36 => ?_⟩
  have h31 : ¬ IsA334166 31 := by decide +kernel
  have h32 : ¬ IsA334166 32 := by decide +kernel
  have h33 : ¬ IsA334166 33 := by decide +kernel
  have h34 : ¬ IsA334166 34 := by decide +kernel
  have h35 : ¬ IsA334166 35 := by decide +kernel
  interval_cases k
  · exact h31
  · exact h32
  · exact h33
  · exact h34
  · exact h35

end Candidates.A334166SetDivisorZumkeller
