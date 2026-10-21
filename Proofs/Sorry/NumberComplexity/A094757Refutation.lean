/-
# A094757 — Murthy: every `n` shares its ratio `n / π(n)` with some `k ≠ n`

## OEIS source (retrieved with `oeis show A094757`, 2026-10-21)

```
NAME:     Least positive k <= n such that n*pi(k) = k*pi(n), where pi(n) is
          the number of primes <= n (A000720).
OFFSET:   1
TERMS:    1,2,3,2,5,2,7,2,9,10,11,12,13,14,10,16,17,18,19,10,21,22,23,16,
          25,26,27,28,29,27,31,32,27,34,35,36,37,38,39,40,41,42,43,44,...
COMMENT (the conjecture, unsigned in the comment, by the entry's author
         Amarnath Murthy):
  Conjecture: For every n there exists a k different from n (possibly
  k > n) such that n*pi(k) = k*pi(n).
COMMENT (later, refuting):
  From _David A. Corneth_, Nov 15 2019: (Start)
  ...
  _Amarnath Murthy_'s conjecture above is false. For n = 3 we have
  pi(n)/n = 2/3. For no other k we have pi(k)/k = 2/3. Therefore the
  conjecture is false. (End)
```

No later comment retracts Corneth's refutation.

## Status

**False.**  This module refutes the conjecture at `n = 3`, Corneth's
witness: `3 π(k) = 2 k` with `k ≥ 1` forces `k = 3`.  For `k ≤ 9` this is a
finite check; for `k ≥ 10`, the Mathlib sieve bound
`Nat.primeCounting'_add_le` with modulus `6` gives
`π(k) ≤ 5 + 2 ⌊(k - 6) / 6⌋`, whence `3 π(k) < 2 k`.

The value `k` ranges over the positive integers, as in the entry's name;
without that guard `k = 0` satisfies `n π(0) = 0 π(n)` trivially.  The
case `n = 1` is a second, degenerate counterexample (`π(k) = 0` forces
`k = 1`), recorded below.

Computational evidence (Python, 2026-10-21): among `1 ≤ k ≤ 10^6` the only
`k` with `π(k) / k = 2/3` is `k = 3`, and `3 π(k) - 2 k ≤ -1` for all
`4 ≤ k ≤ 10^6`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A094757Refutation

/-- Some positive `k` satisfies `n π(k) = k π(n)`: `k = n` when `n ≥ 1`, and
`k = 1` when `n = 0`.  This makes `a` below well defined. -/
theorem exists_pos_mul_primeCounting_eq (n : ℕ) :
    ∃ k : ℕ, 0 < k ∧ n * Nat.primeCounting k = k * Nat.primeCounting n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · exact ⟨1, Nat.one_pos, by simp [hn]⟩
  · exact ⟨n, hn, rfl⟩

/-- OEIS A094757: the least positive `k` with `n π(k) = k π(n)`.  For
`n ≥ 1` (the entry's offset) this least `k` is at most `n`, since `k = n`
qualifies, so it agrees with the entry's "least positive `k ≤ n`".  At the
junk index `n = 0` the value is `1`. -/
noncomputable def a (n : ℕ) : ℕ := Nat.find (exists_pos_mul_primeCounting_eq n)

/-! ## Ground truth -/

/-- The first twenty-four listed terms `a(1), …, a(24)`. -/
theorem a_ground_truth : ∀ n ∈ List.range' 1 24,
    a n = [1, 2, 3, 2, 5, 2, 7, 2, 9, 10, 11, 12, 13, 14, 10, 16, 17, 18, 19, 10,
      21, 22, 23, 16].getD (n - 1) 0 := by
  intro n hn
  rw [a, Nat.find_eq_iff]
  revert n
  decide

/-- `a(n) ≤ n` on the entry's range `n ≥ 1`. -/
theorem a_le (n : ℕ) (hn : 0 < n) : a n ≤ n :=
  Nat.find_min' (exists_pos_mul_primeCounting_eq n) ⟨hn, rfl⟩

/-! ## The conjecture -/

/-- **Murthy's conjecture (A094757).**  Verbatim: "Conjecture: For every n
there exists a k different from n (possibly k > n) such that
n*pi(k) = k*pi(n)."  Here `n` ranges over the entry's offset `n ≥ 1` and
`k` over the positive integers, as in the entry's name. -/
def Conjecture : Prop :=
  ∀ n : ℕ, 0 < n → ∃ k : ℕ, 0 < k ∧ k ≠ n ∧
    n * Nat.primeCounting k = k * Nat.primeCounting n

/-- Satisfiability of the conjecture's body: for `n = 4` the value `k = 2`
works (`4 π(2) = 4 = 2 π(4)`), so the statement is not vacuous. -/
example : 0 < 2 ∧ 2 ≠ 4 ∧ 4 * Nat.primeCounting 2 = 2 * Nat.primeCounting 4 := by
  decide

/-! ## Refutation -/

/-- Sieve bound modulo `6`: for `k ≥ 10`, `3 π(k) < 2 k`. -/
theorem three_mul_primeCounting_lt (k : ℕ) (hk : 10 ≤ k) :
    3 * Nat.primeCounting k < 2 * k := by
  have hsieve : Nat.primeCounting' (7 + (k - 6)) ≤
      Nat.primeCounting' 7 + Nat.totient 6 * ((k - 6) / 6 + 1) :=
    Nat.primeCounting'_add_le (by norm_num) (by norm_num) (k - 6)
  have h7 : Nat.primeCounting' 7 = 3 := by decide
  have h6 : Nat.totient 6 = 2 := by decide
  have hidx : 7 + (k - 6) = k + 1 := by omega
  have hpi : Nat.primeCounting k ≤ 3 + 2 * ((k - 6) / 6 + 1) := by
    rw [Nat.primeCounting, ← hidx, ← h7, ← h6]
    exact hsieve
  omega

/-- For `n = 3` the only positive `k` with `3 π(k) = k π(3)` is `k = 3`. -/
theorem eq_three_of_mul_primeCounting_eq (k : ℕ) (hk : 0 < k)
    (h : 3 * Nat.primeCounting k = k * Nat.primeCounting 3) : k = 3 := by
  have h3 : Nat.primeCounting 3 = 2 := by decide
  rw [h3] at h
  by_cases hsmall : k < 10
  · interval_cases k <;> revert h <;> decide
  · have hlt : 3 * Nat.primeCounting k < 2 * k :=
      three_mul_primeCounting_lt k (by omega)
    omega

/-- For `n = 1` the only positive `k` with `1 π(k) = k π(1)` is `k = 1`:
`π(1) = 0` forces `π(k) = 0`, i.e. `k < 2`. -/
theorem eq_one_of_mul_primeCounting_eq (k : ℕ) (hk : 0 < k)
    (h : 1 * Nat.primeCounting k = k * Nat.primeCounting 1) : k = 1 := by
  have h1 : Nat.primeCounting 1 = 0 := by decide
  rw [h1, mul_zero, one_mul] at h
  by_contra hne
  have h2 : 2 ≤ k := by omega
  have hmono : Nat.primeCounting 2 ≤ Nat.primeCounting k := Nat.monotone_primeCounting h2
  have hpi2 : Nat.primeCounting 2 = 1 := by decide
  omega

/-- **The conjecture is false.**  Counterexample `n = 3` (David A. Corneth,
Nov 15 2019): `π(3)/3 = 2/3`, and no positive `k ≠ 3` has `π(k)/k = 2/3`,
since `3 π(k) < 2 k` for every `k ≥ 4`.  The degenerate `n = 1` also fails
(`theorem a094757_conjecture_false_at_one`); restricting to `n ≥ 2`, which
the author may have intended, does not rescue the claim, because `n = 3`
still fails. -/
theorem a094757_conjecture_false : ¬ Conjecture := by
  intro hconj
  obtain ⟨k, hkpos, hkne, hk⟩ := hconj 3 (by norm_num)
  exact hkne (eq_three_of_mul_primeCounting_eq k hkpos hk)

/-- The conjecture already fails on the range `n ≥ 2`, at `n = 3`. -/
theorem a094757_conjecture_false_of_two_le :
    ¬ ∀ n : ℕ, 2 ≤ n → ∃ k : ℕ, 0 < k ∧ k ≠ n ∧
      n * Nat.primeCounting k = k * Nat.primeCounting n := by
  intro hconj
  obtain ⟨k, hkpos, hkne, hk⟩ := hconj 3 (by norm_num)
  exact hkne (eq_three_of_mul_primeCounting_eq k hkpos hk)

/-- The degenerate counterexample `n = 1`: `π(1) = 0`, and the only
positive `k` with `π(k) = 0` is `k = 1`. -/
theorem a094757_conjecture_false_at_one :
    ¬ ∃ k : ℕ, 0 < k ∧ k ≠ 1 ∧ 1 * Nat.primeCounting k = k * Nat.primeCounting 1 := by
  rintro ⟨k, hkpos, hkne, hk⟩
  exact hkne (eq_one_of_mul_primeCounting_eq k hkpos hk)

end Candidates.A094757Refutation
