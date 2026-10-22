/-
# A074162 — Irvine: `a(k * 5^6) = 0`

## OEIS source (retrieved with `oeis show A074162`, 2026-10-21)

```
NAME:     a(1) = 1; a(n) = smallest multiple of n (>n) using all nonprime digits
          (1,4,6,8,9 and 0) if n is a prime else using all prime digits and 1 if
          n is composite; or 0 if no such number exists.
TERMS:    1,4,6,12,10,12,14,32,27,0,44,72,91,112,75,32,68,72,114,0,231,132,46,
          72,75,52,135,112,116,0,186,352,132,272,175,72,111,152,117,0,164,252,
          86,132,135,322,94,1152,735,0,153,312,106,1512,275,112,171,232,118,0,488
COMMENT:  a(10k) = 0. Are there other values of n such that a(n) =0?
COMMENT:  A pigeonhole argument shows the conjecture to be true (that only
          a(10k) = 0). - _Joshua Zucker_, May 08 2006
COMMENT (the conjecture):
          Conjecture (contradicts Zucker statement): a(k*5^6) = 0.
          - _Sean A. Irvine_, Jan 13 2025
```

"Using all nonprime digits" means "using only digits from the set": the listed
terms `a(2) = 4`, `a(3) = 6` use a single digit.

## Status

This file proves the stated Irvine conjecture.  For a hypothetical admissible
`m`, its decimal digits lie in the zero-free set `{1,2,3,5,7}`.  Consequently,
if `5^6 ∣ m` and `m > 0`, then `m mod 10^6` is a nonzero multiple of `15625`
whose decimal digits are among the digits of `m`; a `decide` check over the 63
nonzero multiples of `15625` below `10^6` shows each has a digit outside that
set.  (Positivity and divisibility alone would not make the remainder nonzero:
`m = 10^6` is a counterexample.)  As a corollary Zucker's claim is false:
`a(15625) = 0` although `10 ∤ 15625`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A074162IrvineWhoseDecimal

/-! ## Definition layer -/

/-- The digits allowed for multiples of `n`: the nonprime digits `{0,1,4,6,8,9}`
when `n` is prime, and the prime digits together with `1`, i.e. `{1,2,3,5,7}`,
otherwise. -/
def allowedDigits (n : ℕ) : Finset ℕ :=
  if n.Prime then {0, 1, 4, 6, 8, 9} else {1, 2, 3, 5, 7}

/-- `m` is a candidate value for `a(n)`: a multiple of `n` exceeding `n` whose
decimal digits all lie in `allowedDigits n`. -/
def Admissible (n m : ℕ) : Prop :=
  n < m ∧ n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d ∈ allowedDigits n

/-- `Admissible n m` is decidable (used by the ground-truth `decide` checks). -/
instance (n m : ℕ) : Decidable (Admissible n m) := by
  unfold Admissible; infer_instance

open Classical in
/-- OEIS A074162: `a(1) = 1`; for `n ≠ 1`, `a(n)` is the least admissible
multiple of `n` (see `Admissible`), or `0` if none exists. -/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 1 then 1 else if h : ∃ m, Admissible n m then Nat.find h else 0

/-- Evaluation lemma for ground-truth checks: if `v` is admissible for `n ≠ 1`
and no smaller number is, then `a n = v`. -/
theorem a_eq_of_admissible {n v : ℕ} (hn : n ≠ 1) (hv : Admissible n v)
    (hmin : ∀ m < v, ¬ Admissible n m) : a n = v := by
  classical
  have hex : ∃ m, Admissible n m := ⟨v, hv⟩
  simp only [a, hn, if_false, dif_pos hex]
  exact (Nat.find_eq_iff hex).2 ⟨hv, hmin⟩

/-- If `n ≠ 1` has no admissible multiple, then `a n = 0`. -/
theorem a_eq_zero_of_forall_not_admissible {n : ℕ} (hn : n ≠ 1)
    (h : ∀ m, ¬ Admissible n m) : a n = 0 := by
  classical
  have hex : ¬ ∃ m, Admissible n m := fun ⟨m, hm⟩ => h m hm
  simp only [a, hn, if_false, dif_neg hex]

/-! ## Ground truth against the DATA line -/

example : a 1 = 1 := by simp [a]

example : a 2 = 4 :=
  a_eq_of_admissible (by norm_num) (by decide) (by decide)

example : a 3 = 6 :=
  a_eq_of_admissible (by norm_num) (by decide) (by decide)

example : a 4 = 12 :=
  a_eq_of_admissible (by norm_num) (by decide) (by decide)

example : a 9 = 27 :=
  a_eq_of_admissible (by norm_num) (by decide) (by decide)

example : a 12 = 72 :=
  a_eq_of_admissible (by norm_num) (by decide) (by decide)

/-! ## Digit lemmas -/

/-- The digit set `{1,2,3,5,7}` used for composite `n`. -/
abbrev compositeDigits : Finset ℕ := {1, 2, 3, 5, 7}

/-- If every decimal digit of `m` lies in a set `S` avoiding `0`, then the same
holds for `m % 10 ^ k`: its digits are the lowest `k` digits of `m`. -/
theorem digits_mod_pow_subset {S : Finset ℕ} (h0 : 0 ∉ S) :
    ∀ (k m : ℕ), (∀ d ∈ Nat.digits 10 m, d ∈ S) →
      ∀ d ∈ Nat.digits 10 (m % 10 ^ k), d ∈ S := by
  intro k
  induction k with
  | zero =>
    intro m _ d hd
    simp only [pow_zero, Nat.mod_one, Nat.digits_zero, List.not_mem_nil] at hd
  | succ k ih =>
    intro m hm d hd
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · simp at hd
    have hdef : Nat.digits 10 m = m % 10 :: Nat.digits 10 (m / 10) :=
      Nat.digits_def' (by norm_num) hpos
    have hlast : m % 10 ∈ S := hm _ (by rw [hdef]; exact List.mem_cons_self)
    have hlast0 : m % 10 ≠ 0 := fun h => h0 (h ▸ hlast)
    have htail : ∀ d ∈ Nat.digits 10 (m / 10), d ∈ S := fun d hd' =>
      hm d (by rw [hdef]; exact List.mem_cons_of_mem _ hd')
    have hsplit : m % 10 ^ (k + 1) = m % 10 + 10 * ((m / 10) % 10 ^ k) := by
      rw [pow_succ', Nat.mod_mul]
    have hdig : Nat.digits 10 (m % 10 ^ (k + 1)) =
        m % 10 :: Nat.digits 10 ((m / 10) % 10 ^ k) := by
      rw [hsplit]
      exact Nat.digits_add 10 (by norm_num) _ _ (Nat.mod_lt _ (by norm_num)) (Or.inl hlast0)
    rw [hdig] at hd
    rcases List.mem_cons.1 hd with rfl | hd'
    · exact hlast
    · exact ih (m / 10) htail d hd'

/-- Finite check: every nonzero multiple of `15625 = 5^6` below `10^6` has a
decimal digit outside `{1,2,3,5,7}`. -/
theorem finite_check : ∀ j < 64, 0 < j →
    ∃ d ∈ Nat.digits 10 (15625 * j), d ∉ compositeDigits := by
  decide

/-- **Core of Irvine's conjecture.** No positive multiple of `5^6 = 15625` has all
its decimal digits in `{1,2,3,5,7}`. -/
theorem not_digits_subset_of_dvd {m : ℕ} (hpos : 0 < m) (hdvd : 15625 ∣ m) :
    ¬ ∀ d ∈ Nat.digits 10 m, d ∈ compositeDigits := by
  intro hm
  have h0 : (0 : ℕ) ∉ compositeDigits := by decide
  set r := m % 10 ^ 6 with hr
  have hrdig : ∀ d ∈ Nat.digits 10 r, d ∈ compositeDigits :=
    digits_mod_pow_subset h0 6 m hm
  have hrdvd : 15625 ∣ r := (Nat.dvd_mod_iff (by norm_num)).2 hdvd
  have hlast : m % 10 ∈ compositeDigits :=
    hm _ (by rw [Nat.digits_def' (by norm_num) hpos]; exact List.mem_cons_self)
  have hrlast : r % 10 = m % 10 := by
    rw [hr, Nat.mod_mod_of_dvd _ (by norm_num)]
  have hrpos : 0 < r := by
    rcases Nat.eq_zero_or_pos r with hr0 | hr0
    · rw [hr0] at hrlast
      rw [← hrlast] at hlast
      exact absurd hlast h0
    · exact hr0
  have hrlt : r < 10 ^ 6 := Nat.mod_lt _ (by norm_num)
  obtain ⟨j, hj⟩ := hrdvd
  have hjlt : j < 64 := by omega
  have hjpos : 0 < j := by
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · omega
    · exact hj0
  obtain ⟨d, hd, hdS⟩ := finite_check j hjlt hjpos
  rw [← hj] at hd
  exact hdS (hrdig d hd)

/-- Every positive multiple of `15625` is composite (it is divisible by `5` and
exceeds `5`), so its allowed digit set is `{1,2,3,5,7}`. -/
theorem allowedDigits_of_dvd {n : ℕ} (hpos : 0 < n) (hdvd : 15625 ∣ n) :
    allowedDigits n = compositeDigits := by
  have hnp : ¬ n.Prime := by
    intro hp
    have h5 : 5 ∣ n := (Nat.dvd_trans (by norm_num) hdvd)
    have hle : 15625 ≤ n := Nat.le_of_dvd hpos hdvd
    rcases (Nat.dvd_prime hp).1 h5 with h | h <;> omega
  simp [allowedDigits, hnp]

/-! ## The conjecture -/

/-- **Irvine's conjecture (A074162, Sean A. Irvine, Jan 13 2025).**

Verbatim: "Conjecture (contradicts Zucker statement): a(k*5^6) = 0."

For every `k ≥ 1` (the sequence has offset `1`), `a(15625 k) = 0`: no multiple
of `15625 k` larger than it has all decimal digits in `{1,2,3,5,7}`. -/
theorem irvine_a_mul_five_pow_six (k : ℕ) (hk : 0 < k) : a (5 ^ 6 * k) = 0 := by
  have hpos : 0 < 5 ^ 6 * k := by positivity
  have hne : 5 ^ 6 * k ≠ 1 := by omega
  refine a_eq_zero_of_forall_not_admissible hne ?_
  rintro m ⟨hlt, hdvd, hdig⟩
  have hdvd' : 15625 ∣ m := Nat.dvd_trans (Dvd.intro k (by norm_num)) hdvd
  rw [allowedDigits_of_dvd hpos (Dvd.intro k (by norm_num))] at hdig
  exact not_digits_subset_of_dvd (by omega) hdvd' hdig

/-- **Zucker's claim is false.** Zucker (May 08 2006) asserted that `a(n) = 0`
only for `n = 10k`; `n = 15625` satisfies `a(n) = 0` with `10 ∤ n`. -/
theorem zucker_claim_false : ¬ ∀ n : ℕ, 1 ≤ n → a n = 0 → 10 ∣ n := by
  intro h
  have ha : a 15625 = 0 := by
    simpa using irvine_a_mul_five_pow_six 1 (by norm_num)
  exact absurd (h 15625 (by norm_num) ha) (by norm_num)

/-- The entry's first comment, `a(10k) = 0` for `k ≥ 1`: every positive multiple
of `10` ends in the digit `0`, which is never allowed for composite `n`, and
`10 k` is composite. -/
theorem a_ten_mul (k : ℕ) (hk : 0 < k) : a (10 * k) = 0 := by
  have hne : 10 * k ≠ 1 := by omega
  refine a_eq_zero_of_forall_not_admissible hne ?_
  rintro m ⟨hlt, hdvd, hdig⟩
  have hnp : ¬ (10 * k).Prime := by
    intro hp
    have h2 : 2 ∣ 10 * k := Nat.dvd_trans (by norm_num) (Dvd.intro k rfl)
    rcases (Nat.dvd_prime hp).1 h2 with h | h <;> omega
  have hmpos : 0 < m := by omega
  have hm10 : m % 10 = 0 := Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Dvd.intro k rfl) hdvd)
  have hmem : m % 10 ∈ allowedDigits (10 * k) :=
    hdig _ (by rw [Nat.digits_def' (by norm_num) hmpos]; exact List.mem_cons_self)
  rw [hm10] at hmem
  simp [allowedDigits, hnp] at hmem

-- Ground truth: `a(10) = 0` and `a(15625) = 0`.
example : a 10 = 0 := by simpa using a_ten_mul 1 (by norm_num)

example : a 15625 = 0 := by simpa using irvine_a_mul_five_pow_six 1 (by norm_num)

-- Non-vacuity of `Admissible`: `a(5) = 10`, where `5` is prime and the digit `0`
-- is allowed.
example : a 5 = 10 :=
  a_eq_of_admissible (by norm_num) (by decide) (by decide)

end Candidates.A074162IrvineWhoseDecimal
