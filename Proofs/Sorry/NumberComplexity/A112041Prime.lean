/-
# A112041 — Dale: the terms after 4 are multiples of 10

## OEIS source (retrieved with `oeis show A112041`, 2026-10-21)

```
NAME:     Numbers k such that 1*k + 1, 3*k + 1, 9*k + 1, 27*k + 1 are all primes.
TERMS:    4,60,180,760,910,1020,1230,1600,1860,2160,2280,2440,3850,5800,7320,
          8680,12940,13780,14740,17350,17400,21840,22720,22960,26040,27010,
          31050,33870,34060,35200,39900,40030,44350,45280,45540,45750,50460,52050
COMMENT (the conjecture):
  Conjecture: all terms except the first are multiples of 10.
  - _Harvey P. Dale_, Mar 26 2015
```

## Status

Triage: "open" in the sense that the entry records no proof; the triage noted
the claim is elementary.  Since `k + 1` is an odd prime for `k > 4`, `k` is
even; modulo 5, each nonzero residue of `k` makes one of `k + 1`, `3k + 1`,
`9k + 1`, `27k + 1` divisible by 5 and larger than 5.  This file proves the
conjecture outright (computational check: no exception for `k ≤ 300000`).
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A112041Prime

/-- Membership in A112041: `k + 1`, `3k + 1`, `9k + 1` and `27k + 1` are all
prime. -/
def IsTerm (k : ℕ) : Prop :=
  (k + 1).Prime ∧ (3 * k + 1).Prime ∧ (9 * k + 1).Prime ∧ (27 * k + 1).Prime

instance : DecidablePred IsTerm := fun k => by
  unfold IsTerm
  infer_instance

/-- Ground truth: the first listed terms belong to A112041. -/
example : IsTerm 4 ∧ IsTerm 60 ∧ IsTerm 180 := by
  refine ⟨?_, ?_, ?_⟩ <;> (unfold IsTerm; norm_num)

/-- Ground truth: sample non-terms (`1`: `9 + 1 = 10`; `10`: `3·10 + 1 = 31`
prime but `9·10 + 1 = 91 = 7·13`; `2`: `3 = 2 + 1` prime but `3·2 + 1 = 7`,
`9·2 + 1 = 19`, `27·2 + 1 = 55`). -/
example : ¬ IsTerm 1 ∧ ¬ IsTerm 10 ∧ ¬ IsTerm 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> (unfold IsTerm; norm_num)

/-- A prime `p` divisible by a prime `q < p` does not exist. -/
theorem not_dvd_of_prime_of_lt {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hlt : q < p) : ¬ q ∣ p := by
  intro hdvd
  have heq : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp hdvd
  omega

/-- If `4 < k` and `k + 1` is prime, then `k` is even. -/
theorem two_dvd_of_prime_succ {k : ℕ} (hk : 4 < k) (h1 : (k + 1).Prime) :
    2 ∣ k := by
  by_contra hodd
  have hdvd : 2 ∣ k + 1 := by omega
  exact not_dvd_of_prime_of_lt h1 Nat.prime_two (by omega) hdvd

/-- If `4 < k` and `k + 1`, `3k + 1`, `9k + 1`, `27k + 1` are prime, then
`5 ∣ k`. -/
theorem five_dvd_of_isTerm {k : ℕ} (hk : 4 < k) (h : IsTerm k) : 5 ∣ k := by
  obtain ⟨h1, h3, h9, h27⟩ := h
  have h5 : Nat.Prime 5 := by norm_num
  have hr : k % 5 = 0 ∨ k % 5 = 1 ∨ k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4 := by omega
  rcases hr with hr | hr | hr | hr | hr
  · omega
  · exact absurd (by omega : 5 ∣ 9 * k + 1) (not_dvd_of_prime_of_lt h9 h5 (by omega))
  · exact absurd (by omega : 5 ∣ 27 * k + 1) (not_dvd_of_prime_of_lt h27 h5 (by omega))
  · exact absurd (by omega : 5 ∣ 3 * k + 1) (not_dvd_of_prime_of_lt h3 h5 (by omega))
  · exact absurd (by omega : 5 ∣ k + 1) (not_dvd_of_prime_of_lt h1 h5 (by omega))

/-- **A112041 (Harvey P. Dale, Mar 26 2015).**  If `k > 4` and `k + 1`,
`3k + 1`, `9k + 1` and `27k + 1` are all prime, then `10 ∣ k`; i.e. every term
of A112041 except the first (`4`) is a multiple of 10. -/
theorem ten_dvd_of_isTerm {k : ℕ} (hk : 4 < k) (h : IsTerm k) : 10 ∣ k := by
  have h2 : 2 ∣ k := two_dvd_of_prime_succ hk h.1
  have h5 : 5 ∣ k := five_dvd_of_isTerm hk h
  omega

/-- Non-vacuity: the hypotheses of `ten_dvd_of_isTerm` hold jointly at `k = 60`. -/
example : 4 < 60 ∧ IsTerm 60 := ⟨by norm_num, by unfold IsTerm; norm_num⟩

end Candidates.A112041Prime
