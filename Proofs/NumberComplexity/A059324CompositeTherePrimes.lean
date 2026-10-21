/-
# A059324 — Lallouet: no prime pair `(p, q > p^2)` with `q - p^2 = 6n - 4`

## OEIS source (retrieved with `oeis show A059324`, 2026-10-21)

```
NAME:     Numbers n such that 6n + 5 is composite.
TERMS:    5,10,12,15,19,20,23,25,26,30,33,34,35,36,40,45,47,49,50,53,54,55,
          56,60,61,62,65,67,68,70,72,75,78,80,82,85,87,88,89,90,91,95,96,100,
          ...
FORMULA:  a(n) = A046953(n-1) - 1.
COMMENT (the conjecture):
  Conjecture: There exists no pair of primes (p, q > p^2) such that
  q - p^2 = 6*n - 4 (see A138479). - Philippe LALLOUET
  (philip.lallouet(AT)orange.fr), Mar 20 2008
```

## Status

Triage status: open (no proof recorded in the entry or found in the
literature by the triage), tractability "trivial".  The argument is an
elementary case analysis on `p`:

* `p = 2`: `q = 6n` is even and larger than `2`, so not prime;
* `p = 3`: `q = 6n + 5`, composite by hypothesis;
* `p ≥ 5`: `p^2 ≡ 1 (mod 3)`, so `3 ∣ q = p^2 + 6n - 4` with `q > 3`.

## Formalization notes

* `n` ranges over `ℕ`; the predicate `InA059324 n` is the entry's NAME
  ("`6n + 5` is composite"), spelled `1 < 6n + 5 ∧ ¬ (6n + 5).Prime`.
  The `1 <` conjunct is automatic and only mirrors "composite".
* The difference `q - p^2` and the right side `6n - 4` are both taken in `ℤ`
  (cast before subtracting), so no `ℕ`-truncation enters the statement.
* The side condition `p^2 < q` from the source ("`q > p^2`") is kept.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A059324CompositeTherePrimes

/-- Membership in OEIS A059324: `n` is such that `6n + 5` is composite
(greater than `1` and not prime). -/
def InA059324 (n : ℕ) : Prop :=
  1 < 6 * n + 5 ∧ ¬ (6 * n + 5).Prime

instance : DecidablePred InA059324 := fun n => by
  unfold InA059324; infer_instance

/-! ## Ground truth against the listed terms `5, 10, 12, 15, 19, 20, …` -/

example : InA059324 5 := by unfold InA059324; norm_num
example : InA059324 10 := by unfold InA059324; norm_num
example : InA059324 12 := by unfold InA059324; norm_num
example : InA059324 19 := by unfold InA059324; norm_num
example : ¬ InA059324 0 := by unfold InA059324; norm_num
example : ¬ InA059324 1 := by unfold InA059324; norm_num
example : ¬ InA059324 4 := by unfold InA059324; norm_num
example : ¬ InA059324 6 := by unfold InA059324; norm_num

/-- Members of A059324 are positive: `n = 0` gives `6n + 5 = 5`, a prime. -/
theorem one_le_of_inA059324 {n : ℕ} (hn : InA059324 n) : 1 ≤ n := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    exact absurd Nat.prime_five hn.2
  · exact hpos

/-- If `p` is a prime other than `3`, then `p^2 ≡ 1 (mod 3)`. -/
theorem sq_mod_three_of_prime_ne_three {p : ℕ} (hp : p.Prime) (h3 : p ≠ 3) :
    p ^ 2 % 3 = 1 := by
  have hndvd : ¬ 3 ∣ p := by
    intro hdvd
    rcases hp.eq_one_or_self_of_dvd 3 hdvd with h | h
    · omega
    · exact h3 h.symm
  have hmod : p % 3 = 1 ∨ p % 3 = 2 := by omega
  rw [Nat.pow_mod]
  rcases hmod with h | h <;> simp [h]

/-- **Lallouet's conjecture (A059324, Philippe Lallouet, Mar 20 2008).**

Verbatim: "Conjecture: There exists no pair of primes (p, q > p^2) such that
q - p^2 = 6*n - 4 (see A138479)."

For every `n` in A059324 (i.e. `6n + 5` composite) there are no primes `p`,
`q` with `p^2 < q` and `q - p^2 = 6n - 4` (difference computed in `ℤ`). -/
theorem not_exists_prime_pair {n : ℕ} (hn : InA059324 n) :
    ¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ^ 2 < q ∧
      (q : ℤ) - (p : ℤ) ^ 2 = 6 * (n : ℤ) - 4 := by
  rintro ⟨p, q, hp, hq, hlt, hdiff⟩
  have hn1 : 1 ≤ n := one_le_of_inA059324 hn
  have hsumZ : (q : ℤ) + 4 = (p : ℤ) ^ 2 + 6 * (n : ℤ) := by linarith
  have hsum : q + 4 = p ^ 2 + 6 * n := by exact_mod_cast hsumZ
  by_cases h2 : p = 2
  · -- `q = 6n` is even and exceeds `2`.
    subst h2
    have hq6 : q = 6 * n := by omega
    have hdvd : 2 ∣ q := ⟨3 * n, by omega⟩
    rcases hq.eq_one_or_self_of_dvd 2 hdvd with h | h <;> omega
  by_cases h3 : p = 3
  · -- `q = 6n + 5`, composite by hypothesis.
    subst h3
    have hq5 : q = 6 * n + 5 := by omega
    exact hn.2 (hq5 ▸ hq)
  · -- `p ≥ 5`: `3 ∣ q` and `q > p^2 ≥ 4`.
    have hsq : p ^ 2 % 3 = 1 := sq_mod_three_of_prime_ne_three hp h3
    have hdvd : 3 ∣ q := by omega
    have hp2 : 2 ≤ p := hp.two_le
    have hp4 : 4 ≤ p ^ 2 := by nlinarith
    rcases hq.eq_one_or_self_of_dvd 3 hdvd with h | h <;> omega

/-- Non-vacuity: `n = 5` lies in A059324, and the hypotheses `p^2 < q` with
`p, q` prime are jointly satisfiable (e.g. `p = 2`, `q = 5`); only the
difference condition fails, as the theorem asserts. -/
example : InA059324 5 ∧ (2 : ℕ).Prime ∧ (5 : ℕ).Prime ∧ 2 ^ 2 < 5 := by
  refine ⟨by unfold InA059324; norm_num, Nat.prime_two, Nat.prime_five, by norm_num⟩

end Candidates.A059324CompositeTherePrimes
