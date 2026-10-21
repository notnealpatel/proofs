/-
# A001274 — Wilson: totient-equal consecutive pairs start composite and
# `≡ 2, 3 (mod 6)`

## OEIS source (retrieved with `oeis show A001274`, 2026-10-21)

```
NAME:     Numbers k such that phi(k) = phi(k+1).
TERMS:    1,3,15,104,164,194,255,495,584,975,2204,2625,2834,3255,3705,5186,
          5187,10604,11715,13365,18315,22935,25545,32864,38804,39524,46215,
          48704,49215,49335,56864,57584,57645,64004,65535,73124,105524,107864,
          123824,131144,164175,184635
COMMENT (the conjecture):
  Conjecture: Except for the first two terms, all terms are composite and
  congruent to either 2 or 3 (mod 6). - _Robert G. Wilson v_, Apr 10 2019
COMMENT (immediately following):
  Paul Kinlaw has noticed that up to 10^13 the only counterexample to the
  above conjecture is a(7424) = 3044760173455. - _Giovanni Resta_, May 23 2019
COMMENT (later):
  There are 42999 terms < 10^15 and (5186,5187) is the only pair of
  consecutive terms. Also, a(22113) = 127872660090175 is another
  counterexample to the conjecture about terms being congruent to 2 or 3
  mod 6. - _Jud McCranie_, Jan 27 2026
```

The entry itself records the counterexample (Kinlaw/Resta, 2019; a second one
by McCranie, 2026); no later comment revives the conjecture.

## Status

**False.**  This module refutes the conjecture with Kinlaw's counterexample
`k = 3044760173455`:

* `k = 5 · 7 · 11 · 13 · 17 · 19 · 41 · 71 · 647`,
* `k + 1 = 2^4 · 73 · 1217 · 2142001`,
* `φ(k) = φ(k + 1) = 1500291072000 = 2^16 · 3^4 · 5^3 · 7 · 17 · 19`,
* `k ≡ 1 (mod 6)` (it is composite, but not `≡ 2, 3 (mod 6)`).

Computational evidence (Sage, `euler_phi`, `factor`): both counterexamples
recorded in the entry satisfy `φ(k) = φ(k+1)` and `k ≡ 1 (mod 6)`.

## Formal conventions

The OEIS sequence lists positive `k`; "the first two terms" are `1` and `3`.
Membership is stated as `φ k = φ (k + 1)` with Mathlib's `Nat.totient`; the
junk value `φ 0 = 0 ≠ 1 = φ 1` already excludes `k = 0`, so no positivity
guard changes the statement.  The conjecture is formalized with explicit
exclusions `k ≠ 1`, `k ≠ 3`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A001274Refutation

/-! ## Definition layer -/

/-- A001274 membership: `k` is a positive integer with `φ(k) = φ(k + 1)`. -/
def IsTerm (k : ℕ) : Prop := 0 < k ∧ Nat.totient k = Nat.totient (k + 1)

instance (k : ℕ) : Decidable (IsTerm k) := by
  unfold IsTerm
  infer_instance

/-! ## Ground truth -/

-- The OEIS terms below `600` are exactly `1, 3, 15, 104, 164, 194, 255, 495, 584`.
example : (Finset.range 600).filter IsTerm = {1, 3, 15, 104, 164, 194, 255, 495, 584} := by
  decide +kernel

/-! ## The conjecture -/

/-- **Wilson's conjecture (A001274, Robert G. Wilson v, Apr 10 2019).**

Verbatim: "Conjecture: Except for the first two terms, all terms are composite
and congruent to either 2 or 3 (mod 6)."

Formalized: every term `k` of A001274 other than the first two terms `1` and
`3` is not prime and satisfies `k % 6 = 2 ∨ k % 6 = 3`.  (Every term other
than `1` is `≥ 3`, so "not prime" is "composite" here.) -/
def Conjecture : Prop :=
  ∀ k : ℕ, IsTerm k → k ≠ 1 → k ≠ 3 → ¬ k.Prime ∧ (k % 6 = 2 ∨ k % 6 = 3)

/-! ## Refutation -/

/-- `φ(3044760173455) = 1500291072000`, from
`3044760173455 = 5 · 7 · 11 · 13 · 17 · 19 · 41 · 71 · 647`. -/
theorem totient_kinlaw : Nat.totient 3044760173455 = 1500291072000 := by
  have hfac : (3044760173455 : ℕ) =
      5 * (7 * (11 * (13 * (17 * (19 * (41 * (71 * 647))))))) := by norm_num
  rw [hfac,
    Nat.totient_mul (by norm_num), Nat.totient_prime (by norm_num),
    Nat.totient_mul (by norm_num), Nat.totient_prime (by norm_num),
    Nat.totient_mul (by norm_num), Nat.totient_prime (by norm_num),
    Nat.totient_mul (by norm_num), Nat.totient_prime (by norm_num),
    Nat.totient_mul (by norm_num), Nat.totient_prime (by norm_num),
    Nat.totient_mul (by norm_num), Nat.totient_prime (by norm_num),
    Nat.totient_mul (by norm_num), Nat.totient_prime (by norm_num),
    Nat.totient_mul (by norm_num), Nat.totient_prime (by norm_num),
    Nat.totient_prime (by norm_num)]

/-- `φ(3044760173456) = 1500291072000`, from
`3044760173456 = 2^4 · 73 · 1217 · 2142001`. -/
theorem totient_kinlaw_succ : Nat.totient (3044760173455 + 1) = 1500291072000 := by
  have hfac : (3044760173455 + 1 : ℕ) = 2 ^ 4 * (73 * (1217 * 2142001)) := by norm_num
  rw [hfac,
    Nat.totient_mul (by norm_num), Nat.totient_prime_pow (by norm_num) (by norm_num),
    Nat.totient_mul (by norm_num), Nat.totient_prime (by norm_num),
    Nat.totient_mul (by norm_num), Nat.totient_prime (by norm_num),
    Nat.totient_prime (by norm_num)]
  norm_num

/-- `3044760173455` (the term `a(7424)`) belongs to A001274. -/
theorem isTerm_kinlaw : IsTerm 3044760173455 :=
  ⟨by norm_num, by rw [totient_kinlaw, totient_kinlaw_succ]⟩

/-- **Wilson's conjecture is false** (Paul Kinlaw, reported by Giovanni Resta,
May 23 2019).

Counterexample: `k = a(7424) = 3044760173455` satisfies
`φ(k) = φ(k + 1) = 1500291072000`, is neither `1` nor `3`, and is composite,
but `k ≡ 1 (mod 6)`.  The composite half of the conjecture survives this
witness; only the residue clause fails.  (McCranie's `a(22113) =
127872660090175` is a second counterexample of the same kind.) -/
theorem conjecture_false : ¬ Conjecture := by
  intro hconj
  have hres := (hconj 3044760173455 isTerm_kinlaw (by norm_num) (by norm_num)).2
  have hmod : (3044760173455 : ℕ) % 6 = 1 := by norm_num
  omega

end Candidates.A001274Refutation
