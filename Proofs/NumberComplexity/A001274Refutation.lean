/-
# A001274 — Wilson: totient-equal consecutive pairs start composite and
# `≡ 2, 3 (mod 6)`

Robert G. Wilson v's conjecture in OEIS A001274 asserts that, except for
`1` and `3`, numbers `k` with `φ(k) = φ(k + 1)` are composite and congruent to
`2` or `3` modulo `6`. Paul Kinlaw's counterexample, reported by Giovanni
Resta, is `k = 3044760173455`: both totients equal `1500291072000`, but
`k ≡ 1 (mod 6)`. Only the residue clause fails at this witness.

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

/-! ## Definitions -/

/-- A001274 membership: `k` is a positive integer with `φ(k) = φ(k + 1)`. -/
def IsTerm (k : ℕ) : Prop := 0 < k ∧ Nat.totient k = Nat.totient (k + 1)

instance (k : ℕ) : Decidable (IsTerm k) := by
  unfold IsTerm
  infer_instance

/-! ## Examples -/

-- The OEIS terms below `600` are exactly `1, 3, 15, 104, 164, 194, 255, 495, 584`.
example : (Finset.range 600).filter IsTerm = {1, 3, 15, 104, 164, 194, 255, 495, 584} := by
  decide +kernel

/-! ## The conjecture -/

/-- **Wilson's conjecture (A001274, Robert G. Wilson v).**

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

/-- **Wilson's conjecture is false** (Paul Kinlaw, reported by Giovanni Resta).

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
