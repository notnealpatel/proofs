/-
# A294646 — refutation of the conjecture "a(n) is never 2 or 2n or 2n-2"

## OEIS source (retrieved 2026-10-21, `oeis show A294646` and https://oeis.org/A294646)

```
NAME:     a(n) = (1/2)^(2*n) mod (2*n+1).
TERMS:    1,1,1,7,1,1,4,1,1,16,1,11,25,1,1,25,4,1,10,1,1,16,1,36,13,1,9,43,1,1,...
COMMENT:  a(n) is the smallest k > 0 such that k*2^(2*n) == 1 (mod 2*n+1).
COMMENT:  1 <= a(n) <= 2*n, and is always coprime to 2*n+1.
COMMENT (the conjecture, unsigned; entry authors below):
  Conjecture: a(n) is never 2 or 2*n or 2*n-2.
AUTHOR:   Robert Israel and Thomas Ordowski, Nov 05 2017
PROGRAM:  (PARI) a(n) = (1/2)^(2*n) % (2*n+1); \\ _Michel Marcus_, Nov 06 2017
```

No later comment in the entry retracts or qualifies the conjecture.

## Status

This module **refutes** the conjecture.  Let `q = 3 * 2^66 + 1` (prime) and
`N = 67 * q = 14831182235262479499331 = 2n + 1` with
`n = 7415591117631239749665`.  Since `3 * 2^(N-1) ≡ -1 (mod N)`, the inverse
power `(1/2)^(2n) mod N` equals `N - 3 = 2n - 2`.  The kernel check uses
`reduce_mod_char` (fast modular exponentiation with a proof term) in
`ZMod N`; no `native_decide`.

The other two clauses (`a(n) ≠ 2`, i.e. `N ∤ 2^N - 1`, and `a(n) ≠ 2n`, i.e.
`2^(N-1) ≢ -1 (mod N)`) are classical and true; they are not formalized here.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A294646Refutation

/-- OEIS A294646: `a(n) = (1/2)^(2n) mod (2n+1)`, i.e. the canonical
representative in `[0, 2n]` of `(2⁻¹)^(2n)` in `ZMod (2n+1)`. -/
def a294646 (n : ℕ) : ℕ := (((2 : ZMod (2 * n + 1))⁻¹) ^ (2 * n)).val

/-- Characterization: if `k < 2n+1` and `k * 2^(2n) ≡ 1 (mod 2n+1)`, then
`a(n) = k`.  This is the entry's first comment ("the smallest `k > 0` such that
`k*2^(2*n) == 1 (mod 2*n+1)`") in the form used for evaluation. -/
theorem a294646_eq_of_mul_pow_eq_one (n k : ℕ) (hk : k < 2 * n + 1)
    (h : (k : ZMod (2 * n + 1)) * (2 : ZMod (2 * n + 1)) ^ (2 * n) = 1) :
    a294646 n = k := by
  have hcop : Nat.Coprime 2 (2 * n + 1) :=
    Nat.coprime_two_left.mpr (odd_two_mul_add_one n)
  have hinv : (2 : ZMod (2 * n + 1)) * (2 : ZMod (2 * n + 1))⁻¹ = 1 := by
    simpa using ZMod.coe_mul_inv_eq_one 2 hcop
  have hk' : ((2 : ZMod (2 * n + 1))⁻¹) ^ (2 * n) = (k : ZMod (2 * n + 1)) := by
    calc ((2 : ZMod (2 * n + 1))⁻¹) ^ (2 * n)
        = ((k : ZMod (2 * n + 1)) * (2 : ZMod (2 * n + 1)) ^ (2 * n)) *
            ((2 : ZMod (2 * n + 1))⁻¹) ^ (2 * n) := by rw [h, one_mul]
      _ = (k : ZMod (2 * n + 1)) *
            ((2 : ZMod (2 * n + 1)) * (2 : ZMod (2 * n + 1))⁻¹) ^ (2 * n) := by
          rw [mul_pow, mul_assoc]
      _ = (k : ZMod (2 * n + 1)) := by rw [hinv, one_pow, mul_one]
  unfold a294646
  rw [hk', ZMod.val_natCast_of_lt hk]

/-! ## Ground truth: the first ten listed terms `1,1,1,7,1,1,4,1,1,16` -/

example : a294646 1 = 1 := a294646_eq_of_mul_pow_eq_one 1 1 (by norm_num) (by decide)
example : a294646 2 = 1 := a294646_eq_of_mul_pow_eq_one 2 1 (by norm_num) (by decide)
example : a294646 3 = 1 := a294646_eq_of_mul_pow_eq_one 3 1 (by norm_num) (by decide)
example : a294646 4 = 7 := a294646_eq_of_mul_pow_eq_one 4 7 (by norm_num) (by decide)
example : a294646 5 = 1 := a294646_eq_of_mul_pow_eq_one 5 1 (by norm_num) (by decide)
example : a294646 6 = 1 := a294646_eq_of_mul_pow_eq_one 6 1 (by norm_num) (by decide)
example : a294646 7 = 4 := a294646_eq_of_mul_pow_eq_one 7 4 (by norm_num) (by decide)
example : a294646 8 = 1 := a294646_eq_of_mul_pow_eq_one 8 1 (by norm_num) (by decide)
example : a294646 9 = 1 := a294646_eq_of_mul_pow_eq_one 9 1 (by norm_num) (by decide)
example : a294646 10 = 16 := a294646_eq_of_mul_pow_eq_one 10 16 (by norm_num) (by decide)

/-! ## The conjecture -/

/-- **Conjecture (A294646, entry of Robert Israel and Thomas Ordowski, Nov 05 2017).**
Verbatim: "Conjecture: a(n) is never 2 or 2*n or 2*n-2."

Stated for `n ≥ 1` (the entry's offset); the value `2n - 2` is formed in `ℤ`
after casting, so no truncated subtraction occurs. -/
def Conjecture : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    a294646 n ≠ 2 ∧ a294646 n ≠ 2 * n ∧ (a294646 n : ℤ) ≠ 2 * (n : ℤ) - 2

/-- The counterexample value: for `n = 7415591117631239749665`
(`2n + 1 = 67 * (3 * 2^66 + 1) = 14831182235262479499331`),
`a(n) = 2n - 2 = 14831182235262479499328`. -/
theorem a294646_counterexample :
    a294646 7415591117631239749665 = 14831182235262479499328 := by
  apply a294646_eq_of_mul_pow_eq_one
  · norm_num
  · norm_num
    reduce_mod_char

/-- **The A294646 conjecture is false.**  At `n = 7415591117631239749665`,
`2n + 1 = 67 * (3 * 2^66 + 1)` with `3 * 2^66 + 1` prime, and
`3 * 2^(2n) ≡ -1 (mod 2n+1)`, so `a(n) = 2n - 2`.  The clause `a(n) ≠ 2n - 2`
fails; the clauses `a(n) ≠ 2` and `a(n) ≠ 2n` are classically true, so the
intended statement presumably was the latter two only. -/
theorem a294646_false : ¬ Conjecture := by
  intro hconj
  have hce := (hconj 7415591117631239749665 (by norm_num)).2.2
  rw [a294646_counterexample] at hce
  norm_num at hce

end Candidates.A294646Refutation
