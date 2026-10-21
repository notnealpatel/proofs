/-
# A220846 — refutation of the injectivity conjecture

## OEIS source (retrieved 2026-10-21 with `oeis show A220846`, cross-checked
against the live entry https://oeis.org/A220846)

```
NAME:     a(n) = sum_(d|n) ((product_(d|n) d) / d).
TERMS:    1,3,4,14,6,72,8,120,39,180,12,4032,14,336,360,1984,18,12636,20,16800,
          672,792,24,829440,155,1092,1080,43904,30,1944000,32,64512,1584,...
COMMENT:  Conjecture: sequence is injective (all terms of this sequence occur
          exactly once).
FORMULA:  a(n) = sum_(d|n) (A007955(n) / d).
          a(p) = p + 1 for prime p.
AUTHOR:   Jaroslav Krizek, Dec 22 2012
```

The conjecture comment carries no separate attribution or date; it is part of
the original submission (Jaroslav Krizek, Dec 22 2012).  No later comment or
extension retracts it.

## Status

This module **refutes** the conjecture.  The entry's own data already lists
`a(4) = 14 = a(13)`: the divisors of `4` are `{1, 2, 4}` with product `8`, so
`a(4) = 8 + 4 + 2 = 14`, while `a(13) = 13 + 1 = 14` by the prime formula.
More generally every composite `n` with `a(n) - 1` prime collides with that
prime; a bounded search finds `(4,13), (6,71), (10,179), (15,359), ...`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A220846Refutation

/-- A220846: `a n = ∑_{d ∣ n} (∏_{e ∣ n} e) / d`.  The division is exact for
`n ≠ 0` because `d` is one of the factors of the product; at `n = 0` the
divisor set is empty and `a 0 = 0`, outside the entry's offset. -/
def a (n : ℕ) : ℕ := ∑ d ∈ n.divisors, (∏ e ∈ n.divisors, e) / d

/-! ## Ground truth against the first listed terms -/

example : a 1 = 1 := by decide
example : a 2 = 3 := by decide
example : a 3 = 4 := by decide
example : a 4 = 14 := by decide
example : a 5 = 6 := by decide
example : a 6 = 72 := by decide
example : a 8 = 120 := by decide
example : a 9 = 39 := by decide
example : a 12 = 4032 := by decide
example : a 13 = 14 := by decide

/-- **The A220846 injectivity conjecture** (Jaroslav Krizek, Dec 22 2012):
"Conjecture: sequence is injective (all terms of this sequence occur exactly
once)", read over the entry's domain of positive integers. -/
def Conjecture : Prop :=
  ∀ m n : ℕ, 0 < m → 0 < n → a m = a n → m = n

/-- The entry's formula `a(p) = p + 1` for prime `p`. -/
theorem a_prime {p : ℕ} (hp : p.Prime) : a p = p + 1 := by
  have hp1 : (1 : ℕ) ≠ p := hp.one_lt.ne
  have hpos : 0 < p := hp.pos
  have hprod : ∏ e ∈ p.divisors, e = p := by
    rw [hp.divisors, Finset.prod_insert (by simpa using hp1), Finset.prod_singleton, one_mul]
  rw [a, hprod, hp.divisors, Finset.sum_insert (by simpa using hp1), Finset.sum_singleton,
    Nat.div_one, Nat.div_self hpos]

/-- **Refutation.** The A220846 injectivity conjecture is false:
`a 4 = 14 = a 13` with `4 ≠ 13`.  The collision is an instance of the general
mechanism `a(p) = p + 1` for prime `p` (see `a_prime`): any composite `n`
whose value `a n - 1` is prime collides with that prime.  No corrected form is
evident from the entry. -/
theorem conjecture_false : ¬ Conjecture := by
  intro h
  have h4 : a 4 = 14 := by decide
  have h13 : a 13 = 14 := by decide
  have heq : (4 : ℕ) = 13 := h 4 13 (by norm_num) (by norm_num) (h4.trans h13.symm)
  exact absurd heq (by norm_num)

end Candidates.A220846Refutation
