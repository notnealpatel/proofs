/-
# A220846 — refutation of the injectivity conjecture

Jaroslav Krizek's injectivity conjecture in OEIS A220846 fails at
`a(4) = a(13) = 14`: the divisor product of `4` is `8`, giving `8+4+2`,
whereas at a prime `p` the value is `p+1`. The sequence is indexed by
positive integers.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A220846Refutation

/-- A220846: `a n = ∑_{d ∣ n} (∏_{e ∣ n} e) / d`.  The division is exact for
`n ≠ 0` because `d` is one of the factors of the product; at `n = 0` the
divisor set is empty and `a 0 = 0`, outside the entry's offset. -/
def a (n : ℕ) : ℕ := ∑ d ∈ n.divisors, (∏ e ∈ n.divisors, e) / d

/-! ## Examples against the first listed terms -/

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

/-- **The A220846 injectivity conjecture** (Jaroslav Krizek):
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
whose value `a n - 1` is prime collides with that prime. -/
theorem conjecture_false : ¬ Conjecture := by
  intro h
  have h4 : a 4 = 14 := by decide
  have h13 : a 13 = 14 := by decide
  have heq : (4 : ℕ) = 13 := h 4 13 (by norm_num) (by norm_num) (h4.trans h13.symm)
  exact absurd heq (by norm_num)

end Candidates.A220846Refutation
