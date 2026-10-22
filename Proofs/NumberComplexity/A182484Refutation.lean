/-
# A182484 — Layman's refutation: `∏ k^(2k-p-1)` square iff `p` prime

The conjecture in OEIS A182484, refuted by John W. Layman (2012):
at the composite `p = 63`, `∏_{k=1}^{62} k^(2k-64)` is an integer square.
The entry's integrality claim for prime `p` cites Vandendriessche–Lee,
Problem A13.

## Formal conventions

* The exponent `2k - p - 1` is negative for `k < (p+1)/2`, so the product is
  computed in `ℚ` with integer exponents (`zpow`); the exponent is formed in
  `ℤ` after casting, so no `Nat` truncation occurs.
* "Perfect square" means the square of an integer: `∃ m : ℤ, x = m ^ 2`.
  (For odd `p` all exponents are even, so the product is always a square in
  `ℚ`; the rational reading would make the conjecture trivially false at
  every odd composite, which is not what the entry means.)
* The conjecture quantifies over `1 < p`.  At `p = 1` the product is empty
  and equals `1 = 1 ^ 2`, a degenerate counterexample excluded by the guard;
  the refutation below uses `p = 63`, not the degenerate case.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A182484Refutation

/-! ## Definitions -/

/-- The A182484 product at an arbitrary natural `p`:
`∏_{k=1}^{p-1} k ^ (2k - p - 1)`, computed in `ℚ` with the exponent in `ℤ`. -/
def prodA (p : ℕ) : ℚ := ∏ k ∈ Finset.Ico 1 p, (k : ℚ) ^ (2 * (k : ℤ) - p - 1)

/-- The A182484 sequence, 0-indexed: `seqA i = a(i + 1) = prodA (prime(i + 1))`,
where `Nat.nth Nat.Prime i` is the `(i+1)`-st prime. -/
noncomputable def seqA (i : ℕ) : ℚ := prodA (Nat.nth Nat.Prime i)

/-- `x` is a perfect square of an integer. -/
def IsIntSquare (x : ℚ) : Prop := ∃ m : ℤ, x = (m : ℚ) ^ 2

/-! ## Examples

The first six listed terms `1, 1, 4, 225, 8930250000, 9001015156742400`
at `p = 2, 3, 5, 7, 11, 13`. -/

example : seqA 0 = 1 := by
  rw [seqA, Nat.nth_prime_zero_eq_two]; decide +kernel

example : seqA 1 = 1 := by
  rw [seqA, Nat.nth_prime_one_eq_three]; decide +kernel

example : seqA 2 = 4 := by
  rw [seqA, Nat.nth_prime_two_eq_five]; decide +kernel

example : seqA 3 = 225 := by
  rw [seqA, Nat.nth_prime_three_eq_seven]; decide +kernel

example : seqA 4 = 8930250000 := by
  rw [seqA, Nat.nth_prime_four_eq_eleven]; decide +kernel

example : prodA 13 = 9001015156742400 := by decide +kernel

-- The degenerate value excluded by the `1 < p` guard.
example : prodA 1 = 1 := by decide +kernel

-- A non-integral value at an odd composite (`p = 9`): the entry's integrality
-- comment is specific to primes.
example : prodA 9 = 2458624 / 9 := by decide +kernel

/-! ## The conjecture -/

/-- **The A182484 conjecture** (recorded in the entry as "Conjecture (false!)").

Formalized: for every natural `p` with `1 < p`, the product
`∏_{k=1}^{p-1} k^(2k-p-1)` is the square of an integer iff `p` is prime. -/
def Conjecture : Prop := ∀ p : ℕ, 1 < p → (IsIntSquare (prodA p) ↔ p.Prime)

/-! ## The counterexample `p = 63` -/

/-- Layman's counterexample: `∏_{k=1}^{62} k^(2k-64)` is the square of an
explicit integer. -/
theorem isIntSquare_prodA_sixtyThree : IsIntSquare (prodA 63) :=
  ⟨322617071056918100735804433928082016376043520195063351896092509174199490959645703042182302386151668949523543219499040294099924718198430758969945930215010078850294650459101251482062350916750511884875643080930881490206972110922172120977139397136211228624611663423067730394730467308881705589059756978234620283802621411047122490497959588173675537109375,
    by decide +kernel⟩

/-- `63 = 3^2 · 7` is not prime. -/
theorem not_prime_sixtyThree : ¬ Nat.Prime 63 := by norm_num

/-- **The A182484 conjecture is false.** Counterexample (John W. Layman,
2012): at `p = 63` the product `∏_{k=1}^{62} k^(2k-64)` is the square
of an integer, yet `63` is not prime.  The true statement behind the entry is
the one-directional integrality comment (`a(n)` is an integer for prime `p`,
Vandendriessche–Lee, Problem A13); squareness does not characterize primes. -/
theorem conjecture_false : ¬ Conjecture := fun hconj =>
  not_prime_sixtyThree ((hconj 63 (by norm_num)).mp isIntSquare_prodA_sixtyThree)

end Candidates.A182484Refutation
