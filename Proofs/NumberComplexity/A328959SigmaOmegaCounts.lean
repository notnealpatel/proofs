/-
# A328959 — sigma_0(n) - 2 - (Omega(n) - 1) * omega(n) is nonnegative for n ≥ 2

Gus Wiseman's conjecture in OEIS A328959, from an idea of Mats Granvik,
asserts nonnegativity of `d(n)-2-(Ω(n)-1)ω(n)` for `n ≥ 2`, with `a(1) = -1`.
In the entry, `omega` (A001222) counts prime factors with multiplicity
(Mathlib `cardFactors`, `Ω`), while `nu` (A001221) counts distinct factors
(Mathlib `cardDistinctFactors`, `ω`). The companion conjecture locating
positive terms at A320632 is not treated.

## Proof

Write `n = ∏ p_i^{e_i}` with `k = ω n` primes, exponents `e_i ≥ 1`,
`S = Σ e_i = Ω n`.  Then `d(n) = ∏ (e_i + 1)` and the claim is
`(S - 1) k + 2 ≤ ∏ (e_i + 1)`, proved by induction over a nonempty finset
(`sub_one_mul_card_add_two_le_prod`).  Adding one exponent `x ≥ 1` to a
family with sum `S ≥ k ≥ 1` leaves the slack
`(x - 1)(kS - 2k + 1) + (k - 1)(S - k) + (k - 1)(k - 2)`, which is
nonnegative since `kS - 2k + 1 ≥ (k - 1)^2`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A328959SigmaOmegaCounts

open ArithmeticFunction

/-- OEIS A328959: `a(n) = sigma_0(n) - 2 - (Ω(n) - 1) * ω(n)`, where `sigma_0`
counts divisors, `Ω` (OEIS `omega`, A001222, Mathlib `cardFactors`) counts prime
factors with multiplicity and `ω` (OEIS `nu`, A001221, Mathlib
`cardDistinctFactors`) counts distinct prime factors.  Computed in `ℤ` (the
entry's terms are signed: `a(1) = -1`). -/
def a (n : ℕ) : ℤ :=
  (sigma 0 n : ℤ) - 2 - ((cardFactors n : ℤ) - 1) * (cardDistinctFactors n : ℤ)

/-! ## Examples against the listed terms -/

/-- Evaluation route for small arguments: rewrite to divisor count and the
prime factor list, evaluate the list by simproc, then decide. -/
macro "a_eval" : tactic => `(tactic| (
  rw [a, sigma_zero_apply, cardFactors_apply, cardDistinctFactors_apply]
  simp only [Nat.primeFactorsList_ofNat]
  decide))

example : a 2 = 0 := by a_eval
example : a 12 = 0 := by a_eval
example : a 30 = 0 := by a_eval
example : a 35 = 0 := by a_eval
example : a 36 = 1 := by a_eval
example : a 60 = 1 := by a_eval
example : a 72 = 2 := by a_eval
example : a 84 = 1 := by a_eval

/-- `a(1) = -1`, the only negative term according to the entry's comment. -/
example : a 1 = -1 := by
  rw [a, sigma_zero_apply, cardFactors_one, cardDistinctFactors_one]
  decide

/-! ## Bridges from the arithmetic functions to the factorization -/

/-- `ω n` is the number of prime factors of `n` as a finset. -/
theorem cardDistinctFactors_eq_card_primeFactors (n : ℕ) :
    cardDistinctFactors n = n.primeFactors.card := by
  rw [cardDistinctFactors_apply, ← List.card_toFinset, Nat.primeFactors]

/-- `Ω n` is the sum of the exponents in the factorization of `n`. -/
theorem cardFactors_eq_sum_primeFactors (n : ℕ) :
    cardFactors n = ∑ p ∈ n.primeFactors, n.factorization p := by
  rw [cardFactors_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]

/-- Every prime factor of a nonzero `n` occurs with exponent at least one. -/
theorem one_le_factorization_of_mem_primeFactors {n p : ℕ} (hn : n ≠ 0)
    (hp : p ∈ n.primeFactors) : 1 ≤ n.factorization p :=
  Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors hp) hn
    (Nat.dvd_of_mem_primeFactors hp)

/-! ## The core finset inequality -/

/-- **Core inequality.** For a nonempty finset `s` and exponents `f i ≥ 1` on `s`,
`(Σ f - 1) * |s| + 2 ≤ ∏ (f i + 1)`. -/
theorem sub_one_mul_card_add_two_le_prod {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f : ι → ℕ) (hf : ∀ i ∈ s, 1 ≤ f i) :
    (((∑ i ∈ s, f i : ℕ) : ℤ) - 1) * s.card + 2 ≤ ∏ i ∈ s, ((f i : ℤ) + 1) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton j =>
    simp only [Finset.sum_singleton, Finset.prod_singleton, Finset.card_singleton,
      Nat.cast_one, mul_one]
    linarith
  | cons j s hj hs ih =>
    have hfs : ∀ i ∈ s, 1 ≤ f i := fun i hi => hf i (Finset.mem_cons_of_mem hi)
    have hfj : 1 ≤ f j := hf j (Finset.mem_cons_self j s)
    have hih := ih hfs
    have hk : 1 ≤ s.card := hs.card_pos
    have hSk : s.card ≤ ∑ i ∈ s, f i := by
      simpa using Finset.card_nsmul_le_sum s f 1 hfs
    rw [Finset.sum_cons, Finset.prod_cons, Finset.card_cons]
    set S : ℕ := ∑ i ∈ s, f i
    set P : ℤ := ∏ i ∈ s, ((f i : ℤ) + 1)
    set k : ℕ := s.card
    set x : ℕ := f j
    have hx : (1 : ℤ) ≤ x := by exact_mod_cast hfj
    have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk
    have hSk' : (k : ℤ) ≤ S := by exact_mod_cast hSk
    -- `kS - 2k + 1 ≥ k^2 - 2k + 1 = (k - 1)^2 ≥ 0`
    have hq : 0 ≤ (k : ℤ) * S - 2 * k + 1 := by nlinarith
    push_cast
    -- slack = (x + 1)·(IH slack) + (x - 1)(kS - 2k + 1) + (k - 1)(S - k) + (k - 1)(k - 2)
    nlinarith [mul_nonneg (sub_nonneg.mpr hx) hq,
      mul_nonneg (sub_nonneg.mpr hk') (sub_nonneg.mpr hSk'),
      mul_le_mul_of_nonneg_left hih (by linarith : (0 : ℤ) ≤ x + 1)]

/-! ## The conjecture -/

/-- **A328959 conjecture (Gus Wiseman; idea of Mats Granvik).**

For every `n ≥ 2`, `0 ≤ sigma_0(n) - 2 - (Ω(n) - 1) * ω(n)`, i.e.
`d(n) ≥ (Ω(n) - 1) ω(n) + 2`.  The guard `2 ≤ n` is the source's exception
`a(1) = -1` (checked above); `a(0)` is outside the entry's offset. -/
theorem a_nonneg (n : ℕ) (hn : 2 ≤ n) : 0 ≤ a n := by
  have hn0 : n ≠ 0 := by omega
  have hne : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
  have hcore := sub_one_mul_card_add_two_le_prod n.primeFactors hne n.factorization
    (fun p hp => one_le_factorization_of_mem_primeFactors hn0 hp)
  have hd : (sigma 0 n : ℤ) = ∏ p ∈ n.primeFactors, ((n.factorization p : ℤ) + 1) := by
    rw [sigma_zero_apply, Nat.card_divisors hn0]
    push_cast
    rfl
  rw [a, hd, cardFactors_eq_sum_primeFactors, cardDistinctFactors_eq_card_primeFactors]
  linarith

/-- The conjecture in the entry's "except for a(1)" form: every term with
positive index other than `a(1)` is nonnegative. -/
theorem a_nonneg_of_ne_one (n : ℕ) (hn0 : n ≠ 0) (hn1 : n ≠ 1) : 0 ≤ a n :=
  a_nonneg n (by omega)

/-- Non-vacuity: the hypothesis `2 ≤ n` is met, e.g. at `n = 72`. -/
example : 0 ≤ a 72 := a_nonneg 72 (by norm_num)

end Candidates.A328959SigmaOmegaCounts
