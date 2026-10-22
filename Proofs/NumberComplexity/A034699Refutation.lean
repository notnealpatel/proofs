/-
# A034699 — Serov: numbers strictly between consecutive primes have distinct
# largest prime-power factors

I. V. Serov's conjecture in OEIS A034699 (2019), refuted by Michel Marcus
(2019). Between consecutive primes `4177` and `4201`, the distinct numbers
`4180 = 2^2 · 5 · 11 · 19` and `4199 = 13 · 17 · 19` both have largest
prime-power factor `19`. The later signed variant is not formalized here.

## Formal conventions

`a n` is the largest prime-power divisor of `n`, with the OEIS convention
`a 1 = 1` (offset 1; `1 = p^0` is the empty product).  The value `a 0 = 1`
is junk outside the OEIS domain and never used: the conjecture only evaluates
`a` strictly between two primes, hence at arguments `≥ 3`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A034699Refutation

/-! ## Definitions -/

/-- A034699: the largest prime-power factor of `n`, i.e. the largest divisor
of `n` that is a prime power (`IsPrimePow`), and `1` when there is none
(`n = 1`, matching the OEIS term `a(1) = 1`). -/
def a (n : ℕ) : ℕ := max 1 ((n.divisors.filter IsPrimePow).sup id)

/-! ## Examples -/

-- The first 79 OEIS terms `a(1), …, a(79)`, evaluated.
example : ((List.range 79).map fun i => a (i + 1)) =
    [1, 2, 3, 4, 5, 3, 7, 8, 9, 5, 11, 4, 13, 7, 5, 16, 17, 9, 19, 5, 7, 11, 23,
      8, 25, 13, 27, 7, 29, 5, 31, 32, 11, 17, 7, 9, 37, 19, 13, 8, 41, 7, 43, 11,
      9, 23, 47, 16, 49, 25, 17, 13, 53, 27, 11, 8, 19, 29, 59, 5, 61, 31, 9, 64,
      13, 11, 67, 17, 23, 7, 71, 9, 73, 37, 25, 19, 11, 13, 79] := by
  decide +kernel

/-! ## The conjecture -/

/-- **Serov's conjecture (A034699, I. V. Serov, 2019).**

Formalized: whenever `p < q` are primes with no prime strictly between them,
`a` is injective on the open interval `(p, q)`. -/
def Conjecture : Prop :=
  ∀ p q : ℕ, p.Prime → q.Prime → p < q → (∀ r : ℕ, p < r → r < q → ¬ r.Prime) →
    Set.InjOn a (Set.Ioo p q)

/-! ## Refutation -/

/-- `4177` and `4201` are consecutive primes. -/
theorem consecutive_primes_4177_4201 :
    Nat.Prime 4177 ∧ Nat.Prime 4201 ∧ ∀ r : ℕ, 4177 < r → r < 4201 → ¬ r.Prime := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro r hlo hhi
  interval_cases r <;> norm_num

/-- `a(4180) = 19`, since `4180 = 2^2 · 5 · 11 · 19`. -/
theorem a_4180 : a 4180 = 19 := by decide +kernel

/-- `a(4199) = 19`, since `4199 = 13 · 17 · 19`. -/
theorem a_4199 : a 4199 = 19 := by decide +kernel

/-- **Serov's conjecture is false** (Michel Marcus, 2019).

Counterexample: `4177 = prime(574)` and `4201 = prime(575)` are consecutive
primes, and the distinct numbers `4180, 4199` strictly between them share the
largest prime-power factor `a(4180) = a(4199) = 19`. -/
theorem conjecture_false : ¬ Conjecture := by
  intro hconj
  obtain ⟨hp, hq, hgap⟩ := consecutive_primes_4177_4201
  have hinj : Set.InjOn a (Set.Ioo 4177 4201) := hconj 4177 4201 hp hq (by norm_num) hgap
  have hmem₁ : (4180 : ℕ) ∈ Set.Ioo 4177 4201 := by norm_num
  have hmem₂ : (4199 : ℕ) ∈ Set.Ioo 4177 4201 := by norm_num
  have heq : a 4180 = a 4199 := by rw [a_4180, a_4199]
  have hcollide : (4180 : ℕ) = 4199 := hinj hmem₁ hmem₂ heq
  omega

end Candidates.A034699Refutation
