/-
# A122399: a prime-modulus period

OEIS A122399, Peter Bala (May 31 2022); e.g.f. formula by Vladeta Jovovic
(Sep 03 2006), with A338040.
For prime `p` and `n ≥ 1`, the sum `Σ_k k^n k! S₂(n,k)` satisfies
`a(n+p-1) ≡ a(n) (mod p)`. Thus `p-1` is a period, not necessarily the
least period; minimality is not claimed. The index restriction is essential:
the periodicity need not extend to `n = 0`.
-/
import Mathlib
import Enumerative.A064618ModEventuallyPeriodic

set_option autoImplicit false

namespace Candidates.A122399BalaPrimeSum

open Finset

/-! ## Definitions -/

/-- OEIS A122399: `a(n) = ∑_{k=0}^{n} k^n k! S(n,k)`, with `S = Nat.stirlingSecond`
the Stirling numbers of the second kind (so `a(0) = 0^0 0! S(0,0) = 1`). -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ range (n + 1), k ^ n * k.factorial * Nat.stirlingSecond n k

example : a 0 = 1 := by decide
example : a 1 = 1 := by decide
example : a 2 = 9 := by decide
example : a 3 = 211 := by decide
example : a 4 = 9285 := by decide

/-! ## Reduction modulo `p` -/

/-- Modulo a prime `p`, `a(m)` is the sum of its terms with `k < p`
(terms with `k > m` vanish because `S(m,k) = 0`, terms with `k ≥ p` because `p ∣ k!`). -/
theorem cast_a_eq_sum_range_prime (p : ℕ) [hp : Fact p.Prime] (m : ℕ) :
    (a m : ZMod p) = ∑ k ∈ range p,
      ((k ^ m * k.factorial * Nat.stirlingSecond m k : ℕ) : ZMod p) := by
  have hbig : (a m : ZMod p) = ∑ k ∈ range (m + 1 + p),
      ((k ^ m * k.factorial * Nat.stirlingSecond m k : ℕ) : ZMod p) := by
    rw [a, Nat.cast_sum]
    refine sum_subset (range_subset_range.mpr (Nat.le_add_right _ _)) fun k _ hk => ?_
    have hmk : m < k := by
      rw [mem_range] at hk
      omega
    rw [Nat.stirlingSecond_eq_zero_of_lt hmk, mul_zero, Nat.cast_zero]
  rw [hbig]
  refine (sum_subset (range_subset_range.mpr (Nat.le_add_left _ _)) fun k _ hk => ?_).symm
  have hpk : p ≤ k := by
    rw [mem_range] at hk
    omega
  rw [ZMod.natCast_eq_zero_iff]
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (Nat.dvd_factorial hp.out.pos hpk) _) _

/-- The surjection formula cast to `ZMod p`:
`k! S(m,k) = ∑_{i ≤ k} (-1)^(k+i) C(k,i) i^m`. -/
theorem cast_factorial_mul_stirlingSecond (p : ℕ) (m k : ℕ) :
    ((k.factorial * Nat.stirlingSecond m k : ℕ) : ZMod p) =
      ∑ i ∈ range (k + 1), (-1) ^ (k + i) * (k.choose i : ZMod p) * (i : ZMod p) ^ m := by
  have h := congrArg (Int.cast : ℤ → ZMod p)
    (Candidates.A064618ModEventuallyPeriodic.factorial_mul_stirlingSecond m k)
  rw [Int.cast_natCast] at h
  rw [h, Candidates.A064618ModEventuallyPeriodic.surjSum]
  push_cast
  rfl

/-- Fermat in `ZMod p`: for `1 ≤ n`, every `x` satisfies `x^(n + (p-1)) = x^n`. -/
theorem pow_add_card_sub_one (p : ℕ) [Fact p.Prime] {n : ℕ} (hn : 1 ≤ n) (x : ZMod p) :
    x ^ (n + (p - 1)) = x ^ n := by
  by_cases hx : x = 0
  · rw [hx, zero_pow (by omega), zero_pow (by omega)]
  · rw [pow_add, ZMod.pow_card_sub_one_eq_one hx, mul_one]

/-- For every `m`, the residue of `a(m)` mod `p` is a fixed polynomial expression in the
powers `x^m`, `x ∈ ZMod p`. -/
theorem cast_a_eq_powSum (p : ℕ) [Fact p.Prime] (m : ℕ) :
    (a m : ZMod p) = ∑ k ∈ range p, (k : ZMod p) ^ m *
      ∑ i ∈ range (k + 1), (-1) ^ (k + i) * (k.choose i : ZMod p) * (i : ZMod p) ^ m := by
  rw [cast_a_eq_sum_range_prime]
  refine sum_congr rfl fun k _ => ?_
  rw [mul_assoc, Nat.cast_mul, cast_factorial_mul_stirlingSecond, Nat.cast_pow]

/-! ## The conjecture -/

/-- **Bala's conjecture (A122399, Peter Bala, May 31 2022), proved.**

Verbatim: "Let p be prime. The sequence obtained by reducing a(n) modulo p for
n >= 1 is purely periodic with period p - 1."

Formal reading: for every prime `p` and every `n ≥ 1`,
`a(n + (p - 1)) ≡ a(n) (mod p)`, i.e. `p - 1` is a period of `a mod p` on
`n ≥ 1` (the minimal period divides `p - 1`). -/
theorem bala_conjecture (p : ℕ) [Fact p.Prime] (n : ℕ) (hn : 1 ≤ n) :
    a (n + (p - 1)) ≡ a n [MOD p] := by
  rw [← ZMod.natCast_eq_natCast_iff, cast_a_eq_powSum, cast_a_eq_powSum]
  simp_rw [pow_add_card_sub_one p hn]

/-! ## Examples -/

-- PROVABLE: the hypotheses are jointly satisfiable and the statement is
-- non-vacuous at the entry's example `p = 7`, `n = 1`: `a(7) ≡ a(1) (mod 7)`.
example : a (1 + (7 - 1)) ≡ a 1 [MOD 7] :=
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  bala_conjecture 7 1 le_rfl

-- PROVABLE: the guard `1 ≤ n` is load-bearing: `a(0) = 1` but `a(6) ≡ 0 (mod 7)`,
-- so the period does not extend back to `n = 0`.
example : ¬ a (0 + (7 - 1)) ≡ a 0 [MOD 7] := by decide

end Candidates.A122399BalaPrimeSum
