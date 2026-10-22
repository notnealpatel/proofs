/-
# A394399 — Sulaiman: twin-prime averages `k` with `gcd(k, σ(k)) = 3` are twice a square

OEIS A394399, Aied Sulaiman: twin-prime averages `k` with
`gcd(k,σ(k)) = 3` are twice a square.

A term `k` satisfies `6 ∣ k` and is not a square (A394757 module).  Since
`2 ∣ k` and `gcd(k, σ k) = 3`, `σ k` is odd, so `k = 2^e s²`
(A016957 module).  `e` even would make `k` a square, so `e = 2j + 1` and
`k = 2 (2^j s)²`.
-/
import Mathlib
import Enumerative.A016957ContainsSomeBut
import NumberComplexity.A394757TwinPrimeSigma

set_option autoImplicit false

namespace Candidates.A394399BothPrimeGcd

open ArithmeticFunction
open Candidates.A394757TwinPrimeSigma (IsTwinPrimeAverage)

/-! ## Definitions

`IsTwinPrimeAverage k := 0 < k ∧ (k - 1).Prime ∧ (k + 1).Prime` (A014574
membership) is reused from `Proofs/NumberComplexity/A394757TwinPrimeSigma.lean`.
-/

/-- A394399 membership: `k` is a twin-prime average (A014574) and
`gcd(k, σ(k)) = 3`. -/
def IsTerm (k : ℕ) : Prop :=
  IsTwinPrimeAverage k ∧ Nat.gcd k (sigma 1 k) = 3

instance (k : ℕ) : Decidable (IsTerm k) := by
  unfold IsTerm; infer_instance

/-! ## Examples -/

-- `σ(18) = 39` and `gcd(18, 39) = 3`.
example : sigma 1 18 = 39 ∧ Nat.gcd 18 39 = 3 := by decide

-- The entry's second example: `σ(5652) = 14378`, `gcd = 2`, so `5652` is not a term.
example : sigma 1 5652 = 14378 ∧ Nat.gcd 5652 14378 = 2 := by decide +kernel

-- The first two listed terms are exactly the terms below `100`.
example : ∀ k < 100, IsTerm k ↔ (k = 18 ∨ k = 72) := by decide

/-! ## Proof -/

/-- A term of A394399 is a term of A394757 (`3` is prime). -/
theorem isTerm_a394757_of_isTerm {k : ℕ} (hk : IsTerm k) :
    Candidates.A394757TwinPrimeSigma.IsTerm k :=
  ⟨hk.1, by rw [hk.2]; exact Nat.prime_three⟩

/-- An even `k` with `gcd(k, σ k) = 3` has odd `σ k`. -/
theorem odd_sigma_of_two_dvd_of_gcd_eq_three {k : ℕ} (h2 : 2 ∣ k)
    (hg : Nat.gcd k (sigma 1 k) = 3) : Odd (sigma 1 k) := by
  rcases Nat.even_or_odd (sigma 1 k) with he | ho
  · have h2g : 2 ∣ Nat.gcd k (sigma 1 k) := Nat.dvd_gcd h2 he.two_dvd
    rw [hg] at h2g
    omega
  · exact ho

/-- **A394399 conjecture (Aied Sulaiman, 2026).**

That is: if `k - 1` and `k + 1` are both prime and
`gcd(k, σ(k)) = 3`, then `k = 2 m²` for some natural `m`. -/
theorem a394399_exists_eq_two_mul_sq {k : ℕ} (hk : IsTerm k) :
    ∃ m : ℕ, k = 2 * m ^ 2 := by
  have h6 : 6 ∣ k :=
    Candidates.A394757TwinPrimeSigma.six_dvd_of_isTerm (isTerm_a394757_of_isTerm hk)
  have hsq : ¬ IsSquare k :=
    Candidates.A394757TwinPrimeSigma.not_isSquare_of_isTwinPrimeAverage hk.1 h6
  have hodd : Odd (sigma 1 k) :=
    odd_sigma_of_two_dvd_of_gcd_eq_three (Nat.dvd_trans (by norm_num) h6) hk.2
  obtain ⟨e, s, hes⟩ :=
    Candidates.A016957ContainsSomeBut.exists_two_pow_mul_sq_of_odd_sigma k hodd
  rcases Nat.even_or_odd e with ⟨j, hj⟩ | ⟨j, hj⟩
  · exact absurd ⟨2 ^ j * s, by rw [hes, hj, pow_add]; ring⟩ hsq
  · exact ⟨2 ^ j * s, by rw [hes, hj]; ring⟩

/-! ## Examples -/

-- Satisfiability of the hypothesis: `18 = 2 · 3²` is a term.
example : IsTerm 18 := by decide


end Candidates.A394399BothPrimeGcd
