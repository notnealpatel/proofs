/-
# A136050 — digit sum of a twin-prime product is one less than a multiple of 9

OEIS A136050, Harvey P. Dale: the decimal digit sum of the product
of twin primes `(p,p+2)` is `8 mod 9` when `3 < p`.
The excluded pair `(3,5)` gives digit sum `6`.

For `3 < p` with `p` and `p + 2` prime, `p` is odd and `p ≢ 0, 1 (mod 3)`, so
`p = 6 k + 5` and `p (p + 2) = 9 (4 k ^ 2 + 8 k + 3) + 8`.  The decimal digit sum is
congruent to its argument modulo 9 (`Nat.modEq_nine_digits_sum`).
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A136050TwinPrimesDecimal

/-! ## Definitions -/

/-- The product `p (p + 2)` of a twin-prime pair `(p, p + 2)`, the terms of A037074 when
`p` runs over the lesser twin primes (A001359). -/
def twinProduct (p : ℕ) : ℕ := p * (p + 2)

/-- The A136050 term attached to the lesser twin prime `p`: the decimal digit sum
(A007953) of the twin-prime product `p (p + 2)` (A037074). -/
def twinDigitSum (p : ℕ) : ℕ := (Nat.digits 10 (twinProduct p)).sum

/-! ### Examples: the first terms of A037074 and A136050

The lesser twin primes begin `3, 5, 11, 17, 29, 41, 59, 71, 101`; A037074 begins
`15, 35, 143, 323, 899, 1763, 3599, 5183, 10403` and A136050 begins
`6, 8, 8, 8, 26, 17, 26, 17, 8`. -/

example : [3, 5, 11, 17, 29, 41, 59, 71, 101].map twinProduct =
    [15, 35, 143, 323, 899, 1763, 3599, 5183, 10403] := by decide

example : [3, 5, 11, 17, 29, 41, 59, 71, 101].map twinDigitSum =
    [6, 8, 8, 8, 26, 17, 26, 17, 8] := by norm_num [twinDigitSum, twinProduct]

/-- The excluded initial term: for the pair `(3, 5)` the digit sum `6` is not one less
than a multiple of 9, so the `3 < p` guard is load-bearing. -/
example : twinDigitSum 3 = 6 ∧ ¬ 9 ∣ twinDigitSum 3 + 1 := by
  norm_num [twinDigitSum, twinProduct]

/-- Non-vacuity: `(5, 7)` is a twin-prime pair with `3 < 5`. -/
example : Nat.Prime 5 ∧ Nat.Prime (5 + 2) ∧ 3 < 5 := by norm_num

/-! ## Proof -/

/-- The lesser member `p > 3` of a twin-prime pair satisfies `p ≡ 5 (mod 6)`. -/
theorem mod_six_eq_five {p : ℕ} (hp : p.Prime) (hq : (p + 2).Prime) (h3 : 3 < p) :
    p % 6 = 5 := by
  have hodd : p % 2 = 1 := by
    by_contra hne
    have htwo : 2 ∣ p := by omega
    have hcases := hp.eq_one_or_self_of_dvd 2 htwo
    omega
  have hnot0 : p % 3 ≠ 0 := by
    -- otherwise `3 ∣ p`, so `p = 3`
    intro h0
    have hcases := hp.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero h0)
    omega
  have hnot1 : p % 3 ≠ 1 := by
    -- otherwise `3 ∣ p + 2`, so `p + 2 = 3`
    intro h1
    have hdvd : 3 ∣ p + 2 := by omega
    have hcases := hq.eq_one_or_self_of_dvd 3 hdvd
    omega
  omega

/-- For the lesser member `p > 3` of a twin-prime pair, `p (p + 2) ≡ 8 (mod 9)`. -/
theorem twinProduct_mod_nine {p : ℕ} (hp : p.Prime) (hq : (p + 2).Prime) (h3 : 3 < p) :
    twinProduct p % 9 = 8 := by
  obtain ⟨k, hk⟩ : ∃ k, p = 6 * k + 5 := ⟨p / 6, by have := mod_six_eq_five hp hq h3; omega⟩
  have hprod : twinProduct p = 8 + 9 * (4 * k ^ 2 + 8 * k + 3) := by
    rw [twinProduct, hk]; ring
  rw [hprod, Nat.add_mul_mod_self_left]

/-- **Dale's conjecture (A136050, Harvey P. Dale, 2016).**

Here the terms are indexed by the lesser twin prime `p` (A001359), the initial
term is `p = 3`, and the term is the decimal digit sum of `p (p + 2)`.  Stated as the
residue: for twin primes `(p, p + 2)` with `3 < p`, the digit sum is `≡ 8 (mod 9)`. -/
theorem twinDigitSum_mod_nine {p : ℕ} (hp : p.Prime) (hq : (p + 2).Prime) (h3 : 3 < p) :
    twinDigitSum p % 9 = 8 := by
  have hcong : twinProduct p ≡ twinDigitSum p [MOD 9] := Nat.modEq_nine_digits_sum _
  rw [← hcong]
  exact twinProduct_mod_nine hp hq h3

/-- Dale’s conjecture (A136050), divisibility form: for twin primes
`(p,p+2)` with `3 < p`, the decimal digit sum of `p(p+2)` plus one
is divisible by `9`. -/
theorem nine_dvd_twinDigitSum_add_one {p : ℕ} (hp : p.Prime) (hq : (p + 2).Prime)
    (h3 : 3 < p) : 9 ∣ twinDigitSum p + 1 := by
  have hres := twinDigitSum_mod_nine hp hq h3
  omega

end Candidates.A136050TwinPrimesDecimal
