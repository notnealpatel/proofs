/-
# A088883 / A088884 — Rotondo: residues mod 6 of the "concat-with-reverse ± 2" primes

Davide Rotondo's conjectures in OEIS A088883 and A088884 (2025): primes
whose concatenation with their reversal, plus `2`, is prime are `1 mod 6`;
for minus `2` they are `5 mod 6`, except `3`. The two numbers cannot both
be prime.

Since `10 ≡ 1 (mod 3)`, `N(p) ≡ 2 · digitsum(p) ≡ 2p (mod 3)`.  If
`p ≡ 2 (mod 3)` then `3 ∣ N(p) + 2`; if `p ≡ 1 (mod 3)` then `3 ∣ N(p) - 2`;
both numbers exceed `3` because `N(p) ≥ 10p ≥ 20`.  The case `p ≡ 0 (mod 3)`
is `p = 3`, where `N = 33`, `35` is composite and `31` is prime; the case
`p = 2` gives `N = 22`, with `24` and `20` both composite.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A088883RotondoPrimeLen

/-! ## Definitions -/

/-- `catRev p` is the decimal concatenation of `p` with its digit reversal,
`N(p) = p * 10^len(p) + reverse(p)`.  `Nat.digits 10 p` is little-endian, so the
reversed digit list supplies the low-order block (the number `reverse(p)`) and
the original list supplies the high-order block (the number `p`). -/
def catRev (p : ℕ) : ℕ :=
  Nat.ofDigits 10 ((Nat.digits 10 p).reverse ++ Nat.digits 10 p)

example : catRev 2 = 22 := by decide
example : catRev 3 = 33 := by decide
example : catRev 7 = 77 := by decide
example : catRev 19 = 1991 := by decide
example : catRev 109 = 109901 := by decide
example : catRev 1039 = 10399301 := by decide

/-- The defining formula `N(p) = p * 10^len(p) + reverse(p)`, where `len(p)` is
the number of decimal digits and `reverse(p)` is read from the reversed digit
list. -/
theorem catRev_eq (p : ℕ) :
    catRev p = p * 10 ^ (Nat.digits 10 p).length +
      Nat.ofDigits 10 (Nat.digits 10 p).reverse := by
  rw [catRev, Nat.ofDigits_append, Nat.ofDigits_digits, List.length_reverse]
  ring

/-! ### Examples: first terms of A088883 and A088884 -/

/-- `7` is in A088883: `77 + 2 = 79` is prime. -/
example : (catRev 7 + 2).Prime := by
  rw [show catRev 7 = 77 by decide]; norm_num

/-- `109` is in A088883: `109901 + 2 = 109903` is prime. -/
example : (catRev 109 + 2).Prime := by
  rw [show catRev 109 = 109901 by decide]; norm_num

/-- `3` is in A088884: `33 - 2 = 31` is prime. -/
example : (catRev 3 - 2).Prime := by
  rw [show catRev 3 = 33 by decide]; norm_num

/-- `5` is in A088884: `55 - 2 = 53` is prime. -/
example : (catRev 5 - 2).Prime := by
  rw [show catRev 5 = 55 by decide]; norm_num

/-- `11` is in A088884: `1111 - 2 = 1109` is prime. -/
example : (catRev 11 - 2).Prime := by
  rw [show catRev 11 = 1111 by decide]; norm_num

/-! ## Helper lemmas -/

/-- For `0 < p`, `N(p) ≥ 10 p`; in particular the natural subtraction
`catRev p - 2` in the statements below never truncates for prime `p`. -/
theorem ten_mul_le_catRev {p : ℕ} (hp : 0 < p) : 10 * p ≤ catRev p := by
  have hlen : (Nat.digits 10 p).length ≠ 0 := by
    rw [Ne, List.length_eq_zero_iff, Nat.digits_eq_nil_iff_eq_zero]
    omega
  have hpow : 10 ≤ 10 ^ (Nat.digits 10 p).length := Nat.le_self_pow hlen 10
  have hmul : 10 * p ≤ p * 10 ^ (Nat.digits 10 p).length := by
    rw [mul_comm p]
    exact Nat.mul_le_mul_right p hpow
  rw [catRev_eq]
  exact le_add_right hmul

/-- Load-bearing congruence: `N(p) ≡ 2p (mod 3)`, because `10 ≡ 1 (mod 3)`
makes `N(p)` congruent to twice the digit sum of `p`. -/
theorem catRev_mod_three (p : ℕ) : catRev p % 3 = 2 * p % 3 := by
  have h1 : catRev p ≡ ((Nat.digits 10 p).reverse ++ Nat.digits 10 p).sum [MOD 3] := by
    have hof := Nat.ofDigits_modEq 10 3 ((Nat.digits 10 p).reverse ++ Nat.digits 10 p)
    simpa [catRev, Nat.ofDigits_one] using hof
  have h2 : p ≡ (Nat.digits 10 p).sum [MOD 3] := Nat.modEq_three_digits_sum p
  rw [List.sum_append, List.sum_reverse] at h1
  have h3 : 2 * p ≡ (Nat.digits 10 p).sum + (Nat.digits 10 p).sum [MOD 3] := by
    rw [two_mul]
    exact Nat.ModEq.add h2 h2
  exact h1.trans h3.symm

/-- If `p ≡ 2 (mod 3)`, then `N(p) + 2` is divisible by `3` and exceeds `3`,
so it is not prime. -/
theorem not_prime_catRev_add_two {p : ℕ} (hp0 : 0 < p) (h3 : p % 3 = 2) :
    ¬ (catRev p + 2).Prime := by
  intro hpr
  have hmod := catRev_mod_three p
  have hdvd : 3 ∣ catRev p + 2 := by omega
  have heq : 3 = catRev p + 2 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hpr).mp hdvd
  have hle := ten_mul_le_catRev hp0
  omega

/-- If `p ≡ 1 (mod 3)`, then `N(p) - 2` is divisible by `3` and exceeds `3`,
so it is not prime. -/
theorem not_prime_catRev_sub_two {p : ℕ} (hp0 : 0 < p) (h3 : p % 3 = 1) :
    ¬ (catRev p - 2).Prime := by
  intro hpr
  have hmod := catRev_mod_three p
  have hle := ten_mul_le_catRev hp0
  have hdvd : 3 ∣ catRev p - 2 := by omega
  have heq : 3 = catRev p - 2 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hpr).mp hdvd
  omega

/-- A prime divisible by `3` is `3`. -/
theorem eq_three_of_prime_of_mod_three {p : ℕ} (hp : p.Prime) (h3 : p % 3 = 0) : p = 3 :=
  ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.dvd_of_mod_eq_zero h3)).symm

/-! ## The conjectures -/

/-- Rotondo's A088883 conjecture (2025): if `p` and `N(p)+2` are prime, where
`N(p)` concatenates `p` with its decimal reversal, then `p ≡ 1 (mod 6)`. -/
theorem a088883_mod_six {p : ℕ} (hp : p.Prime) (h : (catRev p + 2).Prime) :
    p % 6 = 1 := by
  have hp0 : 0 < p := hp.pos
  have hodd := hp.eq_two_or_odd
  rcases (by omega : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2) with h3 | h3 | h3
  · have hp3 : p = 3 := eq_three_of_prime_of_mod_three hp h3
    subst hp3
    rw [show catRev 3 = 33 by decide] at h
    norm_num at h
  · omega
  · exact absurd h (not_prime_catRev_add_two hp0 h3)

/-- Rotondo's A088884 conjecture (2025): if `p ≠ 3` and both `p` and `N(p)-2`
are prime, then `p ≡ 5 (mod 6)`. The natural subtraction does not truncate:
`N(p) ≥ 10p ≥ 20` (`ten_mul_le_catRev`). -/
theorem a088884_mod_six {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (h : (catRev p - 2).Prime) :
    p % 6 = 5 := by
  have hp0 : 0 < p := hp.pos
  rcases (by omega : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2) with h3 | h3 | h3
  · exact absurd (eq_three_of_prime_of_mod_three hp h3) hp3
  · exact absurd h (not_prime_catRev_sub_two hp0 h3)
  · rcases hp.eq_two_or_odd with h2 | h2
    · subst h2
      rw [show catRev 2 = 22 by decide] at h
      norm_num at h
    · omega

/-- The 'vice versa' comment in OEIS A088883 and A088884: for every prime
`p`, `N(p)+2` and `N(p)-2` are not both prime. -/
theorem not_both_prime {p : ℕ} (hp : p.Prime) :
    ¬ ((catRev p + 2).Prime ∧ (catRev p - 2).Prime) := by
  rintro ⟨hplus, hminus⟩
  have hp0 : 0 < p := hp.pos
  rcases (by omega : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2) with h3 | h3 | h3
  · have hp3 : p = 3 := eq_three_of_prime_of_mod_three hp h3
    subst hp3
    rw [show catRev 3 = 33 by decide] at hplus
    norm_num at hplus
  · exact not_prime_catRev_sub_two hp0 h3 hminus
  · exact not_prime_catRev_add_two hp0 h3 hplus

end Candidates.A088883RotondoPrimeLen
