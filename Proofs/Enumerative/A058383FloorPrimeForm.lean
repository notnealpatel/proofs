/-
# A058383: Cloitre's totient characterization

OEIS A058383, Benoit Cloitre (Mar 02 2018).
For `x ≥ 7`, `φ(x) + φ(x-1) = floor((4x-3)/3)` holds exactly when
`x = 1 + 2^a 3^b` is prime with both exponents positive.
This positive-exponent convention is narrower than conventions for
Pierpont primes allowing exponent zero.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A058383FloorPrimeForm

open Nat

/-! ## Definitions -/

/-- Membership in OEIS A058383: `x` is a prime of the form `1 + 2^a * 3^b`
with `a > 0` and `b > 0` (the Pierpont primes other than `2`, `3`, `5`). -/
def IsA058383 (x : ℕ) : Prop :=
  x.Prime ∧ ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ x = 1 + 2 ^ a * 3 ^ b

/-! ### Example: the first listed terms are members -/

example : IsA058383 7 := ⟨by norm_num, 1, 1, by norm_num⟩
example : IsA058383 13 := ⟨by norm_num, 2, 1, by norm_num⟩
example : IsA058383 19 := ⟨by norm_num, 1, 2, by norm_num⟩
example : IsA058383 37 := ⟨by norm_num, 2, 2, by norm_num⟩
example : IsA058383 73 := ⟨by norm_num, 3, 2, by norm_num⟩
example : IsA058383 97 := ⟨by norm_num, 5, 1, by norm_num⟩
example : IsA058383 109 := ⟨by norm_num, 2, 3, by norm_num⟩
example : IsA058383 163 := ⟨by norm_num, 1, 4, by norm_num⟩

/-! ### Example: non-members -/

/-- `17 = 1 + 2^4` is prime but needs `b = 0`. -/
example : ¬ IsA058383 17 := by
  rintro ⟨-, a, b, -, hb, h⟩
  have h3 : 3 ∣ 2 ^ a * 3 ^ b := dvd_mul_of_dvd_right (dvd_pow_self 3 hb.ne') _
  omega

/-- `25 = 1 + 2^3 * 3` has the right shape but is not prime. -/
example : ¬ IsA058383 25 := by
  rintro ⟨hp, -⟩
  norm_num at hp

/-- The equation holds at the first term `x = 7`: `φ 7 + φ 6 = 8 = ⌊25/3⌋`. -/
example : φ 7 + φ (7 - 1) = (4 * 7 - 3) / 3 := by decide

/-- The equation fails at the non-term `x = 8`: `φ 8 + φ 7 = 10 ≠ 9 = ⌊29/3⌋`. -/
example : φ 8 + φ (8 - 1) ≠ (4 * 8 - 3) / 3 := by decide

/-! ## Totient bounds -/

/-- If a prime `p` divides `n`, then `φ n * p ≤ n * (p - 1)`. -/
theorem totient_mul_le_of_dvd {p n : ℕ} (hp : p.Prime) (hpn : p ∣ n) :
    φ n * p ≤ n * (p - 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  obtain ⟨e, k, hk, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p hp.one_lt.ne'
  have he : e ≠ 0 := by
    rintro rfl
    simp only [pow_zero, one_mul] at hpn
    exact hk hpn
  obtain ⟨e, rfl⟩ : ∃ e' : ℕ, e = e' + 1 := ⟨e - 1, by omega⟩
  have hcop : Nat.Coprime (p ^ (e + 1)) k :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hk)
  have hφ : φ (p ^ (e + 1) * k) = p ^ e * (p - 1) * φ k := by
    rw [Nat.totient_mul hcop, Nat.totient_prime_pow hp (Nat.succ_pos e)]
    rfl
  have hk' : φ k ≤ k := Nat.totient_le k
  calc φ (p ^ (e + 1) * k) * p = p ^ (e + 1) * (p - 1) * φ k := by
        rw [hφ, pow_succ]; ring
    _ ≤ p ^ (e + 1) * (p - 1) * k := Nat.mul_le_mul_left _ hk'
    _ = p ^ (e + 1) * k * (p - 1) := by ring

/-- Decomposition of a nonzero multiple of `6`: `m = 2^(a+1) * 3^(b+1) * k` with
`k` prime to `2` and `3`, and then `3 * φ m = 2^(a+1) * 3^(b+1) * φ k`. -/
theorem exists_decomp_of_six_dvd {m : ℕ} (hm : m ≠ 0) (h6 : 6 ∣ m) :
    ∃ a b k : ℕ, ¬ 2 ∣ k ∧ ¬ 3 ∣ k ∧ m = 2 ^ (a + 1) * 3 ^ (b + 1) * k ∧
      3 * φ m = 2 ^ (a + 1) * 3 ^ (b + 1) * φ k := by
  obtain ⟨a, m₁, h2m₁, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm 2 (by norm_num)
  have h2 : (2 : ℕ) ∣ 2 ^ a * m₁ := dvd_trans (by norm_num) h6
  have h3 : (3 : ℕ) ∣ 2 ^ a * m₁ := dvd_trans (by norm_num) h6
  have ha : a ≠ 0 := by
    rintro rfl
    simp only [pow_zero, one_mul] at h2
    exact h2m₁ h2
  have hcop23 : Nat.Coprime 3 (2 ^ a) := Nat.Coprime.pow_right _ (by norm_num)
  have h3m₁ : 3 ∣ m₁ := hcop23.dvd_of_dvd_mul_left h3
  have hm₁ : m₁ ≠ 0 := by
    rintro rfl
    exact h2m₁ (dvd_zero 2)
  obtain ⟨b, k, h3k, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm₁ 3 (by norm_num)
  have hb : b ≠ 0 := by
    rintro rfl
    simp only [pow_zero, one_mul] at h3m₁
    exact h3k h3m₁
  have h2k : ¬ 2 ∣ k := fun hk => h2m₁ (dvd_mul_of_dvd_right hk _)
  obtain ⟨a, rfl⟩ : ∃ a' : ℕ, a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b' : ℕ, b = b' + 1 := ⟨b - 1, by omega⟩
  refine ⟨a, b, k, h2k, h3k, by ring, ?_⟩
  have hc2k : Nat.Coprime (2 ^ (a + 1)) (3 ^ (b + 1) * k) := by
    apply Nat.Coprime.mul_right
    · exact Nat.Coprime.pow _ _ (by norm_num)
    · exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 h2k)
  have hc3k : Nat.Coprime (3 ^ (b + 1)) k :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3k)
  rw [Nat.totient_mul hc2k, Nat.totient_mul hc3k,
    Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos a),
    Nat.totient_prime_pow Nat.prime_three (Nat.succ_pos b)]
  norm_num
  ring

/-! ## The conjecture -/

/-- Forward direction: for `x ≥ 7`, a solution of
`φ x + φ (x - 1) = ⌊(4x - 3)/3⌋` is a term of A058383. -/
theorem isA058383_of_totient_eq {x : ℕ} (hx : 7 ≤ x)
    (h : φ x + φ (x - 1) = (4 * x - 3) / 3) : IsA058383 x := by
  obtain ⟨r, hr⟩ := Nat.totient_even (n := x) (by omega)
  obtain ⟨s, hs⟩ := Nat.totient_even (n := x - 1) (by omega)
  -- the right-hand side is odd unless `x ≡ 1 (mod 3)`
  have hx3 : x % 3 = 1 := by omega
  have h3m : 3 ∣ x - 1 := by omega
  have hφm3 : φ (x - 1) * 3 ≤ (x - 1) * (3 - 1) :=
    totient_mul_le_of_dvd Nat.prime_three h3m
  rcases Nat.even_or_odd x with hev | hodd
  · -- `x` even: the sum is too small
    have hφx2 : φ x * 2 ≤ x * (2 - 1) :=
      totient_mul_le_of_dvd Nat.prime_two (even_iff_two_dvd.mp hev)
    omega
  · -- `x` odd: `6 ∣ x - 1`
    have h6 : 6 ∣ x - 1 := by
      obtain ⟨t, ht⟩ := hodd
      omega
    obtain ⟨a, b, k, -, -, hmk, hφk⟩ := exists_decomp_of_six_dvd (by omega) h6
    have hφx : φ x < x := Nat.totient_lt x (by omega)
    set P := 2 ^ (a + 1) * 3 ^ (b + 1) with hP
    have hPk : φ k ≤ k := Nat.totient_le k
    have hPle : P * φ k ≤ P * k := Nat.mul_le_mul_left P hPk
    -- equality is forced in both bounds
    have hxeq : φ x = x - 1 := by omega
    have hkeq : P * φ k = P * k := by omega
    have hPpos : 0 < P := by positivity
    have hk_eq : φ k = k := Nat.eq_of_mul_eq_mul_left hPpos hkeq
    have hk0 : k ≠ 0 := by
      rintro rfl
      omega
    have hk1 : k = 1 := by
      by_contra hk1
      have hlt := Nat.totient_lt k (by omega)
      omega
    refine ⟨(Nat.totient_eq_iff_prime (by omega)).mp hxeq, a + 1, b + 1,
      Nat.succ_pos a, Nat.succ_pos b, ?_⟩
    rw [hk1, mul_one] at hmk
    omega

/-- Reverse direction: every term of A058383 solves
`φ x + φ (x - 1) = ⌊(4x - 3)/3⌋`. -/
theorem totient_eq_of_isA058383 {x : ℕ} (hx : IsA058383 x) :
    φ x + φ (x - 1) = (4 * x - 3) / 3 := by
  obtain ⟨hp, a, b, ha, hb, rfl⟩ := hx
  obtain ⟨a, rfl⟩ : ∃ a' : ℕ, a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b' : ℕ, b = b' + 1 := ⟨b - 1, by omega⟩
  have hφp : φ (1 + 2 ^ (a + 1) * 3 ^ (b + 1)) = 2 ^ (a + 1) * 3 ^ (b + 1) := by
    rw [Nat.totient_prime hp]
    omega
  have hcop : Nat.Coprime (2 ^ (a + 1)) (3 ^ (b + 1)) := Nat.Coprime.pow _ _ (by norm_num)
  have hφm : φ (2 ^ (a + 1) * 3 ^ (b + 1)) = 2 ^ (a + 1) * 3 ^ b := by
    rw [Nat.totient_mul hcop, Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos a),
      Nat.totient_prime_pow Nat.prime_three (Nat.succ_pos b)]
    norm_num
    ring
  set Q := 2 ^ (a + 1) * 3 ^ b with hQ
  have hPQ : 2 ^ (a + 1) * 3 ^ (b + 1) = 3 * Q := by
    rw [hQ, pow_succ]
    ring
  rw [Nat.add_sub_cancel_left, hφp, hφm, hPQ]
  omega

/-- Cloitre's A058383 characterization: for `x ≥ 7`,
`φ(x) + φ(x-1) = floor((4x-3)/3)` iff `x` is prime of the form
`1+2^a 3^b` with both exponents positive. The bound guards all natural
subtractions. -/
theorem totient_add_totient_sub_one_eq_iff {x : ℕ} (hx : 7 ≤ x) :
    φ x + φ (x - 1) = (4 * x - 3) / 3 ↔ IsA058383 x :=
  ⟨isA058383_of_totient_eq hx, totient_eq_of_isA058383⟩

end Candidates.A058383FloorPrimeForm
