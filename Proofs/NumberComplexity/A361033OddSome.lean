/-
# A361033 — parity of 3(4n)!/(n!(n+1)!^3)

OEIS A361033, Peter Bala: `3(4n)!/(n!(n+1)!³)` is an integer and
is odd iff `n = 2^k-1`, `k ≥ 0`. Legendre's formula gives
`v₂(a(n)) = 3(s₂(n+1)-1)`. Integrality is proved prime by prime,
so natural division is exact.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A361033OddSome

open Nat

/-- OEIS A361033: `a(n) = 3 (4n)! / (n! (n+1)!^3)` (natural-number division;
the division is exact by `denom_dvd_numer`). -/
def a (n : ℕ) : ℕ := 3 * (4 * n)! / (n ! * (n + 1)! ^ 3)

example : a 0 = 3 := rfl
example : a 1 = 9 := rfl
example : a 2 = 280 := rfl
example : a 3 = 17325 := rfl
example : a 4 = 1513512 := rfl
example : a 5 = 162954792 := rfl

/-- Legendre's formula at `p = 2`: `v₂(m!) = m - s₂(m)`. -/
theorem padicValNat_two_factorial (m : ℕ) :
    padicValNat 2 m ! = m - (Nat.digits 2 m).sum := by
  have h := sub_one_mul_padicValNat_factorial (p := 2) m
  simpa using h

/-- The binary digit sum of `4n` equals that of `n`. -/
theorem digits_two_sum_four_mul (n : ℕ) :
    (Nat.digits 2 (4 * n)).sum = (Nat.digits 2 n).sum := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h4 : 4 * n = 2 ^ 2 * n := by norm_num
    rw [h4, Nat.digits_base_pow_mul (by norm_num) hn]
    simp

/-- A positive number has positive binary digit sum. -/
theorem one_le_digits_two_sum {m : ℕ} (hm : 0 < m) : 1 ≤ (Nat.digits 2 m).sum := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rw [Nat.digits_def' (by norm_num) hm, List.sum_cons]
    rcases Nat.mod_two_eq_zero_or_one m with h | h
    · have hpos : 0 < m / 2 := by omega
      have := ih (m / 2) (by omega) hpos
      omega
    · omega

/-- The binary digit sum of `m` is `1` exactly when `m` is a power of two. -/
theorem digits_two_sum_eq_one_iff (m : ℕ) :
    (Nat.digits 2 m).sum = 1 ↔ ∃ k : ℕ, m = 2 ^ k := by
  constructor
  · intro h
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp at h
      rw [Nat.digits_def' (by norm_num) hm, List.sum_cons] at h
      rcases Nat.mod_two_eq_zero_or_one m with hmod | hmod
      · have hpos : 0 < m / 2 := by omega
        obtain ⟨k, hk⟩ := ih (m / 2) (by omega) (by omega)
        exact ⟨k + 1, by rw [pow_succ]; omega⟩
      · have hs : (Nat.digits 2 (m / 2)).sum = 0 := by omega
        have h0 : m / 2 = 0 := by
          by_contra hne
          have := one_le_digits_two_sum (m := m / 2) (by omega)
          omega
        exact ⟨0, by omega⟩
  · rintro ⟨k, rfl⟩
    have h := Nat.digits_base_pow_mul (b := 2) (k := k) (m := 1) (by norm_num) (by norm_num)
    rw [mul_one] at h
    rw [h]
    simp

/-- Per-term Legendre comparison: for `4 ≤ q`,
`⌊n/q⌋ + 3⌊(n+1)/q⌋ ≤ ⌊4n/q⌋`. -/
theorem div_add_three_mul_succ_div_le (n q : ℕ) (hq : 4 ≤ q) :
    n / q + 3 * ((n + 1) / q) ≤ 4 * n / q := by
  have hq0 : 0 < q := by omega
  rw [Nat.le_div_iff_mul_le hq0]
  have h1 : n / q * q ≤ n := Nat.div_mul_le_self n q
  have h2 : (n + 1) / q * q ≤ n + 1 := Nat.div_mul_le_self (n + 1) q
  have h3 : (n + 1) / q ≤ n / q + 1 := by
    rw [Nat.div_le_iff_le_mul_add_pred hq0]
    have hlt := Nat.lt_div_mul_add (a := n) hq0
    nlinarith
  rcases Nat.lt_or_ge ((n + 1) / q) (n / q + 1) with h | h
  · have h' : (n + 1) / q ≤ n / q := by omega
    nlinarith
  · have he : (n + 1) / q = n / q + 1 := le_antisymm h3 h
    rw [he]
    rw [he] at h2
    nlinarith

/-- The `q = 3` term, where the factor `3` of the numerator pays the deficit:
`⌊n/3⌋ + 3⌊(n+1)/3⌋ ≤ 1 + ⌊4n/3⌋`. -/
theorem div_three_add_three_mul_succ_div_three_le (n : ℕ) :
    n / 3 + 3 * ((n + 1) / 3) ≤ 1 + 4 * n / 3 := by
  omega

/-- For an odd prime `p`, `v_p(n!) + 3 v_p((n+1)!) ≤ v_p(3) + v_p((4n)!)`. -/
theorem padicValNat_denom_le_of_ne_two (n p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    padicValNat p n ! + 3 * padicValNat p (n + 1)! ≤
      padicValNat p 3 + padicValNat p (4 * n)! := by
  have hb : ∀ m, m ≤ 4 * n + 1 → log p m < 4 * n + 2 := fun m hm =>
    lt_of_le_of_lt (Nat.log_le_self p m) (by omega)
  rw [padicValNat_factorial (hb n (by omega)), padicValNat_factorial (hb (n + 1) (by omega)),
    padicValNat_factorial (hb (4 * n) (by omega)), Finset.mul_sum, ← Finset.sum_add_distrib]
  have hp3 : 3 ≤ p := by
    have h2le := hp.out.two_le
    omega
  rcases Nat.eq_or_lt_of_le hp3 with h3 | h5
  · subst h3
    have h12 : 1 < 4 * n + 2 := by omega
    rw [Finset.sum_eq_sum_Ico_succ_bot h12 (fun i => n / 3 ^ i + 3 * ((n + 1) / 3 ^ i)),
      Finset.sum_eq_sum_Ico_succ_bot h12 (fun i => 4 * n / 3 ^ i), padicValNat_self]
    have hrest : ∑ i ∈ Finset.Ico (1 + 1) (4 * n + 2), (n / 3 ^ i + 3 * ((n + 1) / 3 ^ i)) ≤
        ∑ i ∈ Finset.Ico (1 + 1) (4 * n + 2), 4 * n / 3 ^ i := by
      apply Finset.sum_le_sum
      intro i hi
      rw [Finset.mem_Ico] at hi
      apply div_add_three_mul_succ_div_le
      calc 4 ≤ 3 ^ 2 := by norm_num
        _ ≤ 3 ^ i := Nat.pow_le_pow_right (by norm_num) hi.1
    have hfirst := div_three_add_three_mul_succ_div_three_le n
    simp only [pow_one]
    omega
  · have hrest : ∑ i ∈ Finset.Ico 1 (4 * n + 2), (n / p ^ i + 3 * ((n + 1) / p ^ i)) ≤
        ∑ i ∈ Finset.Ico 1 (4 * n + 2), 4 * n / p ^ i := by
      apply Finset.sum_le_sum
      intro i hi
      rw [Finset.mem_Ico] at hi
      apply div_add_three_mul_succ_div_le
      calc 4 ≤ p ^ 1 := by rw [pow_one]; omega
        _ ≤ p ^ i := Nat.pow_le_pow_right (by omega) hi.1
    omega

/-- `v₂` of the numerator: `v₂(3 (4n)!) = 4n - s₂(n)`. -/
theorem padicValNat_two_numer (n : ℕ) :
    padicValNat 2 (3 * (4 * n)!) = 4 * n - (Nat.digits 2 n).sum := by
  rw [padicValNat.mul (by norm_num) (by positivity),
    padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3), padicValNat_two_factorial,
    digits_two_sum_four_mul, zero_add]

/-- `v₂` of the denominator: `v₂(n! (n+1)!³) = (n - s₂(n)) + 3 (n + 1 - s₂(n+1))`. -/
theorem padicValNat_two_denom (n : ℕ) :
    padicValNat 2 (n ! * (n + 1)! ^ 3) =
      (n - (Nat.digits 2 n).sum) + 3 * (n + 1 - (Nat.digits 2 (n + 1)).sum) := by
  rw [padicValNat.mul (by positivity) (by positivity), padicValNat.pow,
    padicValNat_two_factorial, padicValNat_two_factorial]

/-- Integrality: `n! (n+1)!³ ∣ 3 (4n)!`. -/
theorem denom_dvd_numer (n : ℕ) : n ! * (n + 1)! ^ 3 ∣ 3 * (4 * n)! := by
  rw [← Nat.factorization_prime_le_iff_dvd (by positivity) (by positivity)]
  intro p hp
  haveI := Fact.mk hp
  rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
  by_cases hp2 : p = 2
  · subst hp2
    rw [padicValNat_two_numer, padicValNat_two_denom]
    have hs := Nat.digit_sum_le 2 n
    have hs' := Nat.digit_sum_le 2 (n + 1)
    have hs1 := one_le_digits_two_sum (m := n + 1) (by omega)
    omega
  · rw [padicValNat.mul (by positivity) (by positivity), padicValNat.pow,
      padicValNat.mul (by norm_num) (by positivity)]
    exact padicValNat_denom_le_of_ne_two n p hp2

/-- `a(n)` is positive. -/
theorem a_pos (n : ℕ) : 0 < a n :=
  Nat.div_pos (Nat.le_of_dvd (by positivity) (denom_dvd_numer n)) (by positivity)

/-- The 2-adic valuation of `a(n)` is `3 (s₂(n+1) - 1)`. -/
theorem padicValNat_two_a (n : ℕ) :
    padicValNat 2 (a n) = 3 * ((Nat.digits 2 (n + 1)).sum - 1) := by
  rw [a, padicValNat.div_of_dvd (denom_dvd_numer n), padicValNat_two_numer,
    padicValNat_two_denom]
  have hs := Nat.digit_sum_le 2 n
  have hs' := Nat.digit_sum_le 2 (n + 1)
  have hs1 := one_le_digits_two_sum (m := n + 1) (by omega)
  omega

/-- A361033 parity conjecture (Peter Bala, 2023), in the form
`a(n)` is odd iff `n + 1` is a power of two. -/
theorem odd_a_iff (n : ℕ) : Odd (a n) ↔ ∃ k : ℕ, n + 1 = 2 ^ k := by
  have hne : a n ≠ 0 := (a_pos n).ne'
  have hv : Odd (a n) ↔ padicValNat 2 (a n) = 0 := by
    rw [padicValNat.eq_zero_iff, Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    simp [hne]
  have hs1 := one_le_digits_two_sum (m := n + 1) (by omega)
  rw [hv, padicValNat_two_a, ← digits_two_sum_eq_one_iff]
  omega

/-- OEIS A361033 conjecture: `a(n) = 3(4n)!/(n!(n+1)!³)` is odd
if and only if `n = 2^k - 1` for some `k ≥ 0` (the subtraction is safe since
`1 ≤ 2^k`). -/
theorem conjecture (n : ℕ) : Odd (a n) ↔ ∃ k : ℕ, n = 2 ^ k - 1 := by
  rw [odd_a_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by omega⟩
  · rintro ⟨k, hk⟩
    have hpos := Nat.one_le_two_pow (n := k)
    exact ⟨k, by omega⟩

end Candidates.A361033OddSome
