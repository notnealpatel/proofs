/-
# A361034 — Bala: `a(n)` is odd iff `n = 2^k - 2`

Peter Bala's conjecture in OEIS A361034 says that
`a(n) = 2520(4n)!/(n!(n+2)!³)` is odd iff `n = 2^k-2` for some `k ≥ 1`.
The integrality theorem is `dvd_numerator` and the parity theorem is
`odd_a_iff`. The argument uses Legendre's formula.  For `p = 2`,
`v₂(a(n)) = 3 + v₂((4n)!) - v₂(n!) - 3 v₂((n+2)!) = 3 (s₂(n+2) - 1)` with `s₂`
the binary digit sum, which vanishes iff `n + 2` is a power of two.  For an
odd prime `p`, the Legendre summands at modulus `q = p^i ≥ 8` are nonnegative,
and the only deficits (`q = 3, 5, 7`) are covered by `v_p(2520)`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A361034OddSome

open Nat

/-- A361034: `a(n) = 2520 * (4n)! / (n! * (n+2)!^3)`, as a natural-number quotient.
The division is exact (`dvd_numerator`), so this is the true value. -/
def a (n : ℕ) : ℕ := 2520 * (4 * n)! / (n ! * (n + 2)! ^ 3)

example : a 0 = 315 := by rfl
example : a 1 = 280 := by rfl
example : a 2 = 3675 := by rfl
example : a 3 = 116424 := by rfl
example : a 4 = 5885880 := by rfl
example : a 5 = 399072960 := by rfl

/-- For `8 ≤ q`, the Legendre summand of `n! (n+2)!^3` at modulus `q` is at most
that of `(4n)!`. -/
theorem div_add_three_mul_div_le (q n : ℕ) (hq : 8 ≤ q) :
    n / q + 3 * ((n + 2) / q) ≤ 4 * n / q := by
  rw [Nat.le_div_iff_mul_le (by omega)]
  have hA : n / q * q ≤ n := Nat.div_mul_le_self n q
  have hB : (n + 2) / q * q ≤ n + 2 := Nat.div_mul_le_self (n + 2) q
  have hBA : (n + 2) / q ≤ n / q + 1 := by
    calc (n + 2) / q ≤ (n + q) / q := Nat.div_le_div_right (by omega)
      _ = n / q + 1 := Nat.add_div_right n (by omega)
  have hAB : n / q ≤ (n + 2) / q := Nat.div_le_div_right (by omega)
  rcases Nat.eq_or_lt_of_le hBA with hEq | hLt
  · rw [hEq] at hB ⊢
    nlinarith
  · have hEq : (n + 2) / q = n / q := by omega
    rw [hEq]
    nlinarith

/-- The first Legendre summand: the deficit at modulus `p` is covered by the
`p`-adic valuation of `2520 = 2^3 * 3^2 * 5 * 7`, for every odd prime `p`. -/
theorem first_term_le (p n : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    n / p + 3 * ((n + 2) / p) ≤ 4 * n / p + padicValNat p 2520 := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases h8 : 8 ≤ p
  · have := div_add_three_mul_div_le p n h8
    omega
  · have hcases : p = 3 ∨ p = 5 ∨ p = 7 := by
      have h2 := hp.two_le
      interval_cases p <;> simp_all (config := {decide := true})
    rcases hcases with rfl | rfl | rfl
    · have h3 : 2 ≤ padicValNat 3 2520 :=
        (padicValNat_dvd_iff_le (by norm_num)).mp (by norm_num)
      have hr := Nat.mod_lt n (show 0 < 3 by norm_num)
      have hn := Nat.div_add_mod n 3
      generalize n % 3 = r at hr hn
      generalize n / 3 = m at hn
      subst hn
      interval_cases r <;> omega
    · have h5 : 1 ≤ padicValNat 5 2520 :=
        (padicValNat_dvd_iff_le (by norm_num)).mp (by norm_num)
      have hr := Nat.mod_lt n (show 0 < 5 by norm_num)
      have hn := Nat.div_add_mod n 5
      generalize n % 5 = r at hr hn
      generalize n / 5 = m at hn
      subst hn
      interval_cases r <;> omega
    · have h7 : 1 ≤ padicValNat 7 2520 :=
        (padicValNat_dvd_iff_le (by norm_num)).mp (by norm_num)
      have hr := Nat.mod_lt n (show 0 < 7 by norm_num)
      have hn := Nat.div_add_mod n 7
      generalize n % 7 = r at hr hn
      generalize n / 7 = m at hn
      subst hn
      interval_cases r <;> omega

/-- For an odd prime `p`, `v_p(n! (n+2)!^3) ≤ v_p(2520 (4n)!)`. -/
theorem padicValNat_denom_le_of_ne_two (p n : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    padicValNat p (n ! * (n + 2)! ^ 3) ≤ padicValNat p (2520 * (4 * n)!) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  rw [padicValNat.mul (factorial_ne_zero _) (pow_ne_zero _ (factorial_ne_zero _)),
    padicValNat.pow,
    padicValNat.mul (by norm_num) (factorial_ne_zero _)]
  set b := 4 * n + 3 with hb
  have hlog : ∀ m, m ≤ 4 * n + 2 → Nat.log p m < b := fun m hm =>
    lt_of_le_of_lt (Nat.log_le_self p m) (by omega)
  rw [padicValNat_factorial (hlog n (by omega)),
    padicValNat_factorial (hlog (n + 2) (by omega)),
    padicValNat_factorial (hlog (4 * n) (by omega))]
  have h1b : 1 < b := by omega
  rw [Finset.sum_eq_sum_Ico_succ_bot h1b, Finset.sum_eq_sum_Ico_succ_bot h1b,
    Finset.sum_eq_sum_Ico_succ_bot h1b, mul_add, Finset.mul_sum]
  have hrest : ∑ i ∈ Finset.Ico (1 + 1) b, n / p ^ i +
      ∑ i ∈ Finset.Ico (1 + 1) b, 3 * ((n + 2) / p ^ i) ≤
      ∑ i ∈ Finset.Ico (1 + 1) b, 4 * n / p ^ i := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi2 : 2 ≤ i := (Finset.mem_Ico.mp hi).1
    apply div_add_three_mul_div_le
    calc 8 ≤ 3 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left h3 2
      _ ≤ p ^ i := Nat.pow_le_pow_right (by omega) hi2
  have hfirst := first_term_le p n hp hp2
  simp only [pow_one]
  omega

/-- Binary digit sum of an even number: `s₂(2m) = s₂(m)`. -/
theorem sum_digits_two_mul (m : ℕ) : (digits 2 (2 * m)).sum = (digits 2 m).sum := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · rw [Nat.digits_def' (by norm_num) (by omega)]
    simp only [List.sum_cons]
    have h1 : 2 * m % 2 = 0 := by omega
    have h2 : 2 * m / 2 = m := by omega
    rw [h1, h2, zero_add]

/-- Binary digit sum of an odd number: `s₂(2m+1) = s₂(m) + 1`. -/
theorem sum_digits_two_mul_add_one (m : ℕ) :
    (digits 2 (2 * m + 1)).sum = (digits 2 m).sum + 1 := by
  rw [Nat.digits_def' (by norm_num) (by omega)]
  simp only [List.sum_cons]
  have h1 : (2 * m + 1) % 2 = 1 := by omega
  have h2 : (2 * m + 1) / 2 = m := by omega
  rw [h1, h2, add_comm]

/-- A positive number has positive binary digit sum. -/
theorem one_le_sum_digits_two (m : ℕ) (hm : 0 < m) : 1 ≤ (digits 2 m).sum := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' m
    · rw [sum_digits_two_mul]
      exact ih j (by omega) (by omega)
    · rw [sum_digits_two_mul_add_one]
      omega

/-- The binary digit sum of `m` is `1` exactly when `m` is a power of two. -/
theorem sum_digits_two_eq_one_iff (m : ℕ) :
    (digits 2 m).sum = 1 ↔ ∃ k : ℕ, m = 2 ^ k := by
  constructor
  · intro hs
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' m
      · rw [sum_digits_two_mul] at hs
        rcases Nat.eq_zero_or_pos j with rfl | hj
        · simp at hs
        · obtain ⟨k, hk⟩ := ih j (by omega) hs
          exact ⟨k + 1, by rw [hk, pow_succ, mul_comm]⟩
      · rw [sum_digits_two_mul_add_one] at hs
        rcases Nat.eq_zero_or_pos j with rfl | hj
        · exact ⟨0, by norm_num⟩
        · have := one_le_sum_digits_two j hj
          omega
  · rintro ⟨k, rfl⟩
    induction k with
    | zero => norm_num
    | succ k ih => rw [pow_succ, mul_comm, sum_digits_two_mul, ih]

/-- Exact 2-adic bookkeeping (Legendre): `v₂(2520 (4n)!) = v₂(n! (n+2)!^3) + 3 (s₂(n+2) - 1)`,
where `s₂` is the binary digit sum (and `1 ≤ s₂(n+2)`, so the subtraction is exact). -/
theorem padicValNat_two_numer (n : ℕ) :
    padicValNat 2 (2520 * (4 * n)!) =
      padicValNat 2 (n ! * (n + 2)! ^ 3) + 3 * ((digits 2 (n + 2)).sum - 1) := by
  have h2520 : padicValNat 2 2520 = 3 := by
    rw [show (2520 : ℕ) = 2 ^ 3 * 315 by norm_num,
      padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by norm_num)]
  have h4n : padicValNat 2 (4 * n)! = padicValNat 2 n ! + 3 * n := by
    rw [show 4 * n = 2 * (2 * n) by ring, padicValNat_factorial_mul,
      padicValNat_factorial_mul]
    ring
  have hn2 := sub_one_mul_padicValNat_factorial (p := 2) (n + 2)
  have hs1 := one_le_sum_digits_two (n + 2) (by omega)
  have hsle := Nat.digit_sum_le 2 (n + 2)
  rw [padicValNat.mul (by norm_num) (factorial_ne_zero _), h2520, h4n,
    padicValNat.mul (factorial_ne_zero _) (pow_ne_zero _ (factorial_ne_zero _)),
    padicValNat.pow]
  rw [show (2 - 1 : ℕ) = 1 from rfl, one_mul] at hn2
  omega

/-- Integrality of A361034: `n! (n+2)!^3 ∣ 2520 (4n)!` for every `n`
(the entry records this only as an observed property). -/
theorem dvd_numerator (n : ℕ) : n ! * (n + 2)! ^ 3 ∣ 2520 * (4 * n)! := by
  have hd : n ! * (n + 2)! ^ 3 ≠ 0 :=
    mul_ne_zero (factorial_ne_zero _) (pow_ne_zero _ (factorial_ne_zero _))
  have hN : 2520 * (4 * n)! ≠ 0 := mul_ne_zero (by norm_num) (factorial_ne_zero _)
  refine (Nat.factorization_prime_le_iff_dvd hd hN).mp fun p hp => ?_
  rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
  by_cases hp2 : p = 2
  · subst hp2
    rw [padicValNat_two_numer]
    omega
  · exact padicValNat_denom_le_of_ne_two p n hp hp2

/-- `v₂(a(n)) = 3 (s₂(n+2) - 1)`, with `s₂` the binary digit sum. -/
theorem padicValNat_two_a (n : ℕ) :
    padicValNat 2 (a n) = 3 * ((digits 2 (n + 2)).sum - 1) := by
  rw [a, padicValNat.div_of_dvd (dvd_numerator n), padicValNat_two_numer]
  omega

/-- `a(n)` is positive. -/
theorem a_pos (n : ℕ) : 0 < a n := by
  have hd : 0 < n ! * (n + 2)! ^ 3 :=
    Nat.mul_pos (factorial_pos _) (pow_pos (factorial_pos _) _)
  have hN : 0 < 2520 * (4 * n)! := Nat.mul_pos (by norm_num) (factorial_pos _)
  exact Nat.div_pos (Nat.le_of_dvd hN (dvd_numerator n)) hd

/-- **A361034 parity conjecture (Peter Bala, OEIS A361034).**
`a(n) = 2520 (4n)! / (n! (n+2)!^3)` is odd if and only if `n = 2^k - 2` for some `k ≥ 1`.
(The quotient is exact by `dvd_numerator`; `2^k - 2` is not truncated since `k ≥ 1`.) -/
theorem odd_a_iff (n : ℕ) : Odd (a n) ↔ ∃ k : ℕ, 1 ≤ k ∧ n = 2 ^ k - 2 := by
  have hs1 := one_le_sum_digits_two (n + 2) (by omega)
  have hodd : Odd (a n) ↔ (digits 2 (n + 2)).sum = 1 := by
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    have hv := padicValNat_two_a n
    have hz := (padicValNat.eq_zero_iff (p := 2) (n := a n))
    have hne : a n ≠ 0 := (a_pos n).ne'
    constructor
    · intro hnd
      have hv0 : padicValNat 2 (a n) = 0 := hz.mpr (Or.inr (Or.inr hnd))
      omega
    · intro h1 hdvd
      have hpos : 0 < padicValNat 2 (a n) :=
        (padicValNat_dvd_iff_le (p := 2) hne).mp (by simpa using hdvd)
      omega
  rw [hodd, sum_digits_two_eq_one_iff]
  constructor
  · rintro ⟨k, hk⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · exact absurd hk (by rw [pow_zero]; omega)
    · exact ⟨k, hk1, by omega⟩
  · rintro ⟨k, hk1, rfl⟩
    have h2k : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk1
    exact ⟨k, by omega⟩

end Candidates.A361034OddSome
