/-
# A361035 — Bala: `9979200 (4n)!/(n! (n+3)!^3)` is odd iff `n = 2^k - 3`

OEIS A361035, Peter Bala: `9979200(4n)!/(n!(n+3)!³)` is an integer
and is odd iff `n = 2^k-3` for `k ≥ 2`.

Legendre's formula.  For an odd prime `p` and `q = p^i ≥ 3`, writing
`n = q m + r`, the deficit `⌊n/q⌋ + 3⌊(n+3)/q⌋ - ⌊4n/q⌋` is at most
`3, 2, 1, 0` according as `q < 4, q < 6, q < 12, q ≥ 12`; summed over the
powers of `p` this is at most `v_p(9979200) = v_p(2^6 3^4 5^2 7 11)`.  For
`p = 2`, `v₂((4n)!) = v₂(n!) + 3n` and `v₂(m!) = m - s₂(m)`, so
`v₂(a(n)) = 3 (s₂(n+3) - 1)`, which vanishes iff `n + 3` is a power of two.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A361035OddSome

open Nat

/-! ## Definitions -/

/-- OEIS A361035: `a(n) = 9979200 * (4n)! / (n! * (n+3)!^3)`, with truncating
natural-number division; `den_dvd_num` shows the division is exact. -/
def a (n : ℕ) : ℕ := 9979200 * (4 * n)! / (n ! * (n + 3)! ^ 3)

-- Examples against the OEIS DATA line `46200, 17325, 116424, 2134440, 67953600`.
example : a 0 = 46200 := by rfl
example : a 1 = 17325 := by rfl
example : a 2 = 116424 := by rfl
example : a 3 = 2134440 := by rfl
example : a 4 = 67953600 := by rfl

/-! ## Odd primes: Legendre deficit bounds -/

/-- Upper bound for the per-power Legendre deficit at the prime power `q ≥ 3`. -/
def defect (q : ℕ) : ℕ := if q < 4 then 3 else if q < 6 then 2 else if q < 12 then 1 else 0

/-- Per-power Legendre comparison: for `q ≥ 3`,
`⌊n/q⌋ + 3⌊(n+3)/q⌋ ≤ ⌊4n/q⌋ + defect q`. -/
theorem term_le (n q : ℕ) (hq : 3 ≤ q) :
    n / q + 3 * ((n + 3) / q) ≤ 4 * n / q + defect q := by
  have hq0 : 0 < q := by omega
  obtain ⟨m, r, hr, rfl⟩ : ∃ m r, r < q ∧ n = q * m + r :=
    ⟨n / q, n % q, Nat.mod_lt _ hq0, (Nat.div_add_mod n q).symm⟩
  have h1 : (q * m + r) / q = m + r / q := by
    rw [add_comm (q * m), Nat.add_mul_div_left _ _ hq0, add_comm]
  have h2 : (q * m + r + 3) / q = m + (r + 3) / q := by
    rw [add_assoc, add_comm (q * m), Nat.add_mul_div_left _ _ hq0, add_comm]
  have h3 : 4 * (q * m + r) / q = 4 * m + 4 * r / q := by
    rw [mul_add, show 4 * (q * m) = q * (4 * m) by ring, add_comm (q * (4 * m)),
      Nat.add_mul_div_left _ _ hq0, add_comm]
  have hrq : r / q = 0 := Nat.div_eq_of_lt hr
  rw [h1, h2, h3, hrq]
  have hdef : 3 * ((r + 3) / q) ≤ 4 * r / q + defect q := by
    by_cases hsmall : r + 3 < q
    · rw [Nat.div_eq_of_lt hsmall, mul_zero]; exact Nat.zero_le _
    · have hone : (r + 3) / q = 1 := by
        rw [Nat.div_eq_iff hq0]; omega
      rw [hone]
      unfold defect
      split_ifs with ha hb hc
      · exact Nat.le_add_left _ _
      · have hA : 1 ≤ 4 * r / q := (Nat.le_div_iff_mul_le hq0).mpr (by omega)
        omega
      · have hA : 2 ≤ 4 * r / q := (Nat.le_div_iff_mul_le hq0).mpr (by omega)
        omega
      · have hA : 3 ≤ 4 * r / q := (Nat.le_div_iff_mul_le hq0).mpr (by omega)
        omega
  omega

/-- For an odd prime `p`, the total deficit over the powers `p^1, …, p^(b-1)` is
covered by `v_p(9979200)`. -/
theorem defect_sum_le (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (b : ℕ) (hb : 3 ≤ b) :
    ∑ i ∈ Finset.Ico 1 b, defect (p ^ i) ≤ padicValNat p 9979200 := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have htail : ∑ i ∈ Finset.Ico 3 b, defect (p ^ i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hi3 : 3 ≤ i := (Finset.mem_Ico.mp hi).1
    have h27 : 27 ≤ p ^ i := calc
      27 = 3 ^ 3 := by norm_num
      _ ≤ p ^ 3 := Nat.pow_le_pow_left hp3 3
      _ ≤ p ^ i := Nat.pow_le_pow_right (by omega) hi3
    unfold defect
    split_ifs <;> omega
  rw [← Finset.sum_Ico_consecutive _ (show 1 ≤ 3 by norm_num) hb, htail, add_zero]
  have hhead : ∑ i ∈ Finset.Ico 1 3, defect (p ^ i) = defect p + defect (p ^ 2) := by
    simp [Finset.sum_Ico_succ_top]
  rw [hhead]
  have : Fact p.Prime := ⟨hp⟩
  by_cases hbig : 13 ≤ p
  · have h2 : 169 ≤ p ^ 2 := by nlinarith
    have hd1 : defect p = 0 := by unfold defect; split_ifs <;> omega
    have hd2 : defect (p ^ 2) = 0 := by unfold defect; split_ifs <;> omega
    rw [hd1, hd2]; exact Nat.zero_le _
  · interval_cases p
    all_goals try (exfalso; norm_num at hp; done)
    all_goals
      first
      | (rw [show defect 3 + defect (3 ^ 2) = 4 by decide]
         exact (padicValNat_dvd_iff_le (by norm_num)).mp (by norm_num))
      | (rw [show defect 5 + defect (5 ^ 2) = 2 by decide]
         exact (padicValNat_dvd_iff_le (by norm_num)).mp (by norm_num))
      | (rw [show defect 7 + defect (7 ^ 2) = 1 by decide]
         exact (padicValNat_dvd_iff_le (by norm_num)).mp (by norm_num))
      | (rw [show defect 11 + defect (11 ^ 2) = 1 by decide]
         exact (padicValNat_dvd_iff_le (by norm_num)).mp (by norm_num))

/-! ## The prime 2: binary digit sums -/

/-- A positive number has positive binary digit sum. -/
theorem digits_two_sum_pos (m : ℕ) (hm : 0 < m) : 0 < (Nat.digits 2 m).sum := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rw [Nat.digits_def' (by norm_num) hm, List.sum_cons]
    by_cases h : m % 2 = 1
    · omega
    · have hpos : 0 < m / 2 := by omega
      have hrec := ih (m / 2) (by omega) hpos
      omega

/-- The binary digit sum of `m` is `1` iff `m` is a power of two. -/
theorem digits_two_sum_eq_one_iff (m : ℕ) :
    (Nat.digits 2 m).sum = 1 ↔ ∃ k, m = 2 ^ k := by
  constructor
  · induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hs
      rcases Nat.eq_zero_or_pos m with h0 | hm
      · subst h0; simp at hs
      rw [Nat.digits_def' (by norm_num) hm, List.sum_cons] at hs
      by_cases h : m % 2 = 1
      · have hz : m / 2 = 0 := by
          by_contra hne
          have hrec := digits_two_sum_pos (m / 2) (Nat.pos_of_ne_zero hne)
          omega
        exact ⟨0, by omega⟩
      · obtain ⟨k, hk⟩ := ih (m / 2) (by omega) (by omega)
        exact ⟨k + 1, by rw [pow_succ]; omega⟩
  · rintro ⟨k, rfl⟩
    have h := Nat.digits_base_pow_mul (b := 2) (k := k) (m := 1) (by norm_num) (by norm_num)
    rw [mul_one] at h
    rw [h, List.sum_append]
    simp

/-- `v₂(9979200) = 6`, since `9979200 = 2^6 · 155925`. -/
theorem padicValNat_two_const : padicValNat 2 9979200 = 6 := by
  have h : (9979200 : ℕ) = 2 ^ 6 * 155925 := by norm_num
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [h, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

/-- `v₂(9979200 · (4n)!) = 6 + v₂(n!) + 3n`. -/
theorem padicValNat_two_num (n : ℕ) :
    padicValNat 2 (9979200 * (4 * n)!) = 6 + padicValNat 2 n ! + 3 * n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [padicValNat.mul (by norm_num) (Nat.factorial_ne_zero _), padicValNat_two_const,
    show 4 * n = 2 * (2 * n) by ring, padicValNat_factorial_mul, padicValNat_factorial_mul]
  ring

/-- Legendre at `p = 2`: `v₂(m!) + s₂(m) = m`. -/
theorem padicValNat_two_factorial (m : ℕ) :
    padicValNat 2 m ! + (Nat.digits 2 m).sum = m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := sub_one_mul_padicValNat_factorial (p := 2) m
  have hle : (Nat.digits 2 m).sum ≤ m := Nat.digit_sum_le 2 m
  simp only [show (2 : ℕ) - 1 = 1 from rfl, one_mul] at h
  omega

/-- `v_p(n! (n+3)!^3) = v_p(n!) + 3 v_p((n+3)!)`. -/
theorem padicValNat_den (p n : ℕ) [Fact p.Prime] :
    padicValNat p (n ! * (n + 3)! ^ 3) = padicValNat p n ! + 3 * padicValNat p (n + 3)! := by
  rw [padicValNat.mul (Nat.factorial_ne_zero _) (pow_ne_zero _ (Nat.factorial_ne_zero _)),
    padicValNat.pow]

/-! ## Integrality -/

/-- **Integrality of A361035 (Bala, 2023).**
`n! (n+3)!^3` divides `9979200 (4n)!` for every `n`, so `a n` is the exact
quotient. -/
theorem den_dvd_num (n : ℕ) : n ! * (n + 3)! ^ 3 ∣ 9979200 * (4 * n)! := by
  have hden : n ! * (n + 3)! ^ 3 ≠ 0 :=
    mul_ne_zero (Nat.factorial_ne_zero _) (pow_ne_zero _ (Nat.factorial_ne_zero _))
  have hnum : 9979200 * (4 * n)! ≠ 0 := mul_ne_zero (by norm_num) (Nat.factorial_ne_zero _)
  rw [← Nat.factorization_le_iff_dvd hden hnum, Finsupp.le_def]
  intro p
  by_cases hp : p.Prime
  swap
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  have : Fact p.Prime := ⟨hp⟩
  rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp, padicValNat_den]
  by_cases hp2 : p = 2
  · subst hp2
    rw [padicValNat_two_num]
    have h3 := padicValNat_two_factorial (n + 3)
    have hpos := digits_two_sum_pos (n + 3) (by omega)
    omega
  · have hp3 : 3 ≤ p := by have := hp.two_le; omega
    set b := 4 * n + 4 with hb
    have hlog : ∀ m, m < b → Nat.log p m < b := fun m hm =>
      lt_of_le_of_lt (Nat.log_le_self p m) hm
    rw [padicValNat.mul (by norm_num) (Nat.factorial_ne_zero _),
      padicValNat_factorial (hlog n (by omega)),
      padicValNat_factorial (hlog (n + 3) (by omega)),
      padicValNat_factorial (b := b) (n := 4 * n) (by
        rcases Nat.eq_zero_or_pos n with h0 | h0
        · subst h0; simp [hb]
        · exact hlog (4 * n) (by omega))]
    have hsum := defect_sum_le p hp hp2 b (by omega)
    have hterm : ∀ i ∈ Finset.Ico 1 b,
        n / p ^ i + 3 * ((n + 3) / p ^ i) ≤ 4 * n / p ^ i + defect (p ^ i) := by
      intro i hi
      apply term_le
      calc 3 ≤ p := hp3
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ i := Nat.pow_le_pow_right (by omega) (Finset.mem_Ico.mp hi).1
    have hsum2 := Finset.sum_le_sum hterm
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum2
    omega

/-- `a n` is positive. -/
theorem a_pos (n : ℕ) : 0 < a n := by
  have hden : 0 < n ! * (n + 3)! ^ 3 :=
    Nat.mul_pos (Nat.factorial_pos _) (pow_pos (Nat.factorial_pos _) _)
  have hnum : 0 < 9979200 * (4 * n)! := Nat.mul_pos (by norm_num) (Nat.factorial_pos _)
  exact Nat.div_pos (Nat.le_of_dvd hnum (den_dvd_num n)) hden

/-- **2-adic valuation of A361035:** `v₂(a n) + 3 = 3 s₂(n+3)`, i.e.
`v₂(a n) = 3 (s₂(n+3) - 1)`. -/
theorem padicValNat_two_a (n : ℕ) :
    padicValNat 2 (a n) + 3 = 3 * (Nat.digits 2 (n + 3)).sum := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdiv := padicValNat.div_of_dvd (p := 2) (den_dvd_num n)
  rw [padicValNat_two_num, padicValNat_den] at hdiv
  have h3 := padicValNat_two_factorial (n + 3)
  have hpos := digits_two_sum_pos (n + 3) (by omega)
  unfold a
  omega

/-! ## The conjecture -/

/-- **Bala's parity conjecture (A361035, 2023), shifted form.**
`a(n) = 9979200 (4n)!/(n! (n+3)!^3)` is odd iff `n + 3 = 2^k` for some `k ≥ 2`. -/
theorem a_odd_iff (n : ℕ) : Odd (a n) ↔ ∃ k, 2 ≤ k ∧ n + 3 = 2 ^ k := by
  have hval := padicValNat_two_a n
  have hpos := a_pos n
  have hodd : Odd (a n) ↔ padicValNat 2 (a n) = 0 := by
    rw [padicValNat.eq_zero_iff, Nat.odd_iff]
    omega
  rw [hodd]
  constructor
  · intro h0
    rw [h0] at hval
    obtain ⟨k, hk⟩ := (digits_two_sum_eq_one_iff (n + 3)).mp (by omega)
    refine ⟨k, ?_, hk⟩
    by_contra hk2
    interval_cases k <;> omega
  · rintro ⟨k, -, hk⟩
    have hs := (digits_two_sum_eq_one_iff (n + 3)).mpr ⟨k, hk⟩
    omega

/-- Bala’s parity conjecture (A361035): `a(n)` is odd iff
`n = 2^k-3` for some `k ≥ 2`. The natural subtraction is exact
since `k ≥ 2` gives `4 ≤ 2^k`. -/
theorem a_odd_iff_eq_two_pow_sub_three (n : ℕ) :
    Odd (a n) ↔ ∃ k, 2 ≤ k ∧ n = 2 ^ k - 3 := by
  rw [a_odd_iff]
  constructor
  · rintro ⟨k, hk, hn⟩
    exact ⟨k, hk, by omega⟩
  · rintro ⟨k, hk, hn⟩
    have h4 : 4 ≤ 2 ^ k := calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    exact ⟨k, hk, by omega⟩

/-! ## Examples -/

-- Both sides of the equivalence are realized: `n = 1 = 2^2 - 3` gives the odd
-- term `17325`; `n = 0` gives the even term `46200`.
example : Odd (a 1) ∧ ∃ k, 2 ≤ k ∧ 1 = 2 ^ k - 3 :=
  ⟨by rw [show a 1 = 17325 by rfl]; decide, 2, le_refl 2, by norm_num⟩
example : ¬ Odd (a 0) := by rw [show a 0 = 46200 by rfl]; decide

end Candidates.A361035OddSome
