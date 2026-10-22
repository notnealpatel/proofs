/-
# A295432 — Bala (Jun 2026): `6 (6n+1) (12n-1)` divides `a(n)`

Peter Bala's conjecture in OEIS A295432 (June 10, 2026) states that
`6(6n+1)(12n-1)` divides `a(n)` for `n ≥ 1`, where
`a(n) = (12n)! (3n)! (2n)! / ((6n)! (6n)! (4n)! n!)`.

## Proof outline

With `J = ⌊12 n / q⌋`, every Legendre term of `a(n)` at `q = p^i` equals
`F J = J + ⌊J/4⌋ + ⌊J/6⌋ - 2⌊J/2⌋ - ⌊J/3⌋ - ⌊J/12⌋ ≥ 0`, which depends only on
`J mod 12` and is `1` exactly for `J mod 12 ∈ {1,5,7,8,9,11}`.
* `q ∣ 6n+1` forces `J = 2t-1` with `t` coprime to `6`, so `J mod 12 ∈ {1,9}`.
* `q ∣ 12n-1` forces `J = t` with `t` coprime to `6`, so `J mod 12 ∈ {1,5,7,11}`.
* `p = 2`: at `2^i ∈ (6n, 12n]`, `J = 1`.
* `p = 3`: descent from `J ∈ {1,2}` at `3^k ≤ 12n < 3^(k+1)`; a chain of
  zero terms keeps `J ≡ 6 (mod 12)` down to `J = 12 n ≡ 0`, a contradiction.
Pairwise coprimality of `6`, `6n+1`, `12n-1` assembles the product.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A295432BalaJunDivides

open Finset Nat

/-- OEIS A295432: `a(n) = (12n)! (3n)! (2n)! / ((6n)! (6n)! (4n)! n!)` (natural-number
division; `den_dvd_num` shows it is exact). -/
def a (n : ℕ) : ℕ :=
  (12 * n)! * (3 * n)! * (2 * n)! / ((6 * n)! * (6 * n)! * (4 * n)! * n !)

example : a 0 = 1 := by decide
example : a 1 = 462 := by decide
example : a 2 = 579462 := by decide
example : a 3 = 825012300 := by decide

/-- The Landau step function in terms of `J = ⌊12x⌋`:
`F J = (J + ⌊J/4⌋ + ⌊J/6⌋) - (2⌊J/2⌋ + ⌊J/3⌋ + ⌊J/12⌋)`. -/
def F (J : ℕ) : ℕ := (J + J / 4 + J / 6) - (2 * (J / 2) + J / 3 + J / 12)

/-- The step identity: `J + ⌊J/4⌋ + ⌊J/6⌋ = 2⌊J/2⌋ + ⌊J/3⌋ + ⌊J/12⌋ + F J`. -/
theorem F_spec (J : ℕ) : J + J / 4 + J / 6 = 2 * (J / 2) + J / 3 + J / 12 + F J := by
  unfold F; omega

/-- `⌊m / q⌋ = ⌊⌊c m / q⌋ / c⌋` for `0 < c`. -/
theorem div_eq_div_div (m c q : ℕ) (hc : 0 < c) :
    m / q = (c * m) / q / c := by
  rw [Nat.div_div_eq_div_mul, mul_comm q c, Nat.mul_div_mul_left _ _ hc]

/-- Termwise identity behind Legendre's formula for `a(n)`. -/
theorem term (n q : ℕ) :
    12 * n / q + 3 * n / q + 2 * n / q
      = 2 * (6 * n / q) + 4 * n / q + n / q + F (12 * n / q) := by
  have h3 : 3 * n / q = 12 * n / q / 4 := by
    rw [div_eq_div_div (3 * n) 4 q (by norm_num)]; ring_nf
  have h2 : 2 * n / q = 12 * n / q / 6 := by
    rw [div_eq_div_div (2 * n) 6 q (by norm_num)]; ring_nf
  have h6 : 6 * n / q = 12 * n / q / 2 := by
    rw [div_eq_div_div (6 * n) 2 q (by norm_num)]; ring_nf
  have h4 : 4 * n / q = 12 * n / q / 3 := by
    rw [div_eq_div_div (4 * n) 3 q (by norm_num)]; ring_nf
  have h1 : n / q = 12 * n / q / 12 := div_eq_div_div n 12 q (by norm_num)
  rw [h3, h2, h6, h4, h1]
  exact F_spec _


/-- Legendre bound used throughout: `b = 12 n + 1`. -/
theorem log_lt_bound (p n k : ℕ) (hk : k ≤ 12 * n) : log p k < 12 * n + 1 :=
  lt_of_le_of_lt ((log_le_self p k).trans hk) (Nat.lt_succ_self _)

/-- Factorization of the numerator minus the denominator is the sum of the step function. -/
theorem factorization_num (n p : ℕ) (hp : p.Prime) :
    ((12 * n)! * (3 * n)! * (2 * n)!).factorization p
      = ((6 * n)! * (6 * n)! * (4 * n)! * n !).factorization p
        + ∑ i ∈ Ico 1 (12 * n + 1), F (12 * n / p ^ i) := by
  have hL : ∀ k, k ≤ 12 * n →
      (k !).factorization p = ∑ i ∈ Ico 1 (12 * n + 1), k / p ^ i :=
    fun k hk => factorization_factorial hp (log_lt_bound p n k hk)
  have hm : ∀ x y : ℕ, x ≠ 0 → y ≠ 0 →
      (x * y).factorization p = x.factorization p + y.factorization p := fun x y hx hy => by
    rw [Nat.factorization_mul hx hy, Finsupp.add_apply]
  have hf := factorial_ne_zero
  rw [hm _ _ (mul_ne_zero (hf _) (hf _)) (hf _), hm _ _ (hf _) (hf _),
    hm _ _ (mul_ne_zero (mul_ne_zero (hf _) (hf _)) (hf _)) (hf _),
    hm _ _ (mul_ne_zero (hf _) (hf _)) (hf _), hm _ _ (hf _) (hf _)]
  rw [hL (12 * n) le_rfl, hL (3 * n) (by omega), hL (2 * n) (by omega), hL (6 * n) (by omega),
    hL (4 * n) (by omega), hL n (by omega)]
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hterm := term n (p ^ i)
  omega

/-- Integrality: the denominator divides the numerator. -/
theorem den_dvd_num (n : ℕ) :
    (6 * n)! * (6 * n)! * (4 * n)! * n ! ∣ (12 * n)! * (3 * n)! * (2 * n)! := by
  rw [← Nat.factorization_prime_le_iff_dvd (by positivity) (by positivity)]
  intro p hp
  rw [factorization_num n p hp]
  exact Nat.le_add_right _ _

/-- Legendre's formula for `a(n)`: `v_p(a(n)) = ∑_{i ≥ 1} F(⌊12 n / p^i⌋)`. -/
theorem factorization_a (n p : ℕ) (hp : p.Prime) :
    (a n).factorization p = ∑ i ∈ Ico 1 (12 * n + 1), F (12 * n / p ^ i) := by
  unfold a
  rw [Nat.factorization_div (den_dvd_num n), Finsupp.tsub_apply, factorization_num n p hp]
  omega

/-- `a(n)` is positive. -/
theorem a_pos (n : ℕ) : 0 < a n :=
  Nat.div_pos (Nat.le_of_dvd (by positivity) (den_dvd_num n)) (by positivity)


/-- Termwise criterion: if `0 < d ≤ 12 n` and every `q ≥ 2` dividing `d` has
`1 ≤ F(⌊12 n / q⌋)`, then `d ∣ a(n)`. -/
theorem dvd_a_of_forall (n d : ℕ) (hd : 0 < d) (hdn : d ≤ 12 * n)
    (h : ∀ q, 2 ≤ q → q ∣ d → 1 ≤ F (12 * n / q)) : d ∣ a n := by
  rw [← Nat.factorization_prime_le_iff_dvd hd.ne' (a_pos n).ne']
  intro p hp
  have hb : d < p ^ (12 * n + 1) :=
    lt_of_le_of_lt (hdn.trans (Nat.le_succ _)) (Nat.lt_pow_self hp.one_lt)
  rw [factorization_a n p hp, Nat.factorization_eq_card_pow_dvd_of_lt hp hd hb,
    Finset.card_filter]
  refine Finset.sum_le_sum fun i hi => ?_
  split_ifs with hdiv
  · have hi1 : 1 ≤ i := (Finset.mem_Ico.mp hi).1
    have hq : 2 ≤ p ^ i :=
      hp.two_le.trans (Nat.le_self_pow (by omega) p)
    exact h _ hq hdiv
  · exact Nat.zero_le _

/-- A prime `p` divides `a(n)` as soon as one Legendre term `F(⌊12 n / p^i⌋)`,
`1 ≤ i ≤ 12 n`, is positive. -/
theorem prime_dvd_a_of_exists (n p i : ℕ) (hp : p.Prime) (hi1 : 1 ≤ i) (hin : i ≤ 12 * n)
    (hF : 1 ≤ F (12 * n / p ^ i)) : p ∣ a n := by
  rw [hp.dvd_iff_one_le_factorization (a_pos n).ne', factorization_a n p hp]
  exact hF.trans (Finset.single_le_sum (f := fun j => F (12 * n / p ^ j))
    (fun _ _ => Nat.zero_le _) (Finset.mem_Ico.mpr ⟨hi1, by omega⟩))


/-- If `q ≥ 2` divides `6 n + 1` then `1 ≤ F(⌊12 n / q⌋)`. -/
theorem F_pos_of_dvd_six (n q : ℕ) (hq : 2 ≤ q) (hdvd : q ∣ 6 * n + 1) :
    1 ≤ F (12 * n / q) := by
  obtain ⟨t, ht⟩ := hdvd
  have h2 : ¬ 2 ∣ t := fun h => by
    have h' := Dvd.dvd.mul_left h q; rw [← ht] at h'; omega
  have h3 : ¬ 3 ∣ t := fun h => by
    have h' := Dvd.dvd.mul_left h q; rw [← ht] at h'; omega
  have ht1 : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · rw [h0] at ht; omega
    · exact h0
  have hJ : 12 * n / q = 2 * t - 1 := by
    apply Nat.div_eq_of_lt_le
    · have : (2 * t - 1) * q = 2 * (q * t) - q := by
        rw [Nat.sub_mul, mul_comm q t]; ring_nf
      omega
    · have : (2 * t - 1 + 1) * q = 2 * (q * t) := by
        rw [Nat.sub_add_cancel (by omega)]; ring
      omega
  rw [hJ]; unfold F; omega

/-- If `q ≥ 2` divides `12 n - 1` (with `1 ≤ n`) then `1 ≤ F(⌊12 n / q⌋)`. -/
theorem F_pos_of_dvd_twelve (n q : ℕ) (hn : 1 ≤ n) (hq : 2 ≤ q) (hdvd : q ∣ 12 * n - 1) :
    1 ≤ F (12 * n / q) := by
  obtain ⟨t, ht⟩ := hdvd
  have h2 : ¬ 2 ∣ t := fun h => by
    have h' := Dvd.dvd.mul_left h q; rw [← ht] at h'; omega
  have h3 : ¬ 3 ∣ t := fun h => by
    have h' := Dvd.dvd.mul_left h q; rw [← ht] at h'; omega
  have hJ : 12 * n / q = t := by
    apply Nat.div_eq_of_lt_le
    · rw [mul_comm]; omega
    · have : (t + 1) * q = q * t + q := by ring
      omega
  rw [hJ]; unfold F; omega

/-- `2 ∣ a(n)` for `1 ≤ n`: the Legendre term at `2^i ∈ (6n, 12n]` equals `F 1 = 1`. -/
theorem two_dvd_a (n : ℕ) (hn : 1 ≤ n) : 2 ∣ a n := by
  set i := log 2 (12 * n) with hi
  have hlo : 2 ^ i ≤ 12 * n := Nat.pow_log_le_self 2 (by omega)
  have hhi : 12 * n < 2 ^ (i + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hi1 : 1 ≤ i := by
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · rw [h0] at hhi; omega
    · exact h0
  have hin : i ≤ 12 * n := Nat.log_le_self 2 _
  apply prime_dvd_a_of_exists n 2 i Nat.prime_two hi1 hin
  have hJ : 12 * n / 2 ^ i = 1 := by
    apply Nat.div_eq_of_lt_le
    · omega
    · rw [pow_succ] at hhi; omega
  rw [hJ]; decide


/-- Descent for the prime `3`: with `J k = ⌊12 n / 3^k⌋`, if `J k ≡ 1, 2, 6 (mod 12)`
then some `F (J j)` with `1 ≤ j ≤ k` is positive. -/
theorem three_descent (n : ℕ) :
    ∀ k, (12 * n / 3 ^ k % 12 = 1 ∨ 12 * n / 3 ^ k % 12 = 2 ∨ 12 * n / 3 ^ k % 12 = 6) →
      ∃ j, 1 ≤ j ∧ j ≤ k ∧ 1 ≤ F (12 * n / 3 ^ j) := by
  intro k
  induction k with
  | zero => intro h; simp only [pow_zero, Nat.div_one] at h; omega
  | succ k ih =>
    intro h
    have hJ : 12 * n / 3 ^ (k + 1) = 12 * n / 3 ^ k / 3 := by
      rw [pow_succ, Nat.div_div_eq_div_mul]
    rw [hJ] at h
    by_cases h1 : 12 * n / 3 ^ k / 3 % 12 = 1
    · refine ⟨k + 1, by omega, le_rfl, ?_⟩
      rw [hJ]; unfold F; omega
    · have hk : 12 * n / 3 ^ k % 12 = 6 ∨ 12 * n / 3 ^ k % 12 = 7 ∨
          12 * n / 3 ^ k % 12 = 8 := by omega
      rcases hk with h6 | h78
      · obtain ⟨j, hj1, hjk, hF⟩ := ih (Or.inr (Or.inr h6))
        exact ⟨j, hj1, by omega, hF⟩
      · have hk1 : 1 ≤ k := by
          rcases Nat.eq_zero_or_pos k with h0 | h0
          · rw [h0, pow_zero, Nat.div_one] at h78; omega
          · exact h0
        exact ⟨k, hk1, by omega, by unfold F; omega⟩

/-- `3 ∣ a(n)` for `1 ≤ n`, via `three_descent` from the index `k = ⌊log₃ 12 n⌋`. -/
theorem three_dvd_a (n : ℕ) (hn : 1 ≤ n) : 3 ∣ a n := by
  set k := log 3 (12 * n) with hk
  have hlo : 3 ^ k ≤ 12 * n := Nat.pow_log_le_self 3 (by omega)
  have hhi : 12 * n < 3 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hkn : k ≤ 12 * n := Nat.log_le_self 3 _
  have hJ : 12 * n / 3 ^ k = 1 ∨ 12 * n / 3 ^ k = 2 := by
    rw [pow_succ] at hhi
    have hpos : 0 < 3 ^ k := by positivity
    have h1 : 1 ≤ 12 * n / 3 ^ k := (Nat.le_div_iff_mul_le hpos).mpr (by omega)
    have h2 : 12 * n / 3 ^ k < 3 := (Nat.div_lt_iff_lt_mul hpos).mpr (by omega)
    omega
  obtain ⟨j, hj1, hjk, hF⟩ := three_descent n k (by omega)
  exact prime_dvd_a_of_exists n 3 j Nat.prime_three hj1 (hjk.trans hkn) hF

/-- `6 n + 1 ∣ a(n)`. -/
theorem six_add_one_dvd_a (n : ℕ) (hn : 1 ≤ n) : 6 * n + 1 ∣ a n :=
  dvd_a_of_forall n (6 * n + 1) (by omega) (by omega)
    fun q hq hdvd => F_pos_of_dvd_six n q hq hdvd

/-- `12 n - 1 ∣ a(n)` for `1 ≤ n`. -/
theorem twelve_sub_one_dvd_a (n : ℕ) (hn : 1 ≤ n) : 12 * n - 1 ∣ a n :=
  dvd_a_of_forall n (12 * n - 1) (by omega) (by omega)
    fun q hq hdvd => F_pos_of_dvd_twelve n q hn hq hdvd

/-- Bala's conjecture (OEIS A295432, June 10, 2026):
`6(6n+1)(12n-1)` divides `a(n)` for `1 ≤ n`. This guard also
keeps the natural subtraction `12n-1` from truncating. -/
theorem bala_conjecture (n : ℕ) (hn : 1 ≤ n) : 6 * (6 * n + 1) * (12 * n - 1) ∣ a n := by
  have hcop1 : Nat.Coprime (6 * n + 1) (12 * n - 1) := by
    rw [← Nat.isCoprime_iff_coprime]
    refine ⟨1 - 4 * (n : ℤ), 2 * n, ?_⟩
    push_cast [show 1 ≤ 12 * n by omega]
    ring
  have hcop6a : Nat.Coprime 6 (6 * n + 1) := by
    rw [← Nat.isCoprime_iff_coprime]
    refine ⟨-(n : ℤ), 1, ?_⟩
    push_cast
    ring
  have hcop6b : Nat.Coprime 6 (12 * n - 1) := by
    rw [← Nat.isCoprime_iff_coprime]
    refine ⟨2 * n, -1, ?_⟩
    push_cast [show 1 ≤ 12 * n by omega]
    ring
  have h6 : 6 ∣ a n :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) (two_dvd_a n hn) (three_dvd_a n hn)
  have hprod : (6 * n + 1) * (12 * n - 1) ∣ a n :=
    hcop1.mul_dvd_of_dvd_of_dvd (six_add_one_dvd_a n hn) (twelve_sub_one_dvd_a n hn)
  rw [mul_assoc]
  exact (Nat.Coprime.mul_right hcop6a hcop6b).mul_dvd_of_dvd_of_dvd h6 hprod

/-- At `n = 1`, `6 · 7 · 11 = 462 = a(1)`. -/
example : 6 * (6 * 1 + 1) * (12 * 1 - 1) ∣ a 1 := bala_conjecture 1 le_rfl

example : 6 * (6 * 1 + 1) * (12 * 1 - 1) = a 1 := by decide

end Candidates.A295432BalaJunDivides
