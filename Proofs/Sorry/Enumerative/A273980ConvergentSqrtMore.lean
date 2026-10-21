/-
# A273980 — Schoenfield: digit excess of √2 convergents via the mantissa of (1+√2)^(k+1)/2

## OEIS source (retrieved with `oeis show A273980`, 2026-10-21)

```
NAME:     Numbers k such that the number of digits in the numerator of the k-th
          convergent of the continued fraction 1+1/(2+1/(2+1/(2+...))) = sqrt(2)
          exceeds the number of digits in the denominator.
TERMS:    8,13,21,26,34,39,47,55,60,68,73,81,86,89,94,102,107,115,120,128,136,
          141,149,154,162,167,175,183,188,196,201,209,217,222,230,235,243,248,...
COMMENT (indexing):
  The square root of two can be expressed as the continued fraction
  1+1/(2+1/(2+1/(2+...))), whose first three convergents are a(1)=1+1/2=3/2,
  a(2)=1+1/(2+1/2)=7/5 and a(3)=1+1/(2+1/(2+1/2))=17/12. At the 8th
  convergent, 1393/985, the number of digits in the numerator exceeds the
  number of digits in the denominator for the first time.
COMMENT (the conjecture; From _Jon E. Schoenfield_, Nov 27 2016):
  Conjecture: an integer k is in the sequence iff s(k)/10^floor(log_10(s(k)))
  is in the interval [1, sqrt(2)] where s(k) = ((1+sqrt(2))^(k+1))/2. (In
  other words, k is in the sequence if and only if ((1+sqrt(2))^(k+1))/2,
  expressed in the form x*10^m where m is the integer such that 1 <= x < 10,
  satisfies x < sqrt(2).)
```

## Status

Triage: open (no proof in the entry or the literature as far as the triage
could tell).  This module proves the conjecture for every `k ≥ 1`, i.e. for
every index of a convergent in the entry's numbering (`a(1) = 3/2`).

## Boundary

The `0`-th convergent `1/1` is a genuine exception to the literal statement:
`s(0) = (1+√2)/2 ≈ 1.207` has mantissa in `[1, √2]`, yet numerator and
denominator both have one digit.  The entry numbers convergents from `1`, so
the guard `1 ≤ k` matches the source; `conjecture_fails_at_zero` records the
exception.

## Proof

With `α = 1+√2`, `β = 1-√2`: `α^(k+1) = p_k + q_k √2`, `β^(k+1) = p_k - q_k √2`,
so `p_k = s + e` and `q_k √2 = s - e` with `e = β^(k+1)/2`, `|e| < 1/4`.  The
numerator has more digits iff some `10^m` satisfies `q_k < 10^m ≤ p_k`.  This is
equivalent to `10^m ≤ s ≤ √2·10^m` once `p_k ≠ 10^m` and `q_k ≠ 10^m`.  Both
follow from the Pell identity `p² - 2q² = ±1`.  For `q = 10^m`, `m ≥ 1`, the
`+1` case is excluded modulo `91`.  There `100` has order `3`, and
`2·100^m + 1` is a nonresidue mod `7` or mod `13`.  The `-1` case is excluded
modulo `4`.  For `p = 10^m`, parity rules out both cases.  Computation (k ≤ 3000,
1200-digit arithmetic) agreed, with `k = 0` the only mismatch.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A273980ConvergentSqrtMore

/-! ## Definition layer -/

/-- The tail `2 + 1/(2 + 1/(⋯ + 1/2))` of the continued fraction of `√2`
with `n + 1` partial quotients all equal to `2`. -/
def cfTail : ℕ → ℚ
  | 0 => 2
  | n + 1 => 2 + 1 / cfTail n

/-- The `k`-th convergent of `1 + 1/(2 + 1/(2 + ⋯))` in the entry's numbering:
`convergent 0 = 1`, `convergent 1 = 1 + 1/2`, `convergent 2 = 1 + 1/(2 + 1/2)`. -/
def convergent : ℕ → ℚ
  | 0 => 1
  | k + 1 => 1 + 1 / cfTail k

/-- Auxiliary pair `(p_n, q_n)` with `(1 + √2)^(n+1) = p_n + q_n √2`; it is shown
below to be the reduced numerator and denominator of `convergent n`. -/
def pq : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | n + 1 => ((pq n).1 + 2 * (pq n).2, (pq n).1 + (pq n).2)

/-- Schoenfield's `s(k) = (1 + √2)^(k+1) / 2`. -/
noncomputable def s (k : ℕ) : ℝ := (1 + √2) ^ (k + 1) / 2

/-- The decimal mantissa `x / 10^⌊log₁₀ x⌋` of a real number `x`. -/
noncomputable def mantissa (x : ℝ) : ℝ := x / 10 ^ ⌊Real.logb 10 x⌋

/-- Membership in A273980: `k ≥ 1` and the numerator of the `k`-th convergent
has more decimal digits than its denominator. -/
def IsA273980 (k : ℕ) : Prop :=
  1 ≤ k ∧ (Nat.digits 10 (convergent k).den).length <
    (Nat.digits 10 (convergent k).num.natAbs).length

/-! ## Ground truth -/

example : convergent 1 = 3 / 2 := by norm_num [convergent, cfTail]
example : convergent 2 = 7 / 5 := by norm_num [convergent, cfTail]
example : convergent 3 = 17 / 12 := by norm_num [convergent, cfTail]
example : convergent 8 = 1393 / 985 := by norm_num [convergent, cfTail]
example : convergent 13 = 114243 / 80782 := by norm_num [convergent, cfTail]
example : pq 8 = (1393, 985) := by decide
example : pq 13 = (114243, 80782) := by decide

/-! ## Integer side -/

/-- Pell identity: `p_n² - 2 q_n² = ±1`, in subtraction-free form. -/
theorem pell (n : ℕ) :
    (pq n).1 ^ 2 = 2 * (pq n).2 ^ 2 + 1 ∨ (pq n).1 ^ 2 + 1 = 2 * (pq n).2 ^ 2 := by
  induction n with
  | zero => right; norm_num [pq]
  | succ n ih =>
    simp only [pq]
    rcases ih with h | h
    · right; nlinarith
    · left; nlinarith

/-- `2·(10^m)² + 1` is never a perfect square: modulo `91`, `100^m` cycles through
`1, 9, 81` and `2·100^m + 1` is a quadratic nonresidue in each case. -/
theorem not_sq_two_mul_pow_ten_sq_add_one (m p : ℕ) : p ^ 2 ≠ 2 * (10 ^ m) ^ 2 + 1 := by
  intro h
  have h1 : p ^ 2 % 91 = (2 * (10 ^ m) ^ 2 + 1) % 91 := by rw [h]
  have hp : p ^ 2 % 91 = (p % 91) ^ 2 % 91 := by rw [Nat.pow_mod]
  have h100 : (2 * (10 ^ m) ^ 2 + 1) % 91 = (2 * (100 ^ (m % 3)) + 1) % 91 := by
    have hsq : (10 ^ m) ^ 2 = (100 ^ 3) ^ (m / 3) * 100 ^ (m % 3) := by
      calc (10 ^ m) ^ 2 = 100 ^ m := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
        _ = 100 ^ (3 * (m / 3) + m % 3) := by rw [Nat.div_add_mod]
        _ = (100 ^ 3) ^ (m / 3) * 100 ^ (m % 3) := by rw [pow_add, pow_mul]
    have hone : (100 ^ 3) ^ (m / 3) % 91 = 1 := by
      rw [Nat.pow_mod]; norm_num
    rw [hsq, Nat.add_mod, Nat.mul_mod, Nat.mul_mod ((100 ^ 3) ^ (m / 3)), hone]
    simp [Nat.add_mod, Nat.mul_mod]
  have hm : m % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hr : p % 91 < 91 := Nat.mod_lt _ (by norm_num)
  rw [hp, h100] at h1
  generalize p % 91 = r at h1 hr
  generalize m % 3 = t at h1 hm
  interval_cases t <;> interval_cases r <;> simp_all

/-- Every denominator `q_n` is positive. -/
theorem q_pos (n : ℕ) : 0 < (pq n).2 := by
  cases n with
  | zero => simp [pq]
  | succ n => simp only [pq]; have hq := q_pos n; omega

/-- Every numerator `p_n` is positive. -/
theorem p_pos (n : ℕ) : 0 < (pq n).1 := by
  cases n with
  | zero => simp [pq]
  | succ n => simp only [pq]; have hq := q_pos n; omega

/-- For `k ≥ 1` the denominator is at least `2`. -/
theorem two_le_q (k : ℕ) (hk : 1 ≤ k) : 2 ≤ (pq k).2 := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have h1 := q_pos n
  have h2 := p_pos n
  simp only [pq]; omega

/-- For `k ≥ 1` the numerator is at least `3`. -/
theorem three_le_p (k : ℕ) (hk : 1 ≤ k) : 3 ≤ (pq k).1 := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have h1 := q_pos n
  have h2 := p_pos n
  simp only [pq]; omega

/-- For `k ≥ 1` the denominator `q_k` (a Pell number) is never a power of `10`. -/
theorem q_ne_pow_ten (k m : ℕ) (hk : 1 ≤ k) : (pq k).2 ≠ 10 ^ m := by
  intro hq
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have h2 := two_le_q k hk
    rw [pow_zero] at hq
    omega
  rcases pell k with h | h
  · rw [hq] at h; exact not_sq_two_mul_pow_ten_sq_add_one m _ h
  · rw [hq] at h
    have h4 : (2 * (10 ^ m) ^ 2) % 4 = 0 := by
      obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
      exact Nat.mod_eq_zero_of_dvd ⟨50 * (10 ^ j) ^ 2, by ring⟩
    have hp : ((pq k).1 ^ 2 + 1) % 4 = ((pq k).1 % 4) ^ 2 % 4 + 1 := by
      rw [Nat.add_mod, Nat.pow_mod]
      have hr : (pq k).1 % 4 < 4 := Nat.mod_lt _ (by norm_num)
      interval_cases (pq k).1 % 4 <;> simp
    have hr : (pq k).1 % 4 < 4 := Nat.mod_lt _ (by norm_num)
    rw [h, h4] at hp
    interval_cases (pq k).1 % 4 <;> simp at hp

/-- For `k ≥ 1` the numerator `p_k` is never a power of `10`. -/
theorem p_ne_pow_ten (k m : ℕ) (hk : 1 ≤ k) : (pq k).1 ≠ 10 ^ m := by
  intro hp
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have h3 := three_le_p k hk
    rw [pow_zero] at hp
    omega
  have h2 : 2 ∣ (10 ^ m) ^ 2 := by
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    exact Dvd.dvd.pow (Dvd.dvd.pow (by norm_num) (by omega)) (by norm_num)
  rcases pell k with h | h <;> rw [hp] at h <;> omega

/-- `p_n` and `q_n` are coprime (from the Pell identity). -/
theorem coprime_pq (n : ℕ) : Nat.Coprime (pq n).1 (pq n).2 := by
  have hd1 : Nat.gcd (pq n).1 (pq n).2 ∣ (pq n).1 ^ 2 :=
    Dvd.dvd.pow (Nat.gcd_dvd_left _ _) (by norm_num)
  have hd2 : Nat.gcd (pq n).1 (pq n).2 ∣ 2 * (pq n).2 ^ 2 :=
    Dvd.dvd.mul_left (Dvd.dvd.pow (Nat.gcd_dvd_right _ _) (by norm_num)) _
  rcases pell n with h | h
  · rw [h] at hd1
    exact Nat.dvd_one.mp ((Nat.dvd_add_right hd2).mp hd1)
  · rw [← h] at hd2
    exact Nat.dvd_one.mp ((Nat.dvd_add_right hd1).mp hd2)

/-- The tail `[2; 2, …, 2]` with `n + 1` twos equals `q_{n+1} / q_n`. -/
theorem cfTail_eq (n : ℕ) : cfTail n = ((pq (n + 1)).2 : ℚ) / (pq n).2 := by
  induction n with
  | zero => norm_num [cfTail, pq]
  | succ n ih =>
    rw [cfTail, ih]
    have h0 : ((pq n).2 : ℚ) ≠ 0 := by exact_mod_cast (q_pos n).ne'
    have h1 : ((pq (n + 1)).2 : ℚ) ≠ 0 := by exact_mod_cast (q_pos (n + 1)).ne'
    have h2 : ((pq (n + 2)).2 : ℚ) = 2 * (pq (n + 1)).2 + (pq n).2 := by
      simp only [pq]; push_cast; ring
    rw [h2]; field_simp

/-- The `k`-th convergent equals `p_k / q_k`. -/
theorem convergent_eq (k : ℕ) : convergent k = ((pq k).1 : ℚ) / (pq k).2 := by
  cases k with
  | zero => norm_num [convergent, pq]
  | succ n =>
    rw [convergent, cfTail_eq]
    have h0 : ((pq n).2 : ℚ) ≠ 0 := by exact_mod_cast (q_pos n).ne'
    have h1 : ((pq (n + 1)).2 : ℚ) ≠ 0 := by exact_mod_cast (q_pos (n + 1)).ne'
    have h2 : ((pq (n + 1)).1 : ℚ) = (pq (n + 1)).2 + (pq n).2 := by
      simp only [pq]; push_cast; ring
    rw [h2]; field_simp

/-- The reduced numerator of the `k`-th convergent is `p_k`. -/
theorem num_convergent (k : ℕ) : (convergent k).num.natAbs = (pq k).1 := by
  have h := Rat.num_div_eq_of_coprime (a := ((pq k).1 : ℤ)) (b := ((pq k).2 : ℤ))
    (by exact_mod_cast q_pos k) (by simpa using coprime_pq k)
  rw [convergent_eq]
  push_cast at h
  rw [h]; simp

/-- The reduced denominator of the `k`-th convergent is `q_k`. -/
theorem den_convergent (k : ℕ) : (convergent k).den = (pq k).2 := by
  have h := Rat.den_div_eq_of_coprime (a := ((pq k).1 : ℤ)) (b := ((pq k).2 : ℤ))
    (by exact_mod_cast q_pos k) (by simpa using coprime_pq k)
  rw [convergent_eq]
  push_cast at h
  exact_mod_cast h

/-! ## Real side -/

/-- Binet-type identities: `(1 ± √2)^(n+1) = p_n ± q_n √2`. -/
theorem binet (n : ℕ) :
    (1 + √2) ^ (n + 1) = (pq n).1 + (pq n).2 * √2 ∧
      (1 - √2) ^ (n + 1) = (pq n).1 - (pq n).2 * √2 := by
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  induction n with
  | zero => simp [pq]
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    simp only [pq]; push_cast
    constructor
    · rw [pow_succ, ih1]; linear_combination ((pq n).2 : ℝ) * h2
    · rw [pow_succ, ih2]; linear_combination ((pq n).2 : ℝ) * h2

/-- `1 < √2`. -/
theorem one_lt_sqrt_two : 1 < √2 := by
  rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- The error term `(1 - √2)^(k+1) / 2` has absolute value below `1/4`. -/
theorem abs_err_lt (k : ℕ) : |(1 - √2) ^ (k + 1) / 2| < 1 / 4 := by
  have hs1 := one_lt_sqrt_two
  have hs2 : √2 < 3 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hb : |1 - √2| < 1 / 2 := by
    rw [abs_sub_comm, abs_of_pos (by linarith)]; linarith
  have hb1 : |1 - √2| ≤ 1 := by linarith
  rw [abs_div, abs_pow, abs_two]
  have hpow : |1 - √2| ^ (k + 1) ≤ |1 - √2| := by
    calc |1 - √2| ^ (k + 1) ≤ |1 - √2| ^ 1 :=
          pow_le_pow_of_le_one (abs_nonneg _) hb1 (by omega)
      _ = |1 - √2| := pow_one _
  linarith

/-- Core comparison: if `p = x + e` and `q √2 = x - e` with `|e| < 1/4`, and
neither `p` nor `q` equals `10^m`, then `q < 10^m ≤ p` iff `10^m ≤ x ≤ √2·10^m`. -/
theorem core (p q : ℕ) (x e : ℝ) (he : |e| < 1 / 4) (hp : (p : ℝ) = x + e)
    (hq : (q : ℝ) * √2 = x - e) (m : ℕ) (hpne : p ≠ 10 ^ m) (hqne : q ≠ 10 ^ m) :
    (q < 10 ^ m ∧ 10 ^ m ≤ p) ↔ ((10 : ℝ) ^ m ≤ x ∧ x ≤ √2 * 10 ^ m) := by
  have hs1 := one_lt_sqrt_two
  obtain ⟨he1, he2⟩ := abs_lt.mp he
  constructor
  · rintro ⟨hq1, hp1⟩
    have hp2 : 10 ^ m + 1 ≤ p := by omega
    have hq2 : q + 1 ≤ 10 ^ m := hq1
    have hp3 : ((10 : ℝ) ^ m + 1) ≤ p := by exact_mod_cast hp2
    have hq3 : (q : ℝ) + 1 ≤ 10 ^ m := by exact_mod_cast hq2
    constructor
    · linarith
    · nlinarith
  · rintro ⟨hx1, hx2⟩
    have hp3 : (10 : ℝ) ^ m < p + 1 := by linarith
    have hq3 : (q : ℝ) < 10 ^ m + 1 := by
      by_contra hc
      push Not at hc
      nlinarith
    have hp4 : 10 ^ m < p + 1 := by exact_mod_cast hp3
    have hq4 : q < 10 ^ m + 1 := by exact_mod_cast hq3
    omega

/-- `q` has fewer decimal digits than `p` iff a power of `10` lies in `(q, p]`. -/
theorem digits_length_lt_iff (p q : ℕ) :
    (Nat.digits 10 q).length < (Nat.digits 10 p).length ↔
      ∃ m : ℕ, q < 10 ^ m ∧ 10 ^ m ≤ p := by
  constructor
  · intro h
    exact ⟨(Nat.digits 10 q).length, Nat.lt_base_pow_length_digits (by norm_num),
      (Nat.lt_digits_length_iff (by norm_num) p).mp h⟩
  · rintro ⟨m, hq, hp⟩
    exact lt_of_le_of_lt ((Nat.digits_length_le_iff (by norm_num) q).mpr hq)
      ((Nat.lt_digits_length_iff (by norm_num) p).mpr hp)

/-- For `x ≥ 1`, the mantissa of `x` lies in `[1, √2]` iff `10^m ≤ x ≤ √2·10^m`
for some natural `m`. -/
theorem mantissa_mem_iff (x : ℝ) (hx : 1 ≤ x) :
    (1 ≤ mantissa x ∧ mantissa x ≤ √2) ↔
      ∃ m : ℕ, (10 : ℝ) ^ m ≤ x ∧ x ≤ √2 * 10 ^ m := by
  have hfl : ⌊Real.logb 10 x⌋ = Int.log 10 x := by
    have hb := Real.floor_logb_natCast (b := 10) (r := x) (by linarith)
    simpa using hb
  set N := Nat.log 10 ⌊x⌋₊ with hN
  have hlog : Int.log 10 x = (N : ℤ) := Int.log_of_one_le_right 10 hx
  have hman : mantissa x = x / 10 ^ N := by
    rw [mantissa, hfl, hlog, zpow_natCast]
  have hlo : (10 : ℝ) ^ N ≤ x := by
    have hz := Int.zpow_log_le_self (b := 10) (r := x) (by norm_num) (by linarith)
    rw [hlog] at hz; exact_mod_cast hz
  have hhi : x < (10 : ℝ) ^ (N + 1) := by
    have hz := Int.lt_zpow_succ_log_self (b := 10) (by norm_num) x
    rw [hlog] at hz; exact_mod_cast hz
  have hpos : (0 : ℝ) < 10 ^ N := by positivity
  have hs2 : √2 < 10 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  rw [hman]
  constructor
  · rintro ⟨-, h2⟩
    refine ⟨N, hlo, ?_⟩
    rwa [div_le_iff₀ hpos] at h2
  · rintro ⟨m, hm1, hm2⟩
    have hmN : m = N := by
      have h1 : m < N + 1 := by
        have hlt : (10 : ℝ) ^ m < 10 ^ (N + 1) := lt_of_le_of_lt hm1 hhi
        exact (pow_lt_pow_iff_right₀ (by norm_num)).mp hlt
      have h2 : N < m + 1 := by
        have hlt : (10 : ℝ) ^ N < 10 ^ (m + 1) := by
          calc (10 : ℝ) ^ N ≤ x := hlo
            _ ≤ √2 * 10 ^ m := hm2
            _ < 10 * 10 ^ m := by gcongr
            _ = 10 ^ (m + 1) := by ring
        exact (pow_lt_pow_iff_right₀ (by norm_num)).mp hlt
      omega
    subst hmN
    constructor
    · rw [le_div_iff₀ hpos]; linarith
    · rw [div_le_iff₀ hpos]; exact hm2

/-! ## The conjecture -/

/-- **Schoenfield's conjecture (A273980, Jon E. Schoenfield, Nov 27 2016), proved
for every convergent index `k ≥ 1`.**

Verbatim: "Conjecture: an integer k is in the sequence iff s(k)/10^floor(log_10(s(k)))
is in the interval [1, sqrt(2)] where s(k) = ((1+sqrt(2))^(k+1))/2."

The numerator of the `k`-th convergent of `√2` has more decimal digits than its
denominator iff the mantissa `s(k) / 10^⌊log₁₀ s(k)⌋` of
`s(k) = (1 + √2)^(k+1)/2` lies in `[1, √2]`.  The guard `1 ≤ k` follows the
entry's numbering (first convergent `3/2`); at `k = 0` the statement fails, see
`conjecture_fails_at_zero`. -/
theorem schoenfield_conjecture (k : ℕ) (hk : 1 ≤ k) :
    (Nat.digits 10 (convergent k).den).length <
        (Nat.digits 10 (convergent k).num.natAbs).length ↔
      1 ≤ mantissa (s k) ∧ mantissa (s k) ≤ √2 := by
  have hs1 := one_lt_sqrt_two
  obtain ⟨b1, b2⟩ := binet k
  have hsk : 1 ≤ s k := by
    have h3' : (3 : ℝ) ≤ (pq k).1 := by exact_mod_cast three_le_p k hk
    have h2' : (2 : ℝ) ≤ (pq k).2 := by exact_mod_cast two_le_q k hk
    rw [s, b1]; nlinarith
  rw [num_convergent, den_convergent, digits_length_lt_iff, mantissa_mem_iff _ hsk]
  refine exists_congr fun m => core (pq k).1 (pq k).2 (s k) ((1 - √2) ^ (k + 1) / 2)
    (abs_err_lt k) ?_ ?_ m (p_ne_pow_ten k m hk) (q_ne_pow_ten k m hk)
  · rw [s]; linear_combination -(b1 + b2) / 2
  · rw [s]; linear_combination -(b1 - b2) / 2

/-- Sequence form: `k` is in A273980 iff `k ≥ 1` and the mantissa of
`s(k) = (1 + √2)^(k+1)/2` lies in `[1, √2]`. -/
theorem isA273980_iff (k : ℕ) :
    IsA273980 k ↔ 1 ≤ k ∧ 1 ≤ mantissa (s k) ∧ mantissa (s k) ≤ √2 := by
  constructor
  · rintro ⟨hk, h⟩
    exact ⟨hk, (schoenfield_conjecture k hk).mp h⟩
  · rintro ⟨hk, h⟩
    exact ⟨hk, (schoenfield_conjecture k hk).mpr h⟩

/-- Boundary exception: at the `0`-th convergent `1/1` the mantissa of `s(0)` lies
in `[1, √2]`, but numerator and denominator have the same number of digits. -/
theorem conjecture_fails_at_zero :
    (1 ≤ mantissa (s 0) ∧ mantissa (s 0) ≤ √2) ∧
      ¬ (Nat.digits 10 (convergent 0).den).length <
        (Nat.digits 10 (convergent 0).num.natAbs).length := by
  have hs1 := one_lt_sqrt_two
  have hs0 : s 0 = (1 + √2) / 2 := by rw [s, zero_add, pow_one]
  refine ⟨?_, ?_⟩
  · rw [mantissa_mem_iff _ (by rw [hs0]; linarith)]
    exact ⟨0, by rw [hs0, pow_zero]; linarith, by rw [hs0, pow_zero, mul_one]; linarith⟩
  · norm_num [convergent]

/-! ## Sanity layer -/

-- `k = 8` (first term) is in the sequence and `k = 7` is not.
example : IsA273980 8 := by
  refine ⟨by norm_num, ?_⟩
  rw [num_convergent, den_convergent, show pq 8 = (1393, 985) by decide]
  norm_num

example : ¬ IsA273980 7 := by
  rintro ⟨-, h⟩
  rw [num_convergent, den_convergent, show pq 7 = (577, 408) by decide] at h
  norm_num at h

end Candidates.A273980ConvergentSqrtMore
