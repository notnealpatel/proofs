/-
# A155200 — Hanna: the 2-adic valuation of a(n) is the binary digit sum of n

## OEIS source (retrieved with `oeis show A155200`, 2026-10-21)

```
NAME:     G.f.: A(x) = exp( Sum_{n>=1} 2^(n^2) * x^n/n ), a power series in x
          with integer coefficients.
TERMS:    1,2,10,188,16774,6745436,11466849412,80444398636280,
          2306003967992402758,268654794629082985019564,...
FORMULA:  a(n) = (1/n)*Sum_{k = 1..n} 2^(k^2)*a(n-k), a(0) = 1.
          - _Vladeta Jovovic_, Feb 04 2009
COMMENT (the conjecture):
  Conjecture: highest exponent of 2 dividing a(n) = A000120(n) = number of
  1's in binary expansion of n, so that a(n)/2^A000120(n) is odd for n >= 0.
  - _Paul D. Hanna_, Sep 01 2009
```

## Status

Triage: open (no proof in the entry; Fried, arXiv:2607.24832, proves only
integrality).  Numerically re-checked here for `n ≤ 130` with exact rationals.
This module proves it (`a155200_padicValRat`), with no `sorry`; the axiom
audit reports only `propext`, `Classical.choice`, `Quot.sound`.

## Formalization

`a : ℕ → ℚ` is defined by the Jovovic recurrence (the entry's equivalent
description of the exponential g.f.); `a_recurrence` restates it verbatim
as `n * a n = ∑_{k=1}^n 2^(k^2) a(n-k)` for `1 ≤ n`.  The conjecture is
stated as `a n ≠ 0 ∧ padicValRat 2 (a n) = (Nat.digits 2 n).sum`.
Integrality (Bala) is not used and not claimed: over `ℚ` the 2-adic
valuation statement makes sense without it.

## Proof

Write `A = E * B` with `E = exp(2x)` and `B = exp(∑_{k≥2} 2^(k^2) x^k / k)`,
realized as the solutions of the log-derivative recurrences `rec dE` and
`rec dB` (no power-series composition): `x F' = D F` determines `F` from
`F(0) = 1`, and Leibniz gives the product.  Then
* `v₂(2^j / j!) = s₂(j)` (Legendre),
* `v₂(b_m) ≥ m + s₂(m)` by strong induction (Kummer and
  `v₂(m) ≤ v₂(C(m,k)) + v₂(k)`),
* in `a(n) = ∑_j e_j b_{n-j}` the term `j = n` has valuation exactly
  `s₂(n)`, every other term strictly more; the ultrametric inequality ends it.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A155200ExpSumEquivalently

open PowerSeries

/-! ## Definitions -/

/-- OEIS A155200: `a 0 = 1` and `a (n+1) = (∑_{k=1}^{n+1} 2^(k^2) a(n+1-k)) / (n+1)`,
the coefficients of `exp (∑_{n≥1} 2^(n^2) x^n / n)` (Jovovic's recurrence, stated with
the index shift `k ↦ k + 1`; see `a_recurrence` for the verbatim form). -/
def a : ℕ → ℚ
  | 0 => 1
  | n + 1 => (∑ k ∈ Finset.range (n + 1), (2 : ℚ) ^ ((k + 1) ^ 2) * a (n - k)) / (n + 1)
decreasing_by omega

/-- The binary digit sum `s₂(n)` (OEIS A000120). -/
def s2 (n : ℕ) : ℕ := (Nat.digits 2 n).sum

/-- The entry's recurrence verbatim: `n * a(n) = ∑_{k=1..n} 2^(k^2) a(n-k)` for `n ≥ 1`. -/
theorem a_recurrence (n : ℕ) (hn : 1 ≤ n) :
    (n : ℚ) * a n = ∑ k ∈ Finset.Icc 1 n, (2 : ℚ) ^ (k ^ 2) * a (n - k) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hI : Finset.Icc 1 (m + 1) = Finset.Ico 1 (m + 1 + 1) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [a, hI, Finset.sum_Ico_eq_sum_range]
  have hm : (m : ℚ) + 1 ≠ 0 := by positivity
  push_cast
  rw [mul_div_cancel₀ _ hm]
  refine Finset.sum_congr (by congr 1) fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [show m + 1 - (1 + k) = m - k by omega, add_comm 1 k]

/-! ## Ground truth: the first listed terms -/

example : a 0 = 1 := by simp [a]
example : a 1 = 2 := by simp [a]
example : a 2 = 10 := by
  rw [a]; norm_num [Finset.sum_range_succ, a]
example : a 3 = 188 := by
  rw [a]; norm_num [Finset.sum_range_succ, a]
example : a 4 = 16774 := by
  rw [a]; norm_num [Finset.sum_range_succ, a]
example : a 5 = 6745436 := by
  rw [a]; norm_num [Finset.sum_range_succ, a]

example : s2 0 = 0 := by decide
example : s2 3 = 2 := by decide
example : s2 6 = 2 := by decide

/-! ## Log-derivative recurrences -/

/-- The solution of `n F_n = ∑_{k=1}^n d_k F_{n-k}`, `F_0 = 1`; formally the coefficients
of `exp (∑_{k≥1} d_k x^k / k)`. -/
def rec (d : ℕ → ℚ) : ℕ → ℚ
  | 0 => 1
  | n + 1 => (∑ k ∈ Finset.range (n + 1), d (k + 1) * rec d (n - k)) / (n + 1)
decreasing_by omega

/-- The power series `∑_{k≥1} d_k x^k` (the constant coefficient is forced to `0`). -/
def D (d : ℕ → ℚ) : ℚ⟦X⟧ := mk fun n => if n = 0 then 0 else d n

/-- Coefficient `n+1` of `D d * G`. -/
lemma coeff_succ_D_mul (d : ℕ → ℚ) (G : ℚ⟦X⟧) (n : ℕ) :
    coeff (n + 1) (D d * G) = ∑ k ∈ Finset.range (n + 1), d (k + 1) * coeff (n - k) G := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_succ,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [D]

/-- Coefficient `n+1` of `X * G'` is `(n+1) G_{n+1}`. -/
lemma coeff_succ_X_mul_derivative (G : ℚ⟦X⟧) (n : ℕ) :
    coeff (n + 1) (X * d⁄dX ℚ G) = coeff (n + 1) G * (n + 1) := by
  rw [coeff_succ_X_mul, coeff_derivative]

/-- `mk (rec d)` solves `X F' = D d * F`. -/
lemma rec_satisfies (d : ℕ → ℚ) : X * d⁄dX ℚ (mk (rec d)) = D d * mk (rec d) := by
  ext n
  cases n with
  | zero => simp [D, coeff_mul]
  | succ n =>
    rw [coeff_succ_X_mul_derivative, coeff_succ_D_mul, coeff_mk, rec]
    simp only [coeff_mk]
    field_simp

/-- Uniqueness: a series with constant coefficient `1` solving `X F' = D d * F` is
`mk (rec d)`. -/
lemma eq_mk_rec (d : ℕ → ℚ) (G : ℚ⟦X⟧) (h0 : constantCoeff G = 1)
    (h : X * d⁄dX ℚ G = D d * G) : G = mk (rec d) := by
  ext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simp [rec, h0]
    | succ n =>
      have hn := congrArg (coeff (n + 1)) h
      rw [coeff_succ_X_mul_derivative, coeff_succ_D_mul] at hn
      rw [coeff_mk, rec]
      have hsum : ∑ k ∈ Finset.range (n + 1), d (k + 1) * coeff (n - k) G
          = ∑ k ∈ Finset.range (n + 1), d (k + 1) * rec d (n - k) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [ih (n - k) (by omega), coeff_mk]
      rw [← hsum, ← hn]
      field_simp

/-- Exponential law: if `D d = D d' + D d''` then `rec d` is the Cauchy product of
`rec d'` and `rec d''`. -/
lemma mk_rec_mul (d d' d'' : ℕ → ℚ) (hd : D d = D d' + D d'') :
    mk (rec d) = mk (rec d') * mk (rec d'') := by
  symm
  apply eq_mk_rec
  · simp [rec]
  · rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hd]
    linear_combination (mk (rec d')) * rec_satisfies d'' + (mk (rec d'')) * rec_satisfies d'

/-! ## The factorization `A = exp(2x) * B` -/

/-- The weights of A155200: `d_k = 2^(k^2)`. -/
def dA (j : ℕ) : ℚ := 2 ^ (j ^ 2)

/-- The weights of `exp(2x)`: `d_1 = 2`, all others `0`. -/
def dE (j : ℕ) : ℚ := if j = 1 then 2 else 0

/-- The weights of `B = exp(∑_{k≥2} 2^(k^2) x^k / k)`. -/
def dB (j : ℕ) : ℚ := if 2 ≤ j then 2 ^ (j ^ 2) else 0

/-- `a` is the log-derivative solution with weights `2^(k^2)`. -/
lemma a_eq_rec (n : ℕ) : a n = rec dA n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simp [a, rec]
    | succ n =>
      rw [a, rec]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [ih (n - k) (by omega), dA]

/-- The weight split `2^(k^2) = [k = 1]·2 + [k ≥ 2]·2^(k^2)` for `k ≥ 1`. -/
lemma D_dA : D dA = D dE + D dB := by
  ext n
  simp only [D, coeff_mk, map_add, dA, dE, dB]
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n <;> norm_num
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos hn, zero_add]
    exact (if_neg (by omega)).symm

/-- `exp(2x)` has coefficients `2^n / n!`. -/
lemma rec_dE (n : ℕ) : rec dE n = 2 ^ n / (n.factorial : ℚ) := by
  induction n with
  | zero => simp [rec]
  | succ n ih =>
    rw [rec, Finset.sum_eq_single 0]
    · rw [Nat.sub_zero, ih, dE, if_pos rfl, Nat.factorial_succ]
      push_cast
      field_simp
      ring
    · intro k _ hk
      rw [dE, if_neg (by omega), zero_mul]
    · intro h
      exact absurd (Finset.mem_range.2 (Nat.succ_pos n)) h

/-- `a(n) = ∑_{k=0}^n (2^k / k!) b(n-k)`. -/
lemma a_eq_sum (n : ℕ) :
    a n = ∑ k ∈ Finset.range (n + 1), rec dE k * rec dB (n - k) := by
  have h := congrArg (coeff n) (mk_rec_mul dA dE dB D_dA)
  rw [coeff_mk, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simp only [coeff_mk] at h
  rw [a_eq_rec, h]

/-! ## Digit sums and valuations -/

/-- Legendre for `p = 2`: `v₂(x!) + s₂(x) = x`. -/
lemma legendre2 (x : ℕ) : padicValNat 2 x.factorial + s2 x = x := by
  have h := sub_one_mul_padicValNat_factorial (p := 2) x
  have hle := Nat.digit_sum_le 2 x
  simp only [s2]
  omega

/-- Kummer for `p = 2`: `v₂(C(m,k)) + s₂(m) = s₂(k) + s₂(m-k)`. -/
lemma kummer2 {m k : ℕ} (hk : k ≤ m) :
    padicValNat 2 (m.choose k) + s2 m = s2 k + s2 (m - k) := by
  have h := Nat.choose_mul_factorial_mul_factorial hk
  have hv := congrArg (padicValNat 2) h
  rw [padicValNat.mul (Nat.mul_ne_zero (Nat.choose_pos hk).ne' (by positivity)) (by positivity),
    padicValNat.mul (Nat.choose_pos hk).ne' (by positivity)] at hv
  have h1 := legendre2 m
  have h2 := legendre2 k
  have h3 := legendre2 (m - k)
  omega

/-- `v₂(m) ≤ v₂(C(m,k)) + v₂(k)` for `1 ≤ k ≤ m`, from `k C(m,k) = m C(m-1,k-1)`. -/
lemma val_le_choose {m k : ℕ} (hk1 : 1 ≤ k) (hkm : k ≤ m) :
    padicValNat 2 m ≤ padicValNat 2 (m.choose k) + padicValNat 2 k := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h := Nat.add_one_mul_choose_eq n j
  have hc : n.choose j ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hc' : (n + 1).choose (j + 1) ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hv := congrArg (padicValNat 2) h
  rw [padicValNat.mul (by omega) hc, padicValNat.mul hc' (by omega)] at hv
  omega

/-- `s₂(k) + v₂(k) + k ≤ k^2` for `k ≥ 2`. -/
lemma s2_add_val_add_le {k : ℕ} (hk : 2 ≤ k) : s2 k + padicValNat 2 k + k ≤ k ^ 2 := by
  have hs : s2 k ≤ k := Nat.digit_sum_le 2 k
  have hv : padicValNat 2 k < k := by
    have hd : 2 ^ padicValNat 2 k ∣ k := pow_padicValNat_dvd
    have hle := Nat.le_of_dvd (by omega) hd
    have hlt := Nat.lt_two_pow_self (n := padicValNat 2 k)
    omega
  rcases Nat.lt_or_ge k 3 with h3 | h3
  · obtain rfl : k = 2 := by omega
    have hs2 : s2 2 = 1 := by decide
    rw [hs2, padicValNat_self]
    norm_num
  · nlinarith

/-- The exponent inequality driving the bound on `b`:
`m + s₂(m) + v₂(m) ≤ k^2 + (m-k) + s₂(m-k)` for `2 ≤ k ≤ m`. -/
lemma key_exponent {m k : ℕ} (hk : 2 ≤ k) (hkm : k ≤ m) :
    m + s2 m + padicValNat 2 m ≤ k ^ 2 + (m - k) + s2 (m - k) := by
  have h1 := kummer2 hkm
  have h2 := val_le_choose (by omega : 1 ≤ k) hkm
  have h3 := s2_add_val_add_le hk
  omega

/-- Subadditivity of the binary digit sum. -/
lemma s2_le_add {n k : ℕ} (hk : k ≤ n) : s2 n ≤ s2 k + s2 (n - k) := by
  have h := kummer2 hk
  omega

/-! ## 2-adic norms -/

/-- `|2^n|₂ = (1/2)^n`. -/
lemma norm_two_pow (n : ℕ) : padicNorm 2 ((2 : ℚ) ^ n) = (1 / 2) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, padicNorm.mul, ih, pow_succ]
    have h := padicNorm.padicNorm_p_of_prime (p := 2)
    push_cast at h
    rw [h, one_div]

/-- `|m|₂ = (1/2)^(v₂ m)` for `m ≠ 0`. -/
lemma norm_natCast {m : ℕ} (hm : m ≠ 0) :
    padicNorm 2 (m : ℚ) = (1 / 2) ^ padicValNat 2 m := by
  rw [padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hm), padicValRat.of_nat, zpow_neg,
    zpow_natCast, one_div, inv_pow, Nat.cast_ofNat]

/-- Antitonicity of `(1/2)^·`. -/
lemma half_pow_le {i j : ℕ} (h : i ≤ j) : ((1 : ℚ) / 2) ^ j ≤ (1 / 2) ^ i :=
  pow_le_pow_of_le_one (by norm_num) (by norm_num) h

/-- `|2^j / j!|₂ = (1/2)^(s₂ j)`. -/
lemma norm_rec_dE (j : ℕ) : padicNorm 2 (rec dE j) = (1 / 2) ^ s2 j := by
  rw [rec_dE, padicNorm.div, norm_two_pow, norm_natCast (Nat.factorial_ne_zero j)]
  have hsplit : ((1 : ℚ) / 2) ^ j = (1 / 2) ^ padicValNat 2 j.factorial * (1 / 2) ^ s2 j := by
    rw [← pow_add, legendre2]
  rw [hsplit]
  have hpos : ((1 : ℚ) / 2) ^ padicValNat 2 j.factorial ≠ 0 := by positivity
  field_simp

/-- `|b_m|₂ ≤ (1/2)^(m + s₂ m)`. -/
lemma norm_rec_dB_le (m : ℕ) : padicNorm 2 (rec dB m) ≤ (1 / 2) ^ (m + s2 m) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    cases m with
    | zero => simp [rec, s2]
    | succ n =>
      set M := n + 1 with hM
      have hS : padicNorm 2 (∑ k ∈ Finset.range (n + 1), dB (k + 1) * rec dB (n - k))
          ≤ (1 / 2) ^ (M + s2 M + padicValNat 2 M) := by
        refine padicNorm.sum_le ⟨0, Finset.mem_range.2 (Nat.succ_pos n)⟩ fun k hk => ?_
        rw [Finset.mem_range] at hk
        rcases Nat.eq_zero_or_pos k with rfl | hk0
        · rw [dB, if_neg (by omega), zero_mul, padicNorm.zero]
          positivity
        · rw [dB, if_pos (by omega), padicNorm.mul, norm_two_pow]
          have hb := ih (n - k) (by omega)
          have hkey := key_exponent (m := M) (k := k + 1) (by omega) (by omega)
          rw [show M - (k + 1) = n - k by omega] at hkey
          calc (1 / 2 : ℚ) ^ ((k + 1) ^ 2) * padicNorm 2 (rec dB (n - k))
              ≤ (1 / 2) ^ ((k + 1) ^ 2) * (1 / 2) ^ (n - k + s2 (n - k)) := by
                gcongr
            _ = (1 / 2) ^ ((k + 1) ^ 2 + (n - k) + s2 (n - k)) := by
                rw [← pow_add, add_assoc]
            _ ≤ (1 / 2) ^ (M + s2 M + padicValNat 2 M) := half_pow_le hkey
      rw [rec, padicNorm.div]
      have hcast : ((n : ℚ) + 1) = ((M : ℕ) : ℚ) := by rw [hM]; push_cast; ring
      rw [hcast, norm_natCast (by omega)]
      rw [div_le_iff₀ (by positivity), ← pow_add]
      exact hS

/-- `|a(n)|₂ = (1/2)^(s₂ n)`. -/
lemma norm_a (n : ℕ) : padicNorm 2 (a n) = (1 / 2) ^ s2 n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [a, s2]
  have hlast : padicNorm 2 (rec dE n * rec dB (n - n)) = (1 / 2) ^ s2 n := by
    rw [Nat.sub_self, padicNorm.mul, norm_rec_dE]
    simp [rec]
  have hrest : padicNorm 2 (∑ k ∈ Finset.range n, rec dE k * rec dB (n - k))
      < (1 / 2) ^ s2 n := by
    refine padicNorm.sum_lt ⟨0, Finset.mem_range.2 hn⟩ fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [padicNorm.mul, norm_rec_dE]
    have hb := norm_rec_dB_le (n - k)
    have hsub := s2_le_add hk.le
    calc (1 / 2 : ℚ) ^ s2 k * padicNorm 2 (rec dB (n - k))
        ≤ (1 / 2) ^ s2 k * (1 / 2) ^ (n - k + s2 (n - k)) := by gcongr
      _ = (1 / 2) ^ (s2 k + (n - k) + s2 (n - k)) := by rw [← pow_add, add_assoc]
      _ ≤ (1 / 2) ^ (s2 n + 1) := half_pow_le (by omega)
      _ < (1 / 2) ^ s2 n := pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) (by omega)
  rw [a_eq_sum, Finset.sum_range_succ, padicNorm.add_eq_max_of_ne (by rw [hlast]; exact hrest.ne),
    hlast, max_eq_right hrest.le]

/-! ## The conjecture -/

/-- **Hanna's conjecture (A155200, Paul D. Hanna, Sep 01 2009), proved.**

Verbatim: "Conjecture: highest exponent of 2 dividing a(n) = A000120(n) = number of 1's in
binary expansion of n, so that a(n)/2^A000120(n) is odd for n >= 0."

For every `n`, `a n ≠ 0` and its 2-adic valuation is the binary digit sum of `n`. -/
theorem a155200_padicValRat (n : ℕ) :
    a n ≠ 0 ∧ padicValRat 2 (a n) = ((Nat.digits 2 n).sum : ℤ) := by
  have hn := norm_a n
  have hne : a n ≠ 0 := by
    intro h
    rw [h, padicNorm.zero] at hn
    exact (pow_ne_zero _ (by norm_num : (1 : ℚ) / 2 ≠ 0)) hn.symm
  refine ⟨hne, ?_⟩
  have hz : (2 : ℚ) ^ (-padicValRat 2 (a n)) = (2 : ℚ) ^ (-((s2 n : ℕ) : ℤ)) := by
    have he := padicNorm.eq_zpow_of_nonzero (p := 2) hne
    rw [Nat.cast_ofNat] at he
    rw [← he, hn, zpow_neg, zpow_natCast, one_div, inv_pow]
  have hinj := zpow_right_injective₀ (a := (2 : ℚ)) (by norm_num) (by norm_num)
  have h : padicValRat 2 (a n) = ((s2 n : ℕ) : ℤ) := neg_inj.1 (hinj hz)
  rw [h, s2]

end Candidates.A155200ExpSumEquivalently
