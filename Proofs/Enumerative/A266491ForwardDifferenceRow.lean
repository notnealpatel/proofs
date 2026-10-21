/-
# A266491 — Curtz: divisibility of the forward-difference rows of `n * A130658(n)`

## OEIS source (retrieved with `oeis show A266491` and https://oeis.org/A266491/internal, 2026-10-21)

```
NAME:     a(n) = n*A130658(n).
TERMS:    0,1,4,6,4,5,12,14,8,9,20,22,12,13,28,30,16,17,36,38,20,21,44,46,24,...
AUTHOR:   _Paul Curtz_, Dec 30 2015
FORMULA:  a(n) = n*(3 - (-1)^((n-1)*n/2))/2.
COMMENT:  Successive differences:
          r(0):    0,   1,    4,    6,   4,    5,   12,   14, ...
          r(1):    1,   3,    2,   -2,   1,    7,    2,   -6, ...
          ...
          r(10): 160, -16, -192,   48, 224,  -80, -256,  112, ...
          Let b(n) = 1, 1, 1, 1, 2, 2, 4, 4, 8, 8, 16, 16, ..., with n>=0, which
          is formed from the terms of A011782 repeated twice.
          Conjecture: all terms of the row r(i) are divisible by b(i).
          Conjecture: the terms of the first column divided by b(n) provide
          0, 1, 2, -3, 0, 5, -6, 7, 0, -9, 10, -11, ..., the absolute values of
          which are listed in A190621.
```

The two conjecture lines carry no separate attribution; they belong to the
entry by Paul Curtz (Dec 30 2015).

## Status

Triage: open (no proof in the entry or the literature as far as the triage
could tell).  Both conjectures are proved below (`b_dvd_row`,
`abs_row_zero`), via the Gaussian-integer identity
`2 a(n) = Re(3 n + (i - 1) n i^n)` and the closed form
`Δ^(k+2) (c n + w n z^n)(m) = w z^m (z-1)^(k+1) (m (z-1) + (k+2) z)`.
Computational re-validation (Python, 2026-10-21): both claims hold for rows
`0..398` over the first `400` terms.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A266491ForwardDifferenceRow

/-! ## Definition layer -/

/-- A266491, by the entry formula `a(n) = n*(3 - (-1)^((n-1)*n/2))/2`.
The inner `n * (n - 1) / 2` is the triangular number (exact in `ℕ`, and
`0` at `n = 0`); the outer `/ 2` in `ℤ` is exact because `3 - (±1) ∈ {2, 4}`. -/
def a (n : ℕ) : ℤ := n * (3 - (-1) ^ (n * (n - 1) / 2)) / 2

/-- The row `r(i)` of the entry: the `i`-th iterated forward difference of `a`
(`r(0) = a`, `r(i+1)(n) = r(i)(n+1) - r(i)(n)`), via Mathlib's `fwdDiff`. -/
def row (i : ℕ) : ℕ → ℤ := (fwdDiff 1)^[i] a

/-- A011782: coefficients of `(1-x)/(1-2x)`, i.e. `1, 1, 2, 4, 8, ...`. -/
def a011782 (k : ℕ) : ℕ := if k = 0 then 1 else 2 ^ (k - 1)

/-- The entry's `b(n)`: the terms of A011782 repeated twice,
`1, 1, 1, 1, 2, 2, 4, 4, 8, 8, ...`. -/
def b (i : ℕ) : ℕ := a011782 (i / 2)

/-- A190621: `a(n) = n` if `n` is not divisible by `4`, otherwise `0`. -/
def a190621 (n : ℕ) : ℕ := if 4 ∣ n then 0 else n

example : (List.range 16).map a = [0, 1, 4, 6, 4, 5, 12, 14, 8, 9, 20, 22, 12, 13, 28, 30] := by
  decide

example : (List.range 8).map (row 1) = [1, 3, 2, -2, 1, 7, 2, -6] := by decide

example : (List.range 8).map (row 2) = [2, -1, -4, 3, 6, -5, -8, 7] := by decide

example : (List.range 8).map (row 3) = [-3, -3, 7, 3, -11, -3, 15, 3] := by decide

example : (List.range 8).map (row 9) = [-72, 88, 72, -120, -72, 152, 72, -184] := by decide

example : (List.range 8).map (row 10) = [160, -16, -192, 48, 224, -80, -256, 112] := by decide

example : (List.range 9).map a011782 = [1, 1, 2, 4, 8, 16, 32, 64, 128] := by decide

example : (List.range 12).map b = [1, 1, 1, 1, 2, 2, 4, 4, 8, 8, 16, 16] := by decide

example : (List.range 12).map a190621 = [0, 1, 2, 3, 0, 5, 6, 7, 0, 9, 10, 11] := by decide

/-- The entry's first column divided by `b`: `0, 1, 2, -3, 0, 5, -6, 7, 0, -9, 10, -11`. -/
example : (List.range 12).map (fun i => row i 0 / b i) = [0, 1, 2, -3, 0, 5, -6, 7, 0, -9, 10, -11] := by
  decide

/-! ## Gaussian-integer model -/

/-- The Gaussian integer `i = √-1` in `ℤ√(-1)`. -/
def gi : ℤ√(-1) := ⟨0, 1⟩

/-- `i ^ 4 = 1`. -/
theorem gi_pow_four : gi ^ 4 = 1 := by decide

/-- The triangular exponent shifts by an even amount under `n ↦ n + 4`. -/
theorem tri_add_four (n : ℕ) :
    (n + 4) * (n + 4 - 1) / 2 = n * (n - 1) / 2 + 2 * (2 * n + 3) := by
  have h : (n + 4) * (n + 4 - 1) = n * (n - 1) + 2 * (2 * (2 * n + 3)) := by
    cases n with
    | zero => rfl
    | succ n =>
      rw [show n + 1 + 4 - 1 = n + 4 by omega, Nat.add_sub_cancel]
      ring
  rw [h, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]

/-- `(-1)^(n(n-1)/2) = Re((1 - i) i^n)`. -/
theorem sign_eq_re (n : ℕ) : (-1 : ℤ) ^ (n * (n - 1) / 2) = ((1 - gi) * gi ^ n).re := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases lt_or_ge n 4 with hn | hn
    · interval_cases n <;> decide
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      rw [tri_add_four, pow_add, pow_mul, neg_one_sq, one_pow, mul_one, ih m (by omega),
        pow_add, gi_pow_four, mul_one]

/-- Closed form, in any commutative ring, of the `(k+2)`-th forward difference of
`n ↦ c n + w n z^n`: it equals `w z^m (z-1)^(k+1) (m (z-1) + (k+2) z)` at `m`. -/
theorem fwdDiff_iter_closed {R : Type*} [CommRing R] (c w z : R) (k m : ℕ) :
    (fwdDiff 1)^[k + 2] (fun n : ℕ => c * n + w * n * z ^ n) m =
      w * z ^ m * (z - 1) ^ (k + 1) * (m * (z - 1) + (k + 2) * z) := by
  induction k generalizing m with
  | zero =>
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, fwdDiff]
    push_cast
    ring
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    simp only [fwdDiff, ih]
    push_cast
    ring

/-- The Gaussian lift `G(n) = 3 n + (i - 1) n i^n`, whose real part is `2 a(n)`. -/
def G (n : ℕ) : ℤ√(-1) := 3 * n + (gi - 1) * n * gi ^ n

/-- `2 a(n) = Re(G(n))`. -/
theorem two_mul_a (n : ℕ) : 2 * a n = (G n).re := by
  have hG : G n = ((3 * n : ℤ) : ℤ√(-1)) - ((n : ℤ) : ℤ√(-1)) * ((1 - gi) * gi ^ n) := by
    unfold G
    push_cast
    ring
  have hs := sign_eq_re n
  have hdvd : (2 : ℤ) ∣ n * (3 - (-1) ^ (n * (n - 1) / 2)) := by
    rcases neg_one_pow_eq_or ℤ (n * (n - 1) / 2) with h | h
    · rw [h]
      exact Dvd.dvd.mul_left ⟨1, by norm_num⟩ _
    · rw [h]
      exact Dvd.dvd.mul_left ⟨2, by norm_num⟩ _
  rw [hG, Zsqrtd.re_sub, Zsqrtd.re_intCast, Zsqrtd.re_smul, ← hs, a, Int.mul_ediv_cancel' hdvd]
  ring

/-- `2 r(k)(n) = Re(Δ^k G (n))`: the real part commutes with forward differences. -/
theorem two_mul_row (k n : ℕ) : 2 * row k n = ((fwdDiff 1)^[k] G n).re := by
  induction k generalizing n with
  | zero => exact two_mul_a n
  | succ k ih =>
    simp only [row, Function.iterate_succ_apply', fwdDiff] at ih ⊢
    rw [Zsqrtd.re_sub, ← ih, ← ih]
    ring

/-- `Δ^(k+2) G (m) = i^m (i-1)^(k+2) (m (i-1) + (k+2) i)`. -/
theorem G_iter (k m : ℕ) : (fwdDiff 1)^[k + 2] G m =
    gi ^ m * (gi - 1) ^ (k + 2) * (m * (gi - 1) + (k + 2) * gi) := by
  have h := fwdDiff_iter_closed (3 : ℤ√(-1)) (gi - 1) gi k m
  have hfun : G = fun n : ℕ => (3 : ℤ√(-1)) * n + (gi - 1) * n * gi ^ n := rfl
  rw [hfun, h]
  ring

/-- `(i - 1)^2 = 2 · (-i)`. -/
theorem gi_sub_one_sq : (gi - 1) ^ 2 = ((2 : ℤ) : ℤ√(-1)) * (-gi) := by decide

/-- Load-bearing step: `2^((k+2)/2)` divides `2 r(k+2)(m)`, because
`(i-1)^(k+2)` is divisible by `2^((k+2)/2)` in `ℤ[i]`. -/
theorem two_pow_dvd_two_mul_row (k m : ℕ) : (2 : ℤ) ^ ((k + 2) / 2) ∣ 2 * row (k + 2) m := by
  rw [two_mul_row, G_iter]
  have hpow : (gi - 1) ^ (k + 2) =
      ((2 ^ ((k + 2) / 2) : ℤ) : ℤ√(-1)) *
        ((-gi) ^ ((k + 2) / 2) * (gi - 1) ^ ((k + 2) % 2)) := by
    conv_lhs => rw [← Nat.div_add_mod (k + 2) 2, pow_add, pow_mul, gi_sub_one_sq, mul_pow]
    push_cast
    ring
  have hd : ((2 ^ ((k + 2) / 2) : ℤ) : ℤ√(-1)) ∣
      gi ^ m * (gi - 1) ^ (k + 2) * (m * (gi - 1) + (k + 2) * gi) := by
    rw [hpow]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) _
  exact ((Zsqrtd.intCast_dvd _ _).1 hd).1

/-- `b(k+2) = 2^(k/2)`. -/
theorem b_add_two (k : ℕ) : b (k + 2) = 2 ^ (k / 2) := by
  rw [b, a011782, if_neg (by omega), show (k + 2) / 2 - 1 = k / 2 by omega]

/-- The closed form `b(i) = 2^((i-2)/2)` (truncated subtraction gives `b(0) = b(1) = 1`). -/
theorem b_eq_two_pow (i : ℕ) : b i = 2 ^ ((i - 2) / 2) := by
  match i with
  | 0 => rfl
  | 1 => rfl
  | k + 2 => rw [b_add_two, Nat.add_sub_cancel]

/-! ## The conjectures -/

/-- **First conjecture of A266491 (Paul Curtz, entry of Dec 30 2015).**

Verbatim: "Conjecture: all terms of the row r(i) are divisible by b(i)."
Here `row i = Δ^i a` and `b = 1, 1, 1, 1, 2, 2, 4, 4, ...` (A011782 repeated
twice).  Proved for every row `i` and every position `n`. -/
theorem b_dvd_row (i n : ℕ) : (b i : ℤ) ∣ row i n := by
  match i with
  | 0 => simp [b, a011782]
  | 1 => simp [b, a011782]
  | k + 2 =>
    have h := two_pow_dvd_two_mul_row k n
    rw [show (k + 2) / 2 = k / 2 + 1 by omega, pow_succ, mul_comm] at h
    rw [b_add_two]
    push_cast
    exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).1 h

/-- `e(K) = Re((i - 1)^K · i)`, the first-column factor. -/
def e (K : ℕ) : ℤ := ((gi - 1) ^ K * gi).re

/-- `(i - 1)^8 = 16`. -/
theorem gi_sub_one_pow_eight : (gi - 1) ^ 8 = ((16 : ℤ) : ℤ√(-1)) := by decide

/-- `|e(r)|` for `r < 8`, by computation. -/
theorem abs_e_lt_eight : ∀ r < 8, |e r| = if 4 ∣ r then 0 else 2 ^ (r / 2) := by decide

/-- `|Re((i - 1)^K · i)| = 0` if `4 ∣ K`, and `2^(K/2)` otherwise. -/
theorem abs_e (K : ℕ) : |e K| = if 4 ∣ K then 0 else 2 ^ (K / 2) := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 8 ∧ K = 8 * q + r :=
    ⟨K / 8, K % 8, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod K 8).symm⟩
  have he : e (8 * q + r) = 16 ^ q * e r := by
    rw [e, e, pow_add, pow_mul, gi_sub_one_pow_eight, ← Int.cast_pow, mul_assoc, Zsqrtd.re_smul]
  rw [he, abs_mul, abs_e_lt_eight r hr, abs_pow, abs_of_pos (by norm_num : (0 : ℤ) < 16)]
  have hdiv : (4 ∣ 8 * q + r) ↔ 4 ∣ r := by omega
  rw [if_congr hdiv rfl rfl, show (8 * q + r) / 2 = 4 * q + r / 2 by omega, pow_add, pow_mul]
  split_ifs <;> norm_num

/-- `2 r(k+2)(0) = (k+2) · e(k+2)`. -/
theorem two_mul_row_zero (k : ℕ) : 2 * row (k + 2) 0 = ((k + 2 : ℕ) : ℤ) * e (k + 2) := by
  rw [two_mul_row, G_iter, e, ← Zsqrtd.re_smul]
  congr 1
  push_cast
  ring

/-- **Second conjecture of A266491 (Paul Curtz, entry of Dec 30 2015), product form.**

Verbatim: "Conjecture: the terms of the first column divided by b(n) provide
0, 1, 2, -3, 0, 5, -6, 7, 0, -9, 10, -11, ..., the absolute values of which are
listed in A190621."  Stated without division: `|r(i)(0)| = b(i) · A190621(i)`
for every `i`; the division form is `abs_row_zero_div`. -/
theorem abs_row_zero (i : ℕ) : |row i 0| = (b i : ℤ) * a190621 i := by
  match i with
  | 0 => decide
  | 1 => decide
  | k + 2 =>
    have h2 : 2 * |row (k + 2) 0| = ((k + 2 : ℕ) : ℤ) * |e (k + 2)| := by
      rw [← abs_two, ← abs_mul, two_mul_row_zero, abs_mul, Nat.abs_cast]
    rw [abs_e] at h2
    rw [b_add_two, a190621]
    split_ifs at h2 ⊢ with h4
    · push_cast
      linarith
    · rw [show (k + 2) / 2 = k / 2 + 1 by omega, pow_succ] at h2
      push_cast at h2 ⊢
      linarith

/-- **Second conjecture of A266491, division form.** The first column `r(i)(0)`
divided by `b(i)` (an exact division by `b_dvd_row`) has absolute value
`A190621(i)`. -/
theorem abs_row_zero_div (i : ℕ) : |row i 0 / (b i : ℤ)| = a190621 i := by
  obtain ⟨c, hc⟩ := b_dvd_row i 0
  have hb : (0 : ℤ) < b i := by
    rw [b_eq_two_pow]
    positivity
  have h := abs_row_zero i
  rw [hc, abs_mul, abs_of_pos hb] at h
  rw [hc, Int.mul_ediv_cancel_left _ hb.ne']
  exact mul_left_cancel₀ hb.ne' h

end Candidates.A266491ForwardDifferenceRow
