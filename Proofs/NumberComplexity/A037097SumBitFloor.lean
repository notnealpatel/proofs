/-
# A037097 — Karttunen: the bit columns of `3^k` are divisible by a power of `x + 1`

Antti Karttunen's conjecture in OEIS A037097, corrected by Qiyuan Gu
(2026), and its A037096 companion. A037097 uses a window of length
`2^(n-1)` (offset 2), A037096 a window of length `2^n` (offset 0),
of the bits `floor(3^k/2^n) mod 2`. Both divisibility exponents are exact.

## Argument

1. `3^(2^(j+1)) = 1 + 2^(j+3) * odd`, by squaring.  So for `n = m + 3` and
   `h = 2^(n-2)`, `3^(k+h) ≡ 3^k + 2^n (mod 2^(n+1))` (as `3^k` is odd), hence
   `bit_n(3^(k+h)) = 1 - bit_n(3^k)`: the column complements itself after `h`.
2. With `s_k = bit_n(3^k)`, `Q = Σ_{k<h} s_k x^k`, `U = Σ_{k<h} x^k`:
   `P_n = Q + x^h (Q + U) = U * ((x+1) Q + x^h)`, using `U (x+1) = x^h + 1`.
3. Over GF(2), `U (x+1) = x^h + 1 = (x+1)^h` (Frobenius, `h` a power of 2), so
   `U = (x+1)^(h-1)`.  The cofactor `(x+1) Q + x^h` takes the value `1` at
   `x = 1`, so the exponent `h - 1` is exact.
4. Applying step 1 twice, the column has period `2h`, so A037096's polynomial
   is `(1 + x^(2h)) P_n = (x+1)^(2h) P_n`, with exact exponent `3h - 1`.
-/
import Mathlib

set_option autoImplicit false

open Polynomial Finset

namespace Candidates.A037097SumBitFloor

/-! ## Definitions (mirrors the entry's PROGRAM and FORMULA lines) -/

/-- The entry's `bit_n(m) = floor(m / 2^n) mod 2`: bit `n` of `m`. -/
def bitN (n m : ℕ) : ℕ := m / 2 ^ n % 2

/-- `colNat n L = Σ_{k<L} bit_n(3^k) * 2^k`, the integer whose binary digit `k`
is bit `n` of `3^k`, for `k < L`. -/
def colNat (n L : ℕ) : ℕ := ∑ k ∈ range L, bitN n (3 ^ k) * 2 ^ k

/-- A037097 (offset 2): `a(n) = Σ_{k=0}^{2^(n-1)-1} bit_n(3^k) * 2^k`. -/
def a037097 (n : ℕ) : ℕ := colNat n (2 ^ (n - 1))

/-- A037096 (offset 0): `a(n) = Σ_{k=0}^{2^n-1} bit_n(3^k) * 2^k`. -/
def a037096 (n : ℕ) : ℕ := colNat n (2 ^ n)

/-- A natural number "considered as a GF(2)[X]-polynomial": binary digit `i`
of `m` becomes the coefficient of `X^i`.  (Every digit of index `≥ m` is zero
since `m < 2^m`, so the range `i < m` loses nothing; see `coeff_gf2OfNat`.) -/
noncomputable def gf2OfNat (m : ℕ) : (ZMod 2)[X] :=
  ∑ i ∈ range m, C ((m / 2 ^ i % 2 : ℕ) : ZMod 2) * X ^ i

/-- The bit-column polynomial `Σ_{k<L} bit_n(3^k) x^k` over GF(2).  For
`L = 2^(n-1)` this is the polynomial `P_n` of A037097, for `L = 2^n` the
polynomial of A037096 (`gf2OfNat_colNat`). -/
noncomputable def colPoly (n L : ℕ) : (ZMod 2)[X] :=
  ∑ k ∈ range L, C ((bitN n (3 ^ k) : ℕ) : ZMod 2) * X ^ k

/-! ## Examples against the DATA lines -/

-- A037097 DATA: 0, 12, 120, 57120, 93321840, 10431955353116229600 (n = 2..7).
example : a037097 2 = 0 := by decide
example : a037097 3 = 12 := by decide
example : a037097 4 = 120 := by decide
example : a037097 5 = 57120 := by decide
example : a037097 6 = 93321840 := by decide
example : a037097 7 = 10431955353116229600 := by decide
-- A037096 DATA: 1, 2, 0, 204, 30840, 3743473440 (n = 0..5).
example : a037096 0 = 1 := by decide
example : a037096 1 = 2 := by decide
example : a037096 2 = 0 := by decide
example : a037096 3 = 204 := by decide
example : a037096 4 = 30840 := by decide
example : a037096 5 = 3743473440 := by decide

/-! ## Reading an integer as a GF(2) polynomial -/

/-- A sum of binary digits `b k ∈ {0,1}` weighted by `2^k`, `k < L`, is
below `2^L`. -/
theorem binSum_lt (b : ℕ → ℕ) (hb : ∀ k, b k < 2) (L : ℕ) :
    ∑ k ∈ range L, b k * 2 ^ k < 2 ^ L := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [sum_range_succ, pow_succ]
    have hbL : b L ≤ 1 := Nat.lt_succ_iff.mp (hb L)
    have hmul : b L * 2 ^ L ≤ 2 ^ L := by
      calc b L * 2 ^ L ≤ 1 * 2 ^ L := Nat.mul_le_mul_right _ hbL
        _ = 2 ^ L := one_mul _
    omega

/-- Digit extraction: binary digit `i` of `Σ_{k<L} b k * 2^k` (with every
`b k ∈ {0,1}`) is `b i` for `i < L` and `0` otherwise. -/
theorem binSum_digit (b : ℕ → ℕ) (hb : ∀ k, b k < 2) (L i : ℕ) :
    (∑ k ∈ range L, b k * 2 ^ k) / 2 ^ i % 2 = if i < L then b i else 0 := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [sum_range_succ]
    rcases lt_trichotomy i L with hiL | rfl | hLi
    · have hpow : 2 ^ L = 2 ^ i * 2 ^ (L - i - 1) * 2 := by
        rw [← pow_add, ← pow_succ]; congr 1; omega
      rw [hpow, show b L * (2 ^ i * 2 ^ (L - i - 1) * 2) = (b L * 2 ^ (L - i - 1) * 2) * 2 ^ i by
          ring, Nat.add_mul_div_right _ _ (by positivity), Nat.add_mul_mod_self_right, ih,
        if_pos hiL, if_pos (Nat.lt_succ_of_lt hiL)]
    · rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt (binSum_lt b hb i), zero_add,
        Nat.mod_eq_of_lt (hb i), if_pos (Nat.lt_succ_self i)]
    · have hlt : ∑ k ∈ range L, b k * 2 ^ k + b L * 2 ^ L < 2 ^ i := by
        have h1 := binSum_lt b hb (L + 1)
        rw [sum_range_succ] at h1
        exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) hLi)
      rw [Nat.div_eq_of_lt hlt, if_neg (by omega)]

/-- The coefficient of `X^i` in `gf2OfNat m` is binary digit `i` of `m`, for
every `i`. -/
theorem coeff_gf2OfNat (m i : ℕ) : (gf2OfNat m).coeff i = ((m / 2 ^ i % 2 : ℕ) : ZMod 2) := by
  rw [gf2OfNat, finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  rw [sum_ite_eq]
  split_ifs with hi
  · rfl
  · have hlt : m < 2 ^ i :=
      lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (by simpa using hi))
    rw [Nat.div_eq_of_lt hlt, Nat.zero_mod, Nat.cast_zero]

/-- Bridge: the integer `colNat n L`, read as a GF(2) polynomial, is the
bit-column polynomial `Σ_{k<L} bit_n(3^k) x^k`. -/
theorem gf2OfNat_colNat (n L : ℕ) : gf2OfNat (colNat n L) = colPoly n L := by
  ext i
  have hb : ∀ k, bitN n (3 ^ k) < 2 := fun k => Nat.mod_lt _ (by norm_num)
  rw [coeff_gf2OfNat, colNat, binSum_digit _ hb, colPoly, finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  rw [sum_ite_eq]
  simp only [mem_range]
  split_ifs <;> simp

-- Examples for the reading: `12 = 0b1100` is the polynomial `x^2 + x^3`.
example : gf2OfNat 12 = X ^ 2 + X ^ 3 := by
  ext i
  rw [coeff_gf2OfNat, coeff_add, coeff_X_pow, coeff_X_pow]
  rcases i with _ | _ | _ | _ | i
  · rfl
  · rfl
  · rfl
  · rfl
  · have hlt : 12 < 2 ^ (i + 4) := by
      rw [pow_add]
      have hpos : 1 ≤ 2 ^ i := Nat.one_le_two_pow
      omega
    rw [Nat.div_eq_of_lt hlt, if_neg (by omega), if_neg (by omega)]
    rfl

/-! ## The column of bit `n` complements itself after half a period -/

/-- `3^(2^(j+1)) = 1 + 2^(j+3) * (odd)` for every `j`. -/
theorem three_pow_two_pow (j : ℕ) : ∃ t : ℕ, 3 ^ 2 ^ (j + 1) = 1 + 2 ^ (j + 3) * (2 * t + 1) := by
  induction j with
  | zero => exact ⟨0, by norm_num⟩
  | succ j ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨t + 2 ^ (j + 1) * (2 * t + 1) ^ 2, ?_⟩
    rw [pow_succ 2 (j + 1), pow_mul, ht]
    ring

/-- Half-period complementation: for `n = m + 3` and `h = 2^(n-2) = 2^(m+1)`,
`bit_n(3^(k+h)) = 1 - bit_n(3^k)`, i.e. `= bit_n(3^k) + 1` in GF(2). -/
theorem bitN_add_half (m k : ℕ) :
    ((bitN (m + 3) (3 ^ (k + 2 ^ (m + 1))) : ℕ) : ZMod 2) =
      ((bitN (m + 3) (3 ^ k) : ℕ) : ZMod 2) + 1 := by
  obtain ⟨t, ht⟩ := three_pow_two_pow m
  obtain ⟨u, hu⟩ : Odd (3 ^ k) := Odd.pow (by decide)
  have hsplit : 3 ^ (k + 2 ^ (m + 1)) = 3 ^ k + (1 + 2 * (u + 3 ^ k * t)) * 2 ^ (m + 3) := by
    rw [pow_add, ht, hu]; ring
  unfold bitN
  rw [hsplit, Nat.add_mul_div_right _ _ (by positivity)]
  push_cast [ZMod.natCast_mod]
  have h2 : (2 : ZMod 2) = 0 := rfl
  rw [h2]; ring

/-! ## Polynomial identities over GF(2) -/

/-- `(1 + x + ⋯ + x^(h-1)) (x + 1) = x^h + 1` over GF(2). -/
theorem geom_mul_X_add_one (h : ℕ) :
    (∑ i ∈ range h, (X : (ZMod 2)[X]) ^ i) * (X + 1) = X ^ h + 1 := by
  have hg := geom_sum_mul (X : (ZMod 2)[X]) h
  rwa [CharTwo.sub_eq_add, CharTwo.sub_eq_add] at hg

/-- Over GF(2), `1 + x + ⋯ + x^(2^e - 1) = (x + 1)^(2^e - 1)`. -/
theorem geom_two_pow (e : ℕ) :
    (∑ i ∈ range (2 ^ e), (X : (ZMod 2)[X]) ^ i) = (X + 1) ^ (2 ^ e - 1) := by
  have hX : (X + 1 : (ZMod 2)[X]) ≠ 0 := X_add_C_ne_zero 1
  apply mul_right_cancel₀ hX
  rw [geom_mul_X_add_one, pow_sub_one_mul (by positivity), add_pow_char_pow, one_pow]

/-- If a GF(2) sequence complements itself after `h` steps, then its window of
length `2h` factors as `(Σ_{i<h} x^i) * ((x + 1) Q + x^h)`, where `Q` is the
window of length `h`. -/
theorem sum_halves (s : ℕ → ZMod 2) (h : ℕ) (hs : ∀ k, s (k + h) = s k + 1) :
    ∑ k ∈ range (h + h), C (s k) * X ^ k =
      (∑ i ∈ range h, (X : (ZMod 2)[X]) ^ i) *
        ((X + 1) * ∑ k ∈ range h, C (s k) * X ^ k + X ^ h) := by
  set Q := ∑ k ∈ range h, C (s k) * X ^ k with hQ
  set U := ∑ i ∈ range h, (X : (ZMod 2)[X]) ^ i with hUdef
  have hU := geom_mul_X_add_one h
  rw [← hUdef] at hU
  have hsecond : ∑ k ∈ range h, C (s (h + k)) * X ^ (h + k) = X ^ h * (Q + U) := by
    rw [hQ, hUdef, ← sum_add_distrib, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [add_comm h k, hs k, pow_add, C_add, C_1]
    ring
  rw [sum_range_add, hsecond]
  linear_combination (-Q) * hU

/-- The cofactor `(x + 1) Q + x^h` for `n = m + 3`, `h = 2^(m+1)`, where `Q` is
the first half-period of the bit-`n` column. -/
noncomputable def cofactor (m : ℕ) : (ZMod 2)[X] :=
  (X + 1) * colPoly (m + 3) (2 ^ (m + 1)) + X ^ 2 ^ (m + 1)

/-- The cofactor takes the value `1` at `x = 1`, so `x + 1` does not divide it. -/
theorem eval_one_cofactor (m : ℕ) : (cofactor m).eval 1 = 1 := by
  have h2 : (1 + 1 : ZMod 2) = 0 := rfl
  simp [cofactor, h2]

/-- Factorization of `P_n` for `n = m + 3`:
`P_n = (x + 1)^(2^(n-2) - 1) * cofactor`. -/
theorem colPoly_half_factor (m : ℕ) :
    colPoly (m + 3) (2 ^ (m + 2)) = (X + 1) ^ (2 ^ (m + 1) - 1) * cofactor m := by
  have hlen : 2 ^ (m + 2) = 2 ^ (m + 1) + 2 ^ (m + 1) := by ring
  rw [colPoly, hlen, sum_halves _ _ (bitN_add_half m), geom_two_pow, cofactor, colPoly]

/-- Factorization of the A037096 polynomial for `n = m + 3`: the column has
period `2^(n-1)`, so it equals `(x + 1)^(2^(n-1)) P_n
= (x + 1)^(3 * 2^(n-2) - 1) * cofactor`. -/
theorem colPoly_full_factor (m : ℕ) :
    colPoly (m + 3) (2 ^ (m + 3)) = (X + 1) ^ (3 * 2 ^ (m + 1) - 1) * cofactor m := by
  have hlen : 2 ^ (m + 3) = 2 ^ (m + 2) + 2 ^ (m + 2) := by ring
  have hper : ∀ k, ((bitN (m + 3) (3 ^ (2 ^ (m + 2) + k)) : ℕ) : ZMod 2) =
      ((bitN (m + 3) (3 ^ k) : ℕ) : ZMod 2) := by
    intro k
    have h2 : (1 + 1 : ZMod 2) = 0 := rfl
    have hk : 2 ^ (m + 2) + k = k + 2 ^ (m + 1) + 2 ^ (m + 1) := by ring
    rw [hk, bitN_add_half, bitN_add_half, add_assoc, h2, add_zero]
  have hsplit : colPoly (m + 3) (2 ^ (m + 3)) =
      (X + 1) ^ (2 ^ (m + 2)) * colPoly (m + 3) (2 ^ (m + 2)) := by
    rw [colPoly, hlen, sum_range_add, colPoly, add_pow_char_pow, one_pow, add_mul, one_mul,
      mul_sum, add_comm]
    congr 1
    refine sum_congr rfl fun k _ => ?_
    rw [hper k, pow_add]
    ring
  rw [hsplit, colPoly_half_factor, ← mul_assoc, ← pow_add]
  congr 2
  have hone : 1 ≤ 2 ^ (m + 1) := Nat.one_le_two_pow
  rw [pow_succ 2 (m + 1)]
  omega

/-- If `R(1) = 1` then `(x + 1)^(e+1)` does not divide `(x + 1)^e * R` over GF(2). -/
theorem not_dvd_of_eval_one (e : ℕ) (R : (ZMod 2)[X]) (hR : R.eval 1 = 1) :
    ¬ (X + 1 : (ZMod 2)[X]) ^ (e + 1) ∣ (X + 1) ^ e * R := by
  intro hdvd
  have hX : (X + 1 : (ZMod 2)[X]) ^ e ≠ 0 := pow_ne_zero _ (X_add_C_ne_zero 1)
  rw [pow_succ, mul_dvd_mul_iff_left hX] at hdvd
  have hev := eval_dvd (x := (1 : ZMod 2)) hdvd
  have h2 : (1 + 1 : ZMod 2) = 0 := rfl
  rw [eval_add, eval_X, eval_one, h2, zero_dvd_iff, hR] at hev
  exact one_ne_zero hev

/-! ## The column-polynomial forms -/

/-- For `n ≥ 3`, `(x + 1)^(2^(n-2) - 1)` divides
`P_n = Σ_{k<2^(n-1)} bit_n(3^k) x^k` in GF(2)[x]. -/
theorem colPoly_half_dvd (n : ℕ) (hn : 3 ≤ n) :
    (X + 1 : (ZMod 2)[X]) ^ (2 ^ (n - 2) - 1) ∣ colPoly n (2 ^ (n - 1)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rw [show m + 3 - 2 = m + 1 by omega, show m + 3 - 1 = m + 2 by omega, colPoly_half_factor]
  exact dvd_mul_right _ _

/-- For `n ≥ 3`, `(x + 1)^(2^(n-2))` does not divide `P_n`. -/
theorem colPoly_half_not_dvd (n : ℕ) (hn : 3 ≤ n) :
    ¬ (X + 1 : (ZMod 2)[X]) ^ (2 ^ (n - 2)) ∣ colPoly n (2 ^ (n - 1)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rw [show m + 3 - 2 = m + 1 by omega, show m + 3 - 1 = m + 2 by omega, colPoly_half_factor]
  have h1 : 2 ^ (m + 1) = 2 ^ (m + 1) - 1 + 1 := (Nat.sub_add_cancel Nat.one_le_two_pow).symm
  have hnd := not_dvd_of_eval_one (2 ^ (m + 1) - 1) _ (eval_one_cofactor m)
  rwa [← h1] at hnd

/-- For `n ≥ 3`, `(x + 1)^(3 * 2^(n-2) - 1)` divides
`Q_n = Σ_{k<2^n} bit_n(3^k) x^k` in GF(2)[x]. -/
theorem colPoly_full_dvd (n : ℕ) (hn : 3 ≤ n) :
    (X + 1 : (ZMod 2)[X]) ^ (3 * 2 ^ (n - 2) - 1) ∣ colPoly n (2 ^ n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rw [show m + 3 - 2 = m + 1 by omega, colPoly_full_factor]
  exact dvd_mul_right _ _

/-- For `n ≥ 3`, `(x + 1)^(3 * 2^(n-2))` does not divide `Q_n`. -/
theorem colPoly_full_not_dvd (n : ℕ) (hn : 3 ≤ n) :
    ¬ (X + 1 : (ZMod 2)[X]) ^ (3 * 2 ^ (n - 2)) ∣ colPoly n (2 ^ n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rw [show m + 3 - 2 = m + 1 by omega, colPoly_full_factor]
  have h1 : 3 * 2 ^ (m + 1) = 3 * 2 ^ (m + 1) - 1 + 1 := by
    have hone : 1 ≤ 2 ^ (m + 1) := Nat.one_le_two_pow
    omega
  have hnd := not_dvd_of_eval_one (3 * 2 ^ (m + 1) - 1) _ (eval_one_cofactor m)
  rwa [← h1] at hnd

/-! ## The conjectures, stated on the OEIS integers -/

/-- Karttunen's A037097 conjecture, corrected by Qiyuan Gu (2026): for `n ≥ 3`,
A037097(n), read as a GF(2) polynomial, is divisible by
`(x+1)^(2^(n-2)-1)`. The guard keeps both subtractions from truncating. -/
theorem A037097_conjecture (n : ℕ) (hn : 3 ≤ n) :
    (X + 1 : (ZMod 2)[X]) ^ (2 ^ (n - 2) - 1) ∣ gf2OfNat (a037097 n) := by
  rw [a037097, gf2OfNat_colNat]
  exact colPoly_half_dvd n hn

/-- The exponent in the A037097 conjecture is exact: for `n ≥ 3`,
`(x + 1)^(2^(n-2))` does not divide A037097(n) read as a GF(2) polynomial. -/
theorem A037097_exponent_exact (n : ℕ) (hn : 3 ≤ n) :
    ¬ (X + 1 : (ZMod 2)[X]) ^ (2 ^ (n - 2)) ∣ gf2OfNat (a037097 n) := by
  rw [a037097, gf2OfNat_colNat]
  exact colPoly_half_not_dvd n hn

/-- The A037096 companion conjecture: for `n ≥ 3`, A037096(n), read as a
GF(2) polynomial, is divisible by `(x+1)^(3*2^(n-2)-1)`. -/
theorem A037096_conjecture (n : ℕ) (hn : 3 ≤ n) :
    (X + 1 : (ZMod 2)[X]) ^ (3 * 2 ^ (n - 2) - 1) ∣ gf2OfNat (a037096 n) := by
  rw [a037096, gf2OfNat_colNat]
  exact colPoly_full_dvd n hn

/-- The exponent in the A037096 conjecture is exact: for `n ≥ 3`,
`(x + 1)^(3 * 2^(n-2))` does not divide A037096(n) read as a GF(2) polynomial. -/
theorem A037096_exponent_exact (n : ℕ) (hn : 3 ≤ n) :
    ¬ (X + 1 : (ZMod 2)[X]) ^ (3 * 2 ^ (n - 2)) ∣ gf2OfNat (a037096 n) := by
  rw [a037096, gf2OfNat_colNat]
  exact colPoly_full_not_dvd n hn

/-! ## Examples -/

-- Non-vacuity at the boundary `n = 3`: `a(3) = 12` reads as `x^2 + x^3`,
-- which is `(x + 1)^1 * x^2`, and the conjecture's exponent there is `1`.
example : gf2OfNat (a037097 3) = (X + 1) ^ (2 ^ (3 - 2) - 1) * X ^ 2 := by
  rw [a037097, gf2OfNat_colNat, show 3 - 1 = 2 by rfl, show (2 : ℕ) ^ 2 = 2 + 2 by rfl]
  simp only [colPoly, sum_range_succ, sum_range_zero]
  have hb : ∀ k : ℕ, bitN 3 (3 ^ k) = 3 ^ k / 8 % 2 := fun k => rfl
  simp only [hb]
  norm_num
  ring

end Candidates.A037097SumBitFloor
