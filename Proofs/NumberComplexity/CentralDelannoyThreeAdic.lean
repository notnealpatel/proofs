/-
# 3-adic valuation of central Delannoy numbers

M. A. Alekseyev, T. Amdeberhan, J. Shallit and I. Vukusic,
“On the p-adic valuations of values of Legendre polynomials”,
arXiv:2505.08935: Theorems `thm:vp-Legendre_explicit_p3` and `thm:main`,
specialized to `p = 3`, and Shallit's conjecture `jeffcon`
(Allouche–Shallit, 2003, p. 453; first proved by Shen, 2023).
For central Delannoy numbers `D(n) = P_n(3)` (A001850), the module
proves the explicit valuations, recurrences, and Oudra's closed form
`v₃(D(n)) = ∑_{k≥0} (⌊n/3^k⌋ mod 2)` (A358360).
This closed form is derived here from the valuation identities; it is not
stated in this form in the cited paper.

Not the paper's route through the expansion of `P_n(x)` at `x = 0`, but an
equivalent integer identity: `D(n) = [x^n] ((x+1)(x+2))^n`, and expanding
`(x+1)(x+2) = 3x + (x^2 + 2)` gives
`D(n) = ∑_j C(n,j) 3^j E(n-j)` with `E(N) = 2^{N/2} C(N, N/2)` for even `N`
and `0` for odd `N`.  The term of least power of `3` dominates 3-adically by
the identities `C(2m,2i) C(2m-2i,m-i) C(2i,i) = C(2m,m) C(m,i)^2` and its odd
analogue, together with `(2i+1) C(2i,i) < 9^i` for `i ≥ 1`.
-/
import Mathlib

set_option autoImplicit false

namespace CentralDelannoyThreeAdic

open Polynomial Finset Nat

/-! ## Definitions and examples -/

/-- The central Delannoy number `D(n) = ∑_{0 ≤ k ≤ n} C(n,k) C(n+k,k)`
(OEIS A001850), the source's `a(n)`; it equals `P_n(3)`, see
`centralDelannoy_eq_eval_shiftedLegendre`. -/
def centralDelannoy (n : ℕ) : ℕ := ∑ k ∈ range (n + 1), n.choose k * (n + k).choose k

/-- The coefficient of `x^N` in `(x^2 + 2)^N`: `2^{N/2} C(N, N/2)` for even `N`,
and `0` for odd `N`. -/
def evenTerm (N : ℕ) : ℕ := if 2 ∣ N then 2 ^ (N / 2) * N.choose (N / 2) else 0

/-- The closed form `∑_{k ≥ 0} (⌊n/3^k⌋ mod 2)`, truncated at `k ≤ n` (all later
terms vanish since `n < 3^k`). -/
def digitParitySum (n : ℕ) : ℕ := ∑ k ∈ range (n + 1), n / 3 ^ k % 2

example : (List.range 6).map centralDelannoy = [1, 3, 13, 63, 321, 1683] := by decide
example : (List.range 8).map evenTerm = [1, 0, 4, 0, 24, 0, 160, 0] := by decide
/-- The first ten terms of OEIS A358360. -/
example : (List.range 10).map digitParitySum = [0, 1, 0, 2, 1, 2, 0, 1, 0, 3] := by decide

/-- Central Delannoy numbers are positive (the `k = 0` term is `1`), so their
3-adic valuations are not junk values of `padicValNat`. -/
theorem centralDelannoy_pos (n : ℕ) : 0 < centralDelannoy n := by
  rw [centralDelannoy, Finset.sum_range_succ']
  simp

/-- Bridge to the source's `P_n(3)`: with Mathlib's shifted Legendre polynomial
`P̃_n(t) = P_n(1 - 2t)`, `D(n) = P̃_n(-1) = P_n(3)`. -/
theorem centralDelannoy_eq_eval_shiftedLegendre (n : ℕ) :
    (centralDelannoy n : ℤ) = (shiftedLegendre n).eval (-1) := by
  rw [shiftedLegendre, eval_finsetSum, centralDelannoy]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [eval_mul, eval_C, eval_pow, eval_X, Nat.choose_symm_add]
  have h1 : ((-1 : ℤ) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
  linear_combination -(((n + k).choose k : ℤ) * (n.choose k : ℤ)) * h1

/-! ## The expansion `D(n) = ∑_j C(n,j) 3^j E(n-j)` -/

/-- `D(n)` is the coefficient of `x^n` in `((x+1)(x+2))^n`. -/
theorem centralDelannoy_eq_coeff (n : ℕ) :
    centralDelannoy n = (((X + C 1 : ℕ[X]) * ((X + C 1) + 1)) ^ n).coeff n := by
  have hpoly : ((X + C 1 : ℕ[X]) * ((X + C 1) + 1)) ^ n
      = ∑ k ∈ range (n + 1), C (n.choose k) * (X + C 1) ^ (n + k) := by
    rw [mul_pow, add_pow (X + C 1) 1, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [one_pow, mul_one, pow_add, ← C_eq_natCast, Nat.cast_id]; ring
  rw [hpoly, finsetSum_coeff, centralDelannoy]
  refine sum_congr rfl fun k _ => ?_
  rw [coeff_C_mul, coeff_X_add_C_pow, one_pow, one_mul, Nat.choose_symm_add]
  simp

/-- The coefficient of `x^N` in `(x^2 + 2)^N` is `evenTerm N`. -/
theorem coeff_X_sq_add_two_pow (N : ℕ) :
    ((X ^ 2 + C 2 : ℕ[X]) ^ N).coeff N = evenTerm N := by
  have hexp : (X ^ 2 + C 2 : ℕ[X]) ^ N = expand ℕ 2 ((X + C 2) ^ N) := by
    rw [map_pow, map_add, expand_X, expand_C]
  rw [hexp, coeff_expand two_pos, coeff_X_add_C_pow, evenTerm]
  split_ifs with h
  · obtain ⟨r, rfl⟩ := h
    have hr : 2 * r - 2 * r / 2 = 2 * r / 2 := by omega
    rw [hr]; simp
  · rfl

/-- `D(n) = ∑_{0 ≤ j ≤ n} C(n,j) 3^j E(n-j)`, the expansion of `(3x + (x^2+2))^n`. -/
theorem centralDelannoy_eq_sum (n : ℕ) :
    centralDelannoy n = ∑ j ∈ range (n + 1), n.choose j * 3 ^ j * evenTerm (n - j) := by
  rw [centralDelannoy_eq_coeff]
  have hfac : ((X + C 1 : ℕ[X]) * ((X + C 1) + 1)) = C 3 * X + (X ^ 2 + C 2) := by
    rw [C_1, map_ofNat C 3, map_ofNat C 2]; ring
  rw [hfac, add_pow, finsetSum_coeff]
  refine sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
  have hterm : (C 3 * X : ℕ[X]) ^ j * (X ^ 2 + C 2) ^ (n - j) * (n.choose j : ℕ[X])
      = C (n.choose j * 3 ^ j) * (X ^ j * (X ^ 2 + C 2) ^ (n - j)) := by
    rw [C_mul, C_pow, ← C_eq_natCast, Nat.cast_id]; ring
  rw [hterm, coeff_C_mul, coeff_X_pow_mul', if_pos hjn, coeff_X_sq_add_two_pow]

/-! ## Binomial identities and size bounds -/

/-- `C(2i+2r, 2i) C(2r, r) C(2i, i) = C(2i+2r, i+r) C(i+r, i)^2`. -/
theorem choose_even_identity (i r : ℕ) :
    (2 * i + 2 * r).choose (2 * i) * (2 * r).choose r * (2 * i).choose i
      = (2 * i + 2 * r).choose (i + r) * (i + r).choose i ^ 2 := by
  have h1 : ((2 * i + 2 * r).choose (2 * i) : ℚ) = (2 * i + 2 * r)! / ((2 * i)! * (2 * r)!) :=
    Nat.cast_add_choose ℚ
  have h2 : ((2 * r).choose r : ℚ) = (2 * r)! / (r ! * r !) := by
    rw [two_mul, Nat.cast_add_choose]
  have h3 : ((2 * i).choose i : ℚ) = (2 * i)! / (i ! * i !) := by
    rw [two_mul, Nat.cast_add_choose]
  have h4 : ((2 * i + 2 * r).choose (i + r) : ℚ)
      = (2 * i + 2 * r)! / ((i + r)! * (i + r)!) := by
    rw [show 2 * i + 2 * r = (i + r) + (i + r) by ring, Nat.cast_add_choose]
  have h5 : ((i + r).choose i : ℚ) = (i + r)! / (i ! * r !) := Nat.cast_add_choose ℚ
  apply Nat.cast_injective (R := ℚ)
  push_cast
  rw [h1, h2, h3, h4, h5]
  field_simp

/-- `C(2i+2r+1, 2i+1) C(2r, r) (2i+1) C(2i, i) = (2i+2r+1) C(2i+2r, i+r) C(i+r, i)^2`. -/
theorem choose_odd_identity (i r : ℕ) :
    (2 * i + 2 * r + 1).choose (2 * i + 1) * (2 * r).choose r * ((2 * i + 1) * (2 * i).choose i)
      = (2 * i + 2 * r + 1) * (2 * i + 2 * r).choose (i + r) * (i + r).choose i ^ 2 := by
  have h1 : ((2 * i + 2 * r + 1).choose (2 * i + 1) : ℚ)
      = (2 * i + 1 + 2 * r)! / ((2 * i + 1)! * (2 * r)!) := by
    rw [show 2 * i + 2 * r + 1 = 2 * i + 1 + 2 * r by ring, Nat.cast_add_choose]
  have h2 : ((2 * r).choose r : ℚ) = (2 * r)! / (r ! * r !) := by
    rw [two_mul, Nat.cast_add_choose]
  have h3 : ((2 * i).choose i : ℚ) = (2 * i)! / (i ! * i !) := by
    rw [two_mul, Nat.cast_add_choose]
  have h4 : ((2 * i + 2 * r).choose (i + r) : ℚ)
      = (2 * i + 2 * r)! / ((i + r)! * (i + r)!) := by
    rw [show 2 * i + 2 * r = (i + r) + (i + r) by ring, Nat.cast_add_choose]
  have h5 : ((i + r).choose i : ℚ) = (i + r)! / (i ! * r !) := Nat.cast_add_choose ℚ
  have h6 : ((2 * i + 1 + 2 * r)! : ℚ) = (2 * i + 2 * r + 1) * (2 * i + 2 * r)! := by
    rw [show 2 * i + 1 + 2 * r = (2 * i + 2 * r) + 1 by ring, Nat.factorial_succ]
    push_cast; ring
  have h7 : ((2 * i + 1)! : ℚ) = (2 * i + 1) * (2 * i)! := by
    rw [Nat.factorial_succ]; push_cast; ring
  apply Nat.cast_injective (R := ℚ)
  push_cast
  rw [h1, h2, h3, h4, h5, h6, h7]
  field_simp

/-- `(2i+1) C(2i, i) < 9^i` for `i ≥ 1`. -/
theorem odd_mul_centralBinom_lt (i : ℕ) (hi : 0 < i) :
    (2 * i + 1) * (2 * i).choose i < 9 ^ i := by
  induction i, hi using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    have hrec := Nat.succ_mul_centralBinom_succ k
    rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at hrec
    have hlt : (k + 1) * ((2 * (k + 1) + 1) * (2 * (k + 1)).choose (k + 1))
        < (k + 1) * 9 ^ (k + 1) := by
      calc (k + 1) * ((2 * (k + 1) + 1) * (2 * (k + 1)).choose (k + 1))
          = (2 * k + 3) * ((k + 1) * (2 * (k + 1)).choose (k + 1)) := by ring
        _ = (2 * k + 3) * (2 * ((2 * k + 1) * (2 * k).choose k)) := by
            rw [hrec]; ring
        _ < (2 * k + 3) * (2 * 9 ^ k) := by
            apply Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
        _ ≤ (k + 1) * 9 ^ (k + 1) := by
            rw [pow_succ]; nlinarith [Nat.one_le_pow k 9 (by norm_num)]
    exact Nat.lt_of_mul_lt_mul_left hlt

/-! ## 3-adic valuation tools -/

/-- If `0 < x < 3^k` then `ν_3(x) < k`. -/
theorem padicValNat_three_lt_of_lt_pow {x k : ℕ} (hx : x ≠ 0) (hlt : x < 3 ^ k) :
    padicValNat 3 x < k := by
  by_contra hle
  have hdvd : 3 ^ k ∣ x := (padicValNat_dvd_iff_le hx).mpr (not_lt.mp hle)
  exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hx) hdvd) (not_le.mpr hlt)

/-- Strict ultrametric step: if `a ≠ 0` and `p^(ν_p(a)+1) ∣ b`, then
`ν_p(a + b) = ν_p(a)`. -/
theorem padicValNat_add_eq_of_pow_succ_dvd {p a b : ℕ} [Fact p.Prime] (ha : a ≠ 0)
    (hb : p ^ (padicValNat p a + 1) ∣ b) : padicValNat p (a + b) = padicValNat p a := by
  have hab : a + b ≠ 0 := by omega
  apply le_antisymm
  · by_contra hlt
    have h1 : p ^ (padicValNat p a + 1) ∣ a + b :=
      (padicValNat_dvd_iff_le hab).mpr (by omega)
    have h2 : p ^ (padicValNat p a + 1) ∣ a := (Nat.dvd_add_left hb).mp h1
    have h3 := (padicValNat_dvd_iff_le ha).mp h2
    omega
  · rw [← padicValNat_dvd_iff_le hab]
    exact dvd_add pow_padicValNat_dvd ((pow_dvd_pow p (Nat.le_succ _)).trans hb)

/-- `ν_3(2^r) = 0`. -/
theorem padicValNat_three_two_pow (r : ℕ) : padicValNat 3 (2 ^ r) = 0 := by
  apply padicValNat.eq_zero_of_not_dvd
  intro h
  have h32 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
  omega

/-- `ν_3(C(2i, i)) < 2i` for `i ≥ 1`. -/
theorem padicValNat_three_choose_two_mul_lt (i : ℕ) (hi : 0 < i) :
    padicValNat 3 ((2 * i).choose i) < 2 * i := by
  apply padicValNat_three_lt_of_lt_pow (Nat.choose_pos (by omega)).ne'
  have h := odd_mul_centralBinom_lt i hi
  rw [pow_mul]
  norm_num
  nlinarith

/-! ## The paper's explicit formula for `p = 3` -/

/-- Paper, Theorem `thm:vp-Legendre_explicit_p3` (even case, `p = 3`):
`ν_3(D(2m)) = ν_3(C(2m, m))`. -/
theorem padicValNat_three_centralDelannoy_two_mul (m : ℕ) :
    padicValNat 3 (centralDelannoy (2 * m)) = padicValNat 3 ((2 * m).choose m) := by
  have hcm : (2 * m).choose m ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hlead : (2 * m).choose 0 * 3 ^ 0 * evenTerm (2 * m - 0) = 2 ^ m * (2 * m).choose m := by
    simp [evenTerm]
  have hv : padicValNat 3 (2 ^ m * (2 * m).choose m) = padicValNat 3 ((2 * m).choose m) := by
    rw [padicValNat.mul (by positivity) hcm, padicValNat_three_two_pow, zero_add]
  rw [centralDelannoy_eq_sum, Finset.sum_range_succ', add_comm, hlead,
    padicValNat_add_eq_of_pow_succ_dvd (by positivity), hv]
  rw [hv]
  apply Finset.dvd_sum
  intro j hj
  have hjlt : j < 2 * m := Finset.mem_range.mp hj
  by_cases hpar : 2 ∣ 2 * m - (j + 1)
  · obtain ⟨i, hi⟩ : ∃ i, j + 1 = 2 * i := ⟨(j + 1) / 2, by omega⟩
    obtain ⟨r, rfl⟩ : ∃ r, m = i + r := ⟨m - i, by omega⟩
    have hipos : 0 < i := by omega
    have hsub : 2 * (i + r) - (j + 1) = 2 * r := by omega
    have hE : evenTerm (2 * r) = 2 ^ r * (2 * r).choose r := by simp [evenTerm]
    rw [hsub, hE, hi, mul_add]
    have hA1 : (2 * i + 2 * r).choose (2 * i) ≠ 0 := (Nat.choose_pos (by omega)).ne'
    have hA2 : (2 * r).choose r ≠ 0 := (Nat.choose_pos (by omega)).ne'
    have hB : (2 * i).choose i ≠ 0 := (Nat.choose_pos (by omega)).ne'
    have hC : (i + r).choose i ≠ 0 := (Nat.choose_pos (by omega)).ne'
    have hM : (2 * i + 2 * r).choose (i + r) ≠ 0 := (Nat.choose_pos (by omega)).ne'
    have hid := congrArg (padicValNat 3) (choose_even_identity i r)
    rw [padicValNat.mul (mul_ne_zero hA1 hA2) hB, padicValNat.mul hA1 hA2,
      padicValNat.mul hM (pow_ne_zero 2 hC),
      padicValNat.pow (p := 3) ((i + r).choose i) 2] at hid
    have hlt := padicValNat_three_choose_two_mul_lt i hipos
    rw [padicValNat_dvd_iff_le (by positivity), padicValNat.mul (by positivity) (by positivity),
      padicValNat.mul hA1 (by positivity), padicValNat.mul (by positivity) hA2,
      padicValNat.prime_pow, padicValNat_three_two_pow]
    omega
  · rw [evenTerm, if_neg hpar, mul_zero]
    exact dvd_zero _

/-- Paper, Theorem `thm:vp-Legendre_explicit_p3` (odd case, `p = 3`):
`ν_3(D(2m+1)) = 1 + ν_3(2m+1) + ν_3(C(2m, m))`. -/
theorem padicValNat_three_centralDelannoy_two_mul_add_one (m : ℕ) :
    padicValNat 3 (centralDelannoy (2 * m + 1))
      = 1 + padicValNat 3 (2 * m + 1) + padicValNat 3 ((2 * m).choose m) := by
  have hcm : (2 * m).choose m ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hodd : ¬ 2 ∣ 2 * m + 1 := by omega
  have hzero : (2 * m + 1).choose 0 * 3 ^ 0 * evenTerm (2 * m + 1 - 0) = 0 := by
    simp [evenTerm, hodd]
  have hlead : (2 * m + 1).choose (0 + 1) * 3 ^ (0 + 1) * evenTerm (2 * m + 1 - (0 + 1))
      = (2 * m + 1) * 3 * (2 ^ m * (2 * m).choose m) := by
    simp [evenTerm]
  have hv : padicValNat 3 ((2 * m + 1) * 3 * (2 ^ m * (2 * m).choose m))
      = 1 + padicValNat 3 (2 * m + 1) + padicValNat 3 ((2 * m).choose m) := by
    rw [padicValNat.mul (by positivity) (by positivity),
      padicValNat.mul (by positivity) (by norm_num),
      padicValNat.mul (by positivity) hcm, padicValNat_three_two_pow, padicValNat_self]
    ring
  rw [centralDelannoy_eq_sum, Finset.sum_range_succ', Finset.sum_range_succ', hzero, add_zero,
    add_comm, hlead, padicValNat_add_eq_of_pow_succ_dvd (by positivity), hv]
  rw [hv]
  apply Finset.dvd_sum
  intro j hj
  have hjlt : j < 2 * m := Finset.mem_range.mp hj
  by_cases hpar : 2 ∣ 2 * m + 1 - (j + 1 + 1)
  · obtain ⟨i, hi⟩ : ∃ i, j + 1 + 1 = 2 * i + 1 := ⟨(j + 1) / 2, by omega⟩
    obtain ⟨r, rfl⟩ : ∃ r, m = i + r := ⟨m - i, by omega⟩
    have hipos : 0 < i := by omega
    have hsub : 2 * (i + r) + 1 - (j + 1 + 1) = 2 * r := by omega
    have hE : evenTerm (2 * r) = 2 ^ r * (2 * r).choose r := by simp [evenTerm]
    rw [hsub, hE, hi, mul_add]
    have hB1 : (2 * i + 2 * r + 1).choose (2 * i + 1) ≠ 0 := (Nat.choose_pos (by omega)).ne'
    have hA2 : (2 * r).choose r ≠ 0 := (Nat.choose_pos (by omega)).ne'
    have hB : (2 * i + 1) * (2 * i).choose i ≠ 0 :=
      mul_ne_zero (by omega) (Nat.choose_pos (by omega)).ne'
    have hC : (i + r).choose i ≠ 0 := (Nat.choose_pos (by omega)).ne'
    have hM : (2 * i + 2 * r).choose (i + r) ≠ 0 := (Nat.choose_pos (by omega)).ne'
    have hid := congrArg (padicValNat 3) (choose_odd_identity i r)
    rw [padicValNat.mul (mul_ne_zero hB1 hA2) hB, padicValNat.mul hB1 hA2,
      padicValNat.mul (mul_ne_zero (by omega) hM) (pow_ne_zero 2 hC),
      padicValNat.mul (by omega) hM, padicValNat.pow (p := 3) ((i + r).choose i) 2] at hid
    have hlt : padicValNat 3 ((2 * i + 1) * (2 * i).choose i) < 2 * i := by
      apply padicValNat_three_lt_of_lt_pow hB
      rw [pow_mul]
      exact odd_mul_centralBinom_lt i hipos
    rw [padicValNat_dvd_iff_le (by positivity), padicValNat.mul (by positivity) (by positivity),
      padicValNat.mul hB1 (by positivity), padicValNat.mul (by positivity) hA2,
      padicValNat.prime_pow, padicValNat_three_two_pow]
    omega
  · rw [evenTerm, if_neg hpar, mul_zero]
    exact dvd_zero _

/-- Paper, Theorem `thm:vp-Legendre_explicit_p3` for `p = 3`, both parities:
`ν_3(D(2m)) = ν_3(C(2m,m))` and `ν_3(D(2m+1)) = 1 + ν_3(2m+1) + ν_3(C(2m,m))`. -/
theorem thm_vp_Legendre_explicit_p3 (m : ℕ) :
    padicValNat 3 (centralDelannoy (2 * m)) = padicValNat 3 ((2 * m).choose m) ∧
      padicValNat 3 (centralDelannoy (2 * m + 1))
        = 1 + padicValNat 3 (2 * m + 1) + padicValNat 3 ((2 * m).choose m) :=
  ⟨padicValNat_three_centralDelannoy_two_mul m,
    padicValNat_three_centralDelannoy_two_mul_add_one m⟩

/-! ## The closed form `∑_k (⌊n/3^k⌋ mod 2)` -/

/-- Extending the range of `∑_k (⌊n/3^k⌋ mod 2)` past `n < 3^B` adds only zeros. -/
theorem sum_range_div_three_pow_mod_two_of_le {n B C : ℕ} (hBC : B ≤ C) (hB : n < 3 ^ B) :
    ∑ k ∈ range C, n / 3 ^ k % 2 = ∑ k ∈ range B, n / 3 ^ k % 2 := by
  symm
  apply Finset.sum_subset (Finset.range_subset_range.mpr hBC)
  intro k _ hkB
  have hk : B ≤ k := by simpa using hkB
  have hlt : n < 3 ^ k := lt_of_lt_of_le hB (Nat.pow_le_pow_right (by norm_num) hk)
  rw [Nat.div_eq_of_lt hlt, Nat.zero_mod]

/-- Any truncation `∑_{k < B}` with `n < 3^B` computes `digitParitySum n`. -/
theorem sum_range_eq_digitParitySum {n B : ℕ} (hB : n < 3 ^ B) :
    ∑ k ∈ range B, n / 3 ^ k % 2 = digitParitySum n := by
  have hn : n < 3 ^ (n + 1) := by
    have hlt := Nat.lt_pow_self (n := n + 1) (a := 3) (by norm_num)
    omega
  rw [digitParitySum, ← sum_range_div_three_pow_mod_two_of_le (le_max_left B (n + 1)) hB,
    ← sum_range_div_three_pow_mod_two_of_le (le_max_right B (n + 1)) hn]

/-- `⌊2m/q⌋ mod 2` is the carry indicator `[q ≤ 2 (m mod q)]`. -/
theorem two_mul_div_mod_two (m q : ℕ) (hq : 0 < q) :
    2 * m / q % 2 = if q ≤ m % q + m % q then 1 else 0 := by
  have hdm := Nat.div_add_mod m q
  have hmod := Nat.mod_lt m hq
  set a := m / q
  set b := m % q
  split_ifs with h
  · have hdiv : 2 * m / q = 2 * a + 1 := by
      apply Nat.div_eq_of_lt_le <;> nlinarith
    omega
  · have hdiv : 2 * m / q = 2 * a := by
      apply Nat.div_eq_of_lt_le <;> nlinarith
    omega

/-- Kummer's theorem for `C(2m, m)` at `p = 3` in closed form:
`ν_3(C(2m,m)) = ∑_k (⌊2m/3^k⌋ mod 2)`. -/
theorem padicValNat_three_choose_two_mul_eq (m : ℕ) :
    padicValNat 3 ((2 * m).choose m) = digitParitySum (2 * m) := by
  have hlog : Nat.log 3 (2 * m) < 2 * m + 1 := Nat.lt_succ_of_le (Nat.log_le_self 3 (2 * m))
  rw [padicValNat_choose (by omega) hlog, Finset.card_filter, digitParitySum,
    Finset.sum_range_succ', Finset.sum_Ico_eq_sum_range]
  simp only [pow_zero, Nat.div_one, Nat.mul_mod_right, add_zero,
    show 2 * m + 1 - 1 = 2 * m by omega, show 2 * m - m = m by omega]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [two_mul_div_mod_two m _ (by positivity), add_comm 1 k]

/-- `#{k < B : 3^k ∣ N} = ν_3(N) + 1` when `N ≠ 0` and `ν_3(N) < B`. -/
theorem sum_range_ite_pow_dvd {N B : ℕ} (hN : N ≠ 0) (hB : padicValNat 3 N < B) :
    ∑ k ∈ range B, (if 3 ^ k ∣ N then 1 else 0) = padicValNat 3 N + 1 := by
  rw [← Finset.card_filter]
  have hset : (range B).filter (fun k => 3 ^ k ∣ N) = range (padicValNat 3 N + 1) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, padicValNat_dvd_iff_le hN]
    omega
  rw [hset, Finset.card_range]

/-- For odd `q`: `⌊(2m+1)/q⌋ mod 2 = ⌊2m/q⌋ mod 2 + [q ∣ 2m+1]`. -/
theorem odd_div_mod_two (m q : ℕ) (hq : Odd q) :
    (2 * m + 1) / q % 2 = 2 * m / q % 2 + if q ∣ 2 * m + 1 then 1 else 0 := by
  rw [Nat.succ_div]
  split_ifs with hd
  · obtain ⟨c, hc⟩ := hd
    have hcodd : Odd c := (Nat.odd_mul.mp (hc ▸ odd_two_mul_add_one m)).2
    have hq0 : 0 < q := hq.pos
    have hcq : (2 * m + 1) / q = c := by rw [hc, Nat.mul_div_cancel_left c hq0]
    rw [Nat.succ_div, if_pos ⟨c, hc⟩] at hcq
    have hc2 := Nat.odd_iff.mp hcodd
    omega
  · simp

/-- `∑_k (⌊(2m+1)/3^k⌋ mod 2) = 1 + ν_3(2m+1) + ∑_k (⌊2m/3^k⌋ mod 2)`. -/
theorem digitParitySum_two_mul_add_one (m : ℕ) :
    digitParitySum (2 * m + 1) = 1 + padicValNat 3 (2 * m + 1) + digitParitySum (2 * m) := by
  have hpt : ∀ k ∈ range (2 * m + 1 + 1), (2 * m + 1) / 3 ^ k % 2
      = 2 * m / 3 ^ k % 2 + if 3 ^ k ∣ 2 * m + 1 then 1 else 0 :=
    fun k _ => odd_div_mod_two m (3 ^ k) (Odd.pow (by decide))
  have hnu : padicValNat 3 (2 * m + 1) < 2 * m + 1 + 1 := by
    have hle : 3 ^ padicValNat 3 (2 * m + 1) ≤ 2 * m + 1 :=
      Nat.le_of_dvd (by omega) pow_padicValNat_dvd
    have hlt : padicValNat 3 (2 * m + 1) < 3 ^ padicValNat 3 (2 * m + 1) :=
      Nat.lt_pow_self (by norm_num)
    omega
  have h2m : 2 * m < 3 ^ (2 * m + 1 + 1) := by
    have hlt := Nat.lt_pow_self (n := 2 * m + 1 + 1) (a := 3) (by norm_num)
    omega
  rw [digitParitySum, Finset.sum_congr rfl hpt, Finset.sum_add_distrib,
    sum_range_eq_digitParitySum h2m, sum_range_ite_pow_dvd (by omega) hnu]
  ring

/-- Closed form (OEIS A358360, Oudra's formula):
`ν_3(D(n)) = ∑_{k ≥ 0} (⌊n/3^k⌋ mod 2)`. -/
theorem padicValNat_three_centralDelannoy_eq_digitParitySum (n : ℕ) :
    padicValNat 3 (centralDelannoy n) = digitParitySum n := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [padicValNat_three_centralDelannoy_two_mul, padicValNat_three_choose_two_mul_eq]
  · rw [padicValNat_three_centralDelannoy_two_mul_add_one, digitParitySum_two_mul_add_one,
      padicValNat_three_choose_two_mul_eq]

/-- The closed form satisfies `g(N) = (N mod 2) + g(⌊N/3⌋)`. -/
theorem digitParitySum_eq_mod_two_add (N : ℕ) :
    digitParitySum N = N % 2 + digitParitySum (N / 3) := by
  have hN : N / 3 < 3 ^ N :=
    lt_of_le_of_lt (Nat.div_le_self N 3) (Nat.lt_pow_self (n := N) (a := 3) (by norm_num))
  have hpt : ∀ k ∈ range N, N / 3 ^ (k + 1) % 2 = N / 3 / 3 ^ k % 2 := by
    intro k _
    rw [Nat.div_div_eq_div_mul, pow_succ']
  rw [digitParitySum, Finset.sum_range_succ', Finset.sum_congr rfl hpt,
    sum_range_eq_digitParitySum hN, pow_zero, Nat.div_one, add_comm]

/-! ## Recurrences -/

/-- Paper, Theorem `thm:main` for `p = 3`: for `0 ≤ a < 3`,
`ν_3(D(3n+a)) = ν_3(D(n)) + ((n + a) mod 2)`, i.e. `+ (n mod 2)` for even `a`
and `+ 1 - (n mod 2)` for odd `a`. -/
theorem padicValNat_three_centralDelannoy_three_mul_add (n a : ℕ) (ha : a < 3) :
    padicValNat 3 (centralDelannoy (3 * n + a))
      = padicValNat 3 (centralDelannoy n) + (n + a) % 2 := by
  rw [padicValNat_three_centralDelannoy_eq_digitParitySum,
    padicValNat_three_centralDelannoy_eq_digitParitySum, digitParitySum_eq_mod_two_add,
    show (3 * n + a) / 3 = n by omega]
  omega

/-- Shallit's conjecture (paper, Conjecture `jeffcon`), case `i ≡ 0, 2 (mod 3)`:
`b(i) = b(⌊i/3⌋) + (⌊i/3⌋ mod 2)` with `b = ν_3 ∘ D`. -/
theorem shallit_of_mod_three_ne_one (i : ℕ) (hi : i % 3 ≠ 1) :
    padicValNat 3 (centralDelannoy i)
      = padicValNat 3 (centralDelannoy (i / 3)) + i / 3 % 2 := by
  rw [padicValNat_three_centralDelannoy_eq_digitParitySum,
    padicValNat_three_centralDelannoy_eq_digitParitySum, digitParitySum_eq_mod_two_add i]
  omega

/-- Shallit's conjecture (paper, Conjecture `jeffcon`), case `i ≡ 1 (mod 3)`:
`b(i) = b(⌊i/9⌋) + 1` with `b = ν_3 ∘ D`. -/
theorem shallit_of_mod_three_eq_one (i : ℕ) (hi : i % 3 = 1) :
    padicValNat 3 (centralDelannoy i) = padicValNat 3 (centralDelannoy (i / 9)) + 1 := by
  rw [padicValNat_three_centralDelannoy_eq_digitParitySum,
    padicValNat_three_centralDelannoy_eq_digitParitySum, digitParitySum_eq_mod_two_add i,
    digitParitySum_eq_mod_two_add (i / 3), show i / 3 / 3 = i / 9 by omega]
  omega

/-- Examples: `D(9) = 1462563 = 3^3 · 54169`, and the closed form gives `3`. -/
example : padicValNat 3 (centralDelannoy 9) = 3 := by
  rw [padicValNat_three_centralDelannoy_eq_digitParitySum]
  decide

end CentralDelannoyThreeAdic
