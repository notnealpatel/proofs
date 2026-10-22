/-
# A291982 — Luschny: `n(n+1)` divides `Euler(n, n+1)` for even `n ≥ 2`

OEIS A291982, Peter Luschny: for even `n ≥ 2`, `n(n+1)` divides
`E_n(n+1)·2^{v₂(n+1)}`. Divisibility is expressed by an integer quotient.
The Euler polynomials are defined by the coefficient recurrence of
`2e^{xt}/(e^t+1)`; `eulerEGF_spec` proves that generating-function identity.

1. Power-series layer: `(e^t + 1) G_x = 2 e^{xt}` (`eulerEGF_spec`), hence
   `G_{x+1} = e^t G_x` and `E_n(x+1) + E_n(x) = 2 x^n`; the reflection
   `t ↦ -t` gives `E_n(0) = 0` for even `n ≥ 2`.
2. Telescoping: for even `n ≥ 2`, `E_n(n+1) = 2 ∑_{j ≤ n} (-1)^j j^n`.
3. Number theory: `n + 1 ∣ 2S` by the reflection `j ↦ n + 1 - j`;
   with `n = 2^e q`, `q` odd: `q ∣ S` because `j ↦ (-1)^j j^n` changes sign
   under `j ↦ j + q` modulo `q`; `2^e ∣ 2S` because odd `j` satisfy
   `j^n ≡ 1 (mod 2^e)` and even `j` satisfy `j^n ≡ 0`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A291982EulerPolynomialSum

open Polynomial Finset
open scoped Nat

/-! ## Definitions -/

/-- The Euler polynomial `E_n(x)`, defined by the coefficient recurrence of the
generating function `2 e^{xt} / (e^t + 1) = ∑ E_n(x) t^n / n!`:
`E_n(x) = x^n - (1/2) ∑_{k < n} C(n,k) E_k(x)`.  See `eulerEGF_spec` for the
generating-function identity. -/
noncomputable def eulerPoly (n : ℕ) : ℚ[X] :=
  X ^ n - Polynomial.C (1 / 2 : ℚ) * ∑ k : Fin n, (n.choose k : ℚ[X]) * eulerPoly k
decreasing_by exact k.2

/-- OEIS A291982: `a(n) = Euler(n, n+1) · 2^{v₂(n+1)}`, as a rational number. -/
noncomputable def a (n : ℕ) : ℚ :=
  (eulerPoly n).eval ((n : ℚ) + 1) * 2 ^ padicValNat 2 (n + 1)

/-- The exponential generating function `∑ E_n(x) t^n / n!` of the Euler
polynomials evaluated at `x`. -/
noncomputable def eulerEGF (x : ℚ) : PowerSeries ℚ :=
  PowerSeries.mk (fun n => (eulerPoly n).eval x / n !)

/-- The alternating power sum `∑_{j=0}^{n} (-1)^j j^n`. -/
def altPowSum (n : ℕ) : ℤ := ∑ j ∈ range (n + 1), (-1) ^ j * (j : ℤ) ^ n

/-! ## Recurrence and generating function -/

/-- The defining recurrence of `eulerPoly`, with the sum over `Finset.range`. -/
theorem eulerPoly_eq (n : ℕ) : eulerPoly n =
    X ^ n - Polynomial.C (1 / 2 : ℚ) * ∑ k ∈ range n, (n.choose k : ℚ[X]) * eulerPoly k := by
  rw [eulerPoly, Fin.sum_univ_eq_sum_range (fun k => (n.choose k : ℚ[X]) * eulerPoly k)]

/-- The recurrence after evaluation at `x`. -/
theorem eulerPoly_eval_eq (n : ℕ) (x : ℚ) : (eulerPoly n).eval x =
    x ^ n - 1 / 2 * ∑ k ∈ range n, (n.choose k : ℚ) * (eulerPoly k).eval x := by
  rw [eulerPoly_eq]
  simp [eval_finsetSum]

/-- Binomial convolution: the `n`-th coefficient of a product of exponential
generating functions `∑ e_k t^k/k!` and `∑ c_k t^k/k!` is
`(∑_{k ≤ n} C(n,k) e_k c_{n-k}) / n!`. -/
theorem coeff_egf_mul (e c : ℕ → ℚ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk (fun k => e k / k !) * PowerSeries.mk (fun k => c k / k !)) =
      (∑ k ∈ range (n + 1), (n.choose k : ℚ) * e k * c (n - k)) / n ! := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i (PowerSeries.mk (fun k => e k / k !)) *
      PowerSeries.coeff j (PowerSeries.mk (fun k => c k / k !))), Finset.sum_div]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  simp only [PowerSeries.coeff_mk]
  have hfac : ((n.choose k : ℕ) : ℚ) * (k ! : ℚ) * ((n - k)! : ℚ) = n ! := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkn
  have h1 : (k ! : ℚ) ≠ 0 := by positivity
  have h2 : ((n - k)! : ℚ) ≠ 0 := by positivity
  have h3 : ((n.choose k : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hkn).ne'
  rw [← hfac]
  field_simp

/-- `exp` as the exponential generating function of the constant sequence `1`. -/
theorem exp_eq_mk : PowerSeries.exp ℚ = PowerSeries.mk (fun k => (fun _ => (1 : ℚ)) k / k !) := by
  ext k
  simp [PowerSeries.coeff_exp]

/-- The `n`-th coefficient of `2 e^{xt}` is `2 x^n / n!`. -/
theorem coeff_two_mul_rescale_exp (x : ℚ) (n : ℕ) :
    PowerSeries.coeff n (2 * PowerSeries.rescale x (PowerSeries.exp ℚ)) = 2 * x ^ n / n ! := by
  rw [show (2 : PowerSeries ℚ) = PowerSeries.C (2 : ℚ) from rfl, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
  simp only [Algebra.algebraMap_self, one_div, map_inv₀, map_natCast]
  ring

/-- **Generating function.** `(e^t + 1) · ∑ E_n(x) t^n/n! = 2 e^{xt}`, i.e.
`∑ E_n(x) t^n/n! = 2 e^{xt} / (e^t + 1)`: `eulerPoly` is the Euler polynomial
of the entry's definition. -/
theorem eulerEGF_spec (x : ℚ) :
    (PowerSeries.exp ℚ + 1) * eulerEGF x = 2 * PowerSeries.rescale x (PowerSeries.exp ℚ) := by
  ext n
  rw [coeff_two_mul_rescale_exp, add_mul, one_mul, mul_comm, map_add, exp_eq_mk, eulerEGF,
    coeff_egf_mul]
  simp only [PowerSeries.coeff_mk, mul_one, Finset.sum_range_succ, Nat.choose_self, Nat.cast_one,
    one_mul]
  have hrec := eulerPoly_eval_eq n x
  have hfac : (n ! : ℚ) ≠ 0 := by positivity
  field_simp
  linear_combination (2 : ℚ) * hrec

/-- `e^t + 1` is a nonzero power series (its constant coefficient is `2`). -/
theorem exp_add_one_ne_zero : PowerSeries.exp ℚ + 1 ≠ 0 := by
  intro h
  have h0 := congrArg (PowerSeries.constantCoeff (R := ℚ)) h
  simp at h0

/-- Shift: `∑ E_n(x+1) t^n/n! = e^t ∑ E_n(x) t^n/n!`. -/
theorem eulerEGF_add_one (x : ℚ) :
    eulerEGF (x + 1) = PowerSeries.exp ℚ * eulerEGF x := by
  apply mul_left_cancel₀ exp_add_one_ne_zero
  rw [eulerEGF_spec, ← PowerSeries.exp_mul_exp_eq_exp_add x 1, PowerSeries.rescale_one,
    RingHom.id_apply]
  linear_combination (-PowerSeries.exp ℚ) * eulerEGF_spec x

/-- The difference equation `E_n(x+1) + E_n(x) = 2 x^n`. -/
theorem eulerPoly_eval_add_one (n : ℕ) (x : ℚ) :
    (eulerPoly n).eval (x + 1) + (eulerPoly n).eval x = 2 * x ^ n := by
  have h : eulerEGF (x + 1) + eulerEGF x = 2 * PowerSeries.rescale x (PowerSeries.exp ℚ) := by
    rw [eulerEGF_add_one, ← eulerEGF_spec]
    ring
  have hn := congrArg (PowerSeries.coeff n) h
  rw [coeff_two_mul_rescale_exp, map_add, eulerEGF, eulerEGF, PowerSeries.coeff_mk,
    PowerSeries.coeff_mk] at hn
  have hfac : (n ! : ℚ) ≠ 0 := by positivity
  field_simp at hn
  linear_combination hn

/-- Reflection at `x = 0`: `G_0(t) + G_0(-t) = 2`, from `2/(e^t+1) + 2/(e^{-t}+1) = 2`. -/
theorem eulerEGF_zero_add_reflect :
    eulerEGF 0 + PowerSeries.rescale (-1) (eulerEGF 0) = 2 := by
  have hA := eulerEGF_spec 0
  have hR0 : PowerSeries.rescale (0 : ℚ) (PowerSeries.exp ℚ) = 1 := by
    rw [PowerSeries.rescale_zero]
    simp
  rw [hR0, mul_one] at hA
  have hB := congrArg (PowerSeries.rescale (-1 : ℚ)) hA
  rw [map_mul, map_add, map_one, map_ofNat] at hB
  have hN : PowerSeries.exp ℚ * PowerSeries.rescale (-1 : ℚ) (PowerSeries.exp ℚ) = 1 := by
    have hadd := PowerSeries.exp_mul_exp_eq_exp_add (A := ℚ) 1 (-1)
    rw [PowerSeries.rescale_one, RingHom.id_apply, add_neg_cancel, hR0] at hadd
    exact hadd
  apply mul_left_cancel₀ exp_add_one_ne_zero
  linear_combination hA + PowerSeries.exp ℚ * hB - (PowerSeries.rescale (-1 : ℚ) (eulerEGF 0)) * hN

/-- `E_n(0) = 0` for every even `n ≥ 2` (here `n ≠ 0`). -/
theorem eulerPoly_eval_zero_of_even (n : ℕ) (hn : Even n) (hn0 : n ≠ 0) :
    (eulerPoly n).eval 0 = 0 := by
  have h := congrArg (PowerSeries.coeff n) eulerEGF_zero_add_reflect
  rw [map_add, PowerSeries.coeff_rescale, eulerEGF, PowerSeries.coeff_mk, hn.neg_one_pow,
    show (2 : PowerSeries ℚ) = PowerSeries.C (2 : ℚ) from rfl, PowerSeries.coeff_C,
    if_neg hn0] at h
  have hfac : (n ! : ℚ) ≠ 0 := by positivity
  field_simp at h
  linarith

/-- Telescoping the difference equation: for every `N`,
`(-1)^N E_n(N) = E_n(0) - 2 ∑_{j < N} (-1)^j j^n`. -/
theorem neg_one_pow_mul_eulerPoly_eval_natCast (n N : ℕ) :
    (-1) ^ N * (eulerPoly n).eval (N : ℚ) =
      (eulerPoly n).eval 0 - 2 * ∑ j ∈ range N, (-1) ^ j * (j : ℚ) ^ n := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hstep := eulerPoly_eval_add_one n (N : ℚ)
    rw [Finset.sum_range_succ, Nat.cast_succ, pow_succ]
    linear_combination ih - (-1) ^ N * hstep

/-- For even `n ≥ 2`, `E_n(n+1) = 2 ∑_{j=0}^{n} (-1)^j j^n`. -/
theorem eulerPoly_eval_succ_eq (n : ℕ) (hn : Even n) (hn0 : n ≠ 0) :
    (eulerPoly n).eval ((n : ℚ) + 1) = 2 * (altPowSum n : ℚ) := by
  have h := neg_one_pow_mul_eulerPoly_eval_natCast n (n + 1)
  rw [eulerPoly_eval_zero_of_even n hn hn0, pow_succ, hn.neg_one_pow, Nat.cast_succ] at h
  have hcast : (altPowSum n : ℚ) = ∑ j ∈ range (n + 1), (-1) ^ j * (j : ℚ) ^ n := by
    simp [altPowSum]
  rw [hcast]
  linear_combination -h

/-! ## Number theory of the alternating power sum -/

/-- Cast of `altPowSum` into a commutative ring. -/
theorem cast_altPowSum {R : Type*} [CommRing R] (n : ℕ) :
    ((altPowSum n : ℤ) : R) = ∑ j ∈ range (n + 1), (-1) ^ j * (j : R) ^ n := by
  simp [altPowSum]

/-- Odd part: if `q` is odd and `n = 2qk` with `k > 0`, then `q ∣ ∑_{j ≤ n} (-1)^j j^n`,
since `j ↦ (-1)^j j^n` changes sign under `j ↦ j + q` modulo `q`. -/
theorem odd_dvd_altPowSum (n q k : ℕ) (hq : Odd q) (hk : 0 < k) (hn : n = 2 * q * k) :
    (q : ℤ) ∣ altPowSum n := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, cast_altPowSum]
  set f : ℕ → ZMod q := fun j => (-1) ^ j * (j : ZMod q) ^ n with hf
  have hshift : ∀ j, f (q + j) = - f j := by
    intro j
    simp only [hf, pow_add, Nat.cast_add, ZMod.natCast_self, zero_add, hq.neg_one_pow]
    ring
  have hblock : ∑ j ∈ range (2 * q), f j = 0 := by
    rw [two_mul, Finset.sum_range_add]
    simp only [hshift, Finset.sum_neg_distrib, add_neg_cancel]
  have hper : ∀ m j, f (2 * q * m + j) = f j := by
    intro m j
    simp only [hf, pow_add, pow_mul, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero,
      zero_mul, zero_add, neg_one_sq, one_pow, one_mul]
  have hsum : ∀ m, ∑ j ∈ range (2 * q * m), f j = 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih, zero_add]
      simp only [hper, hblock]
  have hlast : f n = 0 := by
    have hn0 : n ≠ 0 := by
      rw [hn]; exact Nat.mul_ne_zero (Nat.mul_ne_zero two_ne_zero hq.pos.ne') hk.ne'
    have hcast : (n : ZMod q) = 0 := by
      rw [hn]; push_cast; rw [ZMod.natCast_self]; ring
    simp only [hf, hcast, zero_pow hn0, mul_zero]
  show ∑ j ∈ range (n + 1), f j = 0
  rw [Finset.sum_range_succ, hlast, add_zero, hn, hsum]

/-- For odd `j`, `2^(e+1) ∣ j^(2^e) - 1`. -/
theorem two_pow_succ_dvd_pow_two_pow_sub_one (j : ℤ) (hj : Odd j) (e : ℕ) :
    (2 : ℤ) ^ (e + 1) ∣ j ^ (2 ^ e) - 1 := by
  induction e with
  | zero => simpa using hj.sub_odd odd_one |>.two_dvd
  | succ e ih =>
    have h2 : (2 : ℤ) ∣ j ^ (2 ^ e) + 1 := (hj.pow.add_odd odd_one).two_dvd
    have hfac : j ^ (2 ^ (e + 1)) - 1 = (j ^ (2 ^ e) - 1) * (j ^ (2 ^ e) + 1) := by ring
    rw [hfac, pow_succ]
    exact mul_dvd_mul ih h2

/-- Two-part: if `n = 2^e q` with `e ≥ 1`, `q > 0`, then `2^e ∣ 2 ∑_{j ≤ n} (-1)^j j^n`
(modulo `2^e`, odd `j` give `-1`, even `j` give `0`, and the sum is `-n/2`). -/
theorem two_pow_dvd_two_mul_altPowSum (n e q : ℕ) (he : 1 ≤ e) (hq : 0 < q) (hn : n = 2 ^ e * q) :
    (2 : ℤ) ^ e ∣ 2 * altPowSum n := by
  have hcast2 : ((2 : ℤ) ^ e) = ((2 ^ e : ℕ) : ℤ) := by push_cast; rfl
  rw [hcast2, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast [cast_altPowSum]
  set f : ℕ → ZMod (2 ^ e) := fun j => (-1) ^ j * (j : ZMod (2 ^ e)) ^ n with hf
  have hen : e ≤ n := by
    rw [hn]
    calc e ≤ 2 ^ e := (Nat.lt_two_pow_self).le
      _ ≤ 2 ^ e * q := Nat.le_mul_of_pos_right _ hq
  have heven : ∀ i, f (2 * i) = 0 := by
    intro i
    have h2n : ((2 : ℕ) : ZMod (2 ^ e)) ^ n = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
      exact Nat.pow_dvd_pow 2 hen
    simp only [hf, Nat.cast_mul, mul_pow, h2n, zero_mul, mul_zero]
  have hodd : ∀ i, f (2 * i + 1) = -1 := by
    intro i
    have hdvd : ((2 ^ e : ℕ) : ℤ) ∣ ((2 * i + 1 : ℕ) : ℤ) ^ n - 1 := by
      have h1 := two_pow_succ_dvd_pow_two_pow_sub_one ((2 * i + 1 : ℕ) : ℤ)
        (by push_cast; exact odd_two_mul_add_one _) e
      have h2 := sub_dvd_pow_sub_pow ((((2 * i + 1 : ℕ) : ℤ)) ^ (2 ^ e)) 1 q
      rw [one_pow, ← pow_mul, ← hn] at h2
      push_cast
      exact (pow_dvd_pow 2 (Nat.le_succ e)).trans (h1.trans h2)
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hdvd
    push_cast at hdvd
    have hpow : ((2 * i + 1 : ℕ) : ZMod (2 ^ e)) ^ n = 1 := by
      push_cast
      exact sub_eq_zero.mp hdvd
    simp only [hf, hpow, mul_one]
    rw [pow_succ, pow_mul]
    norm_num
  have hsum : ∀ m, ∑ j ∈ range (2 * m), f j = -(m : ZMod (2 ^ e)) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Nat.mul_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih, heven, hodd]
      push_cast
      ring
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  have hn2 : n = 2 * (2 ^ e' * q) := by rw [hn]; ring
  have hncast : (n : ZMod (2 ^ (e' + 1))) = 0 := by
    rw [ZMod.natCast_eq_zero_iff, hn]
    exact Dvd.intro q rfl
  show 2 * ∑ j ∈ range (n + 1), f j = 0
  rw [Finset.sum_range_succ, hn2, hsum, heven, add_zero]
  rw [hn2] at hncast
  push_cast at hncast ⊢
  linear_combination -hncast

/-- For even `n ≥ 2`, `n + 1 ∣ 2 ∑_{j ≤ n} (-1)^j j^n` (reflection `j ↦ n + 1 - j`). -/
theorem succ_dvd_two_mul_altPowSum (n : ℕ) (hn : Even n) (hn0 : n ≠ 0) :
    ((n + 1 : ℕ) : ℤ) ∣ 2 * altPowSum n := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast [cast_altPowSum]
  set f : ℕ → ZMod (n + 1) := fun j => (-1) ^ j * (j : ZMod (n + 1)) ^ n with hf
  have hrefl : ∀ j ∈ range n, f (n - 1 - j + 1) = - f (j + 1) := by
    intro j hj
    have hjn : j < n := Finset.mem_range.mp hj
    have hidx : n - 1 - j + 1 = n - j := by omega
    have hc : ((n - j : ℕ) : ZMod (n + 1)) = -((j + 1 : ℕ) : ZMod (n + 1)) := by
      have h0 : ((n - j : ℕ) : ZMod (n + 1)) + ((j + 1 : ℕ) : ZMod (n + 1)) = 0 := by
        rw [← Nat.cast_add, show n - j + (j + 1) = n + 1 by omega]
        exact_mod_cast ZMod.natCast_self (n + 1)
      linear_combination h0
    have hsign : ((-1 : ZMod (n + 1)) ^ (n - j)) = -(-1) ^ (j + 1) := by
      have h0 : ((-1 : ZMod (n + 1)) ^ (n - j)) * (-1) ^ j = 1 := by
        rw [← pow_add, show n - j + j = n by omega, hn.neg_one_pow]
      have hsq : ((-1 : ZMod (n + 1)) ^ j) * (-1) ^ j = 1 := by
        rw [← mul_pow]; norm_num
      rw [pow_succ]
      linear_combination (-1 : ZMod (n + 1)) ^ j * h0 - ((-1 : ZMod (n + 1)) ^ (n - j)) * hsq
    simp only [hf, hidx, hc, hsign, hn.neg_pow]
    ring
  have hT : ∑ j ∈ range n, f (j + 1) = - ∑ j ∈ range n, f (j + 1) := by
    conv_lhs => rw [← Finset.sum_range_reflect (fun j => f (j + 1)) n]
    rw [Finset.sum_congr rfl hrefl, Finset.sum_neg_distrib]
  have hf0 : f 0 = 0 := by simp [hf, zero_pow hn0]
  show 2 * ∑ j ∈ range (n + 1), f j = 0
  rw [Finset.sum_range_succ', hf0, add_zero]
  linear_combination hT
/-- For even `n ≥ 2`, `n ∣ 2 ∑_{j ≤ n} (-1)^j j^n`. -/
theorem self_dvd_two_mul_altPowSum (n : ℕ) (hn : Even n) (hn0 : n ≠ 0) :
    (n : ℤ) ∣ 2 * altPowSum n := by
  obtain ⟨e, q, hq, hnq⟩ := Nat.exists_eq_two_pow_mul_odd hn0
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h
      rw [pow_zero, one_mul] at hnq
      exact absurd (hnq ▸ hn) (Nat.not_even_iff_odd.mpr hq)
    · exact h
  have h2 : (2 : ℤ) ^ e ∣ 2 * altPowSum n := two_pow_dvd_two_mul_altPowSum n e q he hq.pos hnq
  have hqd : (q : ℤ) ∣ 2 * altPowSum n := by
    refine Dvd.dvd.mul_left (odd_dvd_altPowSum n q (2 ^ (e - 1)) hq (by positivity) ?_) 2
    rw [hnq]
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ]
    ring
  have hcop : IsCoprime ((2 : ℤ) ^ e) (q : ℤ) := by
    have : IsCoprime ((2 ^ e : ℕ) : ℤ) (q : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr hq))
    simpa using this
  have hmul := hcop.mul_dvd h2 hqd
  have hncast : (n : ℤ) = 2 ^ e * q := by rw [hnq]; push_cast; rfl
  rw [hncast]
  exact hmul

/-- For even `n ≥ 2`, `n (n + 1) ∣ 2 ∑_{j ≤ n} (-1)^j j^n`. -/
theorem mul_succ_dvd_two_mul_altPowSum (n : ℕ) (hn : Even n) (hn0 : n ≠ 0) :
    ((n : ℤ) * (n + 1)) ∣ 2 * altPowSum n := by
  have hcop : IsCoprime (n : ℤ) ((n + 1 : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr (Nat.coprime_self_add_right.mpr (Nat.coprime_one_right n))
  have h := hcop.mul_dvd (self_dvd_two_mul_altPowSum n hn hn0) (succ_dvd_two_mul_altPowSum n hn hn0)
  push_cast at h
  exact h

/-! ## Examples -/

/-- `E_0(x) = 1`. -/
theorem eulerPoly_zero_eval (x : ℚ) : (eulerPoly 0).eval x = 1 := by
  rw [eulerPoly_eval_eq]
  simp

/-- `E_1(x) = x - 1/2`. -/
theorem eulerPoly_one_eval (x : ℚ) : (eulerPoly 1).eval x = x - 1 / 2 := by
  rw [eulerPoly_eval_eq]
  simp [eulerPoly_zero_eval]

/-- `E_2(x) = x^2 - x`. -/
theorem eulerPoly_two_eval (x : ℚ) : (eulerPoly 2).eval x = x ^ 2 - x := by
  rw [eulerPoly_eval_eq]
  simp only [one_div, sum_range_succ, range_one, sum_singleton, Nat.choose_zero_right,
    Nat.cast_one, eulerPoly_zero_eval, mul_one, Nat.choose_succ_self_right, Nat.reduceAdd,
    Nat.cast_ofNat, eulerPoly_one_eval]
  ring

/-- `E_3(x) = x^3 - (3/2) x^2 + 1/4`. -/
theorem eulerPoly_three_eval (x : ℚ) :
    (eulerPoly 3).eval x = x ^ 3 - 3 / 2 * x ^ 2 + 1 / 4 := by
  rw [eulerPoly_eval_eq]
  simp only [one_div, sum_range_succ, range_one, sum_singleton, Nat.choose, Nat.cast_one,
    eulerPoly_zero_eval, mul_one, add_zero, Nat.reduceAdd, Nat.cast_ofNat, eulerPoly_one_eval,
    eulerPoly_two_eval]
  ring

/-- `E_4(x) = x^4 - 2 x^3 + x`. -/
theorem eulerPoly_four_eval (x : ℚ) : (eulerPoly 4).eval x = x ^ 4 - 2 * x ^ 3 + x := by
  rw [eulerPoly_eval_eq]
  simp only [one_div, sum_range_succ, range_one, sum_singleton, Nat.choose, Nat.cast_one,
    eulerPoly_zero_eval, mul_one, add_zero, Nat.reduceAdd, Nat.cast_ofNat, eulerPoly_one_eval,
    eulerPoly_two_eval, eulerPoly_three_eval]
  ring

/-- `v₂` of an odd number is zero (helper for the examples). -/
theorem padicValNat_two_eq_zero_of_odd (m : ℕ) (hm : Odd m) : padicValNat 2 m = 0 :=
  padicValNat.eq_zero_of_not_dvd (by rw [← even_iff_two_dvd, Nat.not_even_iff_odd]; exact hm)

example : a 0 = 1 := by
  rw [a, eulerPoly_zero_eval, padicValNat_two_eq_zero_of_odd 1 odd_one]
  norm_num
example : a 1 = 3 := by
  rw [a, eulerPoly_one_eval, show padicValNat 2 (1 + 1) = 1 from padicValNat.self one_lt_two]
  norm_num
example : a 2 = 6 := by
  rw [a, eulerPoly_two_eval, padicValNat_two_eq_zero_of_odd 3 (by decide)]
  norm_num
example : a 3 = 161 := by
  rw [a, eulerPoly_three_eval, show padicValNat 2 (3 + 1) = 2 by
    rw [show 3 + 1 = 2 ^ 2 by rfl, padicValNat.prime_pow]]
  norm_num
example : a 4 = 380 := by
  rw [a, eulerPoly_four_eval, padicValNat_two_eq_zero_of_odd 5 (by decide)]
  norm_num

/-! ## The conjecture -/

/-- Luschny’s conjecture (A291982): for even `n ≥ 2`, `n(n+1)` divides
`a(n) = E_n(n+1)·2^{v₂(n+1)}`. Divisibility is expressed by an integer
quotient, so it also asserts integrality. Since `n+1` is odd,
`a(n) = E_n(n+1)` in this range. -/
theorem a291982_conjecture (n : ℕ) (hn : Even n) (h2 : 2 ≤ n) :
    ∃ m : ℤ, a n = ((n * (n + 1) : ℤ) : ℚ) * m := by
  have hn0 : n ≠ 0 := by omega
  have hodd : ¬ 2 ∣ n + 1 := by
    rw [← even_iff_two_dvd, Nat.even_add_one, not_not]
    exact hn
  have hv : padicValNat 2 (n + 1) = 0 := padicValNat.eq_zero_of_not_dvd hodd
  obtain ⟨m, hm⟩ := mul_succ_dvd_two_mul_altPowSum n hn hn0
  refine ⟨m, ?_⟩
  rw [a, hv, pow_zero, mul_one, eulerPoly_eval_succ_eq n hn hn0]
  have hmq : ((2 * altPowSum n : ℤ) : ℚ) = (((n : ℤ) * (n + 1) * m : ℤ) : ℚ) := by rw [hm]
  push_cast at hmq ⊢
  exact hmq

/-- Non-vacuity: the hypotheses are met at `n = 2`, where `a(2) = 6 = 2 · 3 · 1`. -/
example : ∃ m : ℤ, a 2 = ((2 * (2 + 1) : ℤ) : ℚ) * m :=
  a291982_conjecture 2 even_two le_rfl

end Candidates.A291982EulerPolynomialSum
