/-
# A050931 — Granvik: vanishing of a Möbius-weighted cube-root-of-unity sum

## OEIS source (retrieved with `oeis show A050931`, 2026-10-21)

```
NAME:     Numbers having a prime factor congruent to 1 mod 6.
TERMS:    7,13,14,19,21,26,28,31,35,37,38,39,42,43,49,52,56,57,61,62,63,65,67,
          70,73,74,76,77,78,79,84,86,91,93,95,97,98,103,104,105,109,111,112,...
COMMENT (the conjecture):
  Conjecture: Numbers m such that abs(Sum_{k=1..m} [k|m]*A008683(k)*(-1)^(2*k/3))
  = 0. - _Mats Granvik_, Jul 06 2024
```

Here `A008683` is the Möbius function `μ` and `(-1)^(2*k/3)` is the principal
value `exp(log(-1) · 2k/3) = exp(2πik/3) = ω^k` with `ω = exp(2πi/3)`; this file
states the conjecture with that literal complex power (`Complex.cpow`) and proves
the bridge `(-1)^(2k/3) = ω^k`.

## Status

Triage: open — no proof in the entry or in the literature as far as the triage
could tell (floating-point check of all `m ≤ 5000`).  Re-validated here by
exact arithmetic in `ℤ[ω]` for all `1 ≤ m ≤ 30000` (Sage, no mismatches).
This module proves the conjecture in full (`granvik`), sorry-free.

## Proof (formalized below)

With `χ` the nontrivial character mod 3 and `χ₀` the principal one,
`2ω^d = 2 - 3χ₀(d) + (ω - ω²)χ(d)` for every `d`.  Hence, for `m ≥ 1`,
`2 S(m) = 2[m = 1] - 3 ∏_{p ∣ m}(1 - χ₀(p)) + (ω - ω²) ∏_{p ∣ m}(1 - χ(p))`,
using `∑_{d ∣ m} μ(d) f(d) = ∏_{p ∣ m} (1 - f(p))` for multiplicative `f`.
A prime `p ≡ 1 (mod 6)` dividing `m` kills both products and forces `m ≠ 1`;
otherwise every factor `1 - χ(p)` is `1` or `2`, so the imaginary part
`√3 · ∏(1 - χ(p))` of `2 S(m)` is nonzero.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A050931GranvikExpHas

open ArithmeticFunction Complex
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-! ## Definition layer -/

/-- Membership predicate of A050931: `m` has a prime factor congruent to `1` mod `6`
(the entry's NAME; the sequence lists the positive `m` satisfying it). -/
def HasPrimeFactorOneModSix (m : ℕ) : Prop :=
  ∃ p, p.Prime ∧ p ∣ m ∧ p % 6 = 1

/-- Granvik's sum, literally as in the OEIS comment:
`Sum_{k=1..m} [k|m] * μ(k) * (-1)^(2k/3)`, with `(-1)^(2k/3)` the principal complex
power. -/
noncomputable def granvikSum (m : ℕ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 m, if k ∣ m then (μ k : ℂ) * (-1 : ℂ) ^ (2 * (k : ℂ) / 3) else 0

/-- The primitive cube root of unity `ω = exp(2πi/3)`. -/
noncomputable def ω : ℂ := Complex.exp (2 * Real.pi * I / 3)

/-! ## Ground truth -/

/-- Bounded reformulation of `HasPrimeFactorOneModSix`, used for decidable checks. -/
theorem hasPrimeFactorOneModSix_iff_bounded {m : ℕ} (hm : 0 < m) :
    HasPrimeFactorOneModSix m ↔
      ∃ p ∈ Finset.range (m + 1), p.Prime ∧ p ∣ m ∧ p % 6 = 1 := by
  constructor
  · rintro ⟨p, hp, hpm, h6⟩
    exact ⟨p, Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.le_of_dvd hm hpm)), hp, hpm, h6⟩
  · rintro ⟨p, -, hp, hpm, h6⟩
    exact ⟨p, hp, hpm, h6⟩

/-- The positive `m ≤ 40` with a prime factor `≡ 1 (mod 6)` are exactly the first
listed terms `7, 13, 14, 19, 21, 26, 28, 31, 35, 37, 38, 39` of A050931. -/
example : ∀ m ∈ Finset.Icc 1 40,
    (∃ p ∈ Finset.range (m + 1), p.Prime ∧ p ∣ m ∧ p % 6 = 1) ↔
      m ∈ ({7, 13, 14, 19, 21, 26, 28, 31, 35, 37, 38, 39} : Finset ℕ) := by
  decide

/-- The `k = 1` term: `granvikSum 1 = (-1)^(2/3)`. -/
example : granvikSum 1 = (-1 : ℂ) ^ (2 * ((1 : ℕ) : ℂ) / 3) := by
  simp [granvikSum]

/-! ## Möbius sums of multiplicative functions -/

/-- For a multiplicative `f : ℕ → ℤ` and `n ≠ 0`,
`∑_{d ∣ n} μ(d) f(d) = ∏_{p ∣ n} (1 - f(p))`. -/
theorem sum_moebius_mul_eq_prod {f : ArithmeticFunction ℤ} (hf : f.IsMultiplicative)
    {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, μ d * f d = ∏ p ∈ n.primeFactors, (1 - f p) := by
  have hF : ((pmul (μ : ArithmeticFunction ℤ) f) * (ζ : ArithmeticFunction ℤ)).IsMultiplicative :=
    (isMultiplicative_moebius.intCast.pmul hf).mul isMultiplicative_zeta.natCast
  have hG : (prodPrimeFactors (fun p => 1 - f p)).IsMultiplicative :=
    IsMultiplicative.prodPrimeFactors _
  have hEq : (pmul (μ : ArithmeticFunction ℤ) f) * (ζ : ArithmeticFunction ℤ) =
      prodPrimeFactors (fun p => 1 - f p) := by
    rw [IsMultiplicative.eq_iff_eq_on_prime_powers _ hF _ hG]
    intro p i hp
    rw [coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp,
      prodPrimeFactors_apply (pow_ne_zero _ hp.ne_zero)]
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [hf.map_one]
    · rw [Nat.primeFactors_prime_pow hi.ne' hp, Finset.prod_singleton]
      induction i, hi using Nat.le_induction with
      | base =>
        simp only [pmul_apply, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
          pow_zero, pow_one, moebius_apply_one, moebius_apply_prime hp, hf.map_one]
        ring
      | succ k hk ih =>
        rw [Finset.sum_range_succ, ih, pmul_apply, moebius_apply_prime_pow hp (by omega)]
        simp only [Nat.add_eq_right, Int.reduceNeg, ite_mul, neg_mul, one_mul, zero_mul,
          add_eq_left, ite_eq_right_iff, neg_eq_zero]
        omega
  have hn' := congrArg (fun F : ArithmeticFunction ℤ => F n) hEq
  simp only [coe_mul_zeta_apply, pmul_apply, prodPrimeFactors_apply hn] at hn'
  simpa using hn'

/-! ## Characters mod 3 -/

/-- The nontrivial Dirichlet character mod 3 as an arithmetic function:
`χ(n) = 1, -1, 0` according as `n ≡ 1, 2, 0 (mod 3)`. -/
def chi : ArithmeticFunction ℤ :=
  ⟨fun n => if n % 3 = 1 then 1 else if n % 3 = 2 then -1 else 0, by simp⟩

/-- The principal Dirichlet character mod 3: `χ₀(n) = 0` if `3 ∣ n`, else `1`. -/
def chiZero : ArithmeticFunction ℤ :=
  ⟨fun n => if n % 3 = 0 then 0 else 1, by simp⟩

/-- Unfolding lemma for `chi`. -/
theorem chi_apply (n : ℕ) :
    chi n = if n % 3 = 1 then 1 else if n % 3 = 2 then -1 else 0 := rfl

/-- Unfolding lemma for `chiZero`. -/
theorem chiZero_apply (n : ℕ) : chiZero n = if n % 3 = 0 then 0 else 1 := rfl

/-- `χ` is (completely) multiplicative. -/
theorem isMultiplicative_chi : chi.IsMultiplicative := by
  refine ⟨by simp [chi_apply], fun {a b} _ => ?_⟩
  simp only [chi_apply, Nat.mul_mod a b]
  have ha := Nat.mod_lt a (by norm_num : 3 > 0)
  have hb := Nat.mod_lt b (by norm_num : 3 > 0)
  interval_cases (a % 3) <;> interval_cases (b % 3) <;> simp

/-- `χ₀` is (completely) multiplicative. -/
theorem isMultiplicative_chiZero : chiZero.IsMultiplicative := by
  refine ⟨by simp [chiZero_apply], fun {a b} _ => ?_⟩
  simp only [chiZero_apply, Nat.mul_mod a b]
  have ha := Nat.mod_lt a (by norm_num : 3 > 0)
  have hb := Nat.mod_lt b (by norm_num : 3 > 0)
  interval_cases (a % 3) <;> interval_cases (b % 3) <;> simp


/-! ## The cube root of unity `ω` -/

/-- `ω` is a primitive cube root of unity. -/
theorem isPrimitiveRoot_ω : IsPrimitiveRoot ω 3 := by
  have h := Complex.isPrimitiveRoot_exp 3 (by norm_num)
  simpa [ω] using h

/-- `ω³ = 1`. -/
theorem ω_pow_three : ω ^ 3 = 1 := isPrimitiveRoot_ω.pow_eq_one

/-- `1 + ω + ω² = 0`. -/
theorem one_add_ω_add_sq : 1 + ω + ω ^ 2 = 0 := by
  have h := isPrimitiveRoot_ω.geom_sum_eq_zero (by norm_num)
  simpa [Finset.sum_range_succ] using h

/-- `Im ω = sin(2π/3) > 0`. -/
theorem zero_lt_ω_im : 0 < ω.im := by
  have him : ω.im = Real.sin (2 * Real.pi / 3) := by
    rw [ω, Complex.exp_im]
    have hre : (2 * (Real.pi : ℂ) * I / 3).re = 0 := by simp
    have himz : (2 * (Real.pi : ℂ) * I / 3).im = 2 * Real.pi / 3 := by simp
    rw [hre, himz, Real.exp_zero, one_mul]
  rw [him]
  apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [Real.pi_pos]

/-- The principal value `(-1)^(2k/3)` equals `ω^k`. -/
theorem neg_one_cpow_eq_ω_pow (k : ℕ) : (-1 : ℂ) ^ (2 * (k : ℂ) / 3) = ω ^ k := by
  rw [Complex.cpow_def_of_ne_zero (by norm_num), Complex.log_neg_one, ω,
    ← Complex.exp_nat_mul]
  congr 1
  ring

/-- Decomposition of `ω^d` through the characters mod 3:
`2 ω^d = 2 - 3 χ₀(d) + (ω - ω²) χ(d)`. -/
theorem two_mul_ω_pow (d : ℕ) :
    2 * ω ^ d = 2 - 3 * (chiZero d : ℂ) + (ω - ω ^ 2) * (chi d : ℂ) := by
  have hd : ω ^ d = ω ^ (d % 3) := by
    conv_lhs => rw [← Nat.div_add_mod d 3, pow_add, pow_mul, ω_pow_three, one_pow, one_mul]
  have h3 := Nat.mod_lt d (by norm_num : 3 > 0)
  rw [hd, chi_apply, chiZero_apply]
  have hsum := one_add_ω_add_sq
  interval_cases (d % 3) <;>
    simp only [pow_zero, pow_one, mul_one, mul_zero, mul_neg, neg_sub, sub_zero, add_zero,
      ↓reduceIte, Int.cast_zero, Int.cast_one, Int.cast_neg, Int.reduceNeg, zero_ne_one,
      one_ne_zero, OfNat.zero_ne_ofNat, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one] <;>
    linear_combination hsum


/-! ## Reduction of Granvik's sum -/

/-- For `m ≥ 1`, Granvik's sum is the divisor sum `∑_{d ∣ m} μ(d) ω^d`. -/
theorem granvikSum_eq_sum_divisors {m : ℕ} (hm : 0 < m) :
    granvikSum m = ∑ d ∈ m.divisors, (μ d : ℂ) * ω ^ d := by
  have hset : m.divisors = (Finset.Icc 1 m).filter (· ∣ m) := by
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hdm, -⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hdm hm, Nat.le_of_dvd hm hdm⟩, hdm⟩
    · rintro ⟨-, hdm⟩
      exact ⟨hdm, hm.ne'⟩
  rw [granvikSum, hset, Finset.sum_filter]
  simp_rw [neg_one_cpow_eq_ω_pow]

/-- `∑_{d ∣ m} μ(d) = 0` for `m ∉ {0, 1}`. -/
theorem sum_divisors_moebius_eq_zero {m : ℕ} (hm : m ≠ 1) :
    ∑ d ∈ m.divisors, μ d = 0 := by
  have h := congrArg (fun F : ArithmeticFunction ℤ => F m) moebius_mul_coe_zeta
  simp only [coe_mul_zeta_apply, one_apply_ne hm] at h
  exact h

/-- `2 ∑_{d ∣ m} μ(d) ω^d = 2 A - 3 B + (ω - ω²) C` with the integer sums
`A = ∑ μ(d)`, `B = ∑ μ(d) χ₀(d)`, `C = ∑ μ(d) χ(d)` over `d ∣ m`. -/
theorem two_mul_sum_divisors (m : ℕ) :
    2 * ∑ d ∈ m.divisors, (μ d : ℂ) * ω ^ d =
      2 * ((∑ d ∈ m.divisors, μ d : ℤ) : ℂ)
        - 3 * ((∑ d ∈ m.divisors, μ d * chiZero d : ℤ) : ℂ)
        + (ω - ω ^ 2) * ((∑ d ∈ m.divisors, μ d * chi d : ℤ) : ℂ) := by
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  linear_combination (μ d : ℂ) * two_mul_ω_pow d


/-! ## The conjecture -/

/-- A prime `p` with `p % 3 = 1` satisfies `p % 6 = 1`. -/
theorem mod_six_eq_one_of_prime {p : ℕ} (hp : p.Prime) (h3 : p % 3 = 1) : p % 6 = 1 := by
  rcases hp.eq_two_or_odd' with rfl | hodd
  · norm_num at h3
  · obtain ⟨k, rfl⟩ := hodd
    omega

/-- **Granvik's conjecture (A050931, Mats Granvik, Jul 06 2024)** — proved.

Verbatim: "Conjecture: Numbers m such that
abs(Sum_{k=1..m} [k|m]*A008683(k)*(-1)^(2*k/3)) = 0."

That is: for every `m ≥ 1`, `|∑_{k=1}^{m} [k ∣ m] μ(k) (-1)^{2k/3}| = 0` (principal
complex power) if and only if `m` has a prime factor congruent to `1` mod `6`, i.e.
`m` is a term of A050931.  The guard `0 < m` matches the sequence's range `m ≥ 1`. -/
theorem granvik (m : ℕ) (hm : 0 < m) :
    ‖granvikSum m‖ = 0 ↔ HasPrimeFactorOneModSix m := by
  rw [norm_eq_zero, granvikSum_eq_sum_divisors hm]
  have h2 := two_mul_sum_divisors m
  rw [sum_moebius_mul_eq_prod isMultiplicative_chiZero hm.ne',
    sum_moebius_mul_eq_prod isMultiplicative_chi hm.ne'] at h2
  constructor
  · intro hS
    by_contra hno
    have hpos : 0 < ∏ p ∈ m.primeFactors, (1 - chi p) := by
      refine Finset.prod_pos fun p hp => ?_
      have hpp := Nat.prime_of_mem_primeFactors hp
      have h3 : p % 3 ≠ 1 := fun h3 =>
        hno ⟨p, hpp, Nat.dvd_of_mem_primeFactors hp, mod_six_eq_one_of_prime hpp h3⟩
      rw [chi_apply]
      split_ifs <;> omega
    have hωsub : ω - ω ^ 2 = 2 * ω + 1 := by linear_combination -one_add_ω_add_sq
    rw [hS, hωsub] at h2
    generalize ∑ d ∈ m.divisors, μ d = A at h2
    generalize ∏ p ∈ m.primeFactors, (1 - chiZero p) = B at h2
    generalize ∏ p ∈ m.primeFactors, (1 - chi p) = C at h2 hpos
    have him := congrArg Complex.im h2
    simp only [mul_zero, Complex.zero_im, Complex.sub_im, Complex.add_im, Complex.mul_im,
      Complex.intCast_re, Complex.intCast_im, Complex.re_ofNat, Complex.im_ofNat,
      Complex.one_im] at him
    have hCpos : (0 : ℝ) < C := by exact_mod_cast hpos
    nlinarith [zero_lt_ω_im]
  · rintro ⟨p, hp, hpm, h6⟩
    have hpf : p ∈ m.primeFactors := Nat.mem_primeFactors.2 ⟨hp, hpm, hm.ne'⟩
    have hp3 : p % 3 = 1 := by omega
    have hB : ∏ q ∈ m.primeFactors, (1 - chiZero q) = 0 :=
      Finset.prod_eq_zero hpf (by simp [chiZero_apply, hp3])
    have hC : ∏ q ∈ m.primeFactors, (1 - chi q) = 0 :=
      Finset.prod_eq_zero hpf (by simp [chi_apply, hp3])
    have hm1 : m ≠ 1 := by
      rintro rfl
      exact hp.one_lt.ne' (Nat.dvd_one.1 hpm)
    rw [hB, hC, sum_divisors_moebius_eq_zero hm1] at h2
    simpa using h2


/-- Non-vacuity, vanishing side: `m = 7` (prime `≡ 1 mod 6`) gives a zero sum. -/
example : ‖granvikSum 7‖ = 0 :=
  (granvik 7 (by norm_num)).2 ⟨7, by norm_num, dvd_rfl, rfl⟩

/-- Non-vacuity, non-vanishing side: `m = 6` has no prime factor `≡ 1 mod 6`. -/
example : ‖granvikSum 6‖ ≠ 0 := by
  rw [Ne, granvik 6 (by norm_num), hasPrimeFactorOneModSix_iff_bounded (by norm_num)]
  decide

end Candidates.A050931GranvikExpHas
