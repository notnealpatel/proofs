/-
# A327123 — Yanev–Kotesovec: coefficient sum of `phi(k) x^k / (1 + x^(2k))`

## OEIS source (retrieved with `oeis show A327123`, 2026-10-21)

```
NAME:     Expansion of Sum_{k>=1} phi(k) * x^k / (1 + x^(2*k)), where phi = A000010.
TERMS:    1,1,1,2,5,1,5,4,5,5,9,2,13,5,5,8,17,5,17,10,5,9,21,4,25,13,13,10,29,5,29,
          16,9,17,25,10,37,17,13,20,41,5,41,18,25,21,45,8,37,25,17,26,53,13,45,20,...
COMMENT:  Moebius transform of A050469.
FORMULA (the conjecture):
  Conjecture: a(n) = Sum_{k=1..n} sin(GCD(k,n) * Pi/2). - _Velin Yanev_ and
  _Vaclav Kotesovec_, Jun 01 2024
```

## Status

Triage: open (no proof in the entry or the literature found by the triage).
Computation: identity checked for `n = 1..1200` by direct series expansion
(Python, 2026-10-21).  Proved below; the argument is the standard one:
`x^k / (1 + x^(2k)) = Sum_{d>=1} chi4(d) x^(k d)` gives `a = phi * chi4`
(Dirichlet convolution), the Pillai-type regrouping
`Sum_{k=1..n} f(gcd(k,n)) = Sum_{d | n} phi(n/d) f(d)` turns the right side
into the same convolution, and `sin(m Pi / 2) = chi4(m)`.

## Definition layer

`a n` is the coefficient of `X^n` in `Sum_{k=1..n} phi(k) X^k (1 + X^(2k))⁻¹`
in `ℚ⟦X⟧`; `coeff_sum_summand_of_le` shows any longer truncation gives the
same coefficient.  `chi4` is Mathlib's `ZMod.χ₄`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A327123CoefficientSumPhi

open PowerSeries Finset

/-- The `k`-th summand `phi(k) * x^k / (1 + x^(2k))` of the generating function of A327123,
as a formal power series over `ℚ`. -/
noncomputable def summand (k : ℕ) : ℚ⟦X⟧ :=
  (Nat.totient k : ℚ⟦X⟧) * X ^ k * (1 + X ^ (2 * k))⁻¹

/-- `a(n)` (A327123): the coefficient of `x^n` in `Sum_{k>=1} phi(k) x^k / (1 + x^(2k))`.
Summands with `k > n` are divisible by `x^(n+1)` and do not contribute to the coefficient of
`x^n`, so the sum is truncated at `k = n` (see `coeff_sum_summand_of_le` for stability). -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n (∑ k ∈ Icc 1 n, summand k)

/-- The series `Sum_{d>=1} chi4(d) x^(k d)`, the claimed expansion of `x^k / (1 + x^(2k))`. -/
noncomputable def chiSeries (k : ℕ) : ℚ⟦X⟧ :=
  mk fun m => if k ∣ m then ((ZMod.χ₄ (m / k : ℕ) : ℤ) : ℚ) else 0

/-- `chi4(d + 2) = -chi4(d)`. -/
lemma chi4_add_two (d : ℕ) : ZMod.χ₄ ((d + 2 : ℕ) : ZMod 4) = -ZMod.χ₄ (d : ZMod 4) := by
  rw [ZMod.χ₄_nat_eq_if_mod_four, ZMod.χ₄_nat_eq_if_mod_four]
  have h4 : d % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have h2 : (d + 2) % 4 = (d % 4 + 2) % 4 := by omega
  interval_cases hd : d % 4 <;> simp [h2] <;> omega

/-- Coefficient of `chiSeries k` at `k * d` is `chi4(d)`. -/
lemma coeff_chiSeries_mul {k : ℕ} (hk : 0 < k) (d : ℕ) :
    coeff (k * d) (chiSeries k) = ((ZMod.χ₄ (d : ℕ) : ℤ) : ℚ) := by
  simp [chiSeries, coeff_mk, Nat.mul_div_cancel_left d hk]

/-- Coefficient of `chiSeries k` off the multiples of `k` vanishes. -/
lemma coeff_chiSeries_of_not_dvd {k m : ℕ} (h : ¬ k ∣ m) : coeff m (chiSeries k) = 0 := by
  simp [chiSeries, coeff_mk, h]

/-- `chiSeries k * (1 + x^(2k)) = x^k` for `k ≥ 1`. -/
lemma chiSeries_mul (k : ℕ) (hk : 0 < k) : chiSeries k * (1 + X ^ (2 * k)) = X ^ k := by
  ext m
  rw [mul_add, mul_one, map_add, coeff_mul_X_pow', coeff_X_pow]
  by_cases hdvd : k ∣ m
  · obtain ⟨d, rfl⟩ := hdvd
    rcases d with _ | _ | d
    · rw [coeff_chiSeries_mul hk]
      have hn : ¬ 2 * k ≤ k * 0 := by omega
      have hne : k * 0 ≠ k := by omega
      simp only [hn, hne, if_false, add_zero]
      decide
    · rw [coeff_chiSeries_mul hk]
      have hn : ¬ 2 * k ≤ k := by omega
      simp only [zero_add, mul_one, if_true, hn, if_false, add_zero]
      decide
    · have hle : 2 * k ≤ k * (d + 2) := by nlinarith
      have hsub : k * (d + 2) - 2 * k = k * d := by
        rw [Nat.mul_add]; omega
      rw [if_pos hle, hsub, coeff_chiSeries_mul hk, coeff_chiSeries_mul hk, chi4_add_two]
      have hne : k * (d + 2) ≠ k := by nlinarith
      simp [hne]
  · have hne : m ≠ k := fun h => hdvd (h ▸ dvd_refl k)
    rw [coeff_chiSeries_of_not_dvd hdvd, if_neg hne]
    split_ifs with hle
    · have hnd : ¬ k ∣ m - 2 * k := by
        intro h
        apply hdvd
        have : k ∣ m - 2 * k + 2 * k := dvd_add h (dvd_mul_left k 2)
        rwa [Nat.sub_add_cancel hle] at this
      rw [coeff_chiSeries_of_not_dvd hnd, add_zero]
    · rw [add_zero]

/-- `x^k / (1 + x^(2k)) = Sum_{d>=1} chi4(d) x^(k d)` for `k ≥ 1`. -/
lemma X_pow_mul_inv_eq (k : ℕ) (hk : 0 < k) :
    (X : ℚ⟦X⟧) ^ k * (1 + X ^ (2 * k))⁻¹ = chiSeries k := by
  have hc : constantCoeff (1 + (X : ℚ⟦X⟧) ^ (2 * k)) ≠ 0 := by
    simp [hk.ne']
  symm
  rw [eq_mul_inv_iff_mul_eq hc, chiSeries_mul k hk]

/-- Coefficient of `x^n` in the `k`-th summand: `phi(k) * chi4(n/k)` if `k ∣ n`, else `0`. -/
lemma coeff_summand {k : ℕ} (hk : 0 < k) (n : ℕ) :
    coeff n (summand k) =
      if k ∣ n then (Nat.totient k : ℚ) * ((ZMod.χ₄ (n / k : ℕ) : ℤ) : ℚ) else 0 := by
  have hs : summand k = PowerSeries.C (Nat.totient k : ℚ) * chiSeries k := by
    rw [summand, mul_assoc, X_pow_mul_inv_eq k hk, map_natCast]
  rw [hs, coeff_C_mul, chiSeries, coeff_mk]
  split_ifs <;> simp

/-- Divisor-sum form: `a(n) = Sum_{d | n} phi(n/d) chi4(d)`. -/
lemma a_eq_sum_divisors (n : ℕ) :
    a n = ∑ d ∈ n.divisors, (Nat.totient (n / d) : ℚ) * ((ZMod.χ₄ (d : ℕ) : ℤ) : ℚ) := by
  have h1 : a n = ∑ k ∈ Icc 1 n,
      (if k ∣ n then (Nat.totient k : ℚ) * ((ZMod.χ₄ (n / k : ℕ) : ℤ) : ℚ) else 0) := by
    rw [a, map_sum]
    refine sum_congr rfl fun k hk => ?_
    exact coeff_summand (by simp only [mem_Icc] at hk; omega) n
  have h2 : (Icc 1 n).filter (· ∣ n) = n.divisors := by
    ext k
    simp only [mem_filter, mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hk1, hkn⟩, hdvd⟩
      exact ⟨hdvd, by omega⟩
    · rintro ⟨hdvd, hn⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hn), Nat.le_of_dvd
        (Nat.pos_of_ne_zero hn) hdvd⟩, hdvd⟩
  rw [h1, ← sum_filter, h2, ← Nat.sum_div_divisors]
  refine sum_congr rfl fun d hd => ?_
  rw [Nat.div_div_self (Nat.dvd_of_mem_divisors hd) (Nat.mem_divisors.1 hd).2]

/-- Pillai-type regrouping: `Sum_{k=1..n} f(gcd(k,n)) = Sum_{d | n} phi(n/d) f(d)`. -/
lemma sum_Icc_gcd_eq {M : Type*} [AddCommGroup M] (n : ℕ) (f : ℕ → M) :
    ∑ k ∈ Icc 1 n, f (Nat.gcd k n) = ∑ d ∈ n.divisors, Nat.totient (n / d) • f d := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  have hshift : ∑ k ∈ Icc 1 n, f (Nat.gcd k n) = ∑ k ∈ range n, f (Nat.gcd n k) := by
    have hA : ∑ k ∈ range (n + 1), f (Nat.gcd n k) =
        ∑ k ∈ range n, f (Nat.gcd n (k + 1)) + f (Nat.gcd n 0) := sum_range_succ' _ _
    have hB : ∑ k ∈ range (n + 1), f (Nat.gcd n k) =
        ∑ k ∈ range n, f (Nat.gcd n k) + f (Nat.gcd n n) := sum_range_succ _ _
    have hC : ∑ k ∈ Icc 1 n, f (Nat.gcd k n) = ∑ k ∈ range n, f (Nat.gcd n (k + 1)) := by
      rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
      refine sum_congr (by simp) fun k _ => ?_
      rw [Nat.gcd_comm, add_comm]
    rw [hC]
    rw [Nat.gcd_zero_right] at hA
    rw [Nat.gcd_self] at hB
    rw [hA] at hB
    exact add_right_cancel hB
  rw [hshift, ← sum_fiberwise_of_maps_to (s := range n) (t := n.divisors)
    (g := fun k => Nat.gcd n k) (fun k _ => Nat.mem_divisors.2 ⟨Nat.gcd_dvd_left n k, hn.ne'⟩)]
  refine sum_congr rfl fun d hd => ?_
  rw [Nat.totient_div_of_dvd (Nat.dvd_of_mem_divisors hd), ← sum_const]
  refine sum_congr rfl fun k hk => ?_
  rw [(mem_filter.1 hk).2]

/-- `sin(m * Pi / 2) = chi4(m)` for natural `m`. -/
lemma sin_nat_mul_pi_div_two (m : ℕ) :
    Real.sin ((m : ℝ) * Real.pi / 2) = ((ZMod.χ₄ (m : ZMod 4) : ℤ) : ℝ) := by
  have hm : (m : ℝ) * Real.pi / 2 = ((m % 4 : ℕ) : ℝ) * Real.pi / 2 + (m / 4 : ℕ) * (2 * Real.pi) := by
    have h : ((m : ℕ) : ℝ) = ((m % 4 : ℕ) : ℝ) + 4 * ((m / 4 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mod_add_div m 4).symm
    rw [h]; ring
  have hχ : ZMod.χ₄ (m : ZMod 4) = ZMod.χ₄ ((m % 4 : ℕ) : ZMod 4) := by
    rw [ZMod.natCast_mod]
  rw [hm, Real.sin_add_nat_mul_two_pi, hχ]
  have h4 : m % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases hr : m % 4
  · simp
  · simp
  · simp
  · have h3 : ((3 : ℕ) : ℝ) * Real.pi / 2 = Real.pi / 2 + Real.pi := by push_cast; ring
    have hc : ZMod.χ₄ ((3 : ℕ) : ZMod 4) = -1 := by decide
    rw [h3, Real.sin_add_pi, Real.sin_pi_div_two, hc]
    norm_num

/-- Truncation stability: for every `N ≥ n`, the coefficient of `x^n` in the partial sum
`Sum_{k=1..N} phi(k) x^k / (1 + x^(2k))` equals `a(n)`; so `a(n)` is the coefficient of `x^n`
of the full series. -/
lemma coeff_sum_summand_of_le {n N : ℕ} (hnN : n ≤ N) :
    coeff n (∑ k ∈ Icc 1 N, summand k) = a n := by
  rw [a, map_sum, map_sum]
  symm
  refine sum_subset (Icc_subset_Icc le_rfl hnN) fun k hkN hkn => ?_
  simp only [mem_Icc] at hkN hkn
  rw [coeff_summand (by omega)]
  split_ifs with hdvd
  · rcases n.eq_zero_or_pos with rfl | hn
    · simp
    · exact absurd (Nat.le_of_dvd hn hdvd) (by omega)
  · rfl

/-- Computable closed form `Sum_{d | n} phi(n/d) chi4(d)` used for ground-truth checks. -/
def closedForm (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors, (Nat.totient (n / d) : ℤ) * ZMod.χ₄ (d : ZMod 4)

/-- `a(n)` equals the integer closed form `closedForm n`. -/
lemma a_eq_closedForm (n : ℕ) : a n = closedForm n := by
  rw [a_eq_sum_divisors, closedForm]
  push_cast
  rfl

/-- The closed form reproduces the first 30 listed terms of A327123. -/
example : (List.range 30).map (fun n => closedForm (n + 1)) =
    [1, 1, 1, 2, 5, 1, 5, 4, 5, 5, 9, 2, 13, 5, 5, 8, 17, 5, 17, 10, 5, 9, 21, 4, 25, 13, 13,
      10, 29, 5] := by
  decide

/-- Ground truth for the power-series definition itself: `a(5) = 5`. -/
example : a 5 = 5 := by
  rw [a_eq_closedForm]
  norm_cast

/-- Character form: `a(n) = Sum_{k=1..n} chi4(gcd(k, n))` (valid for every `n`, including the
trivial case `n = 0` where both sides vanish). -/
theorem a_eq_sum_chi4_gcd (n : ℕ) :
    a n = ∑ k ∈ Icc 1 n, ((ZMod.χ₄ (Nat.gcd k n : ZMod 4) : ℤ) : ℚ) := by
  rw [a_eq_sum_divisors,
    sum_Icc_gcd_eq n (fun d => ((ZMod.χ₄ (d : ZMod 4) : ℤ) : ℚ))]
  refine sum_congr rfl fun d _ => ?_
  rw [nsmul_eq_mul]

/-- Sine form for every `n` (the case `n = 0` is trivial: both sides vanish):
`a(n) = Sum_{k=1..n} sin(gcd(k, n) * Pi / 2)`. -/
theorem a_eq_sum_sin_gcd (n : ℕ) :
    (a n : ℝ) = ∑ k ∈ Icc 1 n, Real.sin ((Nat.gcd k n : ℝ) * Real.pi / 2) := by
  rw [a_eq_sum_chi4_gcd, Rat.cast_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [sin_nat_mul_pi_div_two]
  push_cast
  rfl

/-- **Conjecture of A327123** (Velin Yanev and Vaclav Kotesovec, Jun 01 2024), proved:
for all `n ≥ 1`, the coefficient `a(n)` of `x^n` in `Sum_{k>=1} phi(k) x^k / (1 + x^(2k))`
equals `Sum_{k=1..n} sin(gcd(k, n) * Pi / 2)`. The guard `1 ≤ n` from the source is kept
for fidelity; it is not needed (see `a_eq_sum_sin_gcd`). -/
theorem a327123_conjecture (n : ℕ) (_hn : 0 < n) :
    (a n : ℝ) = ∑ k ∈ Icc 1 n, Real.sin ((Nat.gcd k n : ℝ) * Real.pi / 2) :=
  a_eq_sum_sin_gcd n

/-- Non-vacuity: the hypothesis `0 < n` is satisfiable, and at `n = 1` the identity reads
`a(1) = sin(Pi/2)`. -/
example : (a 1 : ℝ) = ∑ k ∈ Icc 1 1, Real.sin ((Nat.gcd k 1 : ℝ) * Real.pi / 2) :=
  a327123_conjecture 1 Nat.one_pos

end Candidates.A327123CoefficientSumPhi
