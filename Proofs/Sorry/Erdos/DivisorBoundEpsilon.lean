/-
# Divisor bound: `d(n) = O_ε(n^ε)`

## Source

Classical; first proved by C. Runge (1885). Stated as Theorem 315 in
G. H. Hardy and E. M. Wright, *An Introduction to the Theory of Numbers*
(§18.1): `d(n) = O(n^δ)` for every positive `δ`. Wigert (1907) refined it.

## Informal statement (verbatim from the target spec)

For every eps > 0 there is C(eps) such that the number of divisors satisfies
d(n) <= C(eps) * n^eps for all n >= 1.

## Mathlib absence check

Re-checked 2026-10-21 with `leandoc` ("divisor count bound card divisors rpow
epsilon", "number of divisors isBigO", "divisor function upper bound n pow
epsilon") and a grep of Mathlib for `card_divisors` near `rpow`/`isBigO`:
only `Nat.card_divisors` (product formula), `Nat.card_divisors_le_self`, and
`ArithmeticFunction.sigma_le_pow_succ` exist.

## Proof outline

By `Nat.card_divisors`, `d(n) = ∏_{p^a ∥ n} (a + 1)` and
`n^ε = ∏_{p^a ∥ n} (p^ε)^a`. If `p^ε ≥ 2` then `a + 1 ≤ 2^a ≤ (p^ε)^a`.
Otherwise (only primes `p < ⌈2^{1/ε}⌉`) use `(p^ε)^a ≥ 2^{εa} ≥ 1 + aε log 2`,
whence `a + 1 ≤ M (p^ε)^a` with `M = 1 + 1/(ε log 2)`. Hence
`d(n) ≤ M^{⌈2^{1/ε}⌉} n^ε`.

Date: 2026-10-21.
-/
import Mathlib

set_option autoImplicit false

namespace Erdos.DivisorBoundEpsilon

open Finset Real

/-- Ground truth: `d(12) = 6` with Mathlib's `Nat.divisors`. -/
example : (12 : ℕ).divisors.card = 6 := by decide

/-- Ground truth: `d(1) = 1`. -/
example : (1 : ℕ).divisors.card = 1 := by decide

/-- For `c > 0` and every `a : ℕ`, `a + 1 ≤ (1 + 1/c) * (1 + a c)`. -/
lemma add_one_le_mul_one_add_mul {c : ℝ} (hc : 0 < c) (a : ℕ) :
    (a : ℝ) + 1 ≤ (1 + 1 / c) * (1 + a * c) := by
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hexp : (1 + 1 / c) * (1 + a * c) = 1 + a * c + 1 / c + a := by
    field_simp
    ring
  have h1c : 0 ≤ 1 / c := by positivity
  rw [hexp]
  nlinarith [mul_nonneg ha hc.le]

/-- For a natural `p ≥ 2`, `ε > 0` and `a : ℕ`, we have
`1 + a ε log 2 ≤ (p^ε)^a`. -/
lemma one_add_le_rpow_pow {p : ℕ} (hp : 2 ≤ p) {ε : ℝ} (hε : 0 < ε) (a : ℕ) :
    1 + a * (ε * Real.log 2) ≤ ((p : ℝ) ^ ε) ^ a := by
  have h2p : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hbase : (2 : ℝ) ^ ε ≤ (p : ℝ) ^ ε :=
    Real.rpow_le_rpow (by norm_num) h2p hε.le
  have h2eq : (2 : ℝ) ^ ε = Real.exp (ε * Real.log 2) := by
    rw [Real.rpow_def_of_pos (by norm_num), mul_comm]
  calc 1 + a * (ε * Real.log 2) ≤ Real.exp (a * (ε * Real.log 2)) := by
        linarith [Real.add_one_le_exp (a * (ε * Real.log 2))]
    _ = ((2 : ℝ) ^ ε) ^ a := by rw [h2eq, Real.exp_nat_mul]
    _ ≤ ((p : ℝ) ^ ε) ^ a := pow_le_pow_left₀ (by positivity) hbase a

/-- The per-prime constant `M(ε) = 1 + 1/(ε log 2)`. -/
noncomputable def smallPrimeConst (ε : ℝ) : ℝ := 1 + 1 / (ε * Real.log 2)

/-- `M(ε) ≥ 1` for `ε > 0`. -/
lemma one_le_smallPrimeConst {ε : ℝ} (hε : 0 < ε) : 1 ≤ smallPrimeConst ε := by
  have hc : 0 < ε * Real.log 2 := mul_pos hε (Real.log_pos (by norm_num))
  unfold smallPrimeConst
  have : 0 ≤ 1 / (ε * Real.log 2) := by positivity
  linarith

/-- Uniform per-prime bound: for `p ≥ 2`, `a + 1 ≤ M(ε) (p^ε)^a`. -/
lemma add_one_le_const_mul {p : ℕ} (hp : 2 ≤ p) {ε : ℝ} (hε : 0 < ε) (a : ℕ) :
    (a : ℝ) + 1 ≤ smallPrimeConst ε * ((p : ℝ) ^ ε) ^ a := by
  have hc : 0 < ε * Real.log 2 := mul_pos hε (Real.log_pos (by norm_num))
  have hM : 0 ≤ smallPrimeConst ε := (zero_le_one).trans (one_le_smallPrimeConst hε)
  calc (a : ℝ) + 1 ≤ (1 + 1 / (ε * Real.log 2)) * (1 + a * (ε * Real.log 2)) :=
        add_one_le_mul_one_add_mul hc a
    _ ≤ smallPrimeConst ε * ((p : ℝ) ^ ε) ^ a :=
        mul_le_mul_of_nonneg_left (one_add_le_rpow_pow hp hε a) hM

/-- Large-prime bound: if `2 ≤ p^ε` then `a + 1 ≤ (p^ε)^a`. -/
lemma add_one_le_rpow_pow_of_two_le {p : ℕ} {ε : ℝ} (hpε : 2 ≤ (p : ℝ) ^ ε) (a : ℕ) :
    (a : ℝ) + 1 ≤ ((p : ℝ) ^ ε) ^ a := by
  have h2 : ((a + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ a := by
    exact_mod_cast Nat.lt_two_pow_self
  calc (a : ℝ) + 1 = ((a + 1 : ℕ) : ℝ) := by push_cast; ring
    _ ≤ (2 : ℝ) ^ a := h2
    _ ≤ ((p : ℝ) ^ ε) ^ a := pow_le_pow_left₀ (by norm_num) hpε a

/-- `n^ε = ∏_{p ∣ n} (p^ε)^{v_p(n)}` for `n ≠ 0`. -/
lemma rpow_eq_prod_primeFactors {n : ℕ} (hn : n ≠ 0) (ε : ℝ) :
    (n : ℝ) ^ ε = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ ε) ^ n.factorization p := by
  have hprod : (n : ℝ) = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ n.factorization p) := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
    rw [Finsupp.prod, Nat.support_factorization]
    push_cast
    rfl
  rw [hprod, ← Real.finsetProd_rpow _ _ (fun p _ => by positivity)]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg p),
    ← Real.rpow_mul (Nat.cast_nonneg p), mul_comm]

/-- **Divisor bound** (Runge 1885; Hardy–Wright Thm 315). For every `ε > 0` there is a
constant `C` such that `d(n) ≤ C n^ε` for all `n ≥ 1`. -/
theorem card_divisors_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ n : ℕ, 0 < n → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  set M : ℝ := smallPrimeConst ε with hMdef
  set B : ℕ := ⌈(2 : ℝ) ^ (1 / ε)⌉₊ with hBdef
  have hM1 : 1 ≤ M := one_le_smallPrimeConst hε
  refine ⟨M ^ B, fun n hn => ?_⟩
  have hn0 : n ≠ 0 := hn.ne'
  -- per-prime constant: `M` for small primes, `1` for large ones
  let K : ℕ → ℝ := fun p => if p < B then M else 1
  have hlarge : ∀ p : ℕ, B ≤ p → 2 ≤ (p : ℝ) ^ ε := by
    intro p hp
    have hBp : (2 : ℝ) ^ (1 / ε) ≤ p :=
      (Nat.le_ceil _).trans (by exact_mod_cast hp)
    calc (2 : ℝ) = ((2 : ℝ) ^ (1 / ε)) ^ ε := by
          rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hε.ne', Real.rpow_one]
      _ ≤ (p : ℝ) ^ ε := Real.rpow_le_rpow (by positivity) hBp hε.le
  have hlocal : ∀ p ∈ n.primeFactors,
      ((n.factorization p : ℝ) + 1) ≤ K p * ((p : ℝ) ^ ε) ^ n.factorization p := by
    intro p hp
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    by_cases hpB : p < B
    · simp only [K, if_pos hpB]
      exact add_one_le_const_mul hp2 hε _
    · simp only [K, if_neg hpB, one_mul]
      exact add_one_le_rpow_pow_of_two_le (hlarge p (not_lt.mp hpB)) _
  have hKprod : ∏ p ∈ n.primeFactors, K p ≤ M ^ B := by
    have hfilter : ∏ p ∈ n.primeFactors, K p = M ^ (n.primeFactors.filter (· < B)).card := by
      rw [← Finset.prod_const, Finset.prod_filter]
    have hcard : (n.primeFactors.filter (· < B)).card ≤ B := by
      calc (n.primeFactors.filter (· < B)).card ≤ (Finset.range B).card :=
            Finset.card_le_card fun p hp => Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
        _ = B := Finset.card_range B
    rw [hfilter]
    exact pow_le_pow_right₀ hM1 hcard
  have hXnonneg : 0 ≤ ∏ p ∈ n.primeFactors, ((p : ℝ) ^ ε) ^ n.factorization p :=
    Finset.prod_nonneg fun p _ => by positivity
  rw [Nat.card_divisors hn0, rpow_eq_prod_primeFactors hn0]
  push_cast
  calc ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1)
      ≤ ∏ p ∈ n.primeFactors, (K p * ((p : ℝ) ^ ε) ^ n.factorization p) :=
        Finset.prod_le_prod (fun p _ => by positivity) hlocal
    _ = (∏ p ∈ n.primeFactors, K p) *
          ∏ p ∈ n.primeFactors, ((p : ℝ) ^ ε) ^ n.factorization p :=
        Finset.prod_mul_distrib
    _ ≤ M ^ B * ∏ p ∈ n.primeFactors, ((p : ℝ) ^ ε) ^ n.factorization p :=
        mul_le_mul_of_nonneg_right hKprod hXnonneg

/-- **Divisor bound, asymptotic form.** For every `ε > 0`, `d(n) = O(n^ε)` as `n → ∞`. -/
theorem card_divisors_isBigO_rpow {ε : ℝ} (hε : 0 < ε) :
    (fun n : ℕ => (n.divisors.card : ℝ)) =O[Filter.atTop] fun n : ℕ => (n : ℝ) ^ ε := by
  obtain ⟨C, hC⟩ := card_divisors_le_rpow hε
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) ε)]
  exact hC n hn

end Erdos.DivisorBoundEpsilon
