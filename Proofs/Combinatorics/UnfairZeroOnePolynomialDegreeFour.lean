/-
# Unfair 0-1 polynomial conjecture: the case `min (deg P) (deg Q) ≤ 4`

L. Ghidelli, *Progress on the unfair 0-1-polynomials conjecture using
linear recurrences and numerical analysis*, arXiv:2209.09843,
Conjecture 1.2, asks whether monic real polynomials with nonnegative
coefficients whose product is 0-1 must themselves be 0-1. See also
E. Amiot's MathOverflow question 339137, "Factoring 0-1 polynomials",
and Ben Green's *100 open problems*, Problem 28; the probabilistic form
is due to G. Letac (c. 1969).

This file proves only the case where one factor has degree at most 4,
asserted after Ghidelli's Theorem 1.1 and covered by K. G. Hare's
computer-assisted classification, arXiv:2307.07363. The general conjecture
is recorded as a proposition, not proved. The auxiliary results bound
each factor coefficient by 1, identify the nonzero constant terms after
removing powers of `X`, and show that if one factor is 0-1 so is the other.

## Proof outline

Strip common powers of `X` so that `P(0) = Q(0) = 1`.  Every product `p_i q_j` is at most
`r_{i+j} ≤ 1`.  With `d = deg P`, `r_d ≥ p_d q_0 = 1` forces `p_i q_{d-i} = 0` for
`0 < i < d` and `q_d = 0`.  Comparing `r_1, …, r_4` shows `p_1 ∈ {0,1}`; applying the same
argument to the reversed factorization `P.reverse * Q.reverse = (P * Q).reverse` shows
`p_{d-1} ∈ {0,1}`; for `d = 4` the middle coefficient follows from `b q_2 = 0` and `r_2`.
Finally `Q` is `0`-`1` by strong induction on the coefficient index.
-/
import Mathlib

set_option autoImplicit false

open Polynomial

namespace Candidates.UnfairZeroOnePolynomialDegreeFour

/-- A real polynomial is a `0`-`1` (Newman) polynomial when each coefficient is `0` or `1`. -/
def IsZeroOne (f : ℝ[X]) : Prop := ∀ n, f.coeff n = 0 ∨ f.coeff n = 1

/-- `IsZeroOne` agrees with the formulation `f.coeffs ⊆ {1}` (the nonzero coefficients are
all `1`) used e.g. in the formal-conjectures statement of MO 339137. -/
theorem isZeroOne_iff_coeffs_subset (f : ℝ[X]) : IsZeroOne f ↔ f.coeffs ⊆ {1} := by
  constructor
  · intro h c hc
    obtain ⟨n, hn, rfl⟩ := mem_coeffs_iff.mp hc
    rw [mem_support_iff] at hn
    rw [Finset.mem_singleton]
    exact (h n).resolve_left hn
  · intro h n
    by_cases hn : f.coeff n = 0
    · exact Or.inl hn
    · exact Or.inr (Finset.mem_singleton.mp (h (coeff_mem_coeffs hn)))

/-- `X^3 + X + 1` is a `0`-`1` polynomial. -/
example : IsZeroOne (X ^ 3 + X + 1) := by
  intro n
  simp only [coeff_add, coeff_X_pow, coeff_X, coeff_one]
  rcases n with _ | _ | _ | _ | n <;> simp

/-- `X + 1/2` is not a `0`-`1` polynomial. -/
example : ¬ IsZeroOne (X + C (1 / 2)) := by
  intro h
  rcases h 0 with h0 | h0 <;> simp at h0

/-- **The unfair 0-1 polynomial conjecture** (Letac c. 1969; Amiot, MO 339137; Ghidelli
arXiv:2209.09843, Conjecture 1.2): if `P, Q ∈ ℝ[X]` are monic with nonnegative coefficients
and `P * Q` has all coefficients in `{0,1}`, then so do `P` and `Q`.  **Open**; recorded
here as a proposition, not asserted. -/
def UnfairZeroOneConjecture : Prop :=
  ∀ P Q : ℝ[X], P.Monic → Q.Monic → (∀ n, 0 ≤ P.coeff n) → (∀ n, 0 ≤ Q.coeff n) →
    IsZeroOne (P * Q) → IsZeroOne P ∧ IsZeroOne Q

/-- The hypotheses of `isZeroOne_of_natDegree_le_four` hold jointly for
`P = X^4 + 1`, `Q = X + 1` (with `P * Q = X^5 + X^4 + X + 1`). -/
example : (X ^ 4 + 1 : ℝ[X]).Monic ∧ (X + 1 : ℝ[X]).Monic
    ∧ (∀ n, 0 ≤ (X ^ 4 + 1 : ℝ[X]).coeff n) ∧ (∀ n, 0 ≤ (X + 1 : ℝ[X]).coeff n)
    ∧ IsZeroOne ((X ^ 4 + 1) * (X + 1)) ∧ (X ^ 4 + 1 : ℝ[X]).natDegree ≤ 4 := by
  refine ⟨monic_X_pow_add_C 1 (by norm_num), monic_X_add_C 1, ?_, ?_, ?_, ?_⟩
  · intro n; simp only [coeff_add, coeff_X_pow, coeff_one]; split_ifs <;> norm_num
  · intro n; simp only [coeff_add, coeff_X, coeff_one]; split_ifs <;> norm_num
  · intro n
    have hexp : ((X ^ 4 + 1) * (X + 1) : ℝ[X]) = X ^ 5 + X ^ 4 + X + 1 := by ring
    rw [hexp]
    simp only [coeff_add, coeff_X_pow, coeff_X, coeff_one]
    rcases n with _ | _ | _ | _ | _ | _ | n <;> simp
  · exact (natDegree_add_le _ _).trans (by simp)

/-- Each product `p_i q_j` is bounded by the coefficient `r_{i+j}` of `P * Q`
when both factors have nonnegative coefficients. -/
theorem coeff_mul_coeff_le {P Q : ℝ[X]} (hp : ∀ n, 0 ≤ P.coeff n) (hq : ∀ n, 0 ≤ Q.coeff n)
    (i j : ℕ) : P.coeff i * Q.coeff j ≤ (P * Q).coeff (i + j) := by
  rw [coeff_mul]
  have hmem : (i, j) ∈ Finset.HasAntidiagonal.antidiagonal (i + j) := Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl
  exact Finset.single_le_sum (f := fun x : ℕ × ℕ => P.coeff x.1 * Q.coeff x.2)
    (fun x _ => mul_nonneg (hp x.1) (hq x.2)) hmem

/-- Real-arithmetic core, degree two: if `P = 1 + a X + X^2` and `Q = 1 + q₁ X + q₂ X^2 + ⋯`
have nonnegative coefficients and `r₁, r₂ ∈ {0,1}`, then `a ∈ {0,1}`. -/
theorem real_deg_two {a q1 q2 : ℝ} (ha : 0 ≤ a) (hq1 : 0 ≤ q1) (hq2 : 0 ≤ q2)
    (h1 : q1 + a = 0 ∨ q1 + a = 1) (h2 : q2 + a * q1 + 1 = 0 ∨ q2 + a * q1 + 1 = 1) :
    a = 0 ∨ a = 1 := by
  have haq : 0 ≤ a * q1 := mul_nonneg ha hq1
  have hz : a * q1 = 0 := by rcases h2 with h2 | h2 <;> linarith
  rcases mul_eq_zero.mp hz with h | h
  · exact Or.inl h
  · rcases h1 with h1 | h1
    · left; linarith
    · right; linarith

/-- Real-arithmetic core, degree three: for `P = 1 + a X + b X^2 + X^3`, the
coefficient `a` lies in `{0,1}`. -/
theorem real_deg_three {a b q1 q2 q3 : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hq1 : 0 ≤ q1)
    (hq2 : 0 ≤ q2) (hq3 : 0 ≤ q3)
    (h1 : q1 + a = 0 ∨ q1 + a = 1)
    (h2 : q2 + a * q1 + b = 0 ∨ q2 + a * q1 + b = 1)
    (h3 : q3 + a * q2 + b * q1 + 1 = 0 ∨ q3 + a * q2 + b * q1 + 1 = 1) :
    a = 0 ∨ a = 1 := by
  by_contra hne
  push Not at hne
  have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm hne.1)
  have hr1 : q1 + a = 1 := by rcases h1 with h1 | h1 <;> [linarith; exact h1]
  have hq1' : q1 = 1 - a := by linarith
  have hlt : a < 1 := lt_of_le_of_ne (by linarith) hne.2
  have haq2 : 0 ≤ a * q2 := mul_nonneg ha hq2
  have hbq1 : 0 ≤ b * q1 := mul_nonneg hb hq1
  have hs : q3 + a * q2 + b * q1 = 0 := by rcases h3 with h3 | h3 <;> linarith
  have hz2 : a * q2 = 0 := by linarith
  have hzb : b * q1 = 0 := by linarith
  have hq2z : q2 = 0 := (mul_eq_zero.mp hz2).resolve_left hapos.ne'
  have hq1pos : 0 < q1 := by linarith
  have hbz : b = 0 := (mul_eq_zero.mp hzb).resolve_right hq1pos.ne'
  subst hq2z hbz
  rw [hq1'] at h2
  rcases h2 with h2 | h2 <;> nlinarith

/-- Real-arithmetic core, degree four: for `P = 1 + a X + b X^2 + c X^3 + X^4`, the
coefficient `a` lies in `{0,1}`. -/
theorem real_deg_four_one {a b c q1 q2 q3 q4 : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hq1 : 0 ≤ q1) (hq2 : 0 ≤ q2) (hq3 : 0 ≤ q3) (hq4 : 0 ≤ q4)
    (h1 : q1 + a = 0 ∨ q1 + a = 1)
    (h2 : q2 + a * q1 + b = 0 ∨ q2 + a * q1 + b = 1)
    (h3 : q3 + a * q2 + b * q1 + c = 0 ∨ q3 + a * q2 + b * q1 + c = 1)
    (h4 : q4 + a * q3 + b * q2 + c * q1 + 1 = 0 ∨ q4 + a * q3 + b * q2 + c * q1 + 1 = 1) :
    a = 0 ∨ a = 1 := by
  by_contra hne
  push Not at hne
  have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm hne.1)
  have hr1 : q1 + a = 1 := by rcases h1 with h1 | h1 <;> [linarith; exact h1]
  have hq1' : q1 = 1 - a := by linarith
  have hlt : a < 1 := lt_of_le_of_ne (by linarith) hne.2
  have hq1pos : 0 < q1 := by linarith
  have haq3 : 0 ≤ a * q3 := mul_nonneg ha hq3
  have hbq2 : 0 ≤ b * q2 := mul_nonneg hb hq2
  have hcq1 : 0 ≤ c * q1 := mul_nonneg hc hq1
  have hs : q4 + a * q3 + b * q2 + c * q1 = 0 := by rcases h4 with h4 | h4 <;> linarith
  have hz3 : a * q3 = 0 := by linarith
  have hzb : b * q2 = 0 := by linarith
  have hzc : c * q1 = 0 := by linarith
  have hq3z : q3 = 0 := (mul_eq_zero.mp hz3).resolve_left hapos.ne'
  have hcz : c = 0 := (mul_eq_zero.mp hzc).resolve_right hq1pos.ne'
  subst hq3z hcz
  rw [hq1'] at h2 h3
  have hr2 : q2 + a * (1 - a) + b = 1 := by
    rcases h2 with h2 | h2
    · nlinarith
    · exact h2
  rcases (mul_eq_zero.mp hzb) with hb0 | hq2z
  · subst hb0
    have hq2' : q2 = 1 - a + a ^ 2 := by linarith
    rw [hq2'] at h3
    rcases h3 with h3 | h3 <;> nlinarith [mul_pos hapos hapos, mul_pos (mul_pos hapos hapos) hapos]
  · subst hq2z
    have hb' : b = 1 - a + a ^ 2 := by linarith
    rw [hb'] at h3
    rcases h3 with h3 | h3 <;> nlinarith [mul_pos hapos hapos, mul_pos (mul_pos hapos hapos) hapos]

/-- Real-arithmetic core, degree four, middle coefficient: for
`P = 1 + a X + b X^2 + c X^3 + X^4` with `a ∈ {0,1}`, also `b ∈ {0,1}`. -/
theorem real_deg_four_two {a b c q1 q2 q3 q4 : ℝ} (hb : 0 ≤ b)
    (hq1 : 0 ≤ q1) (hq2 : 0 ≤ q2) (hq3 : 0 ≤ q3) (hq4 : 0 ≤ q4)
    (ha01 : a = 0 ∨ a = 1) (hc : 0 ≤ c)
    (h1 : q1 + a = 0 ∨ q1 + a = 1)
    (h2 : q2 + a * q1 + b = 0 ∨ q2 + a * q1 + b = 1)
    (h4 : q4 + a * q3 + b * q2 + c * q1 + 1 = 0 ∨ q4 + a * q3 + b * q2 + c * q1 + 1 = 1) :
    b = 0 ∨ b = 1 := by
  have ha : 0 ≤ a := by rcases ha01 with h | h <;> simp [h]
  have haq3 : 0 ≤ a * q3 := mul_nonneg ha hq3
  have hbq2 : 0 ≤ b * q2 := mul_nonneg hb hq2
  have hcq1 : 0 ≤ c * q1 := mul_nonneg hc hq1
  have hzb : b * q2 = 0 := by rcases h4 with h4 | h4 <;> linarith
  rcases (mul_eq_zero.mp hzb) with hb0 | hq2z
  · exact Or.inl hb0
  · subst hq2z
    have haq1 : a * q1 = 0 := by
      rcases ha01 with h | h
      · rw [h]; ring
      · subst h
        have hq1z : q1 = 0 := by rcases h1 with h1 | h1 <;> linarith
        rw [hq1z]; ring
    rw [haq1] at h2
    rcases h2 with h2 | h2
    · left; linarith
    · right; linarith


section Expansion

variable {P Q : ℝ[X]}

/-- `r₁ = q₁ + p₁` when `p₀ = q₀ = 1`. -/
theorem coeff_mul_one_eq (hp0 : P.coeff 0 = 1) (hq0 : Q.coeff 0 = 1) :
    (P * Q).coeff 1 = Q.coeff 1 + P.coeff 1 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => P.coeff i * Q.coeff j)]
  simp [Finset.sum_range_succ, hp0, hq0]

/-- `r₂ = q₂ + p₁ q₁ + p₂` when `p₀ = q₀ = 1`. -/
theorem coeff_mul_two_eq (hp0 : P.coeff 0 = 1) (hq0 : Q.coeff 0 = 1) :
    (P * Q).coeff 2 = Q.coeff 2 + P.coeff 1 * Q.coeff 1 + P.coeff 2 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => P.coeff i * Q.coeff j)]
  simp [Finset.sum_range_succ, hp0, hq0]

/-- `r₃ = q₃ + p₁ q₂ + p₂ q₁ + p₃` when `p₀ = q₀ = 1`. -/
theorem coeff_mul_three_eq (hp0 : P.coeff 0 = 1) (hq0 : Q.coeff 0 = 1) :
    (P * Q).coeff 3 = Q.coeff 3 + P.coeff 1 * Q.coeff 2 + P.coeff 2 * Q.coeff 1 + P.coeff 3 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => P.coeff i * Q.coeff j)]
  simp [Finset.sum_range_succ, hp0, hq0]

/-- `r₄ = q₄ + p₁ q₃ + p₂ q₂ + p₃ q₁ + p₄` when `p₀ = q₀ = 1`. -/
theorem coeff_mul_four_eq (hp0 : P.coeff 0 = 1) (hq0 : Q.coeff 0 = 1) :
    (P * Q).coeff 4 = Q.coeff 4 + P.coeff 1 * Q.coeff 3 + P.coeff 2 * Q.coeff 2
      + P.coeff 3 * Q.coeff 1 + P.coeff 4 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => P.coeff i * Q.coeff j)]
  simp [Finset.sum_range_succ, hp0, hq0]

end Expansion

/-- Low-end step: if `P` is monic of degree at most `4`, `P(0) = Q(0) = 1`, both factors
have nonnegative coefficients and `P * Q` is `0`-`1`, then `p₁ ∈ {0,1}`. -/
theorem coeff_one_zeroOne {P Q : ℝ[X]} (hp : ∀ n, 0 ≤ P.coeff n) (hq : ∀ n, 0 ≤ Q.coeff n)
    (hp0 : P.coeff 0 = 1) (hq0 : Q.coeff 0 = 1) (hP : P.Monic) (hR : IsZeroOne (P * Q))
    (hd : P.natDegree ≤ 4) : P.coeff 1 = 0 ∨ P.coeff 1 = 1 := by
  obtain ⟨d, hdP⟩ : ∃ d, P.natDegree = d := ⟨_, rfl⟩
  have hlead : P.coeff d = 1 := hdP ▸ hP.coeff_natDegree
  have hhigh : ∀ i, d < i → P.coeff i = 0 := fun i hi =>
    coeff_eq_zero_of_natDegree_lt (hdP ▸ hi)
  have h1 := hR 1
  have h2 := hR 2
  have h3 := hR 3
  have h4 := hR 4
  rw [coeff_mul_one_eq hp0 hq0] at h1
  rw [coeff_mul_two_eq hp0 hq0] at h2
  rw [coeff_mul_three_eq hp0 hq0] at h3
  rw [coeff_mul_four_eq hp0 hq0] at h4
  rw [hdP] at hd
  interval_cases d
  · exact Or.inl (hhigh 1 (by norm_num))
  · exact Or.inr hlead
  · rw [hlead] at h2
    exact real_deg_two (hp 1) (hq 1) (hq 2) h1 h2
  · rw [hlead] at h3
    exact real_deg_three (hp 1) (hp 2) (hq 1) (hq 2) (hq 3) h1 h2 h3
  · rw [hlead] at h4
    exact real_deg_four_one (hp 1) (hp 2) (hp 3) (hq 1) (hq 2) (hq 3) (hq 4) h1 h2 h3 h4

/-- Low-end step for the middle coefficient: if `P` is monic of degree exactly `4`, then
`p₂ ∈ {0,1}` (under the same hypotheses as `coeff_one_zeroOne`). -/
theorem coeff_two_zeroOne {P Q : ℝ[X]} (hp : ∀ n, 0 ≤ P.coeff n) (hq : ∀ n, 0 ≤ Q.coeff n)
    (hp0 : P.coeff 0 = 1) (hq0 : Q.coeff 0 = 1) (hP : P.Monic) (hR : IsZeroOne (P * Q))
    (hd : P.natDegree = 4) : P.coeff 2 = 0 ∨ P.coeff 2 = 1 := by
  have ha01 := coeff_one_zeroOne hp hq hp0 hq0 hP hR hd.le
  have hlead : P.coeff 4 = 1 := hd ▸ hP.coeff_natDegree
  have h1 := hR 1
  have h2 := hR 2
  have h4 := hR 4
  rw [coeff_mul_one_eq hp0 hq0] at h1
  rw [coeff_mul_two_eq hp0 hq0] at h2
  rw [coeff_mul_four_eq hp0 hq0, hlead] at h4
  exact real_deg_four_two (hp 2) (hq 1) (hq 2) (hq 3) (hq 4) ha01 (hp 3) h1 h2 h4


section Reverse

variable {P : ℝ[X]}

/-- If `P(0) = 1`, the trailing degree of `P` is `0`. -/
theorem natTrailingDegree_eq_zero_of_coeff_zero (hp0 : P.coeff 0 = 1) :
    P.natTrailingDegree = 0 :=
  natTrailingDegree_eq_zero_of_constantCoeff_ne_zero (by simp [hp0])

/-- Reversal preserves the degree of a polynomial with `P(0) = 1`. -/
theorem natDegree_reverse_eq (hp0 : P.coeff 0 = 1) : P.reverse.natDegree = P.natDegree := by
  rw [reverse_natDegree, natTrailingDegree_eq_zero_of_coeff_zero hp0, Nat.sub_zero]

/-- The reversal of a monic polynomial has constant coefficient `1`. -/
theorem coeff_zero_reverse_eq (hP : P.Monic) : P.reverse.coeff 0 = 1 := by
  rw [coeff_zero_reverse, hP.leadingCoeff]

/-- The reversal of a polynomial with `P(0) = 1` is monic. -/
theorem monic_reverse (hp0 : P.coeff 0 = 1) : P.reverse.Monic := by
  rw [Monic, reverse_leadingCoeff, trailingCoeff_eq_coeff_zero (by rw [hp0]; norm_num), hp0]

/-- Reversal keeps coefficients nonnegative. -/
theorem reverse_coeff_nonneg (hp : ∀ n, 0 ≤ P.coeff n) (n : ℕ) : 0 ≤ P.reverse.coeff n := by
  rw [coeff_reverse]; exact hp _

/-- The reversal of a `0`-`1` polynomial is `0`-`1`. -/
theorem isZeroOne_reverse (hR : IsZeroOne P) : IsZeroOne P.reverse := by
  intro n; rw [coeff_reverse]; exact hR _

/-- Coefficient `i ≤ deg P` of the reversal is coefficient `deg P - i` of `P`. -/
theorem coeff_reverse_of_le {i : ℕ} (hi : i ≤ P.natDegree) :
    P.reverse.coeff i = P.coeff (P.natDegree - i) := by
  rw [coeff_reverse, revAt_le hi]

end Reverse

/-- Mirrored step: if `P, Q` are monic with nonnegative coefficients, `P(0) = 1`,
`P * Q` is `0`-`1` and `1 ≤ deg P ≤ 4`, then the
coefficient `p_{d-1}` of `P` (where `d = deg P`) lies in `{0,1}`. -/
theorem coeff_pred_zeroOne {P Q : ℝ[X]} (hp : ∀ n, 0 ≤ P.coeff n) (hq : ∀ n, 0 ≤ Q.coeff n)
    (hp0 : P.coeff 0 = 1) (hP : P.Monic) (hQ : Q.Monic)
    (hR : IsZeroOne (P * Q)) (hd : P.natDegree ≤ 4) (hd1 : 1 ≤ P.natDegree) :
    P.coeff (P.natDegree - 1) = 0 ∨ P.coeff (P.natDegree - 1) = 1 := by
  have hrev := coeff_one_zeroOne (reverse_coeff_nonneg hp) (reverse_coeff_nonneg hq)
    (coeff_zero_reverse_eq hP) (coeff_zero_reverse_eq hQ) (monic_reverse hp0)
    (by rw [← reverse_mul_of_domain]; exact isZeroOne_reverse hR)
    (by rw [natDegree_reverse_eq hp0]; exact hd)
  rwa [coeff_reverse_of_le hd1] at hrev

/-- **Normalized degree-`≤ 4` case.** If `P, Q ∈ ℝ[X]` are monic with nonnegative
coefficients, `P(0) = Q(0) = 1`, `P * Q` has all coefficients in `{0,1}` and
`deg P ≤ 4`, then `P` has all coefficients in `{0,1}`. -/
theorem isZeroOne_left_of_normalized {P Q : ℝ[X]} (hp : ∀ n, 0 ≤ P.coeff n)
    (hq : ∀ n, 0 ≤ Q.coeff n) (hp0 : P.coeff 0 = 1) (hq0 : Q.coeff 0 = 1) (hP : P.Monic)
    (hQ : Q.Monic) (hR : IsZeroOne (P * Q)) (hd : P.natDegree ≤ 4) : IsZeroOne P := by
  intro n
  obtain ⟨d, hdP⟩ : ∃ d, P.natDegree = d := ⟨_, rfl⟩
  have hlead : P.coeff d = 1 := hdP ▸ hP.coeff_natDegree
  rcases lt_trichotomy d n with hlt | heq | hgt
  · exact Or.inl (coeff_eq_zero_of_natDegree_lt (hdP ▸ hlt))
  · exact Or.inr (heq ▸ hlead)
  · have h1 := coeff_one_zeroOne hp hq hp0 hq0 hP hR hd
    have hpred := coeff_pred_zeroOne hp hq hp0 hP hQ hR hd (by omega)
    rw [hdP] at hpred hd
    interval_cases d <;> interval_cases n
    all_goals first
      | exact Or.inr hp0
      | exact h1
      | exact hpred
      | exact coeff_two_zeroOne hp hq hp0 hq0 hP hR hdP


/-- Each term `p_i q_j` with both factors in `{0,1}` is a natural number. -/
theorem exists_nat_of_zeroOne_mul {x y : ℝ} (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1) :
    ∃ m : ℕ, x * y = m := by
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> subst hx hy
  exacts [⟨0, by simp⟩, ⟨0, by simp⟩, ⟨0, by simp⟩, ⟨1, by simp⟩]

/-- A finite sum of reals each of which is a natural number is a natural number. -/
theorem exists_nat_of_sum {s : Finset ℕ} {f : ℕ → ℝ} (hf : ∀ i ∈ s, ∃ m : ℕ, f i = m) :
    ∃ m : ℕ, ∑ i ∈ s, f i = m := by
  choose g hg using hf
  refine ⟨∑ i ∈ s.attach, g i.1 i.2, ?_⟩
  rw [Nat.cast_sum, ← Finset.sum_attach s f]
  exact Finset.sum_congr rfl fun i _ => hg i.1 i.2

/-- **Easy half.** If `P(0) = 1`, `P` is a `0`-`1` polynomial, `Q` has nonnegative
coefficients and `P * Q` is `0`-`1`, then `Q` is a `0`-`1` polynomial. -/
theorem isZeroOne_right_of_left {P Q : ℝ[X]} (hp0 : P.coeff 0 = 1) (hPz : IsZeroOne P)
    (hq : ∀ n, 0 ≤ Q.coeff n) (hR : IsZeroOne (P * Q)) : IsZeroOne Q := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hexp : (P * Q).coeff n
        = (∑ i ∈ Finset.range n, P.coeff (i + 1) * Q.coeff (n - (i + 1))) + Q.coeff n := by
      rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => P.coeff i * Q.coeff j), Finset.sum_range_succ']
      simp [hp0]
    obtain ⟨m, hm⟩ : ∃ m : ℕ,
        ∑ i ∈ Finset.range n, P.coeff (i + 1) * Q.coeff (n - (i + 1)) = m :=
      exists_nat_of_sum fun i hi =>
        exists_nat_of_zeroOne_mul (hPz _) (ih _ (by have hin := Finset.mem_range.mp hi; omega))
    have hqn := hq n
    rcases hR n with h | h <;> rw [hexp, hm] at h
    · have hm0 : (m : ℝ) = 0 := le_antisymm (by linarith) (Nat.cast_nonneg m)
      left; linarith
    · have hm1 : m ≤ 1 := by
        have hmR : (m : ℝ) ≤ 1 := by linarith
        exact_mod_cast hmR
      interval_cases m
      · right; simpa using h
      · left; simpa using h


/-- **Coefficient bound.** If `Q` is monic, `P` and `Q` have nonnegative coefficients and
`P * Q` is `0`-`1`, then every coefficient of `P` is at most `1`. -/
theorem coeff_le_one_of_monic {P Q : ℝ[X]} (hQ : Q.Monic) (hp : ∀ n, 0 ≤ P.coeff n)
    (hq : ∀ n, 0 ≤ Q.coeff n) (hR : IsZeroOne (P * Q)) (n : ℕ) : P.coeff n ≤ 1 := by
  have hle := coeff_mul_coeff_le hp hq n Q.natDegree
  rw [hQ.coeff_natDegree, mul_one] at hle
  rcases hR (n + Q.natDegree) with h | h <;> linarith

/-- **Constant terms.** If `P, Q` are monic with nonnegative coefficients, `P * Q` is
`0`-`1` and `P(0) ≠ 0`, `Q(0) ≠ 0`, then `P(0) = Q(0) = 1`. -/
theorem coeff_zero_eq_one {P Q : ℝ[X]} (hP : P.Monic) (hQ : Q.Monic) (hp : ∀ n, 0 ≤ P.coeff n)
    (hq : ∀ n, 0 ≤ Q.coeff n) (hR : IsZeroOne (P * Q)) (hp0 : P.coeff 0 ≠ 0)
    (hq0 : Q.coeff 0 ≠ 0) : P.coeff 0 = 1 ∧ Q.coeff 0 = 1 := by
  have hP1 := coeff_le_one_of_monic hQ hp hq hR 0
  have hQ1 := coeff_le_one_of_monic hP hq hp (by rw [mul_comm]; exact hR) 0
  have hpos : 0 < P.coeff 0 := lt_of_le_of_ne (hp 0) (Ne.symm hp0)
  have hqpos : 0 < Q.coeff 0 := lt_of_le_of_ne (hq 0) (Ne.symm hq0)
  have hr0 : P.coeff 0 * Q.coeff 0 = 1 := by
    have h := hR 0
    rw [mul_coeff_zero] at h
    rcases h with h | h
    · exact absurd h (mul_pos hpos hqpos).ne'
    · exact h
  constructor <;> nlinarith

section Strip

variable {P : ℝ[X]}

/-- If `P(0) = 0` then `P = (P / X) * X`, written with `Polynomial.divX`. -/
theorem eq_divX_mul_X (hp0 : P.coeff 0 = 0) : P = P.divX * X := by
  conv_lhs => rw [← divX_mul_X_add P, hp0, map_zero, add_zero]

/-- If `P` is monic with `P(0) = 0`, then `P.divX` is monic. -/
theorem monic_divX (hP : P.Monic) (hp0 : P.coeff 0 = 0) : P.divX.Monic :=
  Monic.of_mul_monic_right monic_X ((eq_divX_mul_X hp0) ▸ hP)

/-- If `P` is monic with `P(0) = 0`, then `deg (P.divX) + 1 = deg P`. -/
theorem natDegree_divX_add_one (hP : P.Monic) (hp0 : P.coeff 0 = 0) :
    P.divX.natDegree + 1 = P.natDegree := by
  conv_rhs => rw [eq_divX_mul_X hp0]
  rw [natDegree_mul_X (monic_divX hP hp0).ne_zero]

/-- `P.divX` keeps nonnegative coefficients. -/
theorem divX_coeff_nonneg (hp : ∀ n, 0 ≤ P.coeff n) (n : ℕ) : 0 ≤ P.divX.coeff n := by
  rw [coeff_divX]; exact hp _

/-- If `P(0) = 0`, `P` is `0`-`1` exactly when `P.divX` is. -/
theorem isZeroOne_of_divX (hp0 : P.coeff 0 = 0) (h : IsZeroOne P.divX) : IsZeroOne P := by
  intro n
  cases n with
  | zero => exact Or.inl hp0
  | succ n => rw [← coeff_divX]; exact h n

/-- If `P * X` is `0`-`1`, so is `P`. -/
theorem isZeroOne_of_mul_X (h : IsZeroOne (P * X)) : IsZeroOne P := by
  intro n; rw [← coeff_mul_X]; exact h _

end Strip

/-- **Unfair `0`-`1` conjecture, case `deg P ≤ 4`.** Let `P, Q ∈ ℝ[X]` be monic with
nonnegative coefficients such that every coefficient of `P * Q` is `0` or `1`. If
`deg P ≤ 4`, then every coefficient of `P` and of `Q` is `0` or `1`. -/
theorem isZeroOne_of_natDegree_le_four {P Q : ℝ[X]} (hP : P.Monic) (hQ : Q.Monic)
    (hp : ∀ n, 0 ≤ P.coeff n) (hq : ∀ n, 0 ≤ Q.coeff n) (hR : IsZeroOne (P * Q))
    (hd : P.natDegree ≤ 4) : IsZeroOne P ∧ IsZeroOne Q := by
  obtain ⟨N, hN⟩ : ∃ N, P.natDegree + Q.natDegree = N := ⟨_, rfl⟩
  induction N using Nat.strong_induction_on generalizing P Q with
  | _ N ih =>
    by_cases hp0 : P.coeff 0 = 0
    · have hlt := natDegree_divX_add_one hP hp0
      have hR' : IsZeroOne (P.divX * Q) := by
        apply isZeroOne_of_mul_X
        have hEq : P.divX * Q * X = P * Q := by
          conv_rhs => rw [eq_divX_mul_X hp0]
          ring
        rw [hEq]; exact hR
      obtain ⟨h1, h2⟩ := ih _ (by omega) (monic_divX hP hp0) hQ (divX_coeff_nonneg hp) hq hR'
        (by omega) rfl
      exact ⟨isZeroOne_of_divX hp0 h1, h2⟩
    by_cases hq0 : Q.coeff 0 = 0
    · have hlt := natDegree_divX_add_one hQ hq0
      have hR' : IsZeroOne (P * Q.divX) := by
        apply isZeroOne_of_mul_X
        have hEq : P * Q.divX * X = P * Q := by
          conv_rhs => rw [eq_divX_mul_X hq0]
          ring
        rw [hEq]; exact hR
      obtain ⟨h1, h2⟩ := ih _ (by omega) hP (monic_divX hQ hq0) hp (divX_coeff_nonneg hq) hR'
        hd rfl
      exact ⟨h1, isZeroOne_of_divX hq0 h2⟩
    obtain ⟨hp1, hq1⟩ := coeff_zero_eq_one hP hQ hp hq hR hp0 hq0
    have hPz := isZeroOne_left_of_normalized hp hq hp1 hq1 hP hQ hR hd
    exact ⟨hPz, isZeroOne_right_of_left hp1 hPz hq hR⟩

/-- **Unfair `0`-`1` conjecture, case `min (deg P) (deg Q) ≤ 4`.** Symmetric form of
`isZeroOne_of_natDegree_le_four`. -/
theorem isZeroOne_of_min_natDegree_le_four {P Q : ℝ[X]} (hP : P.Monic) (hQ : Q.Monic)
    (hp : ∀ n, 0 ≤ P.coeff n) (hq : ∀ n, 0 ≤ Q.coeff n) (hR : IsZeroOne (P * Q))
    (hd : min P.natDegree Q.natDegree ≤ 4) : IsZeroOne P ∧ IsZeroOne Q := by
  rcases le_total P.natDegree Q.natDegree with hle | hle
  · exact isZeroOne_of_natDegree_le_four hP hQ hp hq hR (by rwa [min_eq_left hle] at hd)
  · have hR' : IsZeroOne (Q * P) := by rw [mul_comm]; exact hR
    have h := isZeroOne_of_natDegree_le_four hQ hP hq hp hR' (by rwa [min_eq_right hle] at hd)
    exact ⟨h.2, h.1⟩

end Candidates.UnfairZeroOnePolynomialDegreeFour
