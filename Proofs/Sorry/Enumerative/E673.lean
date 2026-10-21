/-
  Erdős Problem #673 — sums of ratios of consecutive divisors.
  The first question is proved in the literature (Erdős called it
  trivial in [Er82e]). The upper bound and ground checks are formalized
  in Enumerative.E673; the lower and analytic statements remain archived.

  Verbatim statement (`goof erdos fetch 673`, pulled 2026-08-05):

    "Let $1=d_1<\cdots <d_{\tau(n)}=n$ be the divisors of $n$ and
    \[G(n) = \sum_{1\leq i<\tau(n)}\frac{d_i}{d_{i+1}}.\]
    Is it true that $G(n)\to \infty$ for almost all $n$? Can one prove
    an asymptotic formula for $\sum_{n\leq X}G(n)$?"

  DB remarks: Erdős writes it is 'easy' that the mean of G grows.
  The live entry attributes to Tao the claim that for any m ∣ n,
  τ(n/m)/m ≤ G(n) ≤ τ(n).  Its literal lower bound at m = 1 is false:
  n = 7 gives τ(7) = 2 but G(7) = 1/7.  The corrected lower bound assumes
  2 ≤ m; at m = 2 it still gives τ(n)/4 ≤ G(n) ≤ τ(n) for even n.
  Erdős [Er82e] recalls
  the conjecture as trivial; he and Tenenbaum proved G(n)/τ(n) has a
  continuous distribution function.

  Mathlib inventory (leandoc 2026-08-05): `Nat.divisors` (Finset),
  `Finset.sort (· ≤ ·)` for the increasing divisor list; τ(n) =
  `n.divisors.card`.  "Almost all" density language is mostly absent
  from Mathlib — the density statement is archived, the pointwise
  inequalities are the targets.
-/
import Enumerative.E673

set_option autoImplicit false

namespace ErdosCandidates.E673

/-- **Question 1 (answered YES, trivially)**: `G(n) → ∞` for almost
    all `n` — density form: for every bound `M`, the set of `n ≤ X`
    with `G(n) ≤ M` has density 0.  Follows from the lower bound plus
    "τ(n) → ∞ for almost all n" (normal order of τ; the divisor-count
    density input is the missing Mathlib piece — archived until a
    density toolkit exists). -/
theorem G_tendsto_ae (M : ℚ) :
    Filter.Tendsto
      (fun X : ℕ =>
        (((Finset.Icc 1 X).filter (fun n => G n ≤ M)).card : ℝ) / X)
      Filter.atTop (nhds 0) := by
  sorry

section MeanOrder

open Finset

/-- Dirichlet's hyperbola identity in its simplest form:
    `∑_{n ≤ Y} τ(n) = ∑_{d ≤ Y} ⌊Y/d⌋`. -/
private theorem sum_card_divisors_eq (Y : ℕ) :
    ∑ n ∈ Icc 1 Y, n.divisors.card = ∑ d ∈ Icc 1 Y, Y / d := by
  have h := ArithmeticFunction.sum_Ioc_sigma0_eq_sum_div Y
  simp only [ArithmeticFunction.sigma_zero_apply] at h
  have hI : Icc 1 Y = Ioc 0 Y := by
    ext n
    simp only [mem_Icc, mem_Ioc]
    omega
  rw [hI]
  exact h

/-- Real upper bound `∑_{n ≤ Y} τ(n) ≤ Y (1 + log Y)`. -/
private theorem sum_card_divisors_le (Y : ℕ) :
    (∑ n ∈ Icc 1 Y, (n.divisors.card : ℝ)) ≤ Y * (1 + Real.log Y) := by
  have hcast : (∑ n ∈ Icc 1 Y, (n.divisors.card : ℝ)) =
      ∑ d ∈ Icc 1 Y, ((Y / d : ℕ) : ℝ) := by
    exact_mod_cast sum_card_divisors_eq Y
  have hterm : ∀ d ∈ Icc 1 Y, ((Y / d : ℕ) : ℝ) ≤ (Y : ℝ) * (d : ℝ)⁻¹ := by
    intro d _
    rw [← div_eq_mul_inv]
    exact Nat.cast_div_le
  have hharm : ((harmonic Y : ℚ) : ℝ) = ∑ d ∈ Icc 1 Y, (d : ℝ)⁻¹ := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    rfl
  calc (∑ n ∈ Icc 1 Y, (n.divisors.card : ℝ))
      = ∑ d ∈ Icc 1 Y, ((Y / d : ℕ) : ℝ) := hcast
    _ ≤ ∑ d ∈ Icc 1 Y, (Y : ℝ) * (d : ℝ)⁻¹ := sum_le_sum hterm
    _ = Y * ((harmonic Y : ℚ) : ℝ) := by rw [← mul_sum, hharm]
    _ ≤ Y * (1 + Real.log Y) :=
        mul_le_mul_of_nonneg_left (harmonic_le_one_add_log Y) (Nat.cast_nonneg Y)

/-- Real lower bound `Y log Y - Y ≤ ∑_{n ≤ Y} τ(n)`. -/
private theorem sum_card_divisors_ge (Y : ℕ) :
    Y * Real.log Y - Y ≤ (∑ n ∈ Icc 1 Y, (n.divisors.card : ℝ)) := by
  have hcast : (∑ n ∈ Icc 1 Y, (n.divisors.card : ℝ)) =
      ∑ d ∈ Icc 1 Y, ((Y / d : ℕ) : ℝ) := by
    exact_mod_cast sum_card_divisors_eq Y
  have hterm : ∀ d ∈ Icc 1 Y, (Y : ℝ) * (d : ℝ)⁻¹ - 1 ≤ ((Y / d : ℕ) : ℝ) := by
    intro d _
    rw [← div_eq_mul_inv, ← Nat.floor_div_eq_div (K := ℝ)]
    exact (Nat.sub_one_lt_floor _).le
  have hharm : ((harmonic Y : ℚ) : ℝ) = ∑ d ∈ Icc 1 Y, (d : ℝ)⁻¹ := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    rfl
  have hlog : Real.log Y ≤ ((harmonic Y : ℚ) : ℝ) := by
    have h1 := log_add_one_le_harmonic Y
    by_cases hY : Y = 0
    · subst hY; simp
    · have : Real.log Y ≤ Real.log ((Y + 1 : ℕ) : ℝ) := by
        apply Real.log_le_log (by positivity)
        push_cast; linarith
      linarith
  calc (Y : ℝ) * Real.log Y - Y
      ≤ Y * ((harmonic Y : ℚ) : ℝ) - Y := by
        have := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (α := ℝ) Y)
        linarith
    _ = ∑ d ∈ Icc 1 Y, ((Y : ℝ) * (d : ℝ)⁻¹ - 1) := by
        rw [sum_sub_distrib, ← mul_sum, ← hharm]
        simp
    _ ≤ ∑ d ∈ Icc 1 Y, ((Y / d : ℕ) : ℝ) := sum_le_sum hterm
    _ = _ := hcast.symm

/-- The `G`-sum over `[1, X]` dominates half the divisor-count sum over `[1, X/2]`,
    using only the even arguments `n = 2k` and `τ(k)/2 ≤ G(2k)`. -/
private theorem sum_card_divisors_half_le_sum_G (X : ℕ) :
    (∑ k ∈ Icc 1 (X / 2), (k.divisors.card : ℝ)) / 2 ≤
      (((Icc 1 X).sum G : ℚ) : ℝ) := by
  have hinj : Set.InjOn (fun k : ℕ => 2 * k) (Icc 1 (X / 2) : Set ℕ) := by
    intro a _ b _ h
    simp only at h
    omega
  have hsub : (Icc 1 (X / 2)).image (fun k : ℕ => 2 * k) ⊆ Icc 1 X := by
    intro n hn
    simp only [mem_image, mem_Icc] at hn ⊢
    omega
  have hterm : ∀ k ∈ Icc 1 (X / 2), (k.divisors.card : ℚ) / 2 ≤ G (2 * k) := by
    intro k hk
    have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
    have h := tau_div_le_G (2 * k) 2 (by omega) (dvd_mul_right 2 k) le_rfl
    rwa [Nat.mul_div_cancel_left k (by norm_num : 0 < 2)] at h
  have hQ : (∑ k ∈ Icc 1 (X / 2), (k.divisors.card : ℚ)) / 2 ≤ (Icc 1 X).sum G := by
    calc (∑ k ∈ Icc 1 (X / 2), (k.divisors.card : ℚ)) / 2
        = ∑ k ∈ Icc 1 (X / 2), (k.divisors.card : ℚ) / 2 := by rw [sum_div]
      _ ≤ ∑ k ∈ Icc 1 (X / 2), G (2 * k) := sum_le_sum hterm
      _ = ∑ n ∈ (Icc 1 (X / 2)).image (fun k : ℕ => 2 * k), G n :=
          (sum_image (fun a ha b hb h => hinj ha hb h)).symm
      _ ≤ (Icc 1 X).sum G :=
          sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => G_nonneg n)
  have hR := (Rat.cast_le (K := ℝ)).mpr hQ
  rw [Rat.cast_div, Rat.cast_sum] at hR
  push_cast at hR
  rw [Rat.cast_sum]
  exact hR

/-- **Mean order (archived, not a precise asymptotic formula)**:
    the sum `∑_{n≤X} G(n)` has order `X log X`, expressed by two-sided
    constants. This is weaker than the second question's request for
    an asymptotic formula; no literature-status claim for that question
    follows from the absence of a formal proof here. -/
theorem G_mean_order :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧
      ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
        c₁ * X * Real.log X ≤ (((Finset.Icc 1 X).sum G : ℚ) : ℝ) ∧
        (((Finset.Icc 1 X).sum G : ℚ) : ℝ) ≤ c₂ * X * Real.log X := by
  refine ⟨1 / 16, 2, by norm_num, by norm_num, 256, fun X hX => ?_⟩
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hXpos : (0 : ℝ) < X := by
    have : (256 : ℝ) ≤ X := by exact_mod_cast hX
    linarith
  have hlogX : 8 * Real.log 2 ≤ Real.log X := by
    have h256 : Real.log (256 : ℝ) = 8 * Real.log 2 := by
      rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]
      norm_num
    rw [← h256]
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hX)
  constructor
  · -- lower bound through the even terms
    set Y : ℕ := X / 2 with hYdef
    have hY1 : 1 ≤ Y := by omega
    have hYX : (X : ℝ) / 4 ≤ Y := by
      have h2 : X ≤ 2 * Y + 1 := by omega
      have h2' : (X : ℝ) ≤ 2 * Y + 1 := by exact_mod_cast h2
      have hY1' : (1 : ℝ) ≤ Y := by exact_mod_cast hY1
      linarith
    have hlogY : Real.log X - 2 * Real.log 2 ≤ Real.log Y := by
      have hX4 : (0 : ℝ) < X / 4 := by positivity
      have h := Real.log_le_log hX4 hYX
      rw [Real.log_div hXpos.ne' (by norm_num),
        show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at h
      push_cast at h
      linarith
    have hkey : Real.log X / 2 ≤ Real.log Y - 1 := by linarith
    have hlogXnn : 0 ≤ Real.log X := by linarith
    have hprod : (X : ℝ) / 4 * (Real.log X / 2) ≤ Y * (Real.log Y - 1) :=
      mul_le_mul hYX hkey (by positivity) (by positivity)
    have hT := sum_card_divisors_ge Y
    have hG := sum_card_divisors_half_le_sum_G X
    rw [← hYdef] at hG
    calc 1 / 16 * (X : ℝ) * Real.log X = (X / 4 * (Real.log X / 2)) / 2 := by ring
      _ ≤ (Y * (Real.log Y - 1)) / 2 := by linarith
      _ = (Y * Real.log Y - Y) / 2 := by ring
      _ ≤ (∑ k ∈ Icc 1 Y, (k.divisors.card : ℝ)) / 2 := by linarith
      _ ≤ _ := hG
  · -- upper bound through `G ≤ τ`
    have hterm : ∀ n ∈ Icc 1 X, ((G n : ℚ) : ℝ) ≤ (n.divisors.card : ℝ) := by
      intro n hn
      exact_mod_cast G_le_tau n (mem_Icc.mp hn).1
    have hsum : (((Icc 1 X).sum G : ℚ) : ℝ) ≤ ∑ n ∈ Icc 1 X, (n.divisors.card : ℝ) := by
      push_cast
      exact sum_le_sum hterm
    have hU := sum_card_divisors_le X
    have hone : 1 ≤ Real.log X := by linarith
    have hXX : (X : ℝ) * 1 ≤ X * Real.log X :=
      mul_le_mul_of_nonneg_left hone hXpos.le
    calc (((Icc 1 X).sum G : ℚ) : ℝ) ≤ ∑ n ∈ Icc 1 X, (n.divisors.card : ℝ) := hsum
      _ ≤ X * (1 + Real.log X) := hU
      _ ≤ 2 * X * Real.log X := by linarith

end MeanOrder

end ErdosCandidates.E673

/- SOURCE-FIDELITY REVIEW (corrected 2026-09-12)
   Verdict: CORRECTED LOWER STATEMENT; UPPER AND GROUND CHECKS IN PRODUCTION;
   LOWER AND ANALYTIC STATEMENTS STILL ARCHIVAL SORRIES
   - Verbatim statement matches `goof erdos fetch 673` exactly.
   - G(n) definition via zipWith on sorted divisors faithfully encodes
     sum of d_i/d_{i+1} over consecutive divisor pairs.
   - Arithmetic verified: G(12) = 37/12 correct (1/2+2/3+3/4+4/6+6/12);
     G(7) = 1/7 correct; G(1) = 0 correct (empty sum).
   - The live entry attributes tau(n/m)/m <= G(n) to Tao for any m | n,
     but its m = 1 boundary is false: n = 7 would require 2 <= 1/7.
   - The lower theorem is corrected to require 2 <= m; the upper bound is unchanged.
   - Even-n corollary tau(n)/4 <= G(n) remains correctly justified by
     tau(n) <= 2*tau(n/2) for even n.
   - Erdős–Tenenbaum distribution function and [Er82e] attribution correct.
   - Density-form Q1 encodes the first question, answered in the literature.
   - Mean-order bounds are weaker than the precise asymptotic requested in Q2.
-/
