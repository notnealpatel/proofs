/-
  Erdős Problem #142 — the positive square-product package for the Roth number.

  This module records the *unconditional*, positive-side arithmetic that the
  square-scale analysis of the #142 endpoint rests on.  It is deliberately
  separate from the concurrent fixed-envelope module: it introduces no generic
  name that module also publishes (`rothNumberNat_mul_le`,
  `rothNumberNat_mul_le_comm`), so it integrates independently atop accepted
  `main`.

  The object of study is the *square-scale multiplicativity defect*

      `X(N) = squareScaleDefect N = log (r₃(N)² / r₃(N²))`.

  `SquareScaleCriterion` shows that the #142 endpoint is *equivalent* to
  `X(N) = o(√(log N))`; the present module supplies the two elementary bounds
  that sandwich `X`, and the resulting one-sided asymptotic.

  * **Upper bound.**  The accepted sharp scale-product theorem
    `rothNumberNat_mul_le_rothNumberNat_sub`, plus monotonicity of `r₃`, gives
    the rounded product `r₃ N * r₃ ((M+1)/2) ≤ r₃ (N*M)`; combining it with the
    half comparison `r₃ M ≤ 2 · r₃ ((M+1)/2)` — supplied by iterated
    subadditivity of `r₃` (the `k`-fold `rothNumberNat_add_le`) — yields
    `r₃ N * r₃ M ≤ 2 · r₃ (N*M)` and its
    square specialization `r₃ N ^ 2 ≤ 2 · r₃ (N^2)`.  Hence
    `X(N) ≤ log 2` for `N ≥ 2`.

  * **Lower bound.**  The *same* iterated subadditivity, in the form
    `r₃ (N^2) ≤ N · r₃ N`, gives `-rothLogDeficit N ≤ X(N)` for `N ≥ 1`.

  * **Sandwich and asymptotic.**  Dividing by `√(log N) > 0` for `N ≥ 2` gives
    `-D(N) ≤ X(N)/√(log N) ≤ log 2 / √(log N)`, where
    `D(N) = normalizedDeficit r₃ N`.  Since `log 2 / √(log N) → 0`, the
    normalized defect `X(N)/√(log N)` is *eventually ≤ every* `ε > 0`.

  **This package is one-sided and unconditional.**  It does **not** claim that
  `X(N) ≥ 0` (the logarithm of the defect is *not* asserted nonnegative), does
  **not** claim that `X(N)/√(log N)` converges, and does **not** claim any lower
  `o`/`Ω` bound.  Its upper bound `X ≤ log 2` comes from the rounded
  scale-product inequality together with the half comparison, while its lower
  bound `-rothLogDeficit N ≤ X(N)` comes from iterated subadditivity in the form
  `r₃ (N^2) ≤ N · r₃ N` — not from the scale-product bound.

  No `sorry`, no `unsafe`, no new axioms, and no existing declaration is edited;
  the axiom audit is at the end of the file.
-/

import Erdos.Erdos142.ScaleProduct
import Erdos.Erdos142.ProductDefect
import Erdos.Erdos142.RegularityDiscriminator
import Mathlib.Combinatorics.Additive.AP.Three.Defs

set_option autoImplicit false

open Filter
open scoped Topology

namespace Erdos142

noncomputable section

/-! ## The square-scale defect -/

/-- The square-scale multiplicativity defect of the Roth number at `N`,
`X(N) = log (r₃(N)² / r₃(N²))`.  Its `o(√(log N))` behaviour is equivalent to
the #142 endpoint (`SquareScaleCriterion.tendsto_normalizedDeficit_zero_iff_square_defect`),
and it is the quantity bounded on both sides below. -/
def squareScaleDefect (N : ℕ) : ℝ :=
  Real.log (((rothNumberNat N : ℝ) ^ 2) / (rothNumberNat (N ^ 2) : ℝ))

/-- Ground-truth check: `squareScaleDefect` unfolds to the literal logarithmic
formula used throughout this file. -/
example (N : ℕ) :
    squareScaleDefect N =
      Real.log (((rothNumberNat N : ℝ) ^ 2) / (rothNumberNat (N ^ 2) : ℝ)) := rfl

/-! ## Iterated subadditivity of `r₃` -/

/-- **Iterated subadditivity.**  For all `k, N`,
`r₃ (k * N) ≤ k * r₃ N`.  This is the `k`-fold iteration of the accepted
subadditivity `rothNumberNat_add_le`, and it is the common arithmetic source of
both the upper and the lower square-scale bounds.

The name is deliberately distinct from the generic `rothNumberNat_mul_le` /
`rothNumberNat_mul_le_comm` helpers published by the concurrent fixed-envelope
module, so that this file does not collide with it on integration. -/
theorem rothNumberNat_mul_le_mul_rothNumberNat (k N : ℕ) :
    rothNumberNat (k * N) ≤ k * rothNumberNat N := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc rothNumberNat ((k + 1) * N)
        = rothNumberNat (k * N + N) := by rw [Nat.succ_mul]
      _ ≤ rothNumberNat (k * N) + rothNumberNat N := rothNumberNat_add_le (k * N) N
      _ ≤ k * rothNumberNat N + rothNumberNat N := Nat.add_le_add_right ih _
      _ = (k + 1) * rothNumberNat N := (Nat.succ_mul k (rothNumberNat N)).symm

/-! ## The rounded product bound -/

/-- **Rounded scale-product bound.**  For `N, M ≥ 1` with `K = (M + 1) / 2`,
`r₃ N * r₃ K ≤ r₃ (N * M)`.

The sharp scale-product bound `rothNumberNat_mul_le_rothNumberNat_sub` gives
`r₃ N * r₃ K ≤ r₃ (N * (2 * K - 1))`, and the elementary fact
`2 * K - 1 ≤ M` (where `K = (M + 1) / 2`) plus monotonicity of `r₃` upgrades the
endpoint `N * (2 * K - 1)` to `N * M`. -/
theorem rothNumberNat_mul_rothNumberNat_half_le (N M : ℕ) (_hN : 1 ≤ N) (hM : 1 ≤ M) :
    rothNumberNat N * rothNumberNat ((M + 1) / 2) ≤ rothNumberNat (N * M) := by
  have hsharp : rothNumberNat N * rothNumberNat ((M + 1) / 2) ≤
      rothNumberNat (N * (2 * ((M + 1) / 2) - 1)) := by
    have h := rothNumberNat_mul_le_rothNumberNat_sub N ((M + 1) / 2)
    have heq : 2 * N * ((M + 1) / 2) - N = N * (2 * ((M + 1) / 2) - 1) := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_one]
      ring_nf
    rwa [heq] at h
  have hKM : 2 * ((M + 1) / 2) - 1 ≤ M := by omega
  exact hsharp.trans (rothNumberNat.monotone (Nat.mul_le_mul_left N hKM))

/-! ## The half comparison and the core product bound -/

/-- **Half comparison.**  For every `M` (in particular `M ≥ 1`),
`r₃ M ≤ 2 * r₃ ((M + 1) / 2)`.

Since `M ≤ 2 * ((M + 1) / 2)`, monotonicity of `r₃` and the `k = 2` instance of
iterated subadditivity `r₃ (2 * K) ≤ 2 * r₃ K` close the bound at `K = (M+1)/2`. -/
theorem rothNumberNat_le_two_mul_rothNumberNat_half (M : ℕ) :
    rothNumberNat M ≤ 2 * rothNumberNat ((M + 1) / 2) := by
  have hMle : M ≤ 2 * ((M + 1) / 2) := by omega
  calc rothNumberNat M ≤ rothNumberNat (2 * ((M + 1) / 2)) := rothNumberNat.monotone hMle
    _ ≤ 2 * rothNumberNat ((M + 1) / 2) :=
        rothNumberNat_mul_le_mul_rothNumberNat 2 ((M + 1) / 2)

/-- **Core product bound.**  For `N, M ≥ 1`,
`r₃ N * r₃ M ≤ 2 * r₃ (N * M)`.

Multiply the half comparison `r₃ M ≤ 2 * r₃ ((M+1)/2)` by `r₃ N` and apply the
rounded scale-product bound `r₃ N * r₃ ((M+1)/2) ≤ r₃ (N*M)`. -/
theorem rothNumberNat_mul_le_two_mul_rothNumberNat_mul (N M : ℕ) (hN : 1 ≤ N)
    (hM : 1 ≤ M) :
    rothNumberNat N * rothNumberNat M ≤ 2 * rothNumberNat (N * M) := by
  have hhalf := rothNumberNat_le_two_mul_rothNumberNat_half M
  have hmul := Nat.mul_le_mul_left (rothNumberNat N) hhalf
  have hbase := rothNumberNat_mul_rothNumberNat_half_le N M hN hM
  calc rothNumberNat N * rothNumberNat M
      ≤ rothNumberNat N * (2 * rothNumberNat ((M + 1) / 2)) := hmul
    _ = 2 * (rothNumberNat N * rothNumberNat ((M + 1) / 2)) := by ring
    _ ≤ 2 * rothNumberNat (N * M) := Nat.mul_le_mul_left 2 hbase

/-- **Square specialization.**  For `N ≥ 1`, `r₃ N ^ 2 ≤ 2 * r₃ (N ^ 2)`; this is
the core product bound at `M = N`, with `r₃ N * r₃ N = r₃ N ^ 2` and
`N * N = N ^ 2`. -/
theorem rothNumberNat_sq_le_two_mul_rothNumberNat_sq (N : ℕ) (hN : 1 ≤ N) :
    rothNumberNat N ^ 2 ≤ 2 * rothNumberNat (N ^ 2) := by
  have h := rothNumberNat_mul_le_two_mul_rothNumberNat_mul N N hN hN
  simpa [pow_two] using h

/-! ## The logarithmic upper bound on the square-scale defect -/

/-- **Upper logarithmic bound.**  For `N ≥ 2`,
`X(N) = log (r₃(N)² / r₃(N²)) ≤ log 2`.

The square specialization `r₃ N ^ 2 ≤ 2 * r₃ (N^2)` and positivity of
`r₃ (N^2)` give `r₃(N)² / r₃(N²) ≤ 2`; monotonicity of `log` on the positive
reals closes the bound. -/
theorem log_squareScaleDefect_le_log_two (N : ℕ) (hN : 2 ≤ N) :
    squareScaleDefect N ≤ Real.log 2 := by
  have hN1 : 1 ≤ N := by omega
  have hsq : 1 ≤ N ^ 2 := Nat.one_le_pow 2 N (by omega)
  have hR : (0 : ℝ) < (rothNumberNat N : ℝ) := rothNumberNat_pos_real hN1
  have hR2 : (0 : ℝ) < (rothNumberNat (N ^ 2) : ℝ) := rothNumberNat_pos_real hsq
  have hcast : ((rothNumberNat N : ℝ) ^ 2) ≤ 2 * (rothNumberNat (N ^ 2) : ℝ) := by
    have := rothNumberNat_sq_le_two_mul_rothNumberNat_sq N hN1
    exact_mod_cast this
  have hratio : ((rothNumberNat N : ℝ) ^ 2) / (rothNumberNat (N ^ 2) : ℝ) ≤ 2 := by
    rw [div_le_iff₀ hR2]
    linarith
  have hpos : 0 < ((rothNumberNat N : ℝ) ^ 2) / (rothNumberNat (N ^ 2) : ℝ) :=
    div_pos (pow_pos hR 2) hR2
  rw [squareScaleDefect]
  exact Real.log_le_log hpos hratio

/-! ## The subadditive lower bound on the square-scale defect -/

/-- **Lower logarithmic bound.**  For `N ≥ 1`,
`-rothLogDeficit N ≤ X(N)`, where `rothLogDeficit N = log (N / r₃ N)`.

Iterated subadditivity at `(k, N) = (N, N)` reads `r₃ (N^2) ≤ N * r₃ N`; taking
logarithms, `log r₃(N²) ≤ log N + log r₃ N`, so
`X(N) = 2 log r₃ N - log r₃(N²) ≥ log r₃ N - log N = -rothLogDeficit N`. -/
theorem neg_rothLogDeficit_le_squareScaleDefect (N : ℕ) (hN : 1 ≤ N) :
    -rothLogDeficit N ≤ squareScaleDefect N := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hsq : 1 ≤ N ^ 2 := Nat.one_le_pow 2 N (by omega)
  have hR : (0 : ℝ) < (rothNumberNat N : ℝ) := rothNumberNat_pos_real hN
  have hR2 : (0 : ℝ) < (rothNumberNat (N ^ 2) : ℝ) := rothNumberNat_pos_real hsq
  have hsub : rothNumberNat (N ^ 2) ≤ N * rothNumberNat N := by
    simpa [pow_two] using rothNumberNat_mul_le_mul_rothNumberNat N N
  have hcast : (rothNumberNat (N ^ 2) : ℝ) ≤ (N : ℝ) * (rothNumberNat N : ℝ) := by
    exact_mod_cast hsub
  have hlogle : Real.log (rothNumberNat (N ^ 2) : ℝ) ≤
      Real.log (N : ℝ) + Real.log (rothNumberNat N : ℝ) := by
    have h := Real.log_le_log hR2 hcast
    rwa [Real.log_mul (ne_of_gt hNpos) (ne_of_gt hR)] at h
  have hlogeq : squareScaleDefect N =
      2 * Real.log (rothNumberNat N : ℝ) - Real.log (rothNumberNat (N ^ 2) : ℝ) := by
    rw [squareScaleDefect, Real.log_div (pow_ne_zero 2 (ne_of_gt hR)) (ne_of_gt hR2),
      Real.log_pow]
    norm_num
  rw [hlogeq, rothLogDeficit_eq hN]
  linarith

/-! ## The normalized sandwich -/

/-- **Normalized square-scale sandwich.**  For `N ≥ 2`, with
`D(N) = normalizedDeficit r₃ N`,

`-D(N) ≤ X(N) / √(log N) ≤ log 2 / √(log N)`.

The lower half is the subadditive bound `-rothLogDeficit N ≤ X(N)` divided by
`√(log N) ≥ 0` (using `normalizedDeficit r₃ N = rothLogDeficit N / √(log N)`);
the upper half is the logarithmic bound `X(N) ≤ log 2` divided likewise. -/
theorem squareScaleDefect_normalized_sandwich (N : ℕ) (hN : 2 ≤ N) :
    -normalizedDeficit rothNumberNat N ≤ squareScaleDefect N / Real.sqrt (Real.log (N : ℝ)) ∧
      squareScaleDefect N / Real.sqrt (Real.log (N : ℝ)) ≤
        Real.log 2 / Real.sqrt (Real.log (N : ℝ)) := by
  have hs : (0 : ℝ) ≤ Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_nonneg _
  constructor
  · have h := neg_rothLogDeficit_le_squareScaleDefect N (by omega)
    have hleft : -normalizedDeficit rothNumberNat N =
        -rothLogDeficit N / Real.sqrt (Real.log (N : ℝ)) := by
      rw [normalizedDeficit, logDeficit, rothLogDeficit]
      ring
    rw [hleft]
    exact div_le_div_of_nonneg_right h hs
  · exact div_le_div_of_nonneg_right (log_squareScaleDefect_le_log_two N hN) hs

/-! ## The one-sided asymptotic -/

/-- **One-sided asymptotic.**  For every `ε > 0`, the normalized square-scale
defect is eventually at most `ε`:

`∀ᶠ N in atTop, X(N) / √(log N) ≤ ε`.

This follows from the sandwich upper half and `log 2 / √(log N) → 0`, because
`√(log N) → ∞`.  It is deliberately stated in this eventual/every-`ε` form: it
asserts only an upper bound and **not** convergence of `X(N)/√(log N)`, and it
makes **no** lower (`o`/`Ω`) claim. -/
theorem eventually_squareScaleDefect_normalized_le (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      squareScaleDefect N / Real.sqrt (Real.log (N : ℝ)) ≤ ε := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsqrt : Tendsto (fun N : ℕ => Real.sqrt (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hlog
  have hlim : Tendsto (fun N : ℕ => Real.log 2 / Real.sqrt (Real.log (N : ℝ)))
      atTop (𝓝 0) := hsqrt.const_div_atTop (Real.log 2)
  have hev : ∀ᶠ N : ℕ in atTop,
      Real.log 2 / Real.sqrt (Real.log (N : ℝ)) ≤ ε :=
    hlim.eventually (eventually_le_nhds hε)
  filter_upwards [hev, eventually_ge_atTop 2] with N hle hN
  exact (squareScaleDefect_normalized_sandwich N hN).2.trans hle

/-! ## Ground-truth checks and examples -/

/-- Ground-truth check of iterated subadditivity at `k = 1`. -/
example (N : ℕ) : rothNumberNat (1 * N) ≤ 1 * rothNumberNat N :=
  rothNumberNat_mul_le_mul_rothNumberNat 1 N

/-- Ground-truth check of iterated subadditivity at `k = 2`, `N = 3`: the
Roth number is subadditive along multiples. -/
example : rothNumberNat (2 * 3) ≤ 2 * rothNumberNat 3 :=
  rothNumberNat_mul_le_mul_rothNumberNat 2 3

/-- Ground-truth check of the rounded product bound at `(N, M) = (1, 1)`, where
`K = (1 + 1) / 2 = 1` and both sides are `r₃ 1 = 1`. -/
example : rothNumberNat 1 * rothNumberNat ((1 + 1) / 2) ≤ rothNumberNat (1 * 1) :=
  rothNumberNat_mul_rothNumberNat_half_le 1 1 le_rfl le_rfl

/-- Ground-truth check of the half comparison at `M = 2`: `r₃ 2 ≤ 2 * r₃ 1`. -/
example : rothNumberNat 2 ≤ 2 * rothNumberNat ((2 + 1) / 2) :=
  rothNumberNat_le_two_mul_rothNumberNat_half 2

/-- Ground-truth check of the core product bound at `(N, M) = (2, 2)`. -/
example : rothNumberNat 2 * rothNumberNat 2 ≤ 2 * rothNumberNat (2 * 2) :=
  rothNumberNat_mul_le_two_mul_rothNumberNat_mul 2 2 (by norm_num) (by norm_num)

/-- Ground-truth check of the square specialization at `N = 3`. -/
example : rothNumberNat 3 ^ 2 ≤ 2 * rothNumberNat (3 ^ 2) :=
  rothNumberNat_sq_le_two_mul_rothNumberNat_sq 3 (by norm_num)

/-- Satisfiability of the upper logarithmic bound's hypothesis, exhibited at
`N = 2`. -/
example : squareScaleDefect 2 ≤ Real.log 2 := log_squareScaleDefect_le_log_two 2 (by norm_num)

/-- Satisfiability of the lower logarithmic bound's hypothesis, exhibited at
`N = 1`. -/
example : -rothLogDeficit 1 ≤ squareScaleDefect 1 :=
  neg_rothLogDeficit_le_squareScaleDefect 1 le_rfl

/-- Satisfiability of the sandwich at `N = 2`, both halves simultaneously. -/
example :
    -normalizedDeficit rothNumberNat 2 ≤ squareScaleDefect 2 / Real.sqrt (Real.log (2 : ℝ)) ∧
      squareScaleDefect 2 / Real.sqrt (Real.log (2 : ℝ)) ≤
        Real.log 2 / Real.sqrt (Real.log (2 : ℝ)) :=
  squareScaleDefect_normalized_sandwich 2 (by norm_num)

/-- Satisfiability of the one-sided asymptotic at `ε = 1`. -/
example : ∀ᶠ N : ℕ in atTop,
    squareScaleDefect N / Real.sqrt (Real.log (N : ℝ)) ≤ 1 :=
  eventually_squareScaleDefect_normalized_le 1 (by norm_num)

end

-- Axiom audit for the load-bearing declarations.
#print axioms Erdos142.rothNumberNat_mul_le_mul_rothNumberNat
#print axioms Erdos142.rothNumberNat_mul_rothNumberNat_half_le
#print axioms Erdos142.rothNumberNat_le_two_mul_rothNumberNat_half
#print axioms Erdos142.rothNumberNat_mul_le_two_mul_rothNumberNat_mul
#print axioms Erdos142.rothNumberNat_sq_le_two_mul_rothNumberNat_sq
#print axioms Erdos142.log_squareScaleDefect_le_log_two
#print axioms Erdos142.neg_rothLogDeficit_le_squareScaleDefect
#print axioms Erdos142.squareScaleDefect_normalized_sandwich
#print axioms Erdos142.eventually_squareScaleDefect_normalized_le

end Erdos142
