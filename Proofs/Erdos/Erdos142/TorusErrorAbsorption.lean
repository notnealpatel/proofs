/-
  Erdős Problem #142 — real error-absorption kernel.

  This module isolates the purely real-analytic inequality that an eventual
  EHPS-shaped torus lower bound consumes when it replaces the two additive
  error terms `K` and `(log L)/2` by a single `(δ/2)·√L` allowance.

  The two hypotheses are exactly the two scale constraints that arise from the
  torus parameters (`TorusAsymptoticParameters`): a lower bound on `L` in terms
  of `δ`, and a bound on `K` in terms of `δ` and `L`.

  * `log_le_four_mul_sqrt_sqrt`: for `0 < L`, `log L ≤ 4·√√L`.
  * `eighth_div_delta_le_sqrt_sqrt`: the `4096/δ^4 ≤ L` hypothesis is
    equivalent to `8/δ ≤ √√L`.
  * `torusErrorAbsorption`: the main kernel
    `K + (log L)/2 ≤ (δ/2)·√L`.

  No `sorry`, no new axioms; the target is stated with explicit constants that
  downstream torus estimates can use verbatim.
-/

import Erdos.Erdos142.TorusAsymptoticParameters

set_option autoImplicit false

namespace Erdos142

/-- **Logarithm versus fourth root.**  For every real `L > 0`,
`Real.log L ≤ 4 · √√L`.

Writing `t = √√L` (so `t ≥ 0` and `t^4 = L`), `Real.log_pow` gives
`log L = 4·log t`, and `Real.log_le_self` gives `log t ≤ t`.  The bound holds
trivially when `L ≤ 1` as well, since then `log L ≤ 0 ≤ 4·√√L`. -/
lemma log_le_four_mul_sqrt_sqrt {L : ℝ} (hL : 0 < L) :
    Real.log L ≤ 4 * Real.sqrt (Real.sqrt L) := by
  set t := Real.sqrt (Real.sqrt L) with ht
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have ht2 : t ^ 2 = Real.sqrt L := Real.sq_sqrt (Real.sqrt_nonneg L)
  have ht4 : t ^ 4 = L := by
    rw [show t ^ 4 = (t ^ 2) ^ 2 by ring, ht2, Real.sq_sqrt hL.le]
  have hlog : Real.log L = 4 * Real.log t := by
    rw [← ht4, Real.log_pow]
    norm_num
  rw [hlog]
  have hself := Real.log_le_self ht0
  linarith

/-- **The `4096/δ^4` scale hypothesis is a fourth-root bound.**  For reals
`δ > 0`, `L > 0` with `4096/δ^4 ≤ L`, we have `8/δ ≤ √√L`.

Both `8/δ` and `√√L` are nonnegative and `(8/δ)^4 = 4096/δ^4 ≤ L = (√√L)^4`,
so `pow_le_pow_iff_left₀` at exponent `4` gives the claim. -/
lemma eighth_div_delta_le_sqrt_sqrt {δ L : ℝ} (hδ : 0 < δ) (hL : 0 < L)
    (h : 4096 / δ ^ 4 ≤ L) :
    8 / δ ≤ Real.sqrt (Real.sqrt L) := by
  set t := Real.sqrt (Real.sqrt L) with ht
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have ht2 : t ^ 2 = Real.sqrt L := Real.sq_sqrt (Real.sqrt_nonneg L)
  have ht4 : t ^ 4 = L := by
    rw [show t ^ 4 = (t ^ 2) ^ 2 by ring, ht2, Real.sq_sqrt hL.le]
  have h8 : (8 / δ) ^ 4 = 4096 / δ ^ 4 := by
    rw [div_pow]
    norm_num
  have hle : (8 / δ) ^ 4 ≤ t ^ 4 := by
    rw [h8, ht4]
    exact h
  have h8nn : 0 ≤ 8 / δ := by positivity
  exact (pow_le_pow_iff_left₀ h8nn ht0 (by norm_num : (4 : ℕ) ≠ 0)).mp hle

/-- **Real error-absorption kernel.**  For reals `δ, K, L` with `0 < δ`,
`0 ≤ K`, `4096/δ^4 ≤ L`, and `16·K^2/δ^2 ≤ L`,

`K + Real.log L / 2 ≤ (δ / 2) · Real.sqrt L`.

The two hypotheses bound the two summands against the same allowance `(δ/4)·√L`:

* `16·K^2/δ^2 ≤ L` gives `K^2 ≤ (δ·√L/4)^2`, hence `K ≤ δ·√L/4`;
* with `t = √√L` we have `t^4 = L` and `t > 0`, and `4096/δ^4 ≤ L` gives
  `8/δ ≤ t`, i.e. `8 ≤ δ·t`, hence `2·t ≤ δ·√L/4`;
* `log L ≤ 4·t` (from `log ≤ id` at `t`), so `(log L)/2 ≤ 2·t`.

Adding the two bounds gives `K + (log L)/2 ≤ 2·(δ/4)·√L = (δ/2)·√L`. -/
theorem torusErrorAbsorption {δ K L : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K)
    (hL1 : 4096 / δ ^ 4 ≤ L) (hL2 : 16 * K ^ 2 / δ ^ 2 ≤ L) :
    K + Real.log L / 2 ≤ (δ / 2) * Real.sqrt L := by
  have hLpos : 0 < L :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < 4096 / δ ^ 4) hL1
  set t := Real.sqrt (Real.sqrt L) with ht
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have ht2 : t ^ 2 = Real.sqrt L := Real.sq_sqrt (Real.sqrt_nonneg L)
  have ht4 : t ^ 4 = L := by
    rw [show t ^ 4 = (t ^ 2) ^ 2 by ring, ht2, Real.sq_sqrt hLpos.le]
  have htpos : 0 < t := by
    rcases ht0.eq_or_lt with h | h
    · rw [← h] at ht4
      simp at ht4
      linarith
    · exact h
  have hK2 : K ^ 2 ≤ (δ * Real.sqrt L / 4) ^ 2 := by
    have h16 : 16 * K ^ 2 ≤ L * δ ^ 2 :=
      (div_le_iff₀ (by positivity : (0 : ℝ) < δ ^ 2)).mp hL2
    have hsq : (δ * Real.sqrt L / 4) ^ 2 = δ ^ 2 * L / 16 := by
      rw [div_pow, mul_pow, Real.sq_sqrt hLpos.le]
      norm_num
    rw [hsq]
    nlinarith [h16]
  have hKle : K ≤ δ * Real.sqrt L / 4 := by
    have h0 : 0 ≤ δ * Real.sqrt L / 4 := by positivity
    calc K = Real.sqrt (K ^ 2) := (Real.sqrt_sq hK).symm
      _ ≤ Real.sqrt ((δ * Real.sqrt L / 4) ^ 2) := Real.sqrt_le_sqrt hK2
      _ = δ * Real.sqrt L / 4 := Real.sqrt_sq h0
  have hlog : Real.log L ≤ 4 * t := by
    have hlogeq : Real.log L = 4 * Real.log t := by
      rw [← ht4, Real.log_pow]
      norm_num
    rw [hlogeq]
    have hself := Real.log_le_self ht0
    linarith
  have hδt : 8 ≤ δ * t := by
    have h8t : 8 / δ ≤ t := eighth_div_delta_le_sqrt_sqrt hδ hLpos hL1
    have := (div_le_iff₀ hδ).mp h8t
    linarith
  have hmid : 2 * t ≤ δ * Real.sqrt L / 4 := by
    have hprod : 8 * t ≤ δ * t ^ 2 := by nlinarith [hδt, ht0]
    rw [← ht2]
    nlinarith [hprod]
  have hloghalf : Real.log L / 2 ≤ 2 * t := by linarith
  calc K + Real.log L / 2 ≤ δ * Real.sqrt L / 4 + 2 * t := add_le_add hKle hloghalf
    _ ≤ δ * Real.sqrt L / 4 + δ * Real.sqrt L / 4 := by linarith [hmid]
    _ = (δ / 2) * Real.sqrt L := by ring

-- Ground-truth checks.

/-- Boundary instance: the hypotheses are simultaneously satisfiable at
`δ = 1`, `K = 0`, `L = 4096` (both scale constraints hold with equality for the
first).  This witnesses non-vacuity of `torusErrorAbsorption`. -/
example : (0 : ℝ) + Real.log 4096 / 2 ≤ ((1 : ℝ) / 2) * Real.sqrt 4096 :=
  torusErrorAbsorption (δ := 1) (K := 0) (L := 4096)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Non-vacuous instance with positive `K`: at `δ = 1`, `L = 4096`, the
`K`-hypothesis `16·K^2 ≤ L` holds with equality at `K = 16`, so the additive
error term is genuinely present. -/
example : (16 : ℝ) + Real.log 4096 / 2 ≤ ((1 : ℝ) / 2) * Real.sqrt 4096 :=
  torusErrorAbsorption (δ := 1) (K := 16) (L := 4096)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Boundary instance at the `K`-scale threshold: `δ = 1`, `L = 65536`, `K = 64`
satisfies `16·K^2 = 65536 = L`, so the `K`-hypothesis is again tight while the
`L`-hypothesis `4096 ≤ L` is strict. -/
example : (64 : ℝ) + Real.log 65536 / 2 ≤ ((1 : ℝ) / 2) * Real.sqrt 65536 :=
  torusErrorAbsorption (δ := 1) (K := 64) (L := 65536)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

#print axioms log_le_four_mul_sqrt_sqrt
#print axioms eighth_div_delta_le_sqrt_sqrt
#print axioms torusErrorAbsorption

end Erdos142