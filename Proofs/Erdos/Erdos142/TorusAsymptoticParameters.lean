/-
  Erdős Problem #142 — asymptotic torus parameters.

  This module isolates the *parameter* lemmas that an eventual EHPS-shaped
  lower bound for `rothNumberNat` consumes, independently of the full `δ`
  theorem.

  * `torusRadius N q k = ⌊q · N^(-1/(2k)) / 2⌋` is the integer torus radius.
  * `torusRadius_spec` bundles, under `64 ≤ N`, `N ≤ q`, `1 ≤ k`:
    - nonvanishing: `1 ≤ torusRadius N q k`;
    - `1/4`-scale lower bound: `q · N^(-1/(2k)) / 4 ≤ torusRadius N q k`;
    - `2·`-scale upper bound: `2 · torusRadius N q k ≤ q · N^(-1/(2k))`;
    - strict scale inequality (a `ℕ`-inequality):
      `N · (2 · torusRadius N q k - 1)^(2*k) < q^(2*k)`.
  * `torusRadius_ratio_lower` is the real ratio lower bound for `6 ≤ e`.

  The strict scale proof explicitly handles `ℕ`-subtraction and casts and uses
  the `-1` strictness together with `exp(-log N) = 1/N`.

  No `sorry`, no new axioms; every declaration of `TorusLowerBound` is reused
  verbatim.
-/

import Erdos.Erdos142.TorusLowerBound

set_option autoImplicit false

namespace Erdos142

/-- The integer torus radius at resolution `N`, modulus `q`, and exponent `k`:
`⌊q · exp(-log N / (2k)) / 2⌋`, the integer part of half of the `k`-th-root
rescaling `q · N^(-1/(2k))`.  Here `q` is an arbitrary natural modulus; primality
is not required by this definition or by the radius lemmas, and is supplied only
by the later Roth/torus application.  The factors `1/2` (upper bound) and `1/4`
(lower bound) in `torusRadius_spec` match this halving. -/
noncomputable def torusRadius (N q k : ℕ) : ℕ :=
  Nat.floor ((q : ℝ) * Real.exp (-(Real.log N) / (2 * (k : ℝ))) / 2)

/-- **Scale dominates `8`.**  For `64 ≤ N ≤ q` and `1 ≤ k`, the rescaling
`q · exp(-log N / (2k))` is at least `8`.

Writing `s = exp(-log N / (2k))`, monotonicity of `exp` and `2 ≤ 2k` give
`s ≥ exp(-log N / 2) = 1/√N`, so `q·s ≥ N·s ≥ √N ≥ √64 = 8`. -/
lemma eight_le_q_mul_exp_scale {N q k : ℕ} (hN : 64 ≤ N) (hNq : N ≤ q) (hk : 1 ≤ k) :
    (8 : ℝ) ≤ (q : ℝ) * Real.exp (-(Real.log N) / (2 * (k : ℝ))) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hNr : (0 : ℝ) < (N : ℝ) := by linarith
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have htwo_le : (2 : ℝ) ≤ 2 * (k : ℝ) := by linarith
  have hdiv : Real.log N / (2 * (k : ℝ)) ≤ Real.log N / 2 :=
    div_le_div_of_nonneg_left hlog (by norm_num) htwo_le
  have hneg : -(Real.log N) / 2 ≤ -(Real.log N) / (2 * (k : ℝ)) :=
    calc -(Real.log N) / 2 = -(Real.log N / 2) := by ring
      _ ≤ -(Real.log N / (2 * (k : ℝ))) := neg_le_neg hdiv
      _ = -(Real.log N) / (2 * (k : ℝ)) := by ring
  have hmono : Real.exp (-(Real.log N) / 2) ≤
      Real.exp (-(Real.log N) / (2 * (k : ℝ))) := Real.exp_le_exp.mpr hneg
  have heq : Real.exp (-(Real.log N) / 2) = (Real.sqrt N)⁻¹ := by
    rw [show -(Real.log N) / 2 = -(Real.log N / 2) by ring, Real.exp_neg, Real.exp_half,
      Real.exp_log hNr]
  have hsqrt_inv : (Real.sqrt N)⁻¹ ≤ Real.exp (-(Real.log N) / (2 * (k : ℝ))) := by
    rw [← heq]; exact hmono
  have hqN : (N : ℝ) ≤ (q : ℝ) := by exact_mod_cast hNq
  have hs_nonneg : 0 ≤ Real.exp (-(Real.log N) / (2 * (k : ℝ))) := (Real.exp_pos _).le
  have hNscaled : (N : ℝ) * (Real.sqrt N)⁻¹ ≤
      (N : ℝ) * Real.exp (-(Real.log N) / (2 * (k : ℝ))) :=
    mul_le_mul_of_nonneg_left hsqrt_inv hNr.le
  have hNinv : (N : ℝ) * (Real.sqrt N)⁻¹ = Real.sqrt N := by
    rw [← div_eq_mul_inv, Real.div_sqrt]
  have hsqrt_ge : (8 : ℝ) ≤ Real.sqrt N := by
    have h64 : Real.sqrt 64 = 8 := by
      rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← h64]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hN)
  calc (8 : ℝ) ≤ Real.sqrt N := hsqrt_ge
    _ = (N : ℝ) * (Real.sqrt N)⁻¹ := hNinv.symm
    _ ≤ (N : ℝ) * Real.exp (-(Real.log N) / (2 * (k : ℝ))) := hNscaled
    _ ≤ (q : ℝ) * Real.exp (-(Real.log N) / (2 * (k : ℝ))) :=
        mul_le_mul_of_nonneg_right hqN hs_nonneg

/-- **Nonvanishing of the radius.**  Under `64 ≤ N ≤ q` and `1 ≤ k` the
radius is at least `1`.  Indeed `q·s ≥ 8` gives `q·s/2 ≥ 4`, so
`torusRadius N q k = ⌊q·s/2⌋ ≥ ⌊4⌋ = 4 ≥ 1`. -/
lemma one_le_torusRadius {N q k : ℕ} (hN : 64 ≤ N) (hNq : N ≤ q) (hk : 1 ≤ k) :
    1 ≤ torusRadius N q k := by
  have h8 := eight_le_q_mul_exp_scale hN hNq hk
  have h4 : (4 : ℝ) ≤ (q : ℝ) * Real.exp (-(Real.log N) / (2 * (k : ℝ))) / 2 := by
    linarith
  have hfloor : (4 : ℕ) ≤ torusRadius N q k := by
    rw [torusRadius]
    exact Nat.le_floor h4
  omega

/-- **`1/4`-scale lower bound.**  Under `64 ≤ N ≤ q` and `1 ≤ k`,
`q·s/4 ≤ torusRadius N q k` where `s = exp(-log N / (2k))`.

`Nat.sub_one_lt_floor` gives `q·s/2 - 1 < ⌊q·s/2⌋`, and `q·s ≥ 8` gives
`q·s/4 ≤ q·s/2 - 1`, so the floor exceeds `q·s/4`. -/
lemma scale_div_four_le_torusRadius {N q k : ℕ} (hN : 64 ≤ N) (hNq : N ≤ q)
    (hk : 1 ≤ k) :
    (q : ℝ) * Real.exp (-(Real.log N) / (2 * (k : ℝ))) / 4 ≤ (torusRadius N q k : ℝ) := by
  have h8 := eight_le_q_mul_exp_scale hN hNq hk
  have hsub : (q : ℝ) * Real.exp (-(Real.log N) / (2 * (k : ℝ))) / 2 - 1 <
      (torusRadius N q k : ℝ) := by
    rw [torusRadius]
    exact Nat.sub_one_lt_floor _
  have hfrac : (q : ℝ) * Real.exp (-(Real.log N) / (2 * (k : ℝ))) / 4 ≤
      (q : ℝ) * Real.exp (-(Real.log N) / (2 * (k : ℝ))) / 2 - 1 := by
    linarith
  linarith

set_option linter.unusedVariables false in
/-- **`2·`-scale upper bound.**  Under `64 ≤ N ≤ q` and `1 ≤ k`,
`2 · torusRadius N q k ≤ q·s` where `s = exp(-log N / (2k))`.

This is exactly `Nat.floor_le`: the floor of `q·s/2` does not exceed `q·s/2`.
The hypotheses are carried for a uniform interface with `torusRadius_spec`; the
bound itself holds unconditionally. -/
lemma two_mul_torusRadius_le {N q k : ℕ} (hN : 64 ≤ N) (hNq : N ≤ q) (hk : 1 ≤ k) :
    2 * (torusRadius N q k : ℝ) ≤ (q : ℝ) * Real.exp (-(Real.log N) / (2 * (k : ℝ))) := by
  have hx : (0 : ℝ) ≤ (q : ℝ) * Real.exp (-(Real.log N) / (2 * (k : ℝ))) / 2 := by
    positivity
  have hfloor : (torusRadius N q k : ℝ) ≤
      (q : ℝ) * Real.exp (-(Real.log N) / (2 * (k : ℝ))) / 2 := by
    rw [torusRadius]
    exact Nat.floor_le hx
  linarith

/-- **Strict scale inequality.**  Under `64 ≤ N ≤ q` and `1 ≤ k`,
`N · (2 · torusRadius N q k - 1)^(2*k) < q^(2*k)` as a `ℕ`-inequality.

The upper bound `2·R ≤ q·s` gives `2·R - 1 < q·s`, since the natural
`2·R - 1` casts to `2·R - 1` (as `2·R ≥ 1`).  Raising to `2*k` and using
`s^(2*k) = exp(-log N) = 1/N` turns the right side into `q^(2*k)/N`; multiplying
by `N > 0` and casting back to `ℕ` gives the claim. -/
lemma torusRadius_scale_lt {N q k : ℕ} (hN : 64 ≤ N) (hNq : N ≤ q) (hk : 1 ≤ k) :
    N * (2 * torusRadius N q k - 1) ^ (2 * k) < q ^ (2 * k) := by
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hR1 := one_le_torusRadius hN hNq hk
  have h2R1 : 1 ≤ 2 * torusRadius N q k := by omega
  have hRhi := two_mul_torusRadius_le hN hNq hk
  have hcast : ((2 * torusRadius N q k - 1 : ℕ) : ℝ) =
      2 * (torusRadius N q k : ℝ) - 1 := by
    rw [Nat.cast_sub h2R1]
    push_cast
    ring
  have hlt : ((2 * torusRadius N q k - 1 : ℕ) : ℝ) <
      (q : ℝ) * Real.exp (-(Real.log N) / (2 * (k : ℝ))) := by
    rw [hcast]
    linarith
  have hpowlt : (((2 * torusRadius N q k - 1 : ℕ) : ℝ)) ^ (2 * k) <
      ((q : ℝ) * Real.exp (-(Real.log N) / (2 * (k : ℝ)))) ^ (2 * k) :=
    pow_lt_pow_left₀ hlt (by positivity) (by omega : 2 * k ≠ 0)
  have hspow : Real.exp (-(Real.log N) / (2 * (k : ℝ))) ^ (2 * k) = (N : ℝ)⁻¹ := by
    rw [← Real.exp_nat_mul]
    have hprod : (((2 * k : ℕ)) : ℝ) * (-(Real.log N) / (2 * (k : ℝ))) = -(Real.log N) := by
      push_cast
      field_simp
    rw [hprod, Real.exp_neg, Real.exp_log hNr]
  have hqpow : ((q : ℝ) * Real.exp (-(Real.log N) / (2 * (k : ℝ)))) ^ (2 * k) =
      (q : ℝ) ^ (2 * k) * (N : ℝ)⁻¹ := by
    rw [mul_pow, hspow]
  have hkey : (N : ℝ) * (((2 * torusRadius N q k - 1 : ℕ) : ℝ)) ^ (2 * k) <
      (q : ℝ) ^ (2 * k) := by
    have h1 : (N : ℝ) * (((2 * torusRadius N q k - 1 : ℕ) : ℝ)) ^ (2 * k) <
        (N : ℝ) * ((q : ℝ) * Real.exp (-(Real.log N) / (2 * (k : ℝ)))) ^ (2 * k) :=
      mul_lt_mul_of_pos_left hpowlt hNr
    rw [hqpow] at h1
    have hNinv : (N : ℝ) * (N : ℝ)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hNr)
    calc (N : ℝ) * (((2 * torusRadius N q k - 1 : ℕ) : ℝ)) ^ (2 * k)
        < (N : ℝ) * ((q : ℝ) ^ (2 * k) * (N : ℝ)⁻¹) := h1
      _ = (q : ℝ) ^ (2 * k) := by
          rw [mul_comm ((q : ℝ) ^ (2 * k)) (N : ℝ)⁻¹, ← mul_assoc, hNinv, one_mul]
  rw [← Nat.cast_pow (α := ℝ) (2 * torusRadius N q k - 1),
    ← Nat.cast_pow (α := ℝ) q] at hkey
  exact_mod_cast hkey

/-- **Bundled radius specification.**  For naturals `N, q, k` with `64 ≤ N`,
`N ≤ q`, `1 ≤ k`, the torus radius satisfies all four parameter facts at once:
nonvanishing, the `1/4`-scale lower bound, the `2·`-scale upper bound, and the
strict scale inequality. -/
theorem torusRadius_spec {N q k : ℕ} (hN : 64 ≤ N) (hNq : N ≤ q) (hk : 1 ≤ k) :
    1 ≤ torusRadius N q k ∧
    (q : ℝ) * Real.exp (-(Real.log N) / (2 * (k : ℝ))) / 4 ≤ (torusRadius N q k : ℝ) ∧
    2 * (torusRadius N q k : ℝ) ≤ (q : ℝ) * Real.exp (-(Real.log N) / (2 * (k : ℝ))) ∧
    N * (2 * torusRadius N q k - 1) ^ (2 * k) < q ^ (2 * k) :=
  ⟨one_le_torusRadius hN hNq hk, scale_div_four_le_torusRadius hN hNq hk,
    two_mul_torusRadius_le hN hNq hk, torusRadius_scale_lt hN hNq hk⟩

/-- **Real ratio lower bound.**  For `64 ≤ N ≤ q`, `1 ≤ k`, and any real `6 ≤ e`,
with `R = torusRadius N q k`,

`exp(-log N / k) / (660·k·e^2) ≤ R^2 / (41·k·e^2·q^2 + R^2)`.

Writing `s = exp(-log N / (2k))` (so `s^2 = exp(-log N / k)`), the radius
bounds give `q·s/4 ≤ R ≤ q·s/2`, hence `R^2 ≤ q^2·s^2/4` and
`R^2 ≥ q^2·s^2/16`.  Since `s ≤ 1 ≤ k·e^2`, the upper bound gives
`R^2·s^2 ≤ k·e^2·q^2·s^2/4`, so the numerator satisfies
`exp(-log N/k)·(41·k·e^2·q^2 + R^2) ≤ (165/4)·k·e^2·q^2·s^2`, while the lower
bound gives `R^2·(660·k·e^2) ≥ (165/4)·k·e^2·q^2·s^2`.  Cross-multiplying (both
denominators are positive) finishes. -/
theorem torusRadius_ratio_lower {N q k : ℕ} {e : ℝ} (hN : 64 ≤ N) (hNq : N ≤ q)
    (hk : 1 ≤ k) (he : 6 ≤ e) :
    Real.exp (-(Real.log N) / (k : ℝ)) / (660 * (k : ℝ) * e ^ 2) ≤
      (torusRadius N q k : ℝ) ^ 2 /
        (41 * (k : ℝ) * e ^ 2 * (q : ℝ) ^ 2 + (torusRadius N q k : ℝ) ^ 2) := by
  set s := Real.exp (-(Real.log N) / (2 * (k : ℝ))) with hs
  set R := (torusRadius N q k : ℝ) with hR
  set T := Real.exp (-(Real.log N) / (k : ℝ)) with hT
  have hRlo : (q : ℝ) * s / 4 ≤ R := by
    rw [hs, hR]
    exact scale_div_four_le_torusRadius hN hNq hk
  have hRhi : 2 * R ≤ (q : ℝ) * s := by
    rw [hs, hR]
    exact two_mul_torusRadius_le hN hNq hk
  have hR1 : (1 : ℝ) ≤ R := by
    rw [hR]
    exact_mod_cast one_le_torusRadius hN hNq hk
  have hRpos : 0 < R := by linarith
  have hs0 : 0 ≤ s := by rw [hs]; exact (Real.exp_pos _).le
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := by positivity
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have he1 : (1 : ℝ) ≤ e := by linarith
  have hs1 : s ≤ 1 := by
    rw [hs, Real.exp_le_one_iff]
    have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
    have hkpos : (0 : ℝ) < 2 * (k : ℝ) := by linarith
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hlog) hkpos.le
  have hT2 : T = s ^ 2 := by
    rw [hT, hs, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hs2le : s ^ 2 ≤ (k : ℝ) * e ^ 2 := by
    have hsq : s ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hs0 hs1 2
    have he2 : (1 : ℝ) ≤ e ^ 2 := by nlinarith [he1]
    have h1 : (1 : ℝ) ≤ (k : ℝ) * e ^ 2 := by
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := by linarith
      have := mul_le_mul hk1 he2 (by norm_num) hk0
      simpa using this
    linarith
  have hR2hi : R ^ 2 ≤ ((q : ℝ) * s / 2) ^ 2 := by
    have hle : R ≤ (q : ℝ) * s / 2 := by linarith
    exact pow_le_pow_left₀ hRpos.le hle 2
  have hR2lo : ((q : ℝ) * s / 4) ^ 2 ≤ R ^ 2 := by
    have h0 : 0 ≤ (q : ℝ) * s / 4 := by positivity
    have hle : (q : ℝ) * s / 4 ≤ R := hRlo
    exact pow_le_pow_left₀ h0 hle 2
  have hD1 : 0 < 660 * (k : ℝ) * e ^ 2 := by positivity
  have hD2 : 0 < 41 * (k : ℝ) * e ^ 2 * (q : ℝ) ^ 2 + R ^ 2 := by
    have hsq : 0 < R ^ 2 := pow_pos hRpos 2
    have hterm : 0 ≤ 41 * (k : ℝ) * e ^ 2 * (q : ℝ) ^ 2 := by positivity
    linarith
  rw [div_le_div_iff₀ hD1 hD2, hT2]
  have hRs2 : R ^ 2 * s ^ 2 ≤ (k : ℝ) * e ^ 2 * (q : ℝ) ^ 2 * s ^ 2 / 4 := by
    have h1 : R ^ 2 * s ^ 2 ≤ ((q : ℝ) * s / 2) ^ 2 * s ^ 2 :=
      mul_le_mul_of_nonneg_right hR2hi (sq_nonneg s)
    have h2 : ((q : ℝ) * s / 2) ^ 2 * s ^ 2 = (q : ℝ) ^ 2 * s ^ 4 / 4 := by ring
    have h3 : s ^ 4 ≤ (k : ℝ) * e ^ 2 * s ^ 2 := by
      have h := mul_le_mul_of_nonneg_right hs2le (sq_nonneg s)
      nlinarith [h]
    nlinarith [h1, h2, h3, sq_nonneg (q : ℝ)]
  have hX : s ^ 2 * (41 * (k : ℝ) * e ^ 2 * (q : ℝ) ^ 2 + R ^ 2) ≤
      (165 / 4) * ((k : ℝ) * e ^ 2 * (q : ℝ) ^ 2 * s ^ 2) := by
    nlinarith [hRs2, sq_nonneg s]
  have hY : (165 / 4) * ((k : ℝ) * e ^ 2 * (q : ℝ) ^ 2 * s ^ 2) ≤
      R ^ 2 * (660 * (k : ℝ) * e ^ 2) := by
    have h1 : ((q : ℝ) * s / 4) ^ 2 ≤ R ^ 2 := hR2lo
    have h2 : ((q : ℝ) * s / 4) ^ 2 * (660 * (k : ℝ) * e ^ 2) ≤
        R ^ 2 * (660 * (k : ℝ) * e ^ 2) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h3 : ((q : ℝ) * s / 4) ^ 2 * (660 * (k : ℝ) * e ^ 2) =
        (165 / 4) * ((k : ℝ) * e ^ 2 * (q : ℝ) ^ 2 * s ^ 2) := by ring
    linarith [h2, h3]
  linarith [hX, hY]

-- Ground-truth checks.

/-- At `N = 1`, `k = 1` the scale is `exp 0 = 1`, so `⌊1/2⌋ = 0`: the floor is
genuinely used and the radius is not automatically positive. -/
example : torusRadius 1 1 1 = 0 := by
  rw [torusRadius]
  norm_num [Real.log_one, Real.exp_zero]

/-- The threshold instance `N = q = 64`, `k = 1` has scale
`exp(-log 64 / 2) = 1/8`, so the radius is `⌊64 · (1/8) / 2⌋ = ⌊4⌋ = 4`. -/
example : torusRadius 64 64 1 = 4 := by
  have h64 : (0 : ℝ) < ((64 : ℕ) : ℝ) := by norm_num
  have hexp : Real.exp (-(Real.log ((64 : ℕ) : ℝ)) / (2 * ((1 : ℕ) : ℝ))) = 1 / 8 := by
    rw [show -(Real.log ((64 : ℕ) : ℝ)) / (2 * ((1 : ℕ) : ℝ)) =
        -(Real.log ((64 : ℕ) : ℝ) / 2) by ring]
    rw [Real.exp_neg, Real.exp_half, Real.exp_log h64]
    rw [show Real.sqrt ((64 : ℕ) : ℝ) = 8 by
      rw [show ((64 : ℕ) : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    norm_num
  rw [torusRadius, hexp]
  norm_num

/-- Non-vacuity of the bundled specification: the four facts hold jointly at
`N = q = 64`, `k = 1`, so the hypotheses `64 ≤ N`, `N ≤ q`, `1 ≤ k` are
simultaneously satisfiable. -/
example : 1 ≤ torusRadius 64 64 1 ∧
    (64 : ℝ) * Real.exp (-(Real.log 64) / (2 * ((1 : ℕ) : ℝ))) / 4 ≤ (torusRadius 64 64 1 : ℝ) ∧
    2 * (torusRadius 64 64 1 : ℝ) ≤ (64 : ℝ) * Real.exp (-(Real.log 64) / (2 * ((1 : ℕ) : ℝ))) ∧
    64 * (2 * torusRadius 64 64 1 - 1) ^ (2 * 1) < 64 ^ (2 * 1) :=
  torusRadius_spec (by norm_num) (by norm_num) (by norm_num)

/-- The ratio lower bound is non-vacuous at `N = q = 64`, `k = 1`, `e = 6`. -/
example : Real.exp (-(Real.log 64) / ((1 : ℕ) : ℝ)) / (660 * ((1 : ℕ) : ℝ) * (6 : ℝ) ^ 2) ≤
    (torusRadius 64 64 1 : ℝ) ^ 2 /
      (41 * ((1 : ℕ) : ℝ) * (6 : ℝ) ^ 2 * (64 : ℝ) ^ 2 + (torusRadius 64 64 1 : ℝ) ^ 2) :=
  torusRadius_ratio_lower (by norm_num) (by norm_num) (by norm_num) (by norm_num)

#print axioms one_le_torusRadius
#print axioms scale_div_four_le_torusRadius
#print axioms two_mul_torusRadius_le
#print axioms torusRadius_scale_lt
#print axioms torusRadius_spec
#print axioms torusRadius_ratio_lower

end Erdos142