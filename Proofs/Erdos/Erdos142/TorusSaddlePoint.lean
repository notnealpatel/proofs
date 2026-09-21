/-
  Erdős Problem #142 — the ceiling/saddle-point optimization kernel.

  This module isolates the elementary optimization step that a torus
  saddle-point/ceiling argument consumes: for reals `β, L` with `1 ≤ β` and
  `4 * β ≤ L`, the integer ceiling

    `k = ⌈√(L/β)⌉`

  of the real saddle scale `s = √(L/β)` satisfies

  * `1 ≤ k` (nonvanishing);
  * `(k : ℝ) ≤ 2 * √(L/β)` (at most twice the real scale);
  * `(k : ℝ) * β + L / (k : ℝ) ≤ 2 * √(β * L) + β` (the saddle bound).

  The hypotheses `1 ≤ β`, `4 * β ≤ L` are jointly satisfiable (`β = 1`,
  `L = 4`), and they are exactly what the proof uses: `β ≥ 1` gives `β ≠ 0`
  (so `L/β` is honest and `β * (L/β) = L`), while `L/β ≥ 4` gives
  `s = √(L/β) ≥ 2 ≥ 1` (so `⌈s⌉ ≥ 1` and `⌈s⌉ ≤ 2s`).

  The mathematical content is the standard ceiling relaxation of the saddle
  point.  With `s = √(L/β) ≥ 2` and `k = ⌈s⌉` one has `s ≤ k < s + 1`, hence
  `k ≤ 2s`; and since `k ≥ s > 0`, also `s ^ 2 / k ≤ s`, so
  `k + s ^ 2 / k ≤ (s + 1) + s = 2 * s + 1`.  Multiplying by `β ≥ 0` and using
  `β * s ^ 2 = L` and `√(β * L) = β * s` turns this into the saddle bound.

  All three facts are proved as separate helper lemmas and bundled in
  `saddleK_spec`; `saddle_spec_of_eq` restates the bundle with the ceiling
  exposed as an explicit hypothesis `k = ⌈√(L/β)⌉`.

  No `sorry`, no new axioms.
-/

import Combinatorics.DiscreteOptimization
import Erdos.Erdos142.TorusAsymptoticParameters

set_option autoImplicit false

namespace Erdos142

/-! ### Ceiling arithmetic on a single real scale -/

/-- **Nonvanishing of the ceiling.**  For a real `s` with `1 ≤ s`, the natural
ceiling `⌈s⌉` is at least `1`.  (`⌈s⌉ ≥ 1` because `s > 0`, via
`Nat.ceil_pos`.) -/
lemma one_le_natCeil {s : ℝ} (hs : 1 ≤ s) : 1 ≤ Nat.ceil s := by
  have hs_pos : 0 < s := by linarith
  have : 0 < Nat.ceil s := Nat.ceil_pos.mpr hs_pos
  omega

/-- **The ceiling is at most twice the scale.**  For a real `s` with `1 ≤ s`,
`(⌈s⌉ : ℝ) ≤ 2 * s`.  This is `Nat.ceil_lt_add_one` (`⌈s⌉ < s + 1`) together
with `s + 1 ≤ 2 * s`, which is exactly `1 ≤ s`. -/
lemma natCeil_le_two_mul {s : ℝ} (hs : 1 ≤ s) : (Nat.ceil s : ℝ) ≤ 2 * s := by
  have hlt : (Nat.ceil s : ℝ) < s + 1 := Nat.ceil_lt_add_one (by linarith : 0 ≤ s)
  linarith

/-- **The one-variable saddle inequality.**  For a real `s` with `1 ≤ s`,

`(⌈s⌉ : ℝ) + s ^ 2 / (⌈s⌉ : ℝ) ≤ 2 * s + 1`.

This is a thin compatibility wrapper around the neutral generic statement
`DiscreteOptimization.natCeil_add_sq_div_le`; the statement and proof content
are unchanged, so all consumers keep their signatures. -/
lemma natCeil_add_sq_div_le {s : ℝ} (hs : 1 ≤ s) :
    (Nat.ceil s : ℝ) + s ^ 2 / (Nat.ceil s : ℝ) ≤ 2 * s + 1 :=
  DiscreteOptimization.natCeil_add_sq_div_le hs

/-! ### The ceiling saddle scale `⌈√(L/β)⌉` -/

/-- The integer saddle scale for a modulus parameter `β` and a length parameter
`L`: the ceiling `⌈√(L/β)⌉` of the real saddle scale `√(L/β)`.  The lemmas
below use it under `1 ≤ β` and `4 * β ≤ L`, where `L/β ≥ 4` and the scale is
at least `2`. -/
noncomputable def saddleK (β L : ℝ) : ℕ := Nat.ceil (Real.sqrt (L / β))

/-- **The saddle scale is at least `2`.**  For `1 ≤ β` and `4 * β ≤ L`,
`2 ≤ √(L/β)`.  Indeed `β > 0` and `L ≥ 4 * β` give `L/β ≥ 4 * β / β = 4`,
and `√4 = 2`. -/
lemma two_le_sqrt_div {β L : ℝ} (hβ : 1 ≤ β) (hL : 4 * β ≤ L) :
    2 ≤ Real.sqrt (L / β) := by
  have hβ_pos : 0 < β := by linarith
  have h4 : 4 ≤ L / β := by
    have h := div_le_div_of_nonneg_right hL hβ_pos.le
    have hc : 4 * β / β = 4 := mul_div_cancel_right₀ 4 (ne_of_gt hβ_pos)
    linarith
  have hsqrt4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h := Real.sqrt_le_sqrt h4
  linarith

/-- **Nonvanishing of the saddle scale.**  For `1 ≤ β` and `4 * β ≤ L`,
`1 ≤ saddleK β L`. -/
lemma one_le_saddleK {β L : ℝ} (hβ : 1 ≤ β) (hL : 4 * β ≤ L) : 1 ≤ saddleK β L := by
  have hs : 1 ≤ Real.sqrt (L / β) := le_trans (by norm_num) (two_le_sqrt_div hβ hL)
  simpa [saddleK] using one_le_natCeil hs

/-- **The saddle scale is at most twice the real scale.**  For `1 ≤ β` and
`4 * β ≤ L`, `(saddleK β L : ℝ) ≤ 2 * √(L/β)`. -/
lemma saddleK_le_two_mul_sqrt {β L : ℝ} (hβ : 1 ≤ β) (hL : 4 * β ≤ L) :
    (saddleK β L : ℝ) ≤ 2 * Real.sqrt (L / β) := by
  have hs : 1 ≤ Real.sqrt (L / β) := le_trans (by norm_num) (two_le_sqrt_div hβ hL)
  simpa [saddleK] using natCeil_le_two_mul hs

/-- **The saddle bound.**  For `1 ≤ β` and `4 * β ≤ L`,

`(saddleK β L : ℝ) * β + L / (saddleK β L : ℝ) ≤ 2 * √(β * L) + β`.

Writing `s = √(L/β) ≥ 1` and `k = ⌈s⌉`, the one-variable inequality
`k + s ^ 2 / k ≤ 2 * s + 1` is multiplied by `β ≥ 0`; then `β * s ^ 2 = L`
(since `β ≠ 0` and `s ^ 2 = L/β`) and `√(β * L) = β * s` (since
`β * L = (β * s) ^ 2` and `β * s ≥ 0`) identify the two sides. -/
lemma saddleK_saddle_le {β L : ℝ} (hβ : 1 ≤ β) (hL : 4 * β ≤ L) :
    (saddleK β L : ℝ) * β + L / (saddleK β L : ℝ) ≤ 2 * Real.sqrt (β * L) + β := by
  have hβ_pos : 0 < β := by linarith
  have hL_pos : 0 < L := by linarith
  have hs : 1 ≤ Real.sqrt (L / β) := le_trans (by norm_num) (two_le_sqrt_div hβ hL)
  have hcore : (saddleK β L : ℝ) + Real.sqrt (L / β) ^ 2 / (saddleK β L : ℝ) ≤
      2 * Real.sqrt (L / β) + 1 := by
    simpa [saddleK] using natCeil_add_sq_div_le hs
  have hmul := mul_le_mul_of_nonneg_left hcore hβ_pos.le
  have hsq : Real.sqrt (L / β) ^ 2 = L / β := Real.sq_sqrt (div_nonneg hL_pos.le hβ_pos.le)
  have hβsq : β * Real.sqrt (L / β) ^ 2 = L := by
    rw [hsq, mul_div_cancel₀ L (ne_of_gt hβ_pos)]
  have hsqrt : Real.sqrt (β * L) = β * Real.sqrt (L / β) := by
    have hsq2 : β * L = (β * Real.sqrt (L / β)) ^ 2 := by
      rw [mul_pow]
      nlinarith [hβsq]
    rw [hsq2, Real.sqrt_sq (mul_nonneg hβ_pos.le (Real.sqrt_nonneg _))]
  have hLHS : β * ((saddleK β L : ℝ) + Real.sqrt (L / β) ^ 2 / (saddleK β L : ℝ))
      = (saddleK β L : ℝ) * β + L / (saddleK β L : ℝ) := by
    rw [mul_add, ← mul_div_assoc, hβsq, mul_comm]
  have hRHS : β * (2 * Real.sqrt (L / β) + 1) = 2 * Real.sqrt (β * L) + β := by
    rw [hsqrt]; ring
  rw [hLHS, hRHS] at hmul
  exact hmul

/-! ### Bundled statements -/

/-- **Bundled ceiling/saddle specification.**  For reals `β, L` with `1 ≤ β`
and `4 * β ≤ L`, the ceiling `k = saddleK β L = ⌈√(L/β)⌉` satisfies all three
saddle facts at once:

1. `1 ≤ k`;
2. `(k : ℝ) ≤ 2 * √(L/β)`;
3. `(k : ℝ) * β + L / (k : ℝ) ≤ 2 * √(β * L) + β`. -/
theorem saddleK_spec {β L : ℝ} (hβ : 1 ≤ β) (hL : 4 * β ≤ L) :
    1 ≤ saddleK β L ∧
    (saddleK β L : ℝ) ≤ 2 * Real.sqrt (L / β) ∧
    (saddleK β L : ℝ) * β + L / (saddleK β L : ℝ) ≤ 2 * Real.sqrt (β * L) + β :=
  ⟨one_le_saddleK hβ hL, saddleK_le_two_mul_sqrt hβ hL, saddleK_saddle_le hβ hL⟩

/-- **Bundled saddle specification with the ceiling as an explicit
hypothesis.**  For reals `β, L` with `1 ≤ β` and `4 * β ≤ L`, and any natural
`k` equal to `⌈√(L/β)⌉`, the three saddle facts hold for `k`.  This is
`saddleK_spec` with `saddleK β L` replaced by the explicit witness. -/
theorem saddle_spec_of_eq {β L : ℝ} (k : ℕ) (hk : k = Nat.ceil (Real.sqrt (L / β)))
    (hβ : 1 ≤ β) (hL : 4 * β ≤ L) :
    1 ≤ k ∧
    (k : ℝ) ≤ 2 * Real.sqrt (L / β) ∧
    (k : ℝ) * β + L / (k : ℝ) ≤ 2 * Real.sqrt (β * L) + β := by
  rw [hk]
  exact saddleK_spec hβ hL

-- Ground-truth checks.

/-- At `β = 1`, `L = 4` the scale is `√4 = 2` exactly, so the ceiling is the
integer `2`: the boundary case where `L/β = 4` is a perfect square. -/
example : saddleK 1 4 = 2 := by
  have h4 : Real.sqrt ((4 : ℝ) / 1) = 2 := by
    rw [show (4 : ℝ) / 1 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [saddleK, h4]
  norm_num

/-- Off the perfect-square boundary: at `β = 1`, `L = 5` the scale is `√5`,
which lies strictly between `2` and `3`, so the ceiling is `3`. -/
example : saddleK 1 5 = 3 := by
  have hlt : Real.sqrt ((5 : ℝ) / 1) ≤ 3 := by
    rw [Real.sqrt_le_iff]
    constructor <;> norm_num
  have hgt : (2 : ℝ) < Real.sqrt ((5 : ℝ) / 1) := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hceil : Nat.ceil (Real.sqrt ((5 : ℝ) / 1)) = 3 :=
    (Nat.ceil_eq_iff (by norm_num : (3 : ℕ) ≠ 0)).mpr ⟨hgt, hlt⟩
  simpa [saddleK] using hceil

/-- Non-vacuity of the bundled specification: at `β = 1`, `L = 4` the
hypotheses `1 ≤ β` and `4 * β ≤ L` hold simultaneously, and the third
(nonlinear) saddle fact instantiates to `2 * 1 + 4 / 2 = 4 ≤ 2 * √4 + 1 = 5`. -/
example : (saddleK 1 4 : ℝ) * 1 + 4 / (saddleK 1 4 : ℝ) ≤ 2 * Real.sqrt (1 * 4) + 1 :=
  (saddleK_spec (by norm_num) (by norm_num)).2.2

/-- Non-vacuity of the explicit-hypothesis form at `β = 1`, `L = 4`, `k = 2`. -/
example : ((2 : ℕ) : ℝ) * 1 + 4 / ((2 : ℕ) : ℝ) ≤ 2 * Real.sqrt (1 * 4) + 1 :=
  (saddle_spec_of_eq 2 (by
      have h4 : Real.sqrt ((4 : ℝ) / 1) = 2 := by
        rw [show (4 : ℝ) / 1 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rw [h4]
      norm_num) (by norm_num) (by norm_num)).2.2

#print axioms one_le_natCeil
#print axioms natCeil_le_two_mul
#print axioms natCeil_add_sq_div_le
#print axioms two_le_sqrt_div
#print axioms one_le_saddleK
#print axioms saddleK_le_two_mul_sqrt
#print axioms saddleK_saddle_le
#print axioms saddleK_spec
#print axioms saddle_spec_of_eq

end Erdos142