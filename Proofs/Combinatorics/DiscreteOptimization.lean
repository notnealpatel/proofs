/-
  Discrete optimization — the real ceiling saddle kernel.

  This module isolates the elementary optimization step that ceiling /
  saddle-point arguments consume.  It is a neutral real-analysis statement:
  no torus, `ZMod`, Roth number, or Erdős #142 material appears here.

  For a real `s` with `1 ≤ s`, the integer ceiling `k = ⌈s⌉` of the scale
  satisfies the one-variable saddle inequality

    `(⌈s⌉ : ℝ) + s ^ 2 / (⌈s⌉ : ℝ) ≤ 2 * s + 1`.

  The mathematical content is the standard ceiling relaxation of the saddle
  point: with `s ≤ k < s + 1` one has `k < s + 1`, and since `k ≥ s > 0`
  monotonicity of division gives `s ^ 2 / k ≤ s ^ 2 / s = s`; adding the two
  bounds yields `k + s ^ 2 / k ≤ (s + 1) + s = 2 * s + 1`.

  No `sorry`, no new axioms.
-/

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring

set_option autoImplicit false

namespace DiscreteOptimization

/-- **The one-variable ceiling saddle inequality.**  For a real `s` with
`1 ≤ s`,

`(⌈s⌉ : ℝ) + s ^ 2 / (⌈s⌉ : ℝ) ≤ 2 * s + 1`.

Writing `k = ⌈s⌉`, we have `s ≤ k` (`Nat.le_ceil`) and `k < s + 1`
(`Nat.ceil_lt_add_one`).  Since `k ≥ s > 0`, monotonicity of division gives
`s ^ 2 / k ≤ s ^ 2 / s = s`, and adding `k < s + 1` yields the claim. -/
lemma natCeil_add_sq_div_le {s : ℝ} (hs : 1 ≤ s) :
    (Nat.ceil s : ℝ) + s ^ 2 / (Nat.ceil s : ℝ) ≤ 2 * s + 1 := by
  have hs_pos : 0 < s := by linarith
  have hle : s ≤ (Nat.ceil s : ℝ) := Nat.le_ceil s
  have hlt : (Nat.ceil s : ℝ) < s + 1 := Nat.ceil_lt_add_one (le_of_lt hs_pos)
  have hdiv : s ^ 2 / (Nat.ceil s : ℝ) ≤ s := by
    have h := div_le_div_of_nonneg_left (sq_nonneg s) hs_pos hle
    have hss : s ^ 2 / s = s := by
      rw [pow_two, mul_div_cancel_right₀ s (ne_of_gt hs_pos)]
    linarith [h, hss]
  linarith

end DiscreteOptimization