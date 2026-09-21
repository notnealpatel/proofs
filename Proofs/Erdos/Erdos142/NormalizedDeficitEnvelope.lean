/-
  Erdős Problem #142 — the sharp eventual upper envelope of the normalized deficit.

  `SquareScaleCriterion` records the deterministic analytic kernel that governs
  the #142 endpoint and instantiates it at the actual Roth number `r₃ = rothNumberNat`:
  the *normalized deficit*

      `D(N) = normalizedDeficit r₃ N = log (N / r₃ N) / √(log N)`.

  The accepted unconditional EHPS-shaped lower bound `eventually_rothNumberNat_lower_bound`
  gives, for every positive slack `δ > 0`, an eventual lower bound
  `N · exp(-(torusLeadingConstant + δ)·√(log N)) ≤ r₃ N`.  Taking logarithms turns
  this into the *upper envelope* statement

      `D(N) ≤ torusLeadingConstant + δ`   for all sufficiently large `N`.

  This module records that envelope at arbitrary positive slack, its equivalent
  threshold form `normalizedDeficit r₃ N ≤ C` for any `C > torusLeadingConstant`,
  and the combined two-sided eventual bound `0 ≤ D(N) ≤ torusLeadingConstant + δ`
  (the lower half being `normalizedDeficit_rothNumberNat_nonneg` for `N ≥ 2`).

  **This is a one-sided upper-envelope (limsup-style) result.**  It bounds the
  eventual maximum of `D` by `torusLeadingConstant + δ`; it does **not** assert
  that `D` converges, does **not** assert that `D` attains the envelope, and is
  not a resolution of Erdős Problem #142.

  No `sorry`, no `unsafe`, no new axioms, and no existing declaration is edited;
  the axiom audit is at the end of the file.
-/

import Erdos.Erdos142.SquareScaleCriterion

set_option autoImplicit false

open Filter
open scoped Topology

namespace Erdos142

noncomputable section

/-! ## The sharp upper envelope at arbitrary positive slack -/

/-- **Sharp eventual upper envelope of the normalized deficit, arbitrary slack.**
For every `δ > 0`, the normalized deficit of `r₃` is eventually at most
`torusLeadingConstant + δ`:

`∀ᶠ N in atTop, normalizedDeficit r₃ N ≤ torusLeadingConstant + δ`.

The accepted EHPS-shaped lower bound at slack `δ`,
`N · exp(-(torusLeadingConstant + δ)·√(log N)) ≤ r₃ N`, gives
`log r₃ N ≥ log N - (torusLeadingConstant + δ)·√(log N)`, hence the claim after
division by `√(log N) > 0`.  This is a one-sided upper-envelope (limsup-style)
statement; it does not assert convergence of `normalizedDeficit r₃`, nor that
the envelope is attained. -/
theorem eventually_normalizedDeficit_rothNumberNat_le_add
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      normalizedDeficit rothNumberNat N ≤ torusLeadingConstant + δ := by
  obtain ⟨N₁, hN₁⟩ :=
    eventually_atTop.mp (eventually_rothNumberNat_lower_bound δ hδ)
  refine eventually_atTop.2 ⟨max 2 N₁, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_trans (by norm_num : 1 ≤ 2) (le_max_left 2 N₁)) hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hrpos : (0 : ℝ) < (rothNumberNat N : ℝ) := rothNumberNat_pos_real hN1
  have hlogpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hsqrtpos : 0 < Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_pos.2 hlogpos
  have hlow := hN₁ N (le_trans (le_max_right 2 N₁) hN)
  have hlhs : 0 < (N : ℝ) *
      Real.exp (-(torusLeadingConstant + δ) * Real.sqrt (Real.log (N : ℝ))) :=
    mul_pos hNpos (Real.exp_pos _)
  have hlog := Real.log_le_log hlhs hlow
  rw [Real.log_mul (ne_of_gt hNpos) (Real.exp_ne_zero _), Real.log_exp] at hlog
  have hkey : Real.log (N : ℝ) - Real.log (rothNumberNat N : ℝ) ≤
      (torusLeadingConstant + δ) * Real.sqrt (Real.log (N : ℝ)) := by linarith
  have hD : normalizedDeficit rothNumberNat N =
      (Real.log (N : ℝ) - Real.log (rothNumberNat N : ℝ)) /
        Real.sqrt (Real.log (N : ℝ)) := by
    rw [normalizedDeficit, logDeficit, Real.log_div (ne_of_gt hNpos) (ne_of_gt hrpos)]
  rw [hD]
  exact (div_le_iff₀ hsqrtpos).mpr hkey

/-! ## The equivalent threshold form -/

/-- **Threshold form of the upper envelope.**  For any constant `C` strictly
above `torusLeadingConstant`, the normalized deficit of `r₃` is eventually at
most `C`:

`∀ᶠ N in atTop, normalizedDeficit r₃ N ≤ C`.

This is `eventually_normalizedDeficit_rothNumberNat_le_add` at the positive
slack `δ = C - torusLeadingConstant`; it is the same upper-envelope (limsup)
content, stated as a threshold on an arbitrary level `C`. -/
theorem eventually_normalizedDeficit_rothNumberNat_le
    {C : ℝ} (hC : torusLeadingConstant < C) :
    ∀ᶠ N : ℕ in atTop, normalizedDeficit rothNumberNat N ≤ C := by
  have hδ : 0 < C - torusLeadingConstant := sub_pos.mpr hC
  have h : ∀ᶠ N : ℕ in atTop,
      normalizedDeficit rothNumberNat N ≤ torusLeadingConstant + (C - torusLeadingConstant) :=
    eventually_normalizedDeficit_rothNumberNat_le_add (C - torusLeadingConstant) hδ
  have hsum : torusLeadingConstant + (C - torusLeadingConstant) = C := by ring
  simpa only [hsum] using h

/-! ## The combined two-sided eventual bound -/

/-- **Combined two-sided eventual bound.**  For every `δ > 0`, eventually
`0 ≤ normalizedDeficit r₃ N ≤ torusLeadingConstant + δ`.  The lower half is
`normalizedDeficit_rothNumberNat_nonneg` for `N ≥ 2` (from `1 ≤ r₃ N ≤ N`), and
the upper half is the sharp envelope `eventually_normalizedDeficit_rothNumberNat_le_add`.

This packages `normalizedDeficit r₃` as eventually squeezed between `0` and the
envelope `torusLeadingConstant + δ`; the upper half is the limsup-style bound,
the lower half a genuine two-sided envelope component, and neither asserts
convergence. -/
theorem eventually_nonneg_and_le_normalizedDeficit_rothNumberNat
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      0 ≤ normalizedDeficit rothNumberNat N ∧
        normalizedDeficit rothNumberNat N ≤ torusLeadingConstant + δ := by
  have hge : ∀ᶠ N : ℕ in atTop, 2 ≤ N := eventually_atTop.2 ⟨2, fun N hN => hN⟩
  have hle := eventually_normalizedDeficit_rothNumberNat_le_add δ hδ
  filter_upwards [hge, hle] with N hN hbound
  exact ⟨normalizedDeficit_rothNumberNat_nonneg hN, hbound⟩

/-! ## Sharp specializations -/

/-- **The `δ = 1` case**, recovered as a specialization of the general envelope.
The normalized deficit of `r₃` is eventually at most `torusLeadingConstant + 1`,
agreeing with the accepted bound `eventually_le_normalizedDeficit_rothNumberNat`
in `SquareScaleCriterion`. -/
theorem eventually_normalizedDeficit_rothNumberNat_le_add_one :
    ∀ᶠ N : ℕ in atTop,
      normalizedDeficit rothNumberNat N ≤ torusLeadingConstant + 1 :=
  eventually_normalizedDeficit_rothNumberNat_le_add 1 (by norm_num)

/-- Non-vacuity of the `δ = 1` envelope: unpacking the eventual statement
produces a concrete `N` at which the inequality holds. -/
example : ∃ N : ℕ,
    normalizedDeficit rothNumberNat N ≤ torusLeadingConstant + 1 := by
  obtain ⟨N₀, hN₀⟩ :=
    eventually_atTop.mp eventually_normalizedDeficit_rothNumberNat_le_add_one
  exact ⟨N₀, hN₀ N₀ le_rfl⟩

/-- Non-vacuity of the combined two-sided bound at `δ = 1`: unpacking the
eventual statement produces a concrete `N` witnessing both halves. -/
example : ∃ N : ℕ,
    0 ≤ normalizedDeficit rothNumberNat N ∧
      normalizedDeficit rothNumberNat N ≤ torusLeadingConstant + 1 := by
  obtain ⟨N₀, hN₀⟩ :=
    eventually_atTop.mp (eventually_nonneg_and_le_normalizedDeficit_rothNumberNat 1
      (by norm_num))
  exact ⟨N₀, hN₀ N₀ le_rfl⟩

end

#print axioms Erdos142.eventually_normalizedDeficit_rothNumberNat_le_add
#print axioms Erdos142.eventually_normalizedDeficit_rothNumberNat_le
#print axioms Erdos142.eventually_nonneg_and_le_normalizedDeficit_rothNumberNat
#print axioms Erdos142.eventually_normalizedDeficit_rothNumberNat_le_add_one

end Erdos142