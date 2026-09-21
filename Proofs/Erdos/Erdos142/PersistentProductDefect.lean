/-
  Erdős Problem #142 — persistent, fixed-right-factor product-defect witnesses.

  `ProductDefect.rothProductDefect_unbounded_of_tendsto` shows that the product
  defect `rothProductDefect N M` is unbounded above in the two variables
  jointly, and `FixedRadixDefect.exists_fixed_right_defect_gt` pins the failure
  at a *given* right factor `M ≥ 2` for a *single* left factor `N`.
  `FixedRadixRecurrence.frequently_fixed_right_rothProductDefect_gt` upgrades
  that to arbitrarily late left factors at a fixed right factor, for every
  `B` below the fixed-right threshold

      `T_M = rothLogDeficit M + log ((2 * M - 1) / M)`.

  This file combines the two facts with the unboundedness of the log-deficit
  `rothLogDeficit_unbounded` to obtain *persistent* obstruction statements in
  which the threshold is chosen first and the left-factor witnesses are
  arbitrarily large:

  * `fixed_right_rothProductDefect_threshold_unbounded`: the fixed-right
    thresholds `T_M` are unbounded above across `M ≥ 2`.  The log-deficit alone
    already exceeds `max B 0` at some `M ≠ 1`, and the radix term
    `log ((2 * M - 1) / M)` is nonnegative for `M ≥ 1`.

  * `exists_fixed_right_frequently_rothProductDefect_gt`: for every real `B`
    there is a single `M ≥ 2` with `B < rothProductDefect N M` for `N`
    arbitrarily large.

  * `exists_fixed_right_frequently_mul_lt_rothNumberNat`: for every `C > 0`
    there is a single `M ≥ 2` with
    `C * rothNumberNat N * rothNumberNat M < rothNumberNat (N * (2 * M - 1))`
    for `N` arbitrarily large, i.e. the constant-reverse bound fails
    persistently at one fixed right factor.

  What this does and does not say.  The right factor `M` is selected *once*,
  depending on `B` (respectively `C`), and then the left-factor witnesses `N`
  form an unbounded set; this strengthens the joint unboundedness of the defect
  by fixing the right factor before the witnesses are produced.  It does *not*
  assert that a single `M` serves all `B` simultaneously, does *not* prove
  unboundedness of `rothProductDefect (·, M)` at a fixed `M`, does *not* prove
  asymptotic oscillation or the value of any `limsup` or `liminf`, and does
  *not* resolve Erdős #142.  No `sorry`, no `unsafe`, no new axioms, and no
  existing declaration is edited.
-/

import Erdos.Erdos142.FixedRadixRecurrence

set_option autoImplicit false

open Filter
open scoped Topology

namespace Erdos142

noncomputable section

/-- **Unboundedness of the fixed-right thresholds.**  For every real `B` there
is `M ≥ 2` with

`B < rothLogDeficit M + log ((2 * M - 1) / M)`.

Route: `rothLogDeficit_unbounded` at `max B 0` produces `N ≥ 1` with
`max B 0 < rothLogDeficit N`.  If `N = 1` then `rothLogDeficit 1 = 0`, which
contradicts `max B 0 ≥ 0`; hence `M = N ≥ 2`.  Since `(2 * M - 1) / M ≥ 1` for
`M ≥ 1`, the radix term is nonnegative and may be added to the strict bound.
This selects the right factor `M` from `B` alone; it says nothing about a
single `M` working for all `B`. -/
theorem fixed_right_rothProductDefect_threshold_unbounded :
    ∀ B : ℝ, ∃ M : ℕ, 2 ≤ M ∧
      B < rothLogDeficit M + Real.log (((2 * M - 1 : ℕ) : ℝ) / (M : ℝ)) := by
  intro B
  obtain ⟨N, hN1, hNgt⟩ := rothLogDeficit_unbounded (max B 0)
  have hBmax : B ≤ max B 0 := le_max_left B 0
  refine ⟨N, ?_, ?_⟩
  · by_contra h
    have hN1' : N = 1 := by omega
    rw [hN1', rothLogDeficit_one] at hNgt
    have h0 : (0 : ℝ) ≤ max B 0 := le_max_right B 0
    linarith
  · have hlog : 0 ≤ Real.log (((2 * N - 1 : ℕ) : ℝ) / (N : ℝ)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (by exact_mod_cast (show 0 < N by omega))]
      have hMN : (N : ℝ) ≤ ((2 * N - 1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : N ≤ 2 * N - 1)
      simpa using hMN
    have : B < rothLogDeficit N := lt_of_le_of_lt hBmax hNgt
    linarith

/-- **Arbitrarily late left-factor witnesses at a fixed right factor.**  For
every real `B` there is a single `M ≥ 2` with

`∃ᶠ N : ℕ in atTop, B < rothProductDefect N M`.

Route: `fixed_right_rothProductDefect_threshold_unbounded` produces `M ≥ 2`
with `B` below the fixed-right threshold `T_M`, and
`frequently_fixed_right_rothProductDefect_gt` converts that threshold bound into
arbitrarily large left-factor witnesses.  The right factor `M` is fixed once
per `B`; this does not show that `rothProductDefect (·, M)` is unbounded at that
fixed `M`. -/
theorem exists_fixed_right_frequently_rothProductDefect_gt :
    ∀ B : ℝ, ∃ M : ℕ, 2 ≤ M ∧
      ∃ᶠ N : ℕ in atTop, B < rothProductDefect N M := by
  intro B
  obtain ⟨M, hM, hB⟩ := fixed_right_rothProductDefect_threshold_unbounded B
  exact ⟨M, hM, frequently_fixed_right_rothProductDefect_gt hM hB⟩

/-- **Persistent failure of a constant reverse bound.**  For every real
`C > 0` there is a single `M ≥ 2` with

`C * rothNumberNat N * rothNumberNat M < rothNumberNat (N * (2 * M - 1))`

for `N` arbitrarily large: `∃ᶠ N : ℕ in atTop, ...`.

Route: apply `exists_fixed_right_frequently_rothProductDefect_gt` at
`B = log C` to get `M ≥ 2` and arbitrarily large `N` with
`log C < rothProductDefect N M`.  Intersecting with the eventual set `1 ≤ N`
and rewriting by the log-quotient identity `rothProductDefect_eq_log_div` turns
the defect bound into `C < rothNumberNat (N * (2 * M - 1)) /
(rothNumberNat N * rothNumberNat M)`; `Real.log_lt_log_iff` removes the
logarithm and the division is cleared.  The right factor `M` is fixed while the
witnesses `N` are arbitrarily large; the statement does not exhibit a single
`M` working for all `C`, does not prove unboundedness at fixed `M`, and does
not resolve Erdős #142. -/
theorem exists_fixed_right_frequently_mul_lt_rothNumberNat
    (C : ℝ) (hC : 0 < C) :
    ∃ M : ℕ, 2 ≤ M ∧
      ∃ᶠ N : ℕ in atTop,
        C * (rothNumberNat N : ℝ) * (rothNumberNat M : ℝ) <
          (rothNumberNat (N * (2 * M - 1)) : ℝ) := by
  obtain ⟨M, hM, hfreq⟩ := exists_fixed_right_frequently_rothProductDefect_gt (Real.log C)
  have hM1 : 1 ≤ M := by omega
  refine ⟨M, hM, ?_⟩
  refine (hfreq.and_eventually (eventually_ge_atTop 1)).mono ?_
  intro N hN
  obtain ⟨hNgt, hN1⟩ := hN
  have hNq : 1 ≤ N * (2 * M - 1) := by
    have hq : 1 ≤ 2 * M - 1 := by omega
    have := Nat.mul_le_mul hN1 hq
    simpa using this
  have ha : (0 : ℝ) < (rothNumberNat N : ℝ) := rothNumberNat_pos_real hN1
  have hb : (0 : ℝ) < (rothNumberNat M : ℝ) := rothNumberNat_pos_real hM1
  have hc : (0 : ℝ) < (rothNumberNat (N * (2 * M - 1)) : ℝ) :=
    rothNumberNat_pos_real hNq
  have hquot : (0 : ℝ) < (rothNumberNat (N * (2 * M - 1)) : ℝ) /
      ((rothNumberNat N : ℝ) * (rothNumberNat M : ℝ)) := div_pos hc (mul_pos ha hb)
  have hlog : Real.log C < Real.log ((rothNumberNat (N * (2 * M - 1)) : ℝ) /
      ((rothNumberNat N : ℝ) * (rothNumberNat M : ℝ))) := by
    rw [← rothProductDefect_eq_log_div hN1 hM1]
    exact hNgt
  have hlt : C < (rothNumberNat (N * (2 * M - 1)) : ℝ) /
      ((rothNumberNat N : ℝ) * (rothNumberNat M : ℝ)) :=
    (Real.log_lt_log_iff hC hquot).mp hlog
  have hmul := (lt_div_iff₀ (mul_pos ha hb)).mp hlt
  simpa only [mul_assoc] using hmul

/-- **Non-vacuity of the threshold statement at `M = 2`.**  The threshold
`T_2 = rothLogDeficit 2 + log (3 / 2)` is positive, so the hypothesis of
`frequently_fixed_right_rothProductDefect_gt` is satisfiable at a concrete
small right factor. -/
example : (0 : ℝ) < rothLogDeficit 2 + Real.log (((2 * 2 - 1 : ℕ) : ℝ) / (2 : ℝ)) := by
  have h1 : 0 ≤ rothLogDeficit 2 := rothLogDeficit_nonneg (by norm_num)
  have h2 : 0 < Real.log (((2 * 2 - 1 : ℕ) : ℝ) / (2 : ℝ)) := by
    apply Real.log_pos
    norm_num
  linarith

end

end Erdos142

-- Axiom audit for the load-bearing declarations.
#print axioms Erdos142.fixed_right_rothProductDefect_threshold_unbounded
#print axioms Erdos142.exists_fixed_right_frequently_rothProductDefect_gt
#print axioms Erdos142.exists_fixed_right_frequently_mul_lt_rothNumberNat