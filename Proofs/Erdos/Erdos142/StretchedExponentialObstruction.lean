/-
  Erdős Problem #142 — the stretched-exponential obstruction for the Roth number.

  Let `r₃(N) = rothNumberNat N` and let `λ(N) = rothLogDeficit N = log (N / r₃ N)`
  be the *log-deficit* of the Roth number.  The accepted unconditional
  EHPS-shaped lower bound `TorusAsymptoticLowerBound.eventually_rothNumberNat_lower_bound`,
  in its accepted normalized form
  `NormalizedDeficitEnvelope.eventually_nonneg_and_le_normalizedDeficit_rothNumberNat`,
  says that for every `δ > 0` the normalized deficit

      `D(N) = normalizedDeficit r₃ N = λ(N) / √(log N)`

  satisfies `0 ≤ D(N) ≤ torusLeadingConstant + δ` eventually.  Multiplying back
  by the positive factor `√(log N)` is the whole analytic input of this module:

      `0 ≤ λ(N) ≤ (torusLeadingConstant + δ) · √(log N)`   eventually.

  From this single envelope we obtain, unconditionally:

  * `tendsto_rothLogDeficit_div_rpow_zero`: for **every** real exponent
    `γ > 1/2`, `λ(N) / (log N)^γ → 0`.  Equivalently `λ = o((log N)^γ)` at
    every scale strictly above the critical square-root scale.
  * `not_tendsto_rothLogDeficit_div_rpow`: for every `γ > 1/2` and every real
    `c > 0`, the ratio `λ(N) / (log N)^γ` does **not** tend to `c`.  So the
    log-deficit carries no positive *stretched-exponential leading constant* on
    any scale `(log N)^γ` with `γ > 1/2`: no asymptotic relation of the shape
    `r₃(N) = N · exp(-(c + o(1)) · (log N)^γ)` with `γ > 1/2` and `c > 0` can
    hold.

  The analytic kernel is generic and stated for an arbitrary sequence
  `F : ℕ → ℝ`: eventual nonnegativity plus an eventual bound
  `F N ≤ C · √(log N)` squeezes `F N / (log N)^γ` between `0` and
  `C · (log N)^{1/2 - γ}`, which vanishes because `1/2 - γ < 0`
  (`tendsto_rpow_neg_atTop`), `√x = x^{1/2}` (`Real.sqrt_eq_rpow`), and
  `x^{1/2}/x^γ = x^{1/2-γ}` (`Real.rpow_sub`).

  Finally `le_torusLeadingConstant_of_tendsto_rothLogDeficit_div_sqrt` transfers
  the envelope across the **critical** scale `γ = 1/2`: if the critical
  normalized deficit happens to converge, its limit is at most
  `torusLeadingConstant`.  This is a conditional transfer only; it does **not**
  assert that the critical limit exists, and no critical limit is claimed
  anywhere in this module.

  **Scope.**  These are consequences of the accepted unconditional Roth lower
  bound, and they are a *negative-lane scale classification*: they exclude the
  whole stretched-exponential family above the critical scale, and in particular
  strictly refine the accepted pure-power obstruction
  `PowerLawObstruction.not_tendsto_rothNumberNat_div_rpow` at the logarithmic
  scale.  They are **not** a resolution of Erdős Problem #142: no upper bound on
  `r₃` sharper than the accepted ones is proved, no lower bound is contradicted,
  and nothing is said about the existence or the value of the critical limit
  `lim λ(N)/√(log N)`.

  No `sorry`, no `unsafe`, no new axioms, and no existing declaration is edited;
  the axiom audit is at the end of the file.
-/

import Erdos.Erdos142.NormalizedDeficitEnvelope
import Erdos.Erdos142.ProductDefect
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false

open Filter
open scoped Topology

namespace Erdos142

noncomputable section

/-! ## The pointwise bridge between the two deficits -/

/-- **Bridge between `normalizedDeficit` and `rothLogDeficit`.**  For every `N`,
`normalizedDeficit r₃ N = λ(N) / √(log N)`, i.e. the accepted normalized deficit
is the log-deficit divided by the positive normalizing factor `√(log N)`.
This is definitional (`normalizedDeficit` and `rothLogDeficit` are both
`log (N / r₃ N)` with the same normalization), and it is what lets the accepted
eventual envelope on `normalizedDeficit` be multiplied back into an envelope on
`λ`. -/
theorem normalizedDeficit_rothNumberNat_eq (N : ℕ) :
    normalizedDeficit rothNumberNat N =
      rothLogDeficit N / Real.sqrt (Real.log (N : ℝ)) := rfl

/-- Ground-truth check of the bridge at `N = 4`, where the normalizing factor is
`√(log 4)`; it uses no value of `r₃(4)`. -/
example : normalizedDeficit rothNumberNat 4 =
    rothLogDeficit 4 / Real.sqrt (Real.log (4 : ℝ)) :=
  normalizedDeficit_rothNumberNat_eq 4

/-! ## The eventual envelope on the log-deficit -/

/-- **Two-sided eventual envelope on the log-deficit.**  For every `δ > 0`,
eventually `0 ≤ λ(N) ≤ (torusLeadingConstant + δ) · √(log N)`.

This is the accepted combined normalized bound
`eventually_nonneg_and_le_normalizedDeficit_rothNumberNat` multiplied back by
the positive factor `√(log N)` at `N ≥ 2` (where `log N > 0`), using the
definitional bridge `normalizedDeficit_rothNumberNat_eq`.  It is the exact form
of the accepted EHPS-shaped lower bound that the generic squeeze below
consumes. -/
theorem eventually_nonneg_and_le_rothLogDeficit_mul_sqrt_log
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      0 ≤ rothLogDeficit N ∧
        rothLogDeficit N ≤ (torusLeadingConstant + δ) * Real.sqrt (Real.log (N : ℝ)) := by
  have henv := eventually_nonneg_and_le_normalizedDeficit_rothNumberNat δ hδ
  filter_upwards [henv, eventually_ge_atTop 2] with N hN hN2
  have hlogpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hsqrtpos : 0 < Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_pos.2 hlogpos
  rw [normalizedDeficit_rothNumberNat_eq] at hN
  exact ⟨by simpa using (le_div_iff₀ hsqrtpos).mp hN.1,
    (div_le_iff₀ hsqrtpos).mp hN.2⟩

/-- **Eventual nonnegativity of the log-deficit**, extracted from the accepted
combined normalized bound. -/
theorem eventually_rothLogDeficit_nonneg :
    ∀ᶠ N : ℕ in atTop, 0 ≤ rothLogDeficit N :=
  (eventually_nonneg_and_le_rothLogDeficit_mul_sqrt_log 1 (by norm_num)).mono
    fun _ h => h.1

/-- **Eventual square-root envelope on the log-deficit**, extracted from the
accepted combined normalized bound: `λ(N) ≤ (torusLeadingConstant + δ)·√(log N)`
eventually, for every `δ > 0`. -/
theorem eventually_rothLogDeficit_le_mul_sqrt_log (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      rothLogDeficit N ≤ (torusLeadingConstant + δ) * Real.sqrt (Real.log (N : ℝ)) :=
  (eventually_nonneg_and_le_rothLogDeficit_mul_sqrt_log δ hδ).mono fun _ h => h.2

/-! ## The generic stretched-exponential squeeze -/

/-- **Generic squeeze at every scale above the critical one.**  Let `F : ℕ → ℝ`
be eventually nonnegative and eventually bounded by `C · √(log N)`.  Then for
every real exponent `γ > 1/2` the ratio `F N / (log N)^γ` tends to `0`.

The squeeze is `0 ≤ F N / (log N)^γ ≤ C · (log N)^{1/2 - γ}` for `N ≥ 2`.  The
upper bound follows from `√x = x^{1/2}` (`Real.sqrt_eq_rpow`) and
`x^{1/2}/x^γ = x^{1/2-γ}` (`Real.rpow_sub`); the right-hand side tends to `0`
because `1/2 - γ < 0` (`tendsto_rpow_neg_atTop`) composed with
`log ∘ (↑·) → atTop`, and `squeeze_zero'` closes the goal.

No sign hypothesis on `C` is needed: if `C < 0` the two eventual hypotheses
cannot both hold, and the formal squeeze is unaffected. -/
theorem tendsto_div_rpow_of_eventually_le_const_mul_sqrt_log
    (F : ℕ → ℝ) (C γ : ℝ) (hγ : 1 / 2 < γ)
    (hnn : ∀ᶠ N : ℕ in atTop, 0 ≤ F N)
    (hb : ∀ᶠ N : ℕ in atTop, F N ≤ C * Real.sqrt (Real.log (N : ℝ))) :
    Tendsto (fun N : ℕ => F N / (Real.log (N : ℝ)) ^ γ) atTop (𝓝 0) := by
  have hγneg : 0 < γ - 1 / 2 := by linarith
  have hg : Tendsto (fun N : ℕ => C * (Real.log (N : ℝ)) ^ (1 / 2 - γ)) atTop (𝓝 0) := by
    have hbase : Tendsto (fun N : ℕ => (Real.log (N : ℝ)) ^ (-(γ - 1 / 2)))
        atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hγneg).comp
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    have hmul := hbase.const_mul C
    simpa only [mul_zero, neg_sub] using hmul
  refine squeeze_zero' ?_ ?_ hg
  · filter_upwards [hnn, eventually_ge_atTop 2] with N hF hN
    have hlogpos : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    exact div_nonneg hF (Real.rpow_pos_of_pos hlogpos γ).le
  · filter_upwards [hb, eventually_ge_atTop 2] with N hbN hN
    have hlogpos : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hpowpos : 0 < (Real.log (N : ℝ)) ^ γ := Real.rpow_pos_of_pos hlogpos γ
    refine (div_le_div_of_nonneg_right hbN hpowpos.le).trans_eq ?_
    rw [Real.sqrt_eq_rpow, mul_div_assoc, ← Real.rpow_sub hlogpos]

/-! ## The unconditional stretched-exponential vanishing -/

/-- **Unconditional stretched-exponential vanishing of the log-deficit.**  For
every real exponent `γ > 1/2`,

`Tendsto (fun N : ℕ => λ(N) / (log N)^γ) atTop (𝓝 0)`,

i.e. `λ = o((log N)^γ)` for every `γ > 1/2`.

This is the generic squeeze `tendsto_div_rpow_of_eventually_le_const_mul_sqrt_log`
fed by the accepted envelope at `δ = 1`, i.e. with the explicit constant
`C = torusLeadingConstant + 1 > 0`.  It is unconditional (no #142 hypothesis),
and it says that the log-deficit is negligible against every stretched-
exponential scale strictly above the critical `√(log N)` scale. -/
theorem tendsto_rothLogDeficit_div_rpow_zero (γ : ℝ) (hγ : 1 / 2 < γ) :
    Tendsto (fun N : ℕ => rothLogDeficit N / (Real.log (N : ℝ)) ^ γ) atTop (𝓝 0) :=
  tendsto_div_rpow_of_eventually_le_const_mul_sqrt_log rothLogDeficit
    (torusLeadingConstant + 1) γ hγ
    eventually_rothLogDeficit_nonneg
    (eventually_rothLogDeficit_le_mul_sqrt_log 1 (by norm_num))

/-- **No positive stretched-exponential leading constant.**  For every real
exponent `γ > 1/2` and every real `c > 0`, the ratio `λ(N) / (log N)^γ` does
**not** tend to `c`.

Explicitly, no asymptotic relation `r₃(N) = N · exp(-(c + o(1)) · (log N)^γ)`
with `γ > 1/2` and `c > 0` can hold.  This is a pure scale-classification
statement: the log-deficit is `o((log N)^γ)` at every such scale by
`tendsto_rothLogDeficit_div_rpow_zero`, so uniqueness of limits rules out any
positive limit.  It does not resolve Erdős #142 and says nothing about the
critical scale `γ = 1/2`. -/
theorem not_tendsto_rothLogDeficit_div_rpow (γ c : ℝ)
    (hγ : 1 / 2 < γ) (hc : 0 < c) :
    ¬ Tendsto (fun N : ℕ => rothLogDeficit N / (Real.log (N : ℝ)) ^ γ) atTop (𝓝 c) := by
  intro h
  have hzero := tendsto_rothLogDeficit_div_rpow_zero γ hγ
  exact hc.ne' (tendsto_nhds_unique h hzero)

/-! ## The critical-scale transfer -/

/-- **The critical limit is bounded by `torusLeadingConstant`.**  If the
normalized deficit at the critical scale `γ = 1/2` converges,

`Tendsto (fun N : ℕ => λ(N) / √(log N)) atTop (𝓝 c)`,

then necessarily `c ≤ torusLeadingConstant`.

This is a conditional transfer of the accepted upper envelope
`eventually_normalizedDeficit_rothNumberNat_le_add` across the definitional
bridge `normalizedDeficit_rothNumberNat_eq`: for each `δ > 0` the accepted
envelope gives eventually `normalizedDeficit r₃ N ≤ torusLeadingConstant + δ`,
so `le_of_tendsto` yields `c ≤ torusLeadingConstant + δ`, and
`le_of_forall_pos_le_add` removes the slack.

**The hypothesis is not known to hold.**  Whether the critical normalized
deficit converges is the #142 endpoint itself; this theorem asserts only the
conditional implication and does **not** claim that such a `c` exists, nor any
value for it. -/
theorem le_torusLeadingConstant_of_tendsto_rothLogDeficit_div_sqrt (c : ℝ)
    (h : Tendsto (fun N : ℕ => rothLogDeficit N / Real.sqrt (Real.log (N : ℝ)))
      atTop (𝓝 c)) :
    c ≤ torusLeadingConstant := by
  have hD : Tendsto (fun N : ℕ => normalizedDeficit rothNumberNat N) atTop (𝓝 c) :=
    h.congr' (Eventually.of_forall fun N => (normalizedDeficit_rothNumberNat_eq N).symm)
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  exact le_of_tendsto hD (eventually_normalizedDeficit_rothNumberNat_le_add δ hδ)

/-! ## Non-vacuity checks -/

/-- Satisfiable instance of the generic squeeze: the identically zero sequence
satisfies both eventual hypotheses at every constant `C`, so its quotient by
`(log N)^2` tends to `0`.  This witnesses that the hypotheses of
`tendsto_div_rpow_of_eventually_le_const_mul_sqrt_log` are jointly satisfiable
and that the conclusion is not vacuous. -/
example :
    Tendsto (fun N : ℕ => (0 : ℝ) / (Real.log (N : ℝ)) ^ (2 : ℝ)) atTop (𝓝 0) :=
  tendsto_div_rpow_of_eventually_le_const_mul_sqrt_log (fun _ => 0) 0 2
    (by norm_num) (Eventually.of_forall fun _ => le_rfl)
    (Eventually.of_forall fun _ => by simp)

/-- The conclusion of the critical-scale transfer is satisfiable in the intended
direction: the bound `torusLeadingConstant` is nonnegative, so the claim
`c ≤ torusLeadingConstant` is not an empty statement about a phantom constant. -/
example : (0 : ℝ) ≤ torusLeadingConstant := torusLeadingConstant_pos.le

end

end Erdos142

-- Axiom audit for the public declarations of this module.
#print axioms Erdos142.normalizedDeficit_rothNumberNat_eq
#print axioms Erdos142.eventually_nonneg_and_le_rothLogDeficit_mul_sqrt_log
#print axioms Erdos142.eventually_rothLogDeficit_nonneg
#print axioms Erdos142.eventually_rothLogDeficit_le_mul_sqrt_log
#print axioms Erdos142.tendsto_div_rpow_of_eventually_le_const_mul_sqrt_log
#print axioms Erdos142.tendsto_rothLogDeficit_div_rpow_zero
#print axioms Erdos142.not_tendsto_rothLogDeficit_div_rpow
#print axioms Erdos142.le_torusLeadingConstant_of_tendsto_rothLogDeficit_div_sqrt