/-
  Erdős Problem #142 — unconditional consequences of the eventual torus lower bound.

  This module composes the accepted unconditional lower bound
  `TorusAsymptoticLowerBound.eventually_rothNumberNat_lower_bound` with the
  accepted generic consequences in `AsymptoticConsequences`.  Instantiating the
  eventual bound at `δ = 1`, i.e. at `C = torusLeadingConstant + 1`, discharges
  the Behrend/EHPS-shaped hypothesis of every consequence there and yields three
  unconditional statements about the Roth number `r₃(N) = rothNumberNat N`:

  * `tendsto_rothLogDeficit_div_log_zero`: `rothLogDeficit N / log N → 0`;
  * `rothProductDefect_unbounded`: the product defect is unbounded above;
  * `exists_mul_lt_rothNumberNat`: for every `C > 0` there are `N, M ≥ 1` with
    `C · r₃(N) · r₃(M) < r₃(N · (2M - 1))`.

  Together these rule out *every* constant-factor reverse inequality for the
  accepted scale-product inequality `r₃(N) · r₃(M) ≤ r₃(N · (2M - 1))`: the
  ratio `r₃(N · (2M - 1)) / (r₃(N) · r₃(M))` is unbounded above.

  They do *not* resolve Erdős #142.  No upper bound on `r₃` and no lower bound
  with constant `0` is asserted; the sub-logarithmic deficit established here is
  compatible with the Behrend-class construction and says nothing about whether
  a three-term-progression-free set of density `N^{1-o(1)}` exists.

  No `sorry`, no `unsafe`, no new axioms, and no existing declaration is edited.
-/

import Erdos.Erdos142.TorusAsymptoticLowerBound
import Erdos.Erdos142.AsymptoticConsequences

set_option autoImplicit false

open Filter
open scoped Topology

namespace Erdos142

/-- **Unconditional sub-logarithmic deficit of the Roth number.**
`Tendsto (fun N => rothLogDeficit N / log N) atTop (𝓝 0)`.

This is `tendsto_rothLogDeficit_div_log_of_eventually_lower` fed by the accepted
eventual torus lower bound at `δ = 1`, i.e. with the explicit constant
`C = torusLeadingConstant + 1`.  It is the single premise that the generic
product-defect and no-constant-reverse consequences in `AsymptoticConsequences`
take as input. -/
theorem tendsto_rothLogDeficit_div_log_zero :
    Tendsto (fun N : ℕ => rothLogDeficit N / Real.log (N : ℝ)) atTop (𝓝 0) :=
  tendsto_rothLogDeficit_div_log_of_eventually_lower (torusLeadingConstant + 1)
    (eventually_rothNumberNat_lower_bound 1 (by norm_num))

/-- **Unboundedness of the product defect (unconditional).**  For every real `B`
there are `N, M ≥ 1` with `B < rothProductDefect N M`.

This is `rothProductDefect_unbounded_of_eventually_lower` fed by the eventual
torus lower bound at `δ = 1`.  Unboundedness of the product defect is exactly
the failure of every constant reverse bound for the accepted scale-product
inequality. -/
theorem rothProductDefect_unbounded :
    ∀ B : ℝ, ∃ N M : ℕ, 1 ≤ N ∧ 1 ≤ M ∧ B < rothProductDefect N M :=
  rothProductDefect_unbounded_of_tendsto tendsto_rothLogDeficit_div_log_zero

/-- **No constant reverse bound for the scale-product inequality
(unconditional).**  For every real `C > 0` there are `N, M ≥ 1` with
`C · r₃(N) · r₃(M) < r₃(N · (2M - 1))`.

This is `exists_mul_lt_rothNumberNat_of_eventually_lower` fed by the eventual
torus lower bound at `δ = 1`.  It rules out every constant-factor reverse
inequality for `r₃(N) · r₃(M) ≤ r₃(N · (2M - 1))`, but does not resolve
Erdős #142. -/
theorem exists_mul_lt_rothNumberNat (C : ℝ) (hC : 0 < C) :
    ∃ N M : ℕ, 1 ≤ N ∧ 1 ≤ M ∧
      C * (rothNumberNat N : ℝ) * (rothNumberNat M : ℝ) <
        (rothNumberNat (N * (2 * M - 1)) : ℝ) :=
  exists_mul_lt_rothNumberNat_of_pos tendsto_rothLogDeficit_div_log_zero C hC

end Erdos142

-- Axiom audit for the load-bearing declarations.
#print axioms Erdos142.tendsto_rothLogDeficit_div_log_zero
#print axioms Erdos142.rothProductDefect_unbounded
#print axioms Erdos142.exists_mul_lt_rothNumberNat