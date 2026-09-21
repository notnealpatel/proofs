/-
  Erdős Problem #142 — the pure-power asymptotic obstruction for the Roth number.

  Let `r₃(N) = rothNumberNat N` be the largest size of a three-term-progression-free
  subset of `range N`.  This module records the two unconditional asymptotic
  facts that follow from the accepted explicit finite Roth threshold
  `ExplicitRothThreshold.rothNumberNat_lt_mul_of_explicitRothThreshold_le`
  together with the accepted unconditional logarithmic-deficit limit
  `TorusAsymptoticConsequences.tendsto_rothLogDeficit_div_log_zero`:

  * `tendsto_rothNumberNat_div_nat_zero`:
    `r₃(N) / N → 0` — Roth's density limit, in the explicit-threshold form;
  * `tendsto_log_rothNumberNat_div_log_one`:
    `log r₃(N) / log N → 1` — the logarithmic exponent of `r₃` is `1`;
  * `not_tendsto_rothNumberNat_div_rpow`: for **every** real exponent `α` and
    every real `c > 0`, the ratio `r₃(N) / N ^ α` does **not** tend to `c`.

  The last statement is the no-pure-power-law result: it excludes exactly the
  natural class `r₃(N) ~ c · N ^ α` with `c > 0` and `α` real, and nothing more.
  In particular the two positive facts above are jointly consistent: the
  cardinality has logarithmic exponent `1`, i.e. `r₃(N) = N^{1-o(1)}` in the
  logarithmic sense that `log r₃(N)/log N → 1`, equivalently the density obeys
  `r₃(N)/N = N^{-o(1)}` while still tending to `0`.  This does
  **not** solve Erdős #142: no upper bound on `r₃` sharper than `o(N)` is proved,
  no lower bound of the Behrend/EHPS shape is contradicted, and no finer subpower
  asymptotic formula for `r₃` is supplied.

  No `sorry`, no `unsafe`, no new axioms, and no existing declaration is edited.
-/

import Erdos.Erdos142.ExplicitRothThreshold
import Erdos.Erdos142.TorusAsymptoticConsequences
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

open Filter
open scoped Topology

namespace Erdos142

noncomputable section

/-- **Roth's density limit, unconditionally.**  `Tendsto (fun N : ℕ =>
(rothNumberNat N : ℝ) / (N : ℝ)) atTop (𝓝 0)`.

For every `b > 0` choose a density `δ = min b 1`, so `0 < δ ≤ b` and `δ ≤ 1`;
past `N ≥ explicitRothThreshold δ` the accepted explicit finite Roth threshold
gives `r₃(N) < δ · N`, hence `r₃(N)/N < δ ≤ b`.  Combined with eventual
nonnegativity (`N ≥ 1`) this is exactly `tendsto_order` at the limit `0`. -/
theorem tendsto_rothNumberNat_div_nat_zero :
    Tendsto (fun N : ℕ => (rothNumberNat N : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
  rw [tendsto_order]
  constructor
  · -- eventually the ratio is `≥ 0`, hence `> b` for every `b < 0`
    intro b hb
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hnonneg : 0 ≤ (rothNumberNat N : ℝ) / (N : ℝ) := by positivity
    linarith
  · -- eventually the ratio is `< b` for every `b > 0`
    intro b hb
    obtain ⟨δ, hδpos, hδle, hδone⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ b ∧ δ ≤ 1 :=
      ⟨min b 1, lt_min hb zero_lt_one, min_le_left _ _, min_le_right _ _⟩
    have hev : ∀ᶠ N : ℕ in atTop, explicitRothThreshold δ ≤ (N : ℝ) := by
      filter_upwards [eventually_ge_atTop (Nat.ceil (explicitRothThreshold δ))] with N hN
      have hceil : (Nat.ceil (explicitRothThreshold δ) : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast hN
      exact (Nat.le_ceil (explicitRothThreshold δ)).trans hceil
    filter_upwards [hev, eventually_ge_atTop 1] with N hthr hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hlt := rothNumberNat_lt_mul_of_explicitRothThreshold_le δ N hδpos hδone hthr
    have hdiv : (rothNumberNat N : ℝ) / (N : ℝ) < δ := by
      rw [div_lt_iff₀ hNpos]
      exact hlt
    exact hdiv.trans_le hδle

/-- **The logarithmic exponent of the Roth number is `1`, unconditionally.**
`Tendsto (fun N : ℕ => Real.log (rothNumberNat N : ℝ) / Real.log (N : ℝ))
atTop (𝓝 1)`.

Eventually at `N ≥ 2` both `r₃(N)` and `N` are positive and `log N ≠ 0`, so
`rothLogDeficit_eq` rewrites the ratio as
`log r₃(N)/log N = 1 - rothLogDeficit N / log N`, and the accepted unconditional
limit `tendsto_rothLogDeficit_div_log_zero` makes the right-hand side tend to
`1 - 0 = 1`. -/
theorem tendsto_log_rothNumberNat_div_log_one :
    Tendsto (fun N : ℕ => Real.log (rothNumberNat N : ℝ) / Real.log (N : ℝ))
      atTop (𝓝 1) := by
  have hlim : Tendsto (fun N : ℕ => 1 - rothLogDeficit N / Real.log (N : ℝ))
      atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub tendsto_rothLogDeficit_div_log_zero
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hNne : (N : ℝ) ≠ 1 := by
    exact_mod_cast (by omega : N ≠ 1)
  have hlogN : Real.log (N : ℝ) ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hNpos hNne
  have hsplit :
      (Real.log (N : ℝ) - Real.log (rothNumberNat N : ℝ)) / Real.log (N : ℝ) =
        1 - Real.log (rothNumberNat N : ℝ) / Real.log (N : ℝ) := by
    rw [sub_div, div_self hlogN]
  rw [rothLogDeficit_eq hN1, hsplit]
  ring

/-- **No positive pure power law for the Roth number, at any real exponent.**
For every real exponent `α` and every real constant `c > 0`, the ratio
`r₃(N) / N ^ α` does not tend to `c`.  The exponentiation is `Real.rpow`.

This excludes only the natural class `r₃(N) ~ c · N ^ α` with `c > 0` and real
`α`; it does not solve Erdős #142.

From a hypothetical positive limit `r₃(N)/N ^ α → c` with `c > 0`, continuity of
`Real.log` at `c` and eventual positivity of the ratio make
`log (r₃(N)/N ^ α)` tend to `log c`.  Dividing that bounded numerator by
`log N → +∞` gives `log (r₃(N)/N ^ α)/log N → 0`; using `Real.log_div` and
`Real.log_rpow` at `N ≥ 2` this is `log r₃(N)/log N - α → 0`, so
`log r₃(N)/log N → α`.  Uniqueness of limits against
`tendsto_log_rothNumberNat_div_log_one` forces `α = 1`.  Then `Real.rpow_one`
turns the ratio into `r₃(N)/N`, which tends to `0` by
`tendsto_rothNumberNat_div_nat_zero`; uniqueness forces `c = 0`, contradicting
`c > 0`. -/
theorem not_tendsto_rothNumberNat_div_rpow (α c : ℝ) (hc : 0 < c) :
    ¬ Tendsto (fun N : ℕ => (rothNumberNat N : ℝ) / (N : ℝ) ^ α) atTop (𝓝 c) := by
  intro h
  have hcne : c ≠ 0 := hc.ne'
  -- Continuity of `log` at the positive limit `c`.
  have hlog : Tendsto (fun N : ℕ => Real.log ((rothNumberNat N : ℝ) / (N : ℝ) ^ α))
      atTop (𝓝 (Real.log c)) :=
    (Real.continuousAt_log hcne).tendsto.comp h
  -- The logarithm of the ratio, divided by `log N → +∞`, tends to `0`.
  have hlogN : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hdiv : Tendsto (fun N : ℕ =>
      Real.log ((rothNumberNat N : ℝ) / (N : ℝ) ^ α) / Real.log (N : ℝ))
      atTop (𝓝 0) := hlog.div_atTop hlogN
  -- Eventually the exponent identity `log r₃/log N = log(ratio)/log N + α`.
  have heq : ∀ᶠ N : ℕ in atTop,
      Real.log ((rothNumberNat N : ℝ) / (N : ℝ) ^ α) / Real.log (N : ℝ) + α =
        Real.log (rothNumberNat N : ℝ) / Real.log (N : ℝ) := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hN1 : 1 ≤ N := by omega
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hNne : (N : ℝ) ≠ 1 := by exact_mod_cast (by omega : N ≠ 1)
    have hlogN : Real.log (N : ℝ) ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hNpos hNne
    have hrpos : (0 : ℝ) < (rothNumberNat N : ℝ) := rothNumberNat_pos_real hN1
    have hrpow : (0 : ℝ) < (N : ℝ) ^ α := Real.rpow_pos_of_pos hNpos α
    rw [Real.log_div hrpos.ne' hrpow.ne', Real.log_rpow hNpos α]
    have hsplit :
        (Real.log (rothNumberNat N : ℝ) - α * Real.log (N : ℝ)) / Real.log (N : ℝ) + α =
          Real.log (rothNumberNat N : ℝ) / Real.log (N : ℝ) := by
      field_simp
      ring
    rw [hsplit]
  have hAlpha : Tendsto (fun N : ℕ => Real.log (rothNumberNat N : ℝ) / Real.log (N : ℝ))
      atTop (𝓝 α) := by
    have hsum : Tendsto (fun N : ℕ =>
        Real.log ((rothNumberNat N : ℝ) / (N : ℝ) ^ α) / Real.log (N : ℝ) + α)
        atTop (𝓝 α) := by
      simpa using hdiv.add tendsto_const_nhds
    exact hsum.congr' heq
  -- Uniqueness of limits pins the exponent to `1`.
  have hα : α = 1 := tendsto_nhds_unique hAlpha tendsto_log_rothNumberNat_div_log_one
  rw [hα] at h
  have hratio : Tendsto (fun N : ℕ => (rothNumberNat N : ℝ) / (N : ℝ)) atTop (𝓝 c) := by
    simpa only [Real.rpow_one] using h
  have hzero : c = 0 := tendsto_nhds_unique hratio tendsto_rothNumberNat_div_nat_zero
  exact hc.ne' hzero

/-- Check of the generic exponent-one algebra and positivity at `N = 2`: the
rewrite underlying `not_tendsto_rothNumberNat_div_rpow` is valid for `α = 1`
and `N = 2`, using only `0 < r₃(2)` and `0 < 2`.  It does not prove or use a
value of `r₃(2)`. -/
example : Real.log ((rothNumberNat 2 : ℝ) / (2 : ℝ) ^ (1 : ℝ)) / Real.log (2 : ℝ) + 1 =
    Real.log (rothNumberNat 2 : ℝ) / Real.log (2 : ℝ) := by
  have hlog2 : Real.log (2 : ℝ) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  have hrpow : (0 : ℝ) < (2 : ℝ) ^ (1 : ℝ) := Real.rpow_pos_of_pos (by norm_num) 1
  have hrpos : (0 : ℝ) < (rothNumberNat 2 : ℝ) := rothNumberNat_pos_real (by norm_num)
  rw [Real.log_div hrpos.ne' hrpow.ne', Real.log_rpow (by norm_num : (0 : ℝ) < 2) 1]
  field_simp
  ring

end

end Erdos142

-- Axiom audit for the load-bearing declarations.
#print axioms Erdos142.tendsto_rothNumberNat_div_nat_zero
#print axioms Erdos142.tendsto_log_rothNumberNat_div_log_one
#print axioms Erdos142.not_tendsto_rothNumberNat_div_rpow