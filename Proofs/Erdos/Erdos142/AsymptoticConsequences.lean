/-
  Erdős Problem #142 — asymptotic consequences of an eventual Behrend/EHPS lower bound.

  `ProductDefect.lean` isolates the *subpower hypothesis*

      `Tendsto (fun N => rothLogDeficit N / log N) atTop (𝓝 0)`

  as the single conditional input to the negative/shared product-defect theorem
  `rothProductDefect_unbounded_of_tendsto` and the no-constant-reverse corollary
  `exists_mul_lt_rothNumberNat_of_pos`.

  This file discharges that premise from a *Behrend/EHPS-shaped* eventual lower
  bound on the Roth number: for some real `C`,

      `N * exp (-C * sqrt (log N)) ≤ rothNumberNat N`  eventually in `N`.

  This is exactly the shape produced by the Behrend construction (and the
  refined Elsholtz–Hunter–Pach–Szemerédi-type refinements); the file keeps the
  constant `C` explicit so that a later wrapper can instantiate it from the
  positive-lane quantitative theorem.

  The analytic content is the squeeze
  `0 ≤ rothLogDeficit N / log N ≤ C / sqrt (log N) → 0`: taking logarithms of
  the lower bound gives `rothLogDeficit N ≤ C * sqrt (log N)`, and dividing by
  the positive `log N` yields the right-hand side, which vanishes because
  `sqrt ∘ log ∘ (↑·) → atTop` and `Filter.Tendsto.const_div_atTop`.

  The premises are kept explicit; no actual Roth lower bound is asserted, no
  `sorry`/`axiom`/`unsafe` is used, and the axiom audit is at the end.
-/

import Erdos.Erdos142.ProductDefect

set_option autoImplicit false

open Filter
open scoped Topology

namespace Erdos142

noncomputable section

/-- **Generic squeeze for sub-power deficits.**  Let `D : ℕ → ℝ` be eventually
nonnegative after division by `log N` and eventually bounded by
`C / sqrt (log N)`.  Then `D N / log N → 0`.

This is the analytic core of the file, stated for an arbitrary sequence so that
its satisfiability is transparent: any `D` with `0 ≤ D N ≤ C * sqrt (log N)`
eventually qualifies.  The proof is the squeeze
`0 ≤ D N / log N ≤ C / sqrt (log N)` together with
`sqrt (log N) → atTop` and `Filter.Tendsto.const_div_atTop`. -/
theorem tendsto_div_log_of_eventually_le_const_div_sqrt_log
    (D : ℕ → ℝ) (C : ℝ)
    (hnn : ∀ᶠ N : ℕ in atTop, 0 ≤ D N / Real.log (N : ℝ))
    (hb : ∀ᶠ N : ℕ in atTop,
      D N / Real.log (N : ℝ) ≤ C / Real.sqrt (Real.log (N : ℝ))) :
    Tendsto (fun N : ℕ => D N / Real.log (N : ℝ)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun N : ℕ => Real.sqrt (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hCdiv : Tendsto (fun N : ℕ => C / Real.sqrt (Real.log (N : ℝ))) atTop (𝓝 0) :=
    hlim.const_div_atTop C
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hCdiv hnn hb

/-- **The subpower premise from an eventual Behrend/EHPS lower bound.**  If for
some real `C` the Roth number eventually dominates `N * exp (-C * sqrt (log N))`,
then the log-deficit is sub-logarithmic:
`rothLogDeficit N / log N → 0`.

Route: eventually `N ≥ 2`, so `1 ≤ rothNumberNat N ≤ N` and `log N > 0`.  Taking
logarithms of the lower bound gives `rothLogDeficit N ≤ C * sqrt (log N)`, hence
`0 ≤ rothLogDeficit N / log N ≤ C / sqrt (log N)`, and the right-hand side
vanishes by `Filter.Tendsto.const_div_atTop`. -/
theorem tendsto_rothLogDeficit_div_log_of_eventually_lower
    (C : ℝ)
    (hlower : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) * Real.exp (-C * Real.sqrt (Real.log (N : ℝ))) ≤
        (rothNumberNat N : ℝ)) :
    Tendsto (fun N : ℕ => rothLogDeficit N / Real.log (N : ℝ)) atTop (𝓝 0) := by
  have hev : ∀ᶠ N : ℕ in atTop, 2 ≤ N ∧
      (N : ℝ) * Real.exp (-C * Real.sqrt (Real.log (N : ℝ))) ≤
        (rothNumberNat N : ℝ) :=
    (eventually_atTop.mpr ⟨2, fun N hN => hN⟩).and hlower
  refine tendsto_div_log_of_eventually_le_const_div_sqrt_log rothLogDeficit C ?_ ?_
  · -- eventual nonnegativity of `rothLogDeficit N / log N`
    refine hev.mono ?_
    rintro N ⟨hN2, _⟩
    have hN1 : 1 ≤ N := by omega
    have hlogpos : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < N))
    have hrpos : (0 : ℝ) < (rothNumberNat N : ℝ) := rothNumberNat_pos_real hN1
    have hlogle : Real.log (rothNumberNat N : ℝ) ≤ Real.log (N : ℝ) :=
      Real.log_le_log hrpos (by exact_mod_cast rothNumberNat_le N)
    have hnn : 0 ≤ rothLogDeficit N := by
      rw [rothLogDeficit_eq hN1]
      linarith
    exact div_nonneg hnn hlogpos.le
  · -- eventual upper bound `rothLogDeficit N / log N ≤ C / sqrt (log N)`
    refine hev.mono ?_
    rintro N ⟨hN2, hlow⟩
    have hN1 : 1 ≤ N := by omega
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
    have hlogpos : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < N))
    have hsqrtpos : 0 < Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_pos.mpr hlogpos
    have hrpos : (0 : ℝ) < (rothNumberNat N : ℝ) := rothNumberNat_pos_real hN1
    have hlhs : 0 < (N : ℝ) * Real.exp (-C * Real.sqrt (Real.log (N : ℝ))) :=
      mul_pos hNpos (Real.exp_pos _)
    have hlog := Real.log_le_log hlhs hlow
    have hlogL : Real.log ((N : ℝ) * Real.exp (-C * Real.sqrt (Real.log (N : ℝ)))) =
        Real.log (N : ℝ) - C * Real.sqrt (Real.log (N : ℝ)) := by
      rw [Real.log_mul hNne (Real.exp_ne_zero _), Real.log_exp]
      ring
    rw [hlogL] at hlog
    have hd : rothLogDeficit N ≤ C * Real.sqrt (Real.log (N : ℝ)) := by
      rw [rothLogDeficit_eq hN1]
      linarith
    have hsq : Real.sqrt (Real.log (N : ℝ)) * Real.sqrt (Real.log (N : ℝ)) =
        Real.log (N : ℝ) := Real.mul_self_sqrt hlogpos.le
    have hmul : rothLogDeficit N * Real.sqrt (Real.log (N : ℝ)) ≤ C * Real.log (N : ℝ) := by
      have := mul_le_mul_of_nonneg_right hd hsqrtpos.le
      rwa [mul_assoc, hsq] at this
    exact (div_le_div_iff₀ hlogpos hsqrtpos).mpr hmul

/-- **Unbounded product defect from an eventual Behrend/EHPS lower bound.**
Under the eventual lower bound `N * exp (-C * sqrt (log N)) ≤ rothNumberNat N`,
the product defect of the Roth number is unbounded above: for every real `B`
there are `N, M ≥ 1` with `B < rothProductDefect N M`.

This is `rothProductDefect_unbounded_of_tendsto` fed by the subpower premise
`tendsto_rothLogDeficit_div_log_of_eventually_lower`. -/
theorem rothProductDefect_unbounded_of_eventually_lower
    (C : ℝ)
    (hlower : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) * Real.exp (-C * Real.sqrt (Real.log (N : ℝ))) ≤
        (rothNumberNat N : ℝ)) :
    ∀ B : ℝ, ∃ N M : ℕ, 1 ≤ N ∧ 1 ≤ M ∧ B < rothProductDefect N M :=
  rothProductDefect_unbounded_of_tendsto
    (tendsto_rothLogDeficit_div_log_of_eventually_lower C hlower)

/-- **No-constant-reverse corollary from an eventual Behrend/EHPS lower bound.**
Under the eventual lower bound `N * exp (-C * sqrt (log N)) ≤ rothNumberNat N`,
for every real `C' > 0` there are `N, M ≥ 1` with
`C' * rothNumberNat N * rothNumberNat M < rothNumberNat (N * (2 * M - 1))`.

This is `exists_mul_lt_rothNumberNat_of_pos` fed by the subpower premise. -/
theorem exists_mul_lt_rothNumberNat_of_eventually_lower
    (C : ℝ)
    (hlower : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) * Real.exp (-C * Real.sqrt (Real.log (N : ℝ))) ≤
        (rothNumberNat N : ℝ))
    (C' : ℝ) (hC' : 0 < C') :
    ∃ N M : ℕ, 1 ≤ N ∧ 1 ≤ M ∧
      C' * (rothNumberNat N : ℝ) * (rothNumberNat M : ℝ) <
        (rothNumberNat (N * (2 * M - 1)) : ℝ) :=
  exists_mul_lt_rothNumberNat_of_pos
    (tendsto_rothLogDeficit_div_log_of_eventually_lower C hlower) C' hC'

/-- Ground-truth, satisfiable instance of the generic squeeze: the identically
zero deficit satisfies both eventual hypotheses, so its quotient by `log N`
tends to `0`. -/
example : Tendsto (fun N : ℕ => (0 : ℝ) / Real.log (N : ℝ)) atTop (𝓝 0) :=
  tendsto_div_log_of_eventually_le_const_div_sqrt_log (fun _ => 0) 0
    (Eventually.of_forall (fun N => by simp))
    (Eventually.of_forall (fun N => by simp))

end

end Erdos142

-- Axiom audit for the load-bearing declarations.
#print axioms Erdos142.tendsto_div_log_of_eventually_le_const_div_sqrt_log
#print axioms Erdos142.tendsto_rothLogDeficit_div_log_of_eventually_lower
#print axioms Erdos142.rothProductDefect_unbounded_of_eventually_lower
#print axioms Erdos142.exists_mul_lt_rothNumberNat_of_eventually_lower