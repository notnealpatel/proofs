/-
  Erdős Problem #142 — unconditional rigidity of a finite odd-scale ratio limit
  for the Roth numbers.

  The Roth number `rothNumberNat N` is the largest cardinality of a
  three-term-progression-free subset of `{0, …, N - 1}`.  The accepted
  scale-product bound gives `rothNumberNat N * rothNumberNat M ≤
  rothNumberNat (N * (2 * M - 1))`, so the odd-scale ratio

      `R M N = rothNumberNat (N * (2 * M - 1)) / rothNumberNat N`

  is at least `1` for `N ≥ 1`.

  This file shows that any *finite* limit of `R M N` is forced to the single
  value `2 * M - 1`, eliminating the whole class of "natural wrong" finite
  fixed-odd-scale ratio limits: the ratio cannot settle on any value other than
  the odd scale `2 * M - 1`.

  The three substantive ingredients are:

  * `one_le_rothNumberNat_odd_scale_ratio`: the ratio is at least `1`, from
    monotonicity of `rothNumberNat` alone (`N ≤ N * (2 * M - 1)` for `M ≥ 1`).
    This is a purely unconditional inequality and carries no convergence
    hypothesis and no positivity hypothesis beyond `M, N ≥ 1`.

  * `pos_of_tendsto_rothNumberNat_odd_scale_ratio`: if the ratio tends to a
    finite real `c` then `c > 0`.  The lower bound `R M N ≥ 1` is eventually
    true, so `le_of_tendsto_of_tendsto` pushes it to the limit.  This is what
    makes the logarithm route legitimate.

  * `eq_odd_scale_of_tendsto_rothNumberNat_ratio`: if the ratio tends to a
    finite real `c` then `c = 2 * M - 1`.  Because `c > 0`, `Real.log` is
    continuous at `c` (`Real.continuousAt_log`) and the logarithmic ratio tends
    to `log c`.  On the tail `N ≥ 1` the exact defect identity
    `rothProductDefect_eq_rothLogDeficit` rewrites `log (R M N)` as
    `rothProductDefect N M + log (rothNumberNat M)`, so the defect tends to the
    finite limit `log c - log (rothNumberNat M)`.
    `tendsto_fixed_right_rothProductDefect_eq_threshold` then pins that limit to
    the threshold `rothLogDeficit M + log ((2 * M - 1) / M)`; expanding
    `rothLogDeficit M` via `rothLogDeficit_eq` and collapsing the logarithms
    with `Real.log_div` yields `log c = log (2 * M - 1)`.  Finally
    `Real.log_injOn_pos` and `2 * M - 1 > 0` give `c = 2 * M - 1`.

  * `not_tendsto_rothNumberNat_ratio_of_ne_odd_scale` is the contrapositive: a
    finite limit different from `2 * M - 1` cannot exist.

  What this does and does not say.  This is an unconditional classifier of any
  finite ratio limit, *conditional only on the existence* of that limit.  It does
  not prove that the ratio `R M N` converges, does not prove full regular
  variation of `N ↦ rothNumberNat N`, and asserts nothing about oscillation or
  about `limsup`/`liminf` of the ratio.  In particular it does not resolve
  Erdős #142.  The result is sharp for the compatible boundary model in which
  the index-one relation `rothNumberNat N = N * L N` holds with a slowly varying
  `L`: there the ratio tends to `2 * M - 1` exactly, so the value `2 * M - 1` is
  attained, not merely forced.  The declarations here take the convergence of
  `R M N` as an explicit hypothesis precisely because that convergence is not
  established.

  A note on satisfiability.  The convergence hypothesis is the open content:
  existence of the finite limit is exactly what is not known, so no concrete
  witness for it is constructed here.  What *is* checked below is that (i) the
  unconditional lower bound holds at the concrete boundary input `(M, N) = (1, 1)`,
  witnessing non-vacuity of `one_le_rothNumberNat_odd_scale_ratio`, and
  (ii) the forced value `2 * M - 1` is positive and distinct from the wrong
  fixed-odd-scale value `1` at `M = 2`.  The reality is that the classifiers are
  implications whose antecedent may currently be false; when it holds they carry
  genuine content and the falsifier (loss of positivity or of the defect limit)
  has been excluded.

  No `sorry`, no `unsafe`, no new axioms, no `axiom` declaration, and no
  existing declaration is edited.
-/

import Erdos.Erdos142.FixedRadixRecurrence

set_option autoImplicit false

open Filter
open scoped Topology

namespace Erdos142

noncomputable section

/-- **Unconditional lower bound for the odd-scale ratio.**  For `M, N ≥ 1` the
odd-scale ratio is at least `1`:

`1 ≤ rothNumberNat (N * (2 * M - 1)) / rothNumberNat N`.

Route: `rothNumberNat` is monotone and `N ≤ N * (2 * M - 1)` for `M ≥ 1`, so
`rothNumberNat N ≤ rothNumberNat (N * (2 * M - 1))`; dividing by the positive
`rothNumberNat N` gives the claim.  No convergence hypothesis is involved. -/
theorem one_le_rothNumberNat_odd_scale_ratio {M N : ℕ}
    (hM : 1 ≤ M) (hN : 1 ≤ N) :
    (1 : ℝ) ≤ (rothNumberNat (N * (2 * M - 1)) : ℝ) / (rothNumberNat N : ℝ) := by
  have hNpos : 0 < (rothNumberNat N : ℝ) := rothNumberNat_pos_real hN
  rw [le_div_iff₀ hNpos]
  have hle : rothNumberNat N ≤ rothNumberNat (N * (2 * M - 1)) := by
    apply rothNumberNat.monotone
    calc N = N * 1 := (Nat.mul_one N).symm
      _ ≤ N * (2 * M - 1) := Nat.mul_le_mul_left N (by omega)
  calc (1 : ℝ) * (rothNumberNat N : ℝ) = (rothNumberNat N : ℝ) := one_mul _
    _ ≤ (rothNumberNat (N * (2 * M - 1)) : ℝ) := by exact_mod_cast hle

/-- **Positivity of a finite odd-scale ratio limit.**  For `M ≥ 2`, if the ratio
`(rothNumberNat (N * (2 * M - 1)) : ℝ) / (rothNumberNat N : ℝ)` tends to a finite
real `c`, then `0 < c`.

Route: by `one_le_rothNumberNat_odd_scale_ratio` the ratio is at least `1` for
all `N ≥ 1`, hence eventually along `atTop`; `le_of_tendsto_of_tendsto` transfers
this to the limit, giving `1 ≤ c`. -/
theorem pos_of_tendsto_rothNumberNat_odd_scale_ratio {M : ℕ} (hM : 2 ≤ M) {c : ℝ}
    (h : Tendsto (fun N : ℕ =>
      (rothNumberNat (N * (2 * M - 1)) : ℝ) / (rothNumberNat N : ℝ)) atTop (𝓝 c)) :
    0 < c := by
  have hM1 : 1 ≤ M := by omega
  have hev : ∀ᶠ N : ℕ in atTop,
      (1 : ℝ) ≤ (rothNumberNat (N * (2 * M - 1)) : ℝ) / (rothNumberNat N : ℝ) :=
    eventually_atTop.mpr ⟨1, fun N hN => one_le_rothNumberNat_odd_scale_ratio hM1 hN⟩
  have h1c : (1 : ℝ) ≤ c := le_of_tendsto_of_tendsto tendsto_const_nhds h hev
  linarith

/-- **Rigidity of a finite odd-scale ratio limit.**  For fixed `M ≥ 2`, if the
ratio `(rothNumberNat (N * (2 * M - 1)) : ℝ) / (rothNumberNat N : ℝ)` converges
to a finite real `c`, then necessarily

`c = ((2 * M - 1 : ℕ) : ℝ)`.

Route: `pos_of_tendsto_rothNumberNat_odd_scale_ratio` gives `0 < c`, so `log` is
continuous at `c` and the logarithmic ratio tends to `log c`.  On the eventual
tail the exact identity `rothProductDefect_eq_rothLogDeficit` writes
`log (R M N) = rothProductDefect N M + log (rothNumberNat M)`, so
`rothProductDefect N M` tends to `log c - log (rothNumberNat M)`.
`tendsto_fixed_right_rothProductDefect_eq_threshold` forces that limit to equal
`rothLogDeficit M + log ((2 * M - 1) / M)`; `rothLogDeficit_eq` and `Real.log_div`
collapse the logarithms to `log c = log (2 * M - 1)`, and `Real.log_injOn_pos`
gives `c = 2 * M - 1`.  This classifies every finite limit; it does not prove
that a limit exists. -/
theorem eq_odd_scale_of_tendsto_rothNumberNat_ratio {M : ℕ} (hM : 2 ≤ M) {c : ℝ}
    (h : Tendsto (fun N : ℕ =>
      (rothNumberNat (N * (2 * M - 1)) : ℝ) / (rothNumberNat N : ℝ)) atTop (𝓝 c)) :
    c = ((2 * M - 1 : ℕ) : ℝ) := by
  have hM1 : 1 ≤ M := by omega
  have hcpos : 0 < c := pos_of_tendsto_rothNumberNat_odd_scale_ratio hM h
  have hlog : Tendsto (fun N : ℕ =>
      Real.log ((rothNumberNat (N * (2 * M - 1)) : ℝ) / (rothNumberNat N : ℝ)))
      atTop (𝓝 (Real.log c)) :=
    h.log (ne_of_gt hcpos)
  have hevlog : (fun N : ℕ =>
        Real.log ((rothNumberNat (N * (2 * M - 1)) : ℝ) / (rothNumberNat N : ℝ))
          - Real.log ((rothNumberNat M : ℕ) : ℝ))
      =ᶠ[atTop] (fun N : ℕ => rothProductDefect N M) := by
    refine eventually_atTop.mpr ⟨1, fun N hN => ?_⟩
    dsimp only
    have hNq1 : 1 ≤ N * (2 * M - 1) := by
      apply Nat.one_le_iff_ne_zero.mpr
      exact Nat.mul_ne_zero (by omega) (by omega)
    have hrNq_nat : rothNumberNat (N * (2 * M - 1)) ≠ 0 := by
      have h1 := one_le_rothNumberNat hNq1
      omega
    have hrN_nat : rothNumberNat N ≠ 0 := by
      have h1 := one_le_rothNumberNat hN
      omega
    have hrNq : ((rothNumberNat (N * (2 * M - 1)) : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast hrNq_nat
    have hrN : ((rothNumberNat N : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast hrN_nat
    rw [Real.log_div hrNq hrN, rothProductDefect]
  have hsub : Tendsto (fun N : ℕ =>
      Real.log ((rothNumberNat (N * (2 * M - 1)) : ℝ) / (rothNumberNat N : ℝ))
        - Real.log ((rothNumberNat M : ℕ) : ℝ)) atTop
      (𝓝 (Real.log c - Real.log ((rothNumberNat M : ℕ) : ℝ))) :=
    hlog.sub tendsto_const_nhds
  have hDefect : Tendsto (fun N : ℕ => rothProductDefect N M) atTop
      (𝓝 (Real.log c - Real.log ((rothNumberNat M : ℕ) : ℝ))) :=
    Tendsto.congr' hevlog hsub
  have hthr := tendsto_fixed_right_rothProductDefect_eq_threshold hM hDefect
  have hdefM : rothLogDeficit M =
      Real.log (M : ℝ) - Real.log ((rothNumberNat M : ℕ) : ℝ) :=
    rothLogDeficit_eq hM1
  have hq_pos : (0 : ℝ) < ((2 * M - 1 : ℕ) : ℝ) := by
    have : (0 : ℕ) < 2 * M - 1 := by omega
    exact_mod_cast this
  have hM_ne : (M : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : M ≠ 0)
  have hlogdiv : Real.log (((2 * M - 1 : ℕ) : ℝ) / (M : ℝ)) =
      Real.log ((2 * M - 1 : ℕ) : ℝ) - Real.log (M : ℝ) :=
    Real.log_div (ne_of_gt hq_pos) hM_ne
  rw [hdefM, hlogdiv] at hthr
  have hlogc : Real.log c = Real.log ((2 * M - 1 : ℕ) : ℝ) := by linarith
  exact Real.log_injOn_pos hcpos hq_pos hlogc

/-- **No finite limit off the odd scale.**  For fixed `M ≥ 2`, the ratio
`(rothNumberNat (N * (2 * M - 1)) : ℝ) / (rothNumberNat N : ℝ)` cannot converge to
any finite real `c` with `c ≠ ((2 * M - 1 : ℕ) : ℝ)`.  This is the contrapositive
of `eq_odd_scale_of_tendsto_rothNumberNat_ratio` and excludes the whole natural
wrong finite fixed-odd-scale ratio class.  It does not assert that the ratio
converges. -/
theorem not_tendsto_rothNumberNat_ratio_of_ne_odd_scale {M : ℕ} (hM : 2 ≤ M) {c : ℝ}
    (hcq : c ≠ ((2 * M - 1 : ℕ) : ℝ)) :
    ¬ Tendsto (fun N : ℕ =>
      (rothNumberNat (N * (2 * M - 1)) : ℝ) / (rothNumberNat N : ℝ)) atTop (𝓝 c) :=
  fun h => hcq (eq_odd_scale_of_tendsto_rothNumberNat_ratio hM h)

/-- Ground-truth check of the unconditional lower bound at the concrete input
`M = 1, N = 1`: the example instantiates `one_le_rothNumberNat_odd_scale_ratio`,
witnessing non-vacuity of the bound `1 ≤ ·`.  The example asserts only the
inequality and does not prove that the ratio equals `1` here. -/
example : (1 : ℝ) ≤
    (rothNumberNat (1 * (2 * 1 - 1)) : ℝ) / (rothNumberNat 1 : ℝ) :=
  one_le_rothNumberNat_odd_scale_ratio (M := 1) (N := 1) (by norm_num) (by norm_num)

/-- Ground-truth check of the forced value at `M = 2`: the classifier target
`((2 * 2 - 1 : ℕ) : ℝ) = 3` is positive and distinct from the wrong
fixed-odd-scale value `1`, so the conclusion is a substantive constraint. -/
example : ((2 * 2 - 1 : ℕ) : ℝ) = 3 ∧ (0 : ℝ) < ((2 * 2 - 1 : ℕ) : ℝ) ∧
    ((2 * 2 - 1 : ℕ) : ℝ) ≠ 1 := by
  norm_num

end

end Erdos142

-- Axiom audit for every public declaration.
#print axioms Erdos142.one_le_rothNumberNat_odd_scale_ratio
#print axioms Erdos142.pos_of_tendsto_rothNumberNat_odd_scale_ratio
#print axioms Erdos142.eq_odd_scale_of_tendsto_rothNumberNat_ratio
#print axioms Erdos142.not_tendsto_rothNumberNat_ratio_of_ne_odd_scale