/-
  Erdős Problem #142 — fixed-dilation regularity of the normalized deficit.

  Let `r₃ = rothNumberNat` be the Roth number and let

      `λ(N) = rothLogDeficit N = log (N / r₃ N)`,
      `D(N) = normalizedDeficit r₃ N = λ(N) / √(log N)`

  be the *log-deficit* and the *normalized deficit*.  The accepted unconditional
  EHPS-shaped lower bound (`NormalizedDeficitEnvelope`, re-exported through
  `StretchedExponentialObstruction`) says that for every `δ > 0` eventually
  `0 ≤ λ(N) ≤ (torusLeadingConstant + δ) · √(log N)`, hence eventually
  `0 ≤ D(N) ≤ torusLeadingConstant + δ`.

  This module isolates the behaviour of `λ` and `D` at a **fixed multiplicative
  dilation** `N ↦ q · N`.  Its inputs are two accepted increment facts:

  * the iterated subadditivity `r₃ (q·N) ≤ q · r₃ N` of the Roth number, which
    is the block inequality `FixedRadixUpperEnvelope.rothNumberNat_mul_le_comm`
    and yields `λ(N) ≤ λ(q·N)` through
    `FixedRadixUpperEnvelope.rothLogDeficit_mono_mul` (after commuting `q·N`);
  * the monotonicity `r₃ N ≤ r₃ (q·N)`, which yields the *upper* increment
    bound `λ(q·N) − λ(N) ≤ log q`.

  The main results are:

  * `rothLogDeficit_mul_sub_mem` (with projections `rothLogDeficit_le_mul` and
    `rothLogDeficit_mul_sub_le_log`): for `N ≥ 1` and `q ≥ 1` the pointwise
    two-sided increment bound

        `0 ≤ λ(q·N) − λ(N) ≤ log q`;

  * `tendsto_rothLogDeficit_mul_sub_div_sqrt_zero`: the increment, normalized by
    the critical scale, vanishes,

        `(λ(q·N) − λ(N)) / √(log N) → 0`;

  * `tendsto_normalizedDeficit_rothNumberNat_mul_sub`: the **fixed-dilation
    regularity theorem for the normalized deficit**,

        `D(q·N) − D(N) → 0`   for every fixed `q ≥ 1`.

  The proof of the last statement is a two-sided squeeze at `N ≥ 2`, using the
  accepted envelope with `δ = 1` and the identity

      `√(log (q·N)) − √(log N) = log q / (√(log (q·N)) + √(log N))`,

  which turns the difference `D(q·N) − D(N)` into two terms each bounded by a
  constant multiple of `1/√(log N)` or `1/log(q·N)`.  One has

      `D(q·N) − D(N) ≥ −(torusLeadingConstant + 1) · log q / log(q·N)`,
      `D(q·N) − D(N) ≤ log q / √(log N)`

  eventually; both bounds tend to `0`.  **No sign is asserted for the increment
  `D(q·N) − D(N)` itself**, and `q = 1` is included (where the increment is
  identically zero).

  **Scope.**  This is a *regularity* statement at fixed multiplicative scales.
  It is compatible with a slowly varying, non-convergent `D`: it does **not**
  prove that `D(N)` converges, does **not** produce any limit, and does **not**
  resolve Erdős Problem #142.  What it does show is that bounded fixed
  multiplicative dilations cannot carry normalized-deficit oscillation: any
  oscillation of `D` must escape to unbounded scales.

  Nothing here edits an existing declaration; no `sorry`, no `unsafe` and no new
  axiom is used, and the axiom audit is at the end of the file.
-/

import Erdos.Erdos142.StretchedExponentialObstruction
import Erdos.Erdos142.FixedRadixUpperEnvelope

set_option autoImplicit false

open Filter
open scoped Topology

namespace Erdos142

noncomputable section

/-! ## The pointwise increment bound for the log-deficit -/

/-- **Two-sided increment bound for the log-deficit at fixed dilation.**  For
`N ≥ 1` and `q ≥ 1`,

`0 ≤ λ(q * N) - λ(N) ≤ log q`.

The lower bound is the iterated subadditivity `r₃ (q·N) ≤ q · r₃ N` in the form
`rothLogDeficit_mono_mul` (the commuting orientation `q * N` is handled by
`Nat.mul_comm`).  The upper bound is the *monotonicity* `r₃ N ≤ r₃ (q·N)`:
writing `λ(X) = log X - log r₃ X` for `X ≥ 1`, the increment becomes
`log q - log (r₃ (q·N) / r₃ N)`, and `r₃ (q·N) ≥ r₃ N ≥ 1` makes the second
logarithm nonnegative.  The two bounds therefore have different sources; in
particular the increment itself has no fixed sign. -/
theorem rothLogDeficit_mul_sub_mem {N q : ℕ} (hN : 1 ≤ N) (hq : 1 ≤ q) :
    0 ≤ rothLogDeficit (q * N) - rothLogDeficit N ∧
      rothLogDeficit (q * N) - rothLogDeficit N ≤ Real.log (q : ℝ) := by
  have hle : N ≤ q * N := Nat.le_mul_of_pos_left N (show 0 < q by omega)
  have hqN1 : 1 ≤ q * N := le_trans hN hle
  constructor
  · have hmono : rothLogDeficit N ≤ rothLogDeficit (q * N) := by
      have h := rothLogDeficit_mono_mul (N := N) (q := q) hN hq
      rwa [Nat.mul_comm N q] at h
    linarith
  · have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
    have hlogqN : Real.log (((q * N : ℕ)) : ℝ) = Real.log (q : ℝ) + Real.log (N : ℝ) := by
      rw [Nat.cast_mul, Real.log_mul (ne_of_gt hqpos) (ne_of_gt hNpos)]
    have hrnle : rothNumberNat N ≤ rothNumberNat (q * N) := rothNumberNat.monotone hle
    have hlogn : Real.log ((rothNumberNat N : ℕ) : ℝ) ≤
        Real.log ((rothNumberNat (q * N) : ℕ) : ℝ) :=
      Real.log_le_log (rothNumberNat_pos_real hN) (by exact_mod_cast hrnle)
    rw [rothLogDeficit_eq hqN1, rothLogDeficit_eq hN, hlogqN]
    linarith

/-- Lower half of `rothLogDeficit_mul_sub_mem`: fixed dilation does not decrease
the log-deficit, `λ(N) ≤ λ(q * N)` for `N ≥ 1`, `q ≥ 1`.  Its source is the
iterated subadditivity of the Roth number. -/
theorem rothLogDeficit_le_mul {N q : ℕ} (hN : 1 ≤ N) (hq : 1 ≤ q) :
    rothLogDeficit N ≤ rothLogDeficit (q * N) :=
  sub_nonneg.mp (rothLogDeficit_mul_sub_mem hN hq).1

/-- Upper half of `rothLogDeficit_mul_sub_mem`: the increment at fixed dilation
is at most `log q`, `λ(q * N) - λ(N) ≤ log q` for `N ≥ 1`, `q ≥ 1`.  Its source
is the monotonicity `r₃ N ≤ r₃ (q * N)`, not the subadditivity. -/
theorem rothLogDeficit_mul_sub_le_log {N q : ℕ} (hN : 1 ≤ N) (hq : 1 ≤ q) :
    rothLogDeficit (q * N) - rothLogDeficit N ≤ Real.log (q : ℝ) :=
  (rothLogDeficit_mul_sub_mem hN hq).2

/-- Ground-truth check of the increment bound at the nontrivial pair
`(N, q) = (3, 2)`. -/
example : 0 ≤ rothLogDeficit (2 * 3) - rothLogDeficit 3 ∧
    rothLogDeficit (2 * 3) - rothLogDeficit 3 ≤ Real.log (2 : ℝ) :=
  rothLogDeficit_mul_sub_mem (N := 3) (q := 2) (by norm_num) (by norm_num)

/-- Ground-truth check at `q = 1`: the dilation is trivial and the increment
vanishes. -/
example : rothLogDeficit (1 * 5) - rothLogDeficit 5 = 0 := by
  have h := rothLogDeficit_mul_sub_mem (N := 5) (q := 1) (by norm_num) (by norm_num)
  have h2 : Real.log ((1 : ℕ) : ℝ) = 0 := by norm_num
  rw [h2] at h
  linarith [h.1, h.2]

/-! ## A square-root difference identity -/

/-- **Difference of square roots.**  For `0 < x ≤ y`,

`√y - √x = (y - x) / (√y + √x)`.

This is `(√y - √x)(√y + √x) = (√y)² - (√x)² = y - x` divided by the positive
denominator `√y + √x`.  It is the identity that converts a difference of
`√(log ·)` values into a quotient of logarithms. -/
theorem sqrt_sub_sqrt_eq_div {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    Real.sqrt y - Real.sqrt x = (y - x) / (Real.sqrt y + Real.sqrt x) := by
  have hyle : 0 ≤ y := le_trans hx.le hxy
  have hxle : 0 ≤ x := hx.le
  have hdenpos : 0 < Real.sqrt y + Real.sqrt x := by
    have h1 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
    have h2 : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
    linarith
  rw [eq_div_iff (ne_of_gt hdenpos)]
  rw [mul_comm (Real.sqrt y - Real.sqrt x) (Real.sqrt y + Real.sqrt x),
    ← sq_sub_sq, Real.sq_sqrt hyle, Real.sq_sqrt hxle]

/-- Ground-truth check of `sqrt_sub_sqrt_eq_div` at `(x, y) = (1, 4)`, where
both sides equal `1`. -/
example : Real.sqrt 4 - Real.sqrt 1 = (4 - 1) / (Real.sqrt 4 + Real.sqrt 1) :=
  sqrt_sub_sqrt_eq_div (x := 1) (y := 4) (by norm_num) (by norm_num)

/-! ## Two vanishing limits of elementary normalizing factors -/

/-- The constant over the critical scale `√(log N)` tends to `0`.  This is
`Tendsto.div_atTop` applied to the constant function and to
`√(log N) → atTop`. -/
theorem tendsto_const_div_sqrt_log_zero (c : ℝ) :
    Tendsto (fun N : ℕ => c / Real.sqrt (Real.log (N : ℝ))) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsqrt : Tendsto (fun N : ℕ => Real.sqrt (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hlog
  exact Tendsto.div_atTop tendsto_const_nhds hsqrt

/-- The constant over `log (q * N)` tends to `0`, for every fixed `q ≥ 1`.  Since
`N ↦ q * N → atTop`, so does `N ↦ log (q * N)`, and `Tendsto.div_atTop` gives the
claim. -/
theorem tendsto_const_div_log_mul_zero (c : ℝ) {q : ℕ} (hq : 1 ≤ q) :
    Tendsto (fun N : ℕ => c / Real.log (((q * N : ℕ)) : ℝ)) atTop (𝓝 0) := by
  have hqN_atTop : Tendsto (fun N : ℕ => q * N) atTop atTop :=
    Filter.tendsto_atTop_mono (fun N => Nat.le_mul_of_pos_left N (show 0 < q by omega))
      tendsto_id
  have hcast : Tendsto (fun N : ℕ => (((q * N : ℕ)) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hqN_atTop
  have hlog : Tendsto (fun N : ℕ => Real.log (((q * N : ℕ)) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hcast
  exact Tendsto.div_atTop tendsto_const_nhds hlog

/-! ## Vanishing of the normalized log-deficit increment -/

/-- **The log-deficit increment at fixed dilation is `o(√(log N))`.**  For every
fixed `q ≥ 1`,

`Tendsto (fun N => (λ(q·N) - λ(N)) / √(log N)) atTop (𝓝 0)`.

The squeeze is `0 ≤ (λ(q·N) - λ(N))/√(log N) ≤ log q/√(log N)` eventually
(`N ≥ 1`), the lower bound being the subadditivity half and the upper bound the
monotonicity half of `rothLogDeficit_mul_sub_mem`; the right-hand side vanishes
by `tendsto_const_div_sqrt_log_zero`.  No sign claim beyond nonnegativity of the
increment is made. -/
theorem tendsto_rothLogDeficit_mul_sub_div_sqrt_zero {q : ℕ} (hq : 1 ≤ q) :
    Tendsto (fun N : ℕ =>
        (rothLogDeficit (q * N) - rothLogDeficit N) / Real.sqrt (Real.log (N : ℝ)))
      atTop (𝓝 0) := by
  refine squeeze_zero' (f := fun N : ℕ =>
      (rothLogDeficit (q * N) - rothLogDeficit N) / Real.sqrt (Real.log (N : ℝ)))
    (g := fun N : ℕ => Real.log (q : ℝ) / Real.sqrt (Real.log (N : ℝ))) ?_ ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with N hN
    exact div_nonneg (rothLogDeficit_mul_sub_mem (N := N) (q := q) hN hq).1
      (Real.sqrt_nonneg _)
  · filter_upwards [eventually_ge_atTop 1] with N hN
    exact div_le_div_of_nonneg_right (rothLogDeficit_mul_sub_mem (N := N) (q := q) hN hq).2
      (Real.sqrt_nonneg _)
  · exact tendsto_const_div_sqrt_log_zero (Real.log (q : ℝ))

/-- Commuting form of `tendsto_rothLogDeficit_mul_sub_div_sqrt_zero`: the same
vanishing with the dilation written as `N * q`. -/
theorem tendsto_rothLogDeficit_mul_sub_div_sqrt_zero_comm {q : ℕ} (hq : 1 ≤ q) :
    Tendsto (fun N : ℕ =>
        (rothLogDeficit (N * q) - rothLogDeficit N) / Real.sqrt (Real.log (N : ℝ)))
      atTop (𝓝 0) := by
  simpa only [Nat.mul_comm q] using tendsto_rothLogDeficit_mul_sub_div_sqrt_zero (q := q) hq

/-! ## Fixed-dilation regularity of the normalized deficit -/

/-- **Fixed-dilation regularity of the normalized deficit.**  For every fixed
`q ≥ 1`,

`Tendsto (fun N => D(q * N) - D(N)) atTop (𝓝 0)`,

where `D(N) = normalizedDeficit r₃ N = λ(N)/√(log N)`.

The proof is a two-sided squeeze for `N ≥ 2`.  With `s = √(log N)`,
`s' = √(log (q·N))`, `a = λ(N)`, `b = λ(q·N)` and `L = log q ≥ 0`, the accepted
envelope at `δ = 1` gives `a ≤ (torusLeadingConstant + 1)·s` eventually, while
`a ≤ b ≤ a + L` and `s ≤ s'` hold pointwise.  The identity
`sqrt_sub_sqrt_eq_div` gives `s' - s = L/(s' + s)`, so

`D(q·N) - D(N) ≥ -(torusLeadingConstant + 1) · L / log(q·N)`  and
`D(q·N) - D(N) ≤ L / s`,

both eventually and both tending to `0` by
`tendsto_const_div_log_mul_zero` and `tendsto_const_div_sqrt_log_zero`.

No sign is asserted for `D(q·N) - D(N)`: the two bounds are genuinely two-sided.
The `q = 1` case is included and gives the identically zero increment.  This is a
regularity statement at bounded fixed multiplicative scales; it does **not** give
convergence of `D`, and it does **not** resolve Erdős Problem #142. -/
theorem tendsto_normalizedDeficit_rothNumberNat_mul_sub {q : ℕ} (hq : 1 ≤ q) :
    Tendsto (fun N : ℕ =>
      normalizedDeficit rothNumberNat (q * N) -
        normalizedDeficit rothNumberNat N) atTop (𝓝 0) := by
  have hg : Tendsto (fun N : ℕ =>
      -((torusLeadingConstant + 1) *
        (Real.log (q : ℝ) / Real.log (((q * N : ℕ)) : ℝ)))) atTop (𝓝 0) := by
    have h := (tendsto_const_div_log_mul_zero (Real.log (q : ℝ)) hq).const_mul
      (torusLeadingConstant + 1)
    simpa using h.neg
  have hh : Tendsto (fun N : ℕ => Real.log (q : ℝ) / Real.sqrt (Real.log (N : ℝ)))
      atTop (𝓝 0) := tendsto_const_div_sqrt_log_zero (Real.log (q : ℝ))
  have hbdd : ∀ᶠ N : ℕ in atTop,
      -((torusLeadingConstant + 1) *
          (Real.log (q : ℝ) / Real.log (((q * N : ℕ)) : ℝ))) ≤
        normalizedDeficit rothNumberNat (q * N) - normalizedDeficit rothNumberNat N ∧
      normalizedDeficit rothNumberNat (q * N) - normalizedDeficit rothNumberNat N ≤
        Real.log (q : ℝ) / Real.sqrt (Real.log (N : ℝ)) := by
    filter_upwards [eventually_ge_atTop 2,
      eventually_rothLogDeficit_le_mul_sqrt_log 1 (by norm_num)] with N hN2 henv
    have hN1 : 1 ≤ N := by omega
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
    have hq1' : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have hlogNpos : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hqN1 : 1 ≤ q * N := le_trans hN1 (Nat.le_mul_of_pos_left N (show 0 < q by omega))
    have hqN2 : 2 ≤ q * N := le_trans hN2 (Nat.le_mul_of_pos_left N (show 0 < q by omega))
    have hlogqNpos : 0 < Real.log (((q * N : ℕ)) : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < q * N by omega))
    have hlogmul : Real.log (((q * N : ℕ)) : ℝ) = Real.log (q : ℝ) + Real.log (N : ℝ) := by
      rw [Nat.cast_mul, Real.log_mul (ne_of_gt hqpos) (ne_of_gt hNpos)]
    have hle : Real.log (N : ℝ) ≤ Real.log (((q * N : ℕ)) : ℝ) := by
      rw [hlogmul]
      linarith [Real.log_nonneg hq1']
    have Lnonneg : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hq1'
    have Cnonneg : 0 ≤ torusLeadingConstant + 1 := by linarith [torusLeadingConstant_pos]
    have hincl := rothLogDeficit_mul_sub_mem (N := N) (q := q) hN1 hq
    have hbnonneg : 0 ≤ rothLogDeficit (q * N) := rothLogDeficit_nonneg hqN1
    have hsub_id :
        Real.sqrt (Real.log (((q * N : ℕ)) : ℝ)) - Real.sqrt (Real.log (N : ℝ)) =
          Real.log (q : ℝ) /
            (Real.sqrt (Real.log (((q * N : ℕ)) : ℝ)) + Real.sqrt (Real.log (N : ℝ))) := by
      have h := sqrt_sub_sqrt_eq_div hlogNpos hle
      have hyx : Real.log (((q * N : ℕ)) : ℝ) - Real.log (N : ℝ) = Real.log (q : ℝ) := by
        rw [hlogmul]; ring
      rwa [hyx] at h
    rw [normalizedDeficit_rothNumberNat_eq, normalizedDeficit_rothNumberNat_eq]
    set s : ℝ := Real.sqrt (Real.log (N : ℝ)) with hs
    set s' : ℝ := Real.sqrt (Real.log (((q * N : ℕ)) : ℝ)) with hs'
    have hspos : 0 < s := by rw [hs]; exact Real.sqrt_pos.mpr hlogNpos
    have hs'pos : 0 < s' := by rw [hs']; exact Real.sqrt_pos.mpr hlogqNpos
    have hss : s ≤ s' := by rw [hs, hs']; exact Real.sqrt_le_sqrt hle
    have hD : Real.log (((q * N : ℕ)) : ℝ) = s' ^ 2 := by
      rw [hs']; exact (Real.sq_sqrt hlogqNpos.le).symm
    have hsubs : s' - s = Real.log (q : ℝ) / (s' + s) := by
      rw [hs, hs']; exact hsub_id
    constructor
    · have haC' : rothLogDeficit N / s ≤ torusLeadingConstant + 1 :=
        (div_le_iff₀ hspos).mpr (by rw [hs]; exact henv)
      have hratio : (s' - s) / s' ≤ Real.log (q : ℝ) / Real.log (((q * N : ℕ)) : ℝ) := by
        rw [hsubs, div_div, hD]
        apply div_le_div_of_nonneg_left Lnonneg (by positivity)
        nlinarith [hspos, hs'pos, hss]
      have hstep : -((torusLeadingConstant + 1) *
            (Real.log (q : ℝ) / Real.log (((q * N : ℕ)) : ℝ))) ≤
          rothLogDeficit N / s' - rothLogDeficit N / s := by
        have heq1 : rothLogDeficit N / s' - rothLogDeficit N / s =
            -((rothLogDeficit N / s) * ((s' - s) / s')) := by
          field_simp
          ring
        rw [heq1]
        have hbound : (rothLogDeficit N / s) * ((s' - s) / s') ≤
            (torusLeadingConstant + 1) *
              (Real.log (q : ℝ) / Real.log (((q * N : ℕ)) : ℝ)) :=
          mul_le_mul haC' hratio (div_nonneg (sub_nonneg.mpr hss) hs'pos.le) Cnonneg
        linarith
      have hfirst : rothLogDeficit N / s' - rothLogDeficit N / s ≤
          rothLogDeficit (q * N) / s' - rothLogDeficit N / s :=
        sub_le_sub_right (div_le_div_of_nonneg_right (by linarith [hincl.1]) hs'pos.le) _
      linarith
    · have hbs : rothLogDeficit (q * N) / s' ≤ rothLogDeficit (q * N) / s :=
        div_le_div_of_nonneg_left hbnonneg hspos hss
      calc rothLogDeficit (q * N) / s' - rothLogDeficit N / s
          ≤ rothLogDeficit (q * N) / s - rothLogDeficit N / s := sub_le_sub_right hbs _
        _ = (rothLogDeficit (q * N) - rothLogDeficit N) / s := by rw [sub_div]
        _ ≤ Real.log (q : ℝ) / s := div_le_div_of_nonneg_right hincl.2 hspos.le
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hg hh
    (hbdd.mono fun N h => h.1) (hbdd.mono fun N h => h.2)

/-- Commuting form of `tendsto_normalizedDeficit_rothNumberNat_mul_sub`: the same
regularity statement with the dilation written as `N * q`. -/
theorem tendsto_normalizedDeficit_rothNumberNat_mul_sub_comm {q : ℕ} (hq : 1 ≤ q) :
    Tendsto (fun N : ℕ =>
      normalizedDeficit rothNumberNat (N * q) -
        normalizedDeficit rothNumberNat N) atTop (𝓝 0) := by
  simpa only [Nat.mul_comm q] using tendsto_normalizedDeficit_rothNumberNat_mul_sub (q := q) hq

/-! ## Non-vacuity checks -/

/-- Non-vacuity of the fixed-dilation increment at the nontrivial pair
`(N, q) = (4, 3)`. -/
example : 0 ≤ rothLogDeficit (3 * 4) - rothLogDeficit 4 ∧
    rothLogDeficit (3 * 4) - rothLogDeficit 4 ≤ Real.log (3 : ℝ) :=
  rothLogDeficit_mul_sub_mem (N := 4) (q := 3) (by norm_num) (by norm_num)

/-- The fixed-dilation regularity theorem at `q = 1` is a genuine statement
about the actual normalized deficit: the increment is identically zero. -/
example : Tendsto (fun N : ℕ =>
    normalizedDeficit rothNumberNat (1 * N) - normalizedDeficit rothNumberNat N)
    atTop (𝓝 0) := tendsto_normalizedDeficit_rothNumberNat_mul_sub (q := 1) le_rfl

/-- The conclusion of `tendsto_normalizedDeficit_rothNumberNat_mul_sub` is
satisfiable in the intended trivial case: the identically zero sequence tends to
`0`, so the statement is not vacuous. -/
example : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds

end

end Erdos142

-- Axiom audit for the public declarations of this module.
#print axioms Erdos142.rothLogDeficit_mul_sub_mem
#print axioms Erdos142.rothLogDeficit_le_mul
#print axioms Erdos142.rothLogDeficit_mul_sub_le_log
#print axioms Erdos142.sqrt_sub_sqrt_eq_div
#print axioms Erdos142.tendsto_const_div_sqrt_log_zero
#print axioms Erdos142.tendsto_const_div_log_mul_zero
#print axioms Erdos142.tendsto_rothLogDeficit_mul_sub_div_sqrt_zero
#print axioms Erdos142.tendsto_rothLogDeficit_mul_sub_div_sqrt_zero_comm
#print axioms Erdos142.tendsto_normalizedDeficit_rothNumberNat_mul_sub
#print axioms Erdos142.tendsto_normalizedDeficit_rothNumberNat_mul_sub_comm