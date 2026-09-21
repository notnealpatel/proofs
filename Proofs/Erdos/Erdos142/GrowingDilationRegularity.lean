/-
  Erdős Problem #142 — growing-dilation regularity of the normalized deficit.

  This module continues `FixedDilationRegularity`, which proves the regularity of
  the normalized deficit `D(N) = normalizedDeficit r₃ N = λ(N)/√(log N)` at a
  **fixed** multiplicative dilation `N ↦ q · N` (`q` a fixed natural number):

      `D(q·N) − D(N) → 0`.

  Here the dilation is allowed to **grow with `N`**.  If `q : ℕ → ℕ` is
  eventually positive and the growth is slow compared with the critical scale,

      `log (q N) / √(log N) → 0`   (`log q(N) = o(√(log N))`),

  then the same conclusion holds for the varying dilation `N ↦ q N · N`:

      `D(q N · N) − D(N) → 0`.

  This is the positive square-scale bridge from a fixed radix to every growing
  radix in the class `log q(N) = o(√(log N))`.  The compatible boundary scale is
  a suitably integer-rounded `q` with `log q(N) ~ c √(log N)`: its normalized
  logarithm `log q(N)/√(log N)` tends to `c`, so it satisfies the hypothesis only
  in the borderline case `c = 0` (for instance the constant radix `q ≡ 1`) and
  lies **outside** the theorem for `c ≠ 0`.  The case `q(N) = N` does **not**
  satisfy the hypothesis, and is not covered here.

  **Route.**  The proof reuses the accepted structure of the fixed-q argument,
  but the pointwise input is uniform in `q`, so it applies at the varying value
  `q N`:

  * `rothLogDeficit_mul_sub_mem` (imported): `0 ≤ λ(q·N) − λ(N) ≤ log q`
    for `N ≥ 1`, `q ≥ 1`;
  * the accepted envelope `eventually_rothLogDeficit_le_mul_sqrt_log`, applied
    **at `N`** (not at `q N · N`), giving `λ(N) ≤ (torusLeadingConstant + 1)·√(log N)`
    eventually;
  * the square-root difference identity `sqrt_sub_sqrt_eq_div` (imported), which
    turns `√(log (q N · N)) − √(log N)` into `log (q N)/(√(log (q N·N)) + √(log N))`.

  The only genuinely new analytic input is the crux log-ratio limit

      `log (q N) / log (q N · N) → 0`,

  which follows from `hqc` by the elementary squeeze
  `0 ≤ log (q N)/log (q N · N) ≤ 1/√(log N)` eventually: since `q N ≥ 1` gives
  `log (q N) ≥ 0` and `log (q N · N) ≥ log N > 0`, and `hqc` gives
  `log (q N) ≤ √(log N)` eventually, one has
  `log (q N) · √(log N) ≤ (√(log N))² = log N ≤ log (q N · N)`.

  **Scope.**  As in the fixed-dilation module this is a *regularity* statement: it
  does **not** prove that `D(N)` converges, produces no limit, and does **not**
  resolve Erdős Problem #142.  It says that the radices with
  `log q(N) = o(√(log N))` — a class that grows without bound but stays below the
  critical `√(log N)` scale — cannot carry normalized-deficit oscillation.  It
  makes **no claim at `q(N) = N`** or at any radix outside that class.

  Nothing here edits an existing declaration; no `sorry`, no `unsafe` and no new
  axiom is used, and the axiom audit is at the end of the file.
-/

import Erdos.Erdos142.FixedDilationRegularity

set_option autoImplicit false

open Filter
open scoped Topology

namespace Erdos142

noncomputable section

/-! ## The crux log-ratio limit -/

/-- **Crux log-ratio limit.**  If `q` is eventually positive and
`log (q N) / √(log N) → 0`, then

`log (q N) / log (q N · N) → 0`.

The squeeze is `0 ≤ log (q N)/log (q N · N) ≤ 1/√(log N)` eventually.  For
`N ≥ 2` and `q N ≥ 1` one has `log (q N) ≥ 0` and
`log (q N · N) = log (q N) + log N ≥ log N > 0`; writing `hqc` as
`log (q N) ≤ √(log N)` eventually and multiplying by `√(log N) ≥ 0` gives
`log (q N)·√(log N) ≤ log N ≤ log (q N · N)`, which is the upper bound after
cross-multiplication.  The comparison `1/√(log N) → 0` is
`tendsto_const_div_sqrt_log_zero` from the fixed-dilation module. -/
theorem tendsto_log_div_log_mul_zero (q : ℕ → ℕ)
    (hq : ∀ᶠ N in atTop, 1 ≤ q N)
    (hqc : Tendsto (fun N : ℕ => Real.log (q N : ℝ) /
      Real.sqrt (Real.log (N : ℝ))) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => Real.log (q N : ℝ) /
      Real.log ((q N * N : ℕ) : ℝ)) atTop (𝓝 0) := by
  have hsmall : ∀ᶠ N : ℕ in atTop,
      Real.log (q N : ℝ) / Real.sqrt (Real.log (N : ℝ)) ≤ 1 :=
    hqc.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
  refine squeeze_zero'
    (f := fun N : ℕ => Real.log (q N : ℝ) / Real.log ((q N * N : ℕ) : ℝ))
    (g := fun N : ℕ => 1 / Real.sqrt (Real.log (N : ℝ))) ?_ ?_ ?_
  · filter_upwards [hq, eventually_ge_atTop 2] with N hqN hN2
    have hqpos : (0 : ℝ) < (q N : ℝ) := by exact_mod_cast (show 0 < q N by omega)
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hlogNpos : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hlogmul : Real.log (((q N * N : ℕ)) : ℝ) =
        Real.log (q N : ℝ) + Real.log (N : ℝ) := by
      rw [Nat.cast_mul, Real.log_mul (ne_of_gt hqpos) (ne_of_gt hNpos)]
    have hlogqNpos : 0 < Real.log (((q N * N : ℕ)) : ℝ) := by
      rw [hlogmul]
      have h1 : 0 ≤ Real.log (q N : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hqN : (1 : ℝ) ≤ (q N : ℝ))
      linarith
    exact div_nonneg
      (Real.log_nonneg (by exact_mod_cast hqN : (1 : ℝ) ≤ (q N : ℝ)))
      hlogqNpos.le
  · filter_upwards [hq, hsmall, eventually_ge_atTop 2] with N hqN hsmallN hN2
    have hqpos : (0 : ℝ) < (q N : ℝ) := by exact_mod_cast (show 0 < q N by omega)
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hlogNpos : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hspos : 0 < Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_pos.mpr hlogNpos
    have hlogq_le : Real.log (q N : ℝ) ≤ Real.sqrt (Real.log (N : ℝ)) := by
      have h := (div_le_iff₀ hspos).mp hsmallN
      linarith
    have hlogmul : Real.log (((q N * N : ℕ)) : ℝ) =
        Real.log (q N : ℝ) + Real.log (N : ℝ) := by
      rw [Nat.cast_mul, Real.log_mul (ne_of_gt hqpos) (ne_of_gt hNpos)]
    have hle : Real.log (N : ℝ) ≤ Real.log (((q N * N : ℕ)) : ℝ) := by
      rw [hlogmul]
      have h1 : 0 ≤ Real.log (q N : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hqN : (1 : ℝ) ≤ (q N : ℝ))
      linarith
    have hden : 0 < Real.log (((q N * N : ℕ)) : ℝ) := lt_of_lt_of_le hlogNpos hle
    rw [div_le_div_iff₀ hden hspos]
    have hcross : Real.log (q N : ℝ) * Real.sqrt (Real.log (N : ℝ)) ≤
        Real.log (((q N * N : ℕ)) : ℝ) := by
      have h1 : Real.log (q N : ℝ) * Real.sqrt (Real.log (N : ℝ)) ≤
          Real.sqrt (Real.log (N : ℝ)) * Real.sqrt (Real.log (N : ℝ)) :=
        mul_le_mul_of_nonneg_right hlogq_le (Real.sqrt_nonneg _)
      rw [Real.mul_self_sqrt hlogNpos.le] at h1
      linarith
    linarith
  · exact tendsto_const_div_sqrt_log_zero 1

/-! ## The eventual two-sided bound at a growing dilation -/

/-- **Eventual two-sided bound for the growing dilation.**  For every eventually
positive `q : ℕ → ℕ` (no growth hypothesis needed),

`-((torusLeadingConstant + 1) · log (q N)/log (q N · N)) ≤ D(q N · N) − D(N) ≤ log (q N)/√(log N)`

eventually.

This is the fixed-q two-sided bound `tendsto_normalizedDeficit_rothNumberNat_mul_sub`
with the *uniform* pointwise increment `rothLogDeficit_mul_sub_mem` evaluated at
`(N, q N)`, and with the accepted envelope applied **at `N`** (not at `q N · N`).
No sign is asserted for the increment itself.  The lower comparison is the log
ratio `log (q N)/log (q N · N)`; the upper comparison is `log (q N)/√(log N)`.
Both are exactly the factors that vanish under the growth hypothesis of
`tendsto_normalizedDeficit_rothNumberNat_growing_mul_sub`. -/
theorem eventually_normalizedDeficit_growing_mul_sub_bounds
    (q : ℕ → ℕ) (hq : ∀ᶠ N in atTop, 1 ≤ q N) :
    ∀ᶠ N : ℕ in atTop,
      -((torusLeadingConstant + 1) *
          (Real.log (q N : ℝ) / Real.log ((q N * N : ℕ) : ℝ))) ≤
        normalizedDeficit rothNumberNat (q N * N) - normalizedDeficit rothNumberNat N ∧
      normalizedDeficit rothNumberNat (q N * N) - normalizedDeficit rothNumberNat N ≤
        Real.log (q N : ℝ) / Real.sqrt (Real.log (N : ℝ)) := by
  filter_upwards [hq, eventually_ge_atTop 2,
    eventually_rothLogDeficit_le_mul_sqrt_log 1 (by norm_num)] with N hqN hN2 henv
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hqpos : (0 : ℝ) < (q N : ℝ) := by exact_mod_cast (show 0 < q N by omega)
  have hq1' : (1 : ℝ) ≤ (q N : ℝ) := by exact_mod_cast hqN
  have hlogNpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hqN1 : 1 ≤ q N * N :=
    le_trans hN1 (Nat.le_mul_of_pos_left N (show 0 < q N by omega))
  have hqN2 : 2 ≤ q N * N :=
    le_trans hN2 (Nat.le_mul_of_pos_left N (show 0 < q N by omega))
  have hlogqNpos : 0 < Real.log (((q N * N : ℕ)) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < q N * N by omega))
  have hlogmul : Real.log (((q N * N : ℕ)) : ℝ) =
      Real.log (q N : ℝ) + Real.log (N : ℝ) := by
    rw [Nat.cast_mul, Real.log_mul (ne_of_gt hqpos) (ne_of_gt hNpos)]
  have hle : Real.log (N : ℝ) ≤ Real.log (((q N * N : ℕ)) : ℝ) := by
    rw [hlogmul]
    linarith [Real.log_nonneg hq1']
  have Lnonneg : 0 ≤ Real.log (q N : ℝ) := Real.log_nonneg hq1'
  have Cnonneg : 0 ≤ torusLeadingConstant + 1 := by linarith [torusLeadingConstant_pos]
  have hincl := rothLogDeficit_mul_sub_mem (N := N) (q := q N) hN1 hqN
  have hbnonneg : 0 ≤ rothLogDeficit (q N * N) := rothLogDeficit_nonneg hqN1
  have hsub_id :
      Real.sqrt (Real.log (((q N * N : ℕ)) : ℝ)) - Real.sqrt (Real.log (N : ℝ)) =
        Real.log (q N : ℝ) /
          (Real.sqrt (Real.log (((q N * N : ℕ)) : ℝ)) + Real.sqrt (Real.log (N : ℝ))) := by
    have h := sqrt_sub_sqrt_eq_div hlogNpos hle
    have hyx : Real.log (((q N * N : ℕ)) : ℝ) - Real.log (N : ℝ) = Real.log (q N : ℝ) := by
      rw [hlogmul]; ring
    rwa [hyx] at h
  rw [normalizedDeficit_rothNumberNat_eq, normalizedDeficit_rothNumberNat_eq]
  set s : ℝ := Real.sqrt (Real.log (N : ℝ)) with hs
  set s' : ℝ := Real.sqrt (Real.log (((q N * N : ℕ)) : ℝ)) with hs'
  have hspos : 0 < s := by rw [hs]; exact Real.sqrt_pos.mpr hlogNpos
  have hs'pos : 0 < s' := by rw [hs']; exact Real.sqrt_pos.mpr hlogqNpos
  have hss : s ≤ s' := by rw [hs, hs']; exact Real.sqrt_le_sqrt hle
  have hD : Real.log (((q N * N : ℕ)) : ℝ) = s' ^ 2 := by
    rw [hs']; exact (Real.sq_sqrt hlogqNpos.le).symm
  have hsubs : s' - s = Real.log (q N : ℝ) / (s' + s) := by
    rw [hs, hs']; exact hsub_id
  constructor
  · have haC' : rothLogDeficit N / s ≤ torusLeadingConstant + 1 :=
      (div_le_iff₀ hspos).mpr (by rw [hs]; exact henv)
    have hratio : (s' - s) / s' ≤
        Real.log (q N : ℝ) / Real.log (((q N * N : ℕ)) : ℝ) := by
      rw [hsubs, div_div, hD]
      apply div_le_div_of_nonneg_left Lnonneg (by positivity)
      nlinarith [hspos, hs'pos, hss]
    have hstep : -((torusLeadingConstant + 1) *
          (Real.log (q N : ℝ) / Real.log (((q N * N : ℕ)) : ℝ))) ≤
        rothLogDeficit N / s' - rothLogDeficit N / s := by
      have heq1 : rothLogDeficit N / s' - rothLogDeficit N / s =
          -((rothLogDeficit N / s) * ((s' - s) / s')) := by
        field_simp
        ring
      rw [heq1]
      have hbound : (rothLogDeficit N / s) * ((s' - s) / s') ≤
          (torusLeadingConstant + 1) *
            (Real.log (q N : ℝ) / Real.log (((q N * N : ℕ)) : ℝ)) :=
        mul_le_mul haC' hratio (div_nonneg (sub_nonneg.mpr hss) hs'pos.le) Cnonneg
      linarith
    have hfirst : rothLogDeficit N / s' - rothLogDeficit N / s ≤
        rothLogDeficit (q N * N) / s' - rothLogDeficit N / s :=
      sub_le_sub_right (div_le_div_of_nonneg_right (by linarith [hincl.1]) hs'pos.le) _
    linarith
  · have hbs : rothLogDeficit (q N * N) / s' ≤ rothLogDeficit (q N * N) / s :=
      div_le_div_of_nonneg_left hbnonneg hspos hss
    calc rothLogDeficit (q N * N) / s' - rothLogDeficit N / s
        ≤ rothLogDeficit (q N * N) / s - rothLogDeficit N / s := sub_le_sub_right hbs _
      _ = (rothLogDeficit (q N * N) - rothLogDeficit N) / s := by rw [sub_div]
      _ ≤ Real.log (q N : ℝ) / s := div_le_div_of_nonneg_right hincl.2 hspos.le

/-! ## Growing-dilation regularity of the normalized deficit -/

/-- **Growing-dilation regularity of the normalized deficit.**  Let `q : ℕ → ℕ`
be eventually positive with `log (q N) / √(log N) → 0`.  Then

`Tendsto (fun N => D(q N · N) − D(N)) atTop (𝓝 0)`,

where `D(N) = normalizedDeficit r₃ N = λ(N)/√(log N)`.

This is the two-sided squeeze of
`eventually_normalizedDeficit_growing_mul_sub_bounds`: the lower comparison
`-((torusLeadingConstant + 1) · log (q N)/log (q N · N))` vanishes by the crux
limit `tendsto_log_div_log_mul_zero`, and the upper comparison
`log (q N)/√(log N)` vanishes by the hypothesis `hqc` itself.

The class `log q(N) = o(√(log N))` is genuinely unbounded: a suitably
integer-rounded boundary scale with `log q(N) ~ c √(log N)` has normalized
logarithm `log q(N)/√(log N)` tending to `c`, so it satisfies the hypothesis only
for `c = 0` (the constant radix `q ≡ 1` is the compatible instance) and lies
**outside** the theorem for `c ≠ 0`.  The theorem says nothing at `q(N) = N`
(where `log q(N)/√(log N) → ∞`) and nothing about the critical `√(log N)`-scale
radices: it does **not** prove that `D` converges, does **not** produce a limit,
and does **not** resolve Erdős Problem #142. -/
theorem tendsto_normalizedDeficit_rothNumberNat_growing_mul_sub
    (q : ℕ → ℕ) (hq : ∀ᶠ N in atTop, 1 ≤ q N)
    (hqc : Tendsto (fun N : ℕ => Real.log (q N : ℝ) /
      Real.sqrt (Real.log (N : ℝ))) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ =>
      normalizedDeficit rothNumberNat (q N * N) -
        normalizedDeficit rothNumberNat N) atTop (𝓝 0) := by
  have hg : Tendsto (fun N : ℕ =>
      -((torusLeadingConstant + 1) *
        (Real.log (q N : ℝ) / Real.log ((q N * N : ℕ) : ℝ)))) atTop (𝓝 0) := by
    have h := (tendsto_log_div_log_mul_zero q hq hqc).const_mul
      (torusLeadingConstant + 1)
    simpa using h.neg
  have hbdd := eventually_normalizedDeficit_growing_mul_sub_bounds q hq
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hg hqc
    (hbdd.mono fun N h => h.1) (hbdd.mono fun N h => h.2)

/-- Commuting form of `tendsto_normalizedDeficit_rothNumberNat_growing_mul_sub`:
the same regularity statement with the dilation written as `N * q N`. -/
theorem tendsto_normalizedDeficit_rothNumberNat_growing_mul_sub_comm
    (q : ℕ → ℕ) (hq : ∀ᶠ N in atTop, 1 ≤ q N)
    (hqc : Tendsto (fun N : ℕ => Real.log (q N : ℝ) /
      Real.sqrt (Real.log (N : ℝ))) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ =>
      normalizedDeficit rothNumberNat (N * q N) -
        normalizedDeficit rothNumberNat N) atTop (𝓝 0) :=
  (tendsto_normalizedDeficit_rothNumberNat_growing_mul_sub q hq hqc).congr'
    (Eventually.of_forall fun N => by rw [Nat.mul_comm (q N)])

/-! ## Non-vacuity and consistency checks -/

/-- The growth hypothesis is satisfiable: the constant radix `q ≡ 1` is the
`c = 0` compatible case of the boundary scale, and here
`log (q N)/√(log N) = 0` for every `N`.  Here we record the concrete instance
`q ≡ 1`.

(A suitably integer-rounded boundary scale with `log q(N) ~ c √(log N)` has
`log (q N)/√(log N) → c`, so it satisfies the hypothesis only at `c = 0` and lies
outside the theorem for `c ≠ 0`.) -/
example : Tendsto (fun N : ℕ => Real.log (((fun _ : ℕ => 1) N : ℕ) : ℝ) /
    Real.sqrt (Real.log (N : ℝ))) atTop (𝓝 0) := by
  have h : (fun N : ℕ => Real.log (((fun _ : ℕ => 1) N : ℕ) : ℝ) /
      Real.sqrt (Real.log (N : ℝ))) = fun _ : ℕ => (0 : ℝ) := by
    funext N
    norm_num
  rw [h]
  exact tendsto_const_nhds

/-- The crux log-ratio limit at the constant radix `q ≡ 2`, obtained from the
theorem rather than by direct computation. -/
example : Tendsto (fun N : ℕ => Real.log (((fun _ : ℕ => 2) N : ℕ) : ℝ) /
    Real.log (((fun _ : ℕ => 2) N * N : ℕ) : ℝ)) atTop (𝓝 0) :=
  tendsto_log_div_log_mul_zero (fun _ => 2)
    (Eventually.of_forall fun _ => by norm_num)
    (by simpa using tendsto_const_div_sqrt_log_zero (Real.log (2 : ℝ)))

/-- Consistency with the accepted fixed-dilation theorem: for the constant radix
`q ≡ 2` the growing-dilation theorem specialises to a genuine statement about
`D(2·N) − D(N)`, reproducing the fixed-dilation conclusion.  This witnesses that
the growth hypothesis is satisfiable and that the new theorem is not vacuous. -/
example : Tendsto (fun N : ℕ =>
    normalizedDeficit rothNumberNat ((fun _ : ℕ => 2) N * N) -
      normalizedDeficit rothNumberNat N) atTop (𝓝 0) :=
  tendsto_normalizedDeficit_rothNumberNat_growing_mul_sub (fun _ => 2)
    (Eventually.of_forall fun _ => by norm_num)
    (by simpa using tendsto_const_div_sqrt_log_zero (Real.log (2 : ℝ)))

end

end Erdos142

-- Axiom audit for the public declarations of this module.
#print axioms Erdos142.tendsto_log_div_log_mul_zero
#print axioms Erdos142.eventually_normalizedDeficit_growing_mul_sub_bounds
#print axioms Erdos142.tendsto_normalizedDeficit_rothNumberNat_growing_mul_sub
#print axioms Erdos142.tendsto_normalizedDeficit_rothNumberNat_growing_mul_sub_comm
