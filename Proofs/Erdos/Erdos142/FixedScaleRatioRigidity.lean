/-
  Erdős Problem #142 — rigidity of a finite fixed-integer-scale ratio limit
  for the Roth numbers, at every integer scale `q ≥ 2`.

  The Roth number `rothNumberNat N` is the largest cardinality of a
  three-term-progression-free subset of `{0, …, N - 1}`.  For an integer scale
  `q ≥ 2` the *fixed-scale dilation ratio* is

      `N ↦ (rothNumberNat (N * q) : ℝ) / (rothNumberNat N : ℝ)`,

  the ratio of the Roth number at `N * q` to the Roth number at `N`.

  This file shows that any *finite* limit `c` of that ratio is forced to the
  single value `q`:

      `Tendsto (fun N => (rothNumberNat (N * q) : ℝ) / (rothNumberNat N : ℝ))
        atTop (𝓝 c)  →  c = q`.

  This strictly extends the accepted odd-scale classifier
  `eq_odd_scale_of_tendsto_rothNumberNat_ratio` from the odd scales
  `2 * M - 1` to *every* integer scale `q ≥ 2`, in particular to the even
  scales that the odd-scale statement cannot reach.

  The proof is unconditional and uses only the accepted logarithmic-exponent
  limit `tendsto_log_rothNumberNat_div_log_one` (`log r₃(N) / log N → 1`) plus
  monotonicity of `rothNumberNat`.  It proceeds along the geometric
  subsequence `N = q ^ k`, writing `b k = log (rothNumberNat (q ^ k) : ℝ)`:

  * `b` is monotone nondecreasing, so `b (k + 1) - b k ≥ 0`; equivalently the
    scale ratio is at least `1` because `N ≤ N * q` for `q ≥ 1` and the
    denominator `rothNumberNat N` is positive for `N ≥ 1`.

  * Composing the hypothesized ratio limit with the geometric subsequence
    `k ↦ q ^ k` (which tends to `atTop` by
    `tendsto_pow_atTop_atTop_of_one_lt`) and applying continuity of `Real.log`
    at the positive limit `c` gives, via `Real.log_div`,
    `b (k + 1) - b k → log c`.

  * Cesàro's lemma (`Filter.Tendsto.cesaro`) together with the telescoping
    identity `Finset.sum_range_sub` then gives `(b k - b 0) / k → log c`; the
    term `b 0 / k` tends to `0`, hence `b k / k → log c`.

  * Independently, composing `tendsto_log_rothNumberNat_div_log_one` with
    `k ↦ q ^ k` gives `b k / log (q ^ k) → 1`.  Since `log (q ^ k) = k log q`
    for `k ≥ 1`, the exact factorization
    `b k / k = (b k / log (q ^ k)) * (log (q ^ k) / k)` on the tail `k ≥ 1`
    yields `b k / k → log q`.

  * Uniqueness of limits gives `log c = log q`, and `Real.log_injOn_pos`
    together with `c > 0`, `q > 0` gives `c = q`.

  The scale `q = 1` is excluded by `q ≥ 2`; the value `c = 0` is ruled out by
  the monotone lower bound `c ≥ 1`; the vanishing denominator at `N = 0` is
  handled on the eventual tail `N ≥ 1`.

  The companion theorem `eq_scale_of_asymptotic_comparison` transfers the
  conclusion to an arbitrary real comparison function `f` with
  `rothNumberNat N / f N → 1`: if `f (N * q) / f N → c` then `c = q`.
  Positivity of `f` is *derived* from the ratio asymptotic, never assumed.
  `not_exists_asymptotic_comparison_of_ne_scale` and
  `not_tendsto_rothNumberNat_mul_ratio_of_ne_scale` are the corresponding
  nonexistence corollaries for `c ≠ q`.

  What this does and does not say.  This is an unconditional *necessary
  condition* for the existence of a finite fixed-scale ratio limit: when such a
  limit exists, its value is pinned to `q`.  Because the logarithmic exponent of
  `r₃` is `1`, the standard regular-variation route through an index `α ≠ 1`
  was already excluded; the present statement is therefore best read as a
  broader fixed-dilation necessary condition applying to *arbitrary* candidate
  comparison functions, not as a new upper or lower bound on `r₃`.  It does not
  prove that the ratio converges, does not prove `r₃(N)/N → 0` by any new
  route, does not establish the square estimate, does not exclude oscillation,
  and does not supply an asymptotic formula for `r₃`.  The convergence
  antecedent of these classifiers remains open.  In particular the theorem does
  not resolve Erdős #142.

  A note on satisfiability.  The convergence of the scale ratio is exactly the
  open content, so no witness for the dilation-ratio hypothesis is constructed.
  What is checked below is that (i) the comparison hypothesis
  `rothNumberNat N / f N → 1` is satisfiable, with the concrete choice
  `f = rothNumberNat`, and (ii) the excluded value `c = 0` is genuinely
  excluded at `q = 2`, so the nonexistence corollary is non-vacuous.

  No `sorry`, no `unsafe`, no `axiom`, no `native_decide`, and no existing
  declaration is edited.
-/

import Erdos.Erdos142.PowerLawObstruction
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

set_option autoImplicit false

open Filter
open scoped Topology

namespace Erdos142

noncomputable section

/-- **Rigidity of a finite fixed-integer-scale ratio limit.**  For fixed
`q ≥ 2`, if the fixed-scale dilation ratio
`(rothNumberNat (N * q) : ℝ) / (rothNumberNat N : ℝ)` converges to a finite real
`c`, then necessarily `c = (q : ℝ)`.

Route: monotonicity gives eventual ratio `≥ 1`, hence `c ≥ 1 > 0`, so `log` is
continuous at `c`.  Along the geometric subsequence `N = q ^ k`, writing
`b k = log (rothNumberNat (q ^ k) : ℝ)`, the composed ratio limit together with
`Real.log_div` gives `b (k + 1) - b k → log c`; Cesàro
(`Filter.Tendsto.cesaro`) plus the telescoping identity
(`Finset.sum_range_sub`) gives `b k / k → log c`.  Independently, composing
`tendsto_log_rothNumberNat_div_log_one` with `q ^ k` gives
`b k / log (q ^ k) → 1`, and `log (q ^ k) = k log q` on `k ≥ 1` turns the exact
factorization `b k / k = (b k / log (q ^ k)) * (log (q ^ k) / k)` into
`b k / k → log q`.  Uniqueness of limits gives `log c = log q`, and
`Real.log_injOn_pos` with `c > 0`, `q > 0` gives `c = q`.  The theorem
classifies every finite limit; it does not prove that a limit exists. -/
theorem eq_scale_of_tendsto_rothNumberNat_mul_ratio {q : ℕ} (hq : 2 ≤ q) {c : ℝ}
    (h : Tendsto (fun N : ℕ =>
      (rothNumberNat (N * q) : ℝ) / (rothNumberNat N : ℝ)) atTop (𝓝 c)) :
    c = (q : ℝ) := by
  have hq1 : 1 ≤ q := by omega
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hqne : (q : ℝ) ≠ 1 := by exact_mod_cast (by omega : q ≠ 1)
  have hlogq_ne : Real.log (q : ℝ) ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hqpos hqne
  -- Every power of `q` is at least `1`, so the Roth numbers there are positive.
  have hone : ∀ k : ℕ, 1 ≤ q ^ k :=
    fun k => Nat.one_le_iff_ne_zero.mpr (pow_ne_zero k (by omega))
  -- Positivity of the limit, from the monotone lower bound `ratio ≥ 1`.
  have hcpos : 0 < c := by
    have hev : ∀ᶠ N : ℕ in atTop,
        (1 : ℝ) ≤ (rothNumberNat (N * q) : ℝ) / (rothNumberNat N : ℝ) := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      have hNpos : 0 < (rothNumberNat N : ℝ) := rothNumberNat_pos_real hN
      rw [le_div_iff₀ hNpos]
      have hle : rothNumberNat N ≤ rothNumberNat (N * q) := by
        refine rothNumberNat.monotone ?_
        calc N = N * 1 := (Nat.mul_one N).symm
          _ ≤ N * q := Nat.mul_le_mul_left N hq1
      calc (1 : ℝ) * (rothNumberNat N : ℝ) = (rothNumberNat N : ℝ) := one_mul _
        _ ≤ (rothNumberNat (N * q) : ℝ) := by exact_mod_cast hle
    have h1c : (1 : ℝ) ≤ c := le_of_tendsto_of_tendsto tendsto_const_nhds h hev
    linarith
  have hcne : c ≠ 0 := ne_of_gt hcpos
  -- The geometric subsequence `N = q ^ k` tends to `atTop`.
  have hpow : Tendsto (fun k : ℕ => q ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by omega : (1 : ℕ) < q)
  -- The scale ratio along the geometric subsequence.
  have hgeom : Tendsto (fun k : ℕ =>
      (rothNumberNat (q ^ (k + 1)) : ℝ) / (rothNumberNat (q ^ k) : ℝ)) atTop (𝓝 c) := by
    refine (h.comp hpow).congr' ?_
    filter_upwards with k
    dsimp only [Function.comp_apply]
    rw [← pow_succ]
  -- The logarithmic increments along the geometric subsequence.
  let b : ℕ → ℝ := fun k => Real.log (rothNumberNat (q ^ k) : ℝ)
  have hloggeom : Tendsto (fun k : ℕ => Real.log
      ((rothNumberNat (q ^ (k + 1)) : ℝ) / (rothNumberNat (q ^ k) : ℝ)))
      atTop (𝓝 (Real.log c)) :=
    (Real.continuousAt_log hcne).tendsto.comp hgeom
  have hd : Tendsto (fun k : ℕ => b (k + 1) - b k) atTop (𝓝 (Real.log c)) := by
    refine hloggeom.congr' (Eventually.of_forall ?_)
    intro k
    rw [Real.log_div (rothNumberNat_pos_real (hone (k + 1))).ne'
      (rothNumberNat_pos_real (hone k)).ne']
  -- Cesàro's lemma and the telescoping identity give `b k / k → log c`.
  have hces : Tendsto (fun k : ℕ => (k : ℝ)⁻¹ * (b k - b 0)) atTop (𝓝 (Real.log c)) := by
    refine hd.cesaro.congr' (Eventually.of_forall ?_)
    intro k
    rw [Finset.sum_range_sub b k]
  have hb0 : Tendsto (fun k : ℕ => b 0 / (k : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hb_div : Tendsto (fun k : ℕ => b k / (k : ℝ)) atTop (𝓝 (Real.log c)) := by
    have h2 : Tendsto (fun k : ℕ => b k / (k : ℝ) - b 0 / (k : ℝ))
        atTop (𝓝 (Real.log c)) :=
      hces.congr' (Eventually.of_forall (fun k => by ring))
    have hsum : Tendsto (fun k : ℕ =>
        (b k / (k : ℝ) - b 0 / (k : ℝ)) + b 0 / (k : ℝ))
        atTop (𝓝 (Real.log c + 0)) := h2.add hb0
    simpa using hsum
  -- The independent logarithmic-exponent limit, along the same subsequence.
  have hl : Tendsto (fun k : ℕ => b k / Real.log ((q ^ k : ℕ) : ℝ)) atTop (𝓝 1) :=
    tendsto_log_rothNumberNat_div_log_one.comp hpow
  have hlogk : Tendsto (fun k : ℕ => Real.log ((q ^ k : ℕ) : ℝ) / (k : ℝ))
      atTop (𝓝 (Real.log (q : ℝ))) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    rw [Nat.cast_pow, Real.log_pow]
    field_simp
  -- The exact factorization `b k / k = (b k / log (q ^ k)) * (log (q ^ k) / k)`.
  have hfac : (fun k : ℕ => b k / (k : ℝ)) =ᶠ[atTop] (fun k : ℕ =>
      (b k / Real.log ((q ^ k : ℕ) : ℝ)) * (Real.log ((q ^ k : ℕ) : ℝ) / (k : ℝ))) := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    have hlogk0 : Real.log ((q ^ k : ℕ) : ℝ) ≠ 0 := by
      rw [Nat.cast_pow, Real.log_pow]
      exact mul_ne_zero hk0 hlogq_ne
    field_simp
  have hb_scale : Tendsto (fun k : ℕ => b k / (k : ℝ)) atTop (𝓝 (Real.log (q : ℝ))) := by
    have hlim : Tendsto (fun k : ℕ =>
        (b k / Real.log ((q ^ k : ℕ) : ℝ)) * (Real.log ((q ^ k : ℕ) : ℝ) / (k : ℝ)))
        atTop (𝓝 (Real.log (q : ℝ))) := by
      simpa using hl.mul hlogk
    exact hlim.congr' hfac.symm
  -- Uniqueness of limits and injectivity of `log` on the positive reals.
  have hlogeq : Real.log c = Real.log (q : ℝ) := tendsto_nhds_unique hb_div hb_scale
  exact Real.log_injOn_pos hcpos hqpos hlogeq

/-- **Fixed-scale rigidity for any asymptotic comparison function.**  For fixed
`q ≥ 2`, suppose a real function `f` satisfies `rothNumberNat N / f N → 1` and
its fixed-scale dilation ratio has a finite limit `f (N * q) / f N → c`.  Then
`c = q`.

Route: from `rothNumberNat N / f N → 1` and eventual `rothNumberNat N > 0` we
derive eventual `f N > 0` (positivity is derived, never assumed).  The map
`N ↦ N * q` tends to `atTop`, so composing the ratio asymptotic gives
`rothNumberNat (N*q) / f (N*q) → 1`, and inverting gives
`(rothNumberNat N / f N)⁻¹ → 1`.  On the eventual tail the exact field identity
expresses `rothNumberNat (N*q) / rothNumberNat N` as the product of those three
convergent factors, hence it tends to `1 * c * 1 = c`, and the accepted
classifier `eq_scale_of_tendsto_rothNumberNat_mul_ratio` forces `c = q`. -/
theorem eq_scale_of_asymptotic_comparison {q : ℕ} (hq : 2 ≤ q) {f : ℕ → ℝ} {c : ℝ}
    (hf : Tendsto (fun N => (rothNumberNat N : ℝ) / f N) atTop (𝓝 1))
    (hc : Tendsto (fun N => f (N * q) / f N) atTop (𝓝 c)) :
    c = (q : ℝ) := by
  have hq1 : 1 ≤ q := by omega
  have hNq : Tendsto (fun N : ℕ => N * q) atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    refine ⟨b, fun a ha => ?_⟩
    calc b ≤ a := ha
      _ = a * 1 := (Nat.mul_one a).symm
      _ ≤ a * q := Nat.mul_le_mul_left a hq1
  have hev_ratio_gt : ∀ᶠ N : ℕ in atTop,
      (1 / 2 : ℝ) < (rothNumberNat N : ℝ) / f N :=
    (tendsto_order.1 hf).1 (1 / 2) (by norm_num)
  have hev_rN_pos : ∀ᶠ N : ℕ in atTop, (0 : ℝ) < (rothNumberNat N : ℝ) :=
    eventually_atTop.mpr ⟨1, fun N hN => rothNumberNat_pos_real hN⟩
  have hev_fpos : ∀ᶠ N : ℕ in atTop, 0 < f N := by
    filter_upwards [hev_ratio_gt, hev_rN_pos] with N hratio hrpos
    have hratio' : 0 < (rothNumberNat N : ℝ) / f N := by linarith
    rcases lt_trichotomy (f N) 0 with hlt | heq | hgt
    · exact absurd hratio'
        (not_lt.mpr (le_of_lt (div_neg_of_pos_of_neg hrpos hlt)))
    · rw [heq, div_zero] at hratio'
      exact absurd hratio' (lt_irrefl 0)
    · exact hgt
  have hev_fpos_q : ∀ᶠ N : ℕ in atTop, 0 < f (N * q) :=
    hNq.eventually hev_fpos
  have hev_rN_ne : ∀ᶠ N : ℕ in atTop, (rothNumberNat N : ℝ) ≠ 0 :=
    eventually_atTop.mpr ⟨1, fun N hN => ne_of_gt (rothNumberNat_pos_real hN)⟩
  have hev_eq : (fun N : ℕ =>
        (rothNumberNat (N * q) : ℝ) / (rothNumberNat N : ℝ))
      =ᶠ[atTop] (fun N : ℕ =>
        ((rothNumberNat (N * q) : ℝ) / f (N * q))
          * (f (N * q) / f N)
          * (((rothNumberNat N : ℝ) / f N)⁻¹)) := by
    filter_upwards [hev_fpos, hev_fpos_q, hev_rN_ne] with N hfN hfNq hrN
    have hfN' : f N ≠ 0 := ne_of_gt hfN
    have hfNq' : f (N * q) ≠ 0 := ne_of_gt hfNq
    field_simp
  have hA : Tendsto (fun N : ℕ =>
      (rothNumberNat (N * q) : ℝ) / f (N * q)) atTop (𝓝 1) :=
    hf.comp hNq
  have hC : Tendsto (fun N : ℕ =>
      ((rothNumberNat N : ℝ) / f N)⁻¹) atTop (𝓝 (1 : ℝ)) := by
    simpa using hf.inv₀ one_ne_zero
  have hprod : Tendsto (fun N : ℕ =>
      ((rothNumberNat (N * q) : ℝ) / f (N * q))
        * (f (N * q) / f N)
        * (((rothNumberNat N : ℝ) / f N)⁻¹)) atTop (𝓝 c) := by
    simpa using (hA.mul hc).mul hC
  have hlim : Tendsto (fun N : ℕ =>
      (rothNumberNat (N * q) : ℝ) / (rothNumberNat N : ℝ)) atTop (𝓝 c) :=
    Tendsto.congr' hev_eq.symm hprod
  exact eq_scale_of_tendsto_rothNumberNat_mul_ratio hq hlim

/-- **No finite limit off the integer scale.**  For fixed `q ≥ 2`, the ratio
`(rothNumberNat (N * q) : ℝ) / (rothNumberNat N : ℝ)` cannot converge to any
finite real `c` with `c ≠ (q : ℝ)`.  This is the contrapositive of
`eq_scale_of_tendsto_rothNumberNat_mul_ratio`.  It does not assert that the
ratio converges. -/
theorem not_tendsto_rothNumberNat_mul_ratio_of_ne_scale {q : ℕ} (hq : 2 ≤ q) {c : ℝ}
    (hcq : c ≠ (q : ℝ)) :
    ¬ Tendsto (fun N : ℕ =>
      (rothNumberNat (N * q) : ℝ) / (rothNumberNat N : ℝ)) atTop (𝓝 c) :=
  fun h => hcq (eq_scale_of_tendsto_rothNumberNat_mul_ratio hq h)

/-- **No asymptotic comparison function with a wrong finite integer-scale
ratio.**  For fixed `q ≥ 2`, there is no real function `f` with
`rothNumberNat N / f N → 1` and `f (N * q) / f N → c` for any `c ≠ q`.  This is
the nonexistence corollary of `eq_scale_of_asymptotic_comparison`.  It does not
assert that any ratio limit exists. -/
theorem not_exists_asymptotic_comparison_of_ne_scale {q : ℕ} (hq : 2 ≤ q) {c : ℝ}
    (hcq : c ≠ (q : ℝ)) :
    ¬ ∃ f : ℕ → ℝ,
      Tendsto (fun N => (rothNumberNat N : ℝ) / f N) atTop (𝓝 1) ∧
      Tendsto (fun N => f (N * q) / f N) atTop (𝓝 c) := by
  rintro ⟨f, hf, hc⟩
  exact hcq (eq_scale_of_asymptotic_comparison hq hf hc)

/-- Ground-truth non-vacuity check of the excluded value: at `q = 2` the value
`c = 0` is genuinely different from the forced value `q = 2`, so the
nonexistence corollary `not_tendsto_rothNumberNat_mul_ratio_of_ne_scale`
excludes a real value and the lower bound `c ≥ 1` is substantive. -/
example : ¬ Tendsto (fun N : ℕ =>
    (rothNumberNat (N * 2) : ℝ) / (rothNumberNat N : ℝ)) atTop (𝓝 0) :=
  not_tendsto_rothNumberNat_mul_ratio_of_ne_scale (q := 2) (by norm_num) (by norm_num)

/-- Ground-truth satisfiability check of the comparison hypothesis: the
concrete choice `f = rothNumberNat` makes `rothNumberNat N / f N` eventually
`1`, hence tends to `1`.  This witnesses non-vacuity of the first hypothesis of
`eq_scale_of_asymptotic_comparison`; it does not witness the dilation-ratio
hypothesis, whose convergence is the open content. -/
example : Tendsto (fun N : ℕ => (rothNumberNat N : ℝ) / (rothNumberNat N : ℝ))
    atTop (𝓝 1) := by
  apply Tendsto.congr' _ tendsto_const_nhds
  filter_upwards [eventually_atTop.mpr
    ⟨1, fun N hN => rothNumberNat_pos_real hN⟩] with N hN
  exact (div_self (ne_of_gt hN)).symm

/-- Ground-truth check of the forced value at `q = 2`: `((2 : ℕ) : ℝ) = 2` is
positive and distinct from the excluded value `0`, so the conclusion of
`eq_scale_of_tendsto_rothNumberNat_mul_ratio` is a substantive constraint. -/
example : ((2 : ℕ) : ℝ) = 2 ∧ (0 : ℝ) < ((2 : ℕ) : ℝ) ∧ ((2 : ℕ) : ℝ) ≠ 0 := by
  norm_num

end

end Erdos142

-- Axiom audit for every public declaration.
#print axioms Erdos142.eq_scale_of_tendsto_rothNumberNat_mul_ratio
#print axioms Erdos142.eq_scale_of_asymptotic_comparison
#print axioms Erdos142.not_tendsto_rothNumberNat_mul_ratio_of_ne_scale
#print axioms Erdos142.not_exists_asymptotic_comparison_of_ne_scale