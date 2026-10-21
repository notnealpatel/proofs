/-
# A010786 — Kotesovec: the growth constant of the floor-factorial numbers

## OEIS source (retrieved with `oeis show A010786`, 2026-10-21)

```
NAME:     Floor-factorial numbers: a(n) = Product_{k=1..n} floor(n/k).
TERMS:    1,1,2,3,8,10,36,42,128,216,600,660,3456,3744,9408,18900,61440,65280,
          279936,295488,1152000,2116800,4878720,5100480,31850496,41472000,...
FORMULA (the conjecture):
          From _Vaclav Kotesovec_, Oct 03 2018: (Start)
          log(a(n)) ~ c * (n - log(2*Pi*n)/2), where c = 0.7885...
          Conjecture: c = A085361. (End)
FORMULA:  From _Ridouane Oudra_, Jan 18 2025:
          a(n) = Product_{k=1..n} ((k+1)/k)^floor(n/(k+1)).
```

A085361 (`oeis show A085361`): "Decimal expansion of the number
c = Sum_{n>=1} (zeta(n+1)-1)/n", with the formula
"Equals Sum_{n>=2} log(n/(n-1))/n".

## Status

Triage: open (no proof in the entry or the literature as far as the triage
could tell).  This module proves the conjecture: `conjecture_A010786` (the
printed `~` form with the constant written as A085361's zeta series) and
`tendsto_log_a_div_A085361` (the equivalent limit form).

## Proof outline

Writing `log m = Σ_{i<m-1} log((i+2)/(i+1))` and swapping the order of
summation, using `#{k ≤ n : i + 2 ≤ ⌊n/k⌋} = ⌊n/(i+2)⌋`, gives Oudra's formula
`log a(n) = Σ_{i<n} ⌊n/(i+2)⌋ log((i+2)/(i+1))` (`log_a_eq`).  Comparing with
`n Σ_{i<n} log((i+2)/(i+1))/(i+2)` termwise gives an error in
`[0, Σ_{i<n} log((i+2)/(i+1))] = [0, log(n+1)]` (`error_bounds`), so
`log a(n)/n → cAG := Σ_{i≥0} log((i+2)/(i+1))/(i+2)`.  Since `cAG > 0` and
`log(2πn)/n → 0`, the `~` form follows.  Expanding
`log((j+2)/(j+1)) = -log(1 - 1/(j+2)) = Σ_m 1/((m+1)(j+2)^(m+1))` and swapping
the nonnegative double series identifies `cAG` with A085361's zeta series
(`cAG_eq_A085361`).
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A010786ProdFloorKotesovec

open Real Filter Topology Asymptotics

noncomputable section

/-! ## Definitions and ground truth -/

/-- The floor-factorial number `a(n) = ∏_{k=1}^{n} ⌊n/k⌋` (OEIS A010786);
`n / k` is natural-number (floor) division, and `a 0 = 1` (empty product). -/
def a (n : ℕ) : ℕ := ∏ k ∈ Finset.Icc 1 n, n / k

example : a 4 = 8 := by decide

example : (List.range 20).map a =
    [1, 1, 2, 3, 8, 10, 36, 42, 128, 216, 600, 660, 3456, 3744, 9408, 18900, 61440, 65280,
      279936, 295488] := by decide

/-- `logStep i = log((i+2)/(i+1))`, the increment `log(j) - log(j-1)` at `j = i + 2`. -/
def logStep (i : ℕ) : ℝ := Real.log (((i : ℝ) + 2) / ((i : ℝ) + 1))

/-- `cTerm i = log((i+2)/(i+1))/(i+2)`, the `j = i + 2` term of
`Σ_{j≥2} log(j/(j-1))/j`. -/
def cTerm (i : ℕ) : ℝ := logStep i / ((i : ℝ) + 2)

/-- The constant `Σ_{j≥2} log(j/(j-1))/j` (the second form of A085361),
indexed from `j = i + 2`. Its summability is `summable_cTerm`. -/
def cAG : ℝ := ∑' i : ℕ, cTerm i

/-- The constant A085361 as named in its entry, `Σ_{n≥1} (ζ(n+1) - 1)/n`,
indexed from `n = m + 1`; `ζ` is Mathlib's `riemannZeta` and the value at the
real point `m + 2 > 1` is real, so `.re` loses nothing. -/
def A085361 : ℝ := ∑' m : ℕ, ((riemannZeta ((m : ℂ) + 2)).re - 1) / ((m : ℝ) + 1)

/-! ## Oudra's formula for `log a(n)` -/

/-- Telescoping: `log(m + 1) = Σ_{i<m} log((i+2)/(i+1))`. -/
lemma log_succ_eq_sum_logStep (m : ℕ) :
    Real.log ((m : ℝ) + 1) = ∑ i ∈ Finset.range m, logStep i := by
  have h := Finset.sum_range_sub (fun i : ℕ => Real.log ((i : ℝ) + 1)) m
  simp only [Nat.cast_zero, zero_add, Real.log_one, sub_zero] at h
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [logStep, Real.log_div (by positivity) (by positivity)]
  push_cast
  ring_nf

/-- For `1 ≤ m ≤ n`, `log m = Σ_{i<n, i+2 ≤ m} log((i+2)/(i+1))`. -/
lemma log_eq_sum_ite (n m : ℕ) (h1 : 1 ≤ m) (h2 : m ≤ n) :
    Real.log (m : ℝ) = ∑ i ∈ Finset.range n, if i + 2 ≤ m then logStep i else 0 := by
  obtain ⟨p, rfl⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
  rw [← Finset.sum_filter]
  have hf : (Finset.range n).filter (fun i => i + 2 ≤ p + 1) = Finset.range p := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hf, ← log_succ_eq_sum_logStep]
  push_cast
  rfl

/-- The counting step: `#{k ∈ [1, n] : i + 2 ≤ ⌊n/k⌋} = ⌊n/(i+2)⌋`. -/
lemma card_filter_le_div (n i : ℕ) :
    ((Finset.Icc 1 n).filter (fun k => i + 2 ≤ n / k)).card = n / (i + 2) := by
  have hset : (Finset.Icc 1 n).filter (fun k => i + 2 ≤ n / k) = Finset.Icc 1 (n / (i + 2)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hk1, _⟩, hk⟩
      refine ⟨hk1, ?_⟩
      rw [Nat.le_div_iff_mul_le (by omega)] at hk ⊢
      rw [mul_comm]
      exact hk
    · rintro ⟨hk1, hk⟩
      have hdl : n / (i + 2) ≤ n := Nat.div_le_self _ _
      refine ⟨⟨hk1, hk.trans hdl⟩, ?_⟩
      rw [Nat.le_div_iff_mul_le (by omega)] at hk ⊢
      rw [mul_comm]
      exact hk
  rw [hset, Nat.card_Icc, Nat.add_sub_cancel]

/-- Oudra's formula in logarithmic form:
`log a(n) = Σ_{i<n} ⌊n/(i+2)⌋ · log((i+2)/(i+1))`. -/
theorem log_a_eq (n : ℕ) :
    Real.log (a n : ℝ) = ∑ i ∈ Finset.range n, ((n / (i + 2) : ℕ) : ℝ) * logStep i := by
  have hpos : ∀ k ∈ Finset.Icc 1 n, (n / k : ℕ) ≠ 0 := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    exact (Nat.div_pos hk.2 (by omega)).ne'
  rw [a, Nat.cast_prod, Real.log_prod (fun k hk => by exact_mod_cast hpos k hk)]
  have step : ∀ k ∈ Finset.Icc 1 n, Real.log ((n / k : ℕ) : ℝ)
      = ∑ i ∈ Finset.range n, if i + 2 ≤ n / k then logStep i else 0 := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    exact log_eq_sum_ite n (n / k) (Nat.div_pos hk.2 (by omega)) (Nat.div_le_self _ _)
  rw [Finset.sum_congr rfl step, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, card_filter_le_div, nsmul_eq_mul]

/-! ## Elementary bounds and summability -/

/-- `log((i+2)/(i+1)) ≥ 0`. -/
lemma logStep_nonneg (i : ℕ) : 0 ≤ logStep i := by
  apply Real.log_nonneg
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- `log((i+2)/(i+1)) ≤ 1/(i+1)`. -/
lemma logStep_le (i : ℕ) : logStep i ≤ 1 / ((i : ℝ) + 1) := by
  have h := Real.log_le_sub_one_of_pos (x := ((i : ℝ) + 2) / ((i : ℝ) + 1)) (by positivity)
  have he : ((i : ℝ) + 2) / ((i : ℝ) + 1) - 1 = 1 / ((i : ℝ) + 1) := by
    field_simp
    ring
  rw [logStep]
  linarith

/-- The terms of `cAG` are nonnegative. -/
lemma cTerm_nonneg (i : ℕ) : 0 ≤ cTerm i := div_nonneg (logStep_nonneg i) (by positivity)

/-- The terms of `cAG` are dominated by `1/(i+1)^2`. -/
lemma cTerm_le (i : ℕ) : cTerm i ≤ 1 / ((i : ℝ) + 1) ^ 2 := by
  have h1 : cTerm i ≤ (1 / ((i : ℝ) + 1)) / ((i : ℝ) + 2) :=
    div_le_div_of_nonneg_right (logStep_le i) (by positivity)
  have h2 : (1 / ((i : ℝ) + 1)) / ((i : ℝ) + 2) ≤ 1 / ((i : ℝ) + 1) ^ 2 := by
    rw [div_div, sq]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  exact h1.trans h2

/-- The series `Σ_{j≥2} log(j/(j-1))/j` converges. -/
lemma summable_cTerm : Summable cTerm := by
  have hs : Summable (fun i : ℕ => 1 / ((i : ℝ) + 1) ^ 2) := by
    have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    simpa using h
  exact hs.of_nonneg_of_le cTerm_nonneg cTerm_le

/-- The constant is positive (its first term is `log 2 / 2`). -/
lemma cAG_pos : 0 < cAG := by
  have h0 : 0 < cTerm 0 := by
    simp only [cTerm, logStep, Nat.cast_zero, zero_add, div_one]
    exact div_pos (Real.log_pos one_lt_two) two_pos
  exact lt_of_lt_of_le h0 (summable_cTerm.le_tsum 0 fun j _ => cTerm_nonneg j)

/-- `⌊n/(i+2)⌋ ≤ n/(i+2) ≤ ⌊n/(i+2)⌋ + 1` in `ℝ`. -/
lemma floor_div_bounds (n i : ℕ) :
    ((n / (i + 2) : ℕ) : ℝ) ≤ (n : ℝ) / ((i : ℝ) + 2) ∧
      (n : ℝ) / ((i : ℝ) + 2) ≤ ((n / (i + 2) : ℕ) : ℝ) + 1 := by
  constructor
  · have h := Nat.cast_div_le (α := ℝ) (m := n) (n := i + 2)
    simpa using h
  · have h := Nat.lt_div_mul_add (a := n) (b := i + 2) (by omega)
    have hr : (n : ℝ) < ((n / (i + 2) : ℕ) : ℝ) * ((i : ℝ) + 2) + ((i : ℝ) + 2) := by
      exact_mod_cast h
    rw [div_le_iff₀ (by positivity)]
    nlinarith

/-- The error bound: `0 ≤ n · Σ_{i<n} cTerm i - log a(n) ≤ log(n+1)`. -/
theorem error_bounds (n : ℕ) :
    0 ≤ (n : ℝ) * (∑ i ∈ Finset.range n, cTerm i) - Real.log (a n : ℝ) ∧
      (n : ℝ) * (∑ i ∈ Finset.range n, cTerm i) - Real.log (a n : ℝ) ≤
        Real.log ((n : ℝ) + 1) := by
  have hdiff : (n : ℝ) * (∑ i ∈ Finset.range n, cTerm i) - Real.log (a n : ℝ)
      = ∑ i ∈ Finset.range n,
          ((n : ℝ) / ((i : ℝ) + 2) - ((n / (i + 2) : ℕ) : ℝ)) * logStep i := by
    rw [log_a_eq, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cTerm]
    ring
  rw [hdiff, log_succ_eq_sum_logStep]
  constructor
  · refine Finset.sum_nonneg fun i _ => mul_nonneg ?_ (logStep_nonneg i)
    linarith [(floor_div_bounds n i).1]
  · refine Finset.sum_le_sum fun i _ => ?_
    have hb := floor_div_bounds n i
    have hg := logStep_nonneg i
    nlinarith

/-! ## The limit -/

/-- `log(n+1)/n → 0`. -/
lemma tendsto_log_succ_div :
    Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) / (n : ℝ)) atTop (𝓝 0) := by
  have h := Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  refine (h.comp hn).congr fun n => ?_
  simp only [Function.comp_apply, pow_one, one_mul]
  ring_nf

/-- `log n / n → 0`. -/
lemma tendsto_log_div :
    Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  refine (h.comp tendsto_natCast_atTop_atTop).congr fun n => ?_
  simp only [Function.comp_apply, pow_one, one_mul, add_zero]

/-- `log a(n) / n → Σ_{j≥2} log(j/(j-1))/j`. -/
theorem tendsto_log_a_div :
    Tendsto (fun n : ℕ => Real.log (a n : ℝ) / (n : ℝ)) atTop (𝓝 cAG) := by
  set E : ℕ → ℝ := fun n => (n : ℝ) * (∑ i ∈ Finset.range n, cTerm i) - Real.log (a n : ℝ)
    with hE
  have hsum : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, cTerm i) atTop (𝓝 cAG) :=
    summable_cTerm.hasSum.tendsto_sum_nat
  have hE0 : Tendsto (fun n : ℕ => E n / (n : ℝ)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      tendsto_log_succ_div ?_ ?_
    · exact Eventually.of_forall fun n => div_nonneg (error_bounds n).1 (Nat.cast_nonneg n)
    · exact Eventually.of_forall fun n =>
        div_le_div_of_nonneg_right (error_bounds n).2 (Nat.cast_nonneg n)
  have hlim := hsum.sub hE0
  rw [sub_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  simp only [hE]
  field_simp
  ring

/-- Kotesovec's asymptotic with the constant `Σ_{j≥2} log(j/(j-1))/j`:
`log a(n) ~ cAG · (n - log(2πn)/2)`. -/
theorem kotesovec_cAG :
    (fun n : ℕ => Real.log (a n : ℝ)) ~[atTop]
      (fun n : ℕ => cAG * ((n : ℝ) - Real.log (2 * π * n) / 2)) := by
  have hv : Tendsto (fun n : ℕ => cAG * ((n : ℝ) - Real.log (2 * π * n) / 2) / (n : ℝ))
      atTop (𝓝 cAG) := by
    have hl : Tendsto (fun n : ℕ => Real.log (2 * π * n) / (n : ℝ)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => Real.log (2 * π) / (n : ℝ)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
      have h2 := h1.add tendsto_log_div
      rw [add_zero] at h2
      refine h2.congr' ?_
      filter_upwards [eventually_ne_atTop 0] with n hn
      have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
      rw [Real.log_mul (by positivity) hn', add_div]
    have h3 := tendsto_const_nhds (x := cAG) |>.mul (tendsto_const_nhds (x := (1 : ℝ)) |>.sub
      (hl.div_const 2))
    rw [zero_div, sub_zero, mul_one] at h3
    refine h3.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    field_simp
  apply Asymptotics.isEquivalent_of_tendsto_one
  have hq := tendsto_log_a_div.div hv cAG_pos.ne'
  rw [div_self cAG_pos.ne'] at hq
  refine hq.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  simp only [Pi.div_apply]
  rw [div_div_div_cancel_right₀ hn']

/-! ## The constant equals A085361's zeta series -/

/-- The double-series term `1/((m+1)(j+2)^(m+2))`. -/
def doubleTerm (j m : ℕ) : ℝ := 1 / (((m : ℝ) + 1) * ((j : ℝ) + 2) ^ (m + 2))

/-- The double-series terms are nonnegative. -/
lemma doubleTerm_nonneg (j m : ℕ) : 0 ≤ doubleTerm j m := by
  unfold doubleTerm
  positivity

/-- Row sums: `Σ_m 1/((m+1)(j+2)^(m+2)) = log((j+2)/(j+1))/(j+2)`, from
`-log(1-x) = Σ_m x^(m+1)/(m+1)` at `x = 1/(j+2)`. -/
lemma hasSum_doubleTerm_row (j : ℕ) : HasSum (fun m => doubleTerm j m) (cTerm j) := by
  set x : ℝ := 1 / ((j : ℝ) + 2) with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x < 1 := by
    rw [hx, div_lt_one (by positivity)]
    linarith
  have h := (Real.hasSum_pow_div_log_of_abs_lt_one (x := x)
    (by rw [abs_lt]; constructor <;> linarith)).mul_left x
  have hlog : -Real.log (1 - x) = logStep j := by
    have h1 : 1 - x = (((j : ℝ) + 2) / ((j : ℝ) + 1))⁻¹ := by
      rw [hx, inv_div]
      field_simp
      ring
    rw [h1, Real.log_inv, neg_neg, logStep]
  have hval : x * -Real.log (1 - x) = cTerm j := by
    rw [hlog, cTerm, hx]
    ring
  rw [hval] at h
  refine h.congr_fun fun m => ?_
  rw [doubleTerm, hx, div_pow, one_pow, pow_succ _ (m + 1)]
  field_simp

/-- Each row of the double series is summable. -/
lemma summable_doubleTerm_row (j : ℕ) : Summable (fun m => doubleTerm j m) :=
  (hasSum_doubleTerm_row j).summable

/-- The double series is summable on `ℕ × ℕ` (nonnegative, rows sum to `cTerm`). -/
lemma summable_doubleTerm_uncurry : Summable (Function.uncurry doubleTerm) := by
  have h : Summable (fun p : ℕ × ℕ => doubleTerm p.1 p.2) := by
    rw [summable_prod_of_nonneg (fun p => doubleTerm_nonneg p.1 p.2)]
    refine ⟨fun j => summable_doubleTerm_row j, ?_⟩
    simp_rw [(hasSum_doubleTerm_row _).tsum_eq]
    exact summable_cTerm
  exact h

/-- `ζ(m+2) - 1 = Σ_{j≥0} 1/(j+2)^(m+2)`. -/
lemma zeta_re_sub_one (m : ℕ) :
    (riemannZeta ((m : ℂ) + 2)).re - 1 = ∑' j : ℕ, 1 / ((j : ℝ) + 2) ^ (m + 2) := by
  have hz := zeta_nat_eq_tsum_of_gt_one (k := m + 2) (by omega)
  have hc : ((m + 2 : ℕ) : ℂ) = (m : ℂ) + 2 := by
    push_cast
    ring
  rw [hc] at hz
  have hr : ∑' n : ℕ, 1 / (n : ℂ) ^ (m + 2) = ((∑' n : ℕ, 1 / (n : ℝ) ^ (m + 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    push_cast
    rfl
  rw [hz, hr, Complex.ofReal_re]
  have hs : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (m + 2)) :=
    Real.summable_one_div_nat_pow.mpr (by omega)
  rw [hs.tsum_eq_zero_add, ((summable_nat_add_iff 1).mpr hs).tsum_eq_zero_add]
  push_cast
  simp only [zero_pow (by omega : m + 2 ≠ 0), div_zero, zero_add, one_pow, div_one,
    add_sub_cancel_left]
  congr 1
  funext j
  ring_nf

/-- The two descriptions of A085361 agree:
`Σ_{j≥2} log(j/(j-1))/j = Σ_{n≥1} (ζ(n+1) - 1)/n`. -/
theorem cAG_eq_A085361 : cAG = A085361 := by
  have hcol : ∀ m : ℕ, ∑' j : ℕ, doubleTerm j m =
      ((riemannZeta ((m : ℂ) + 2)).re - 1) / ((m : ℝ) + 1) := by
    intro m
    rw [zeta_re_sub_one, div_eq_mul_inv, mul_comm, ← tsum_mul_left]
    congr 1
    funext j
    rw [doubleTerm]
    field_simp
  have hcolsum : ∀ m : ℕ, Summable (fun j => doubleTerm j m) := by
    intro m
    have hsym : Summable (fun p : ℕ × ℕ => doubleTerm p.2 p.1) :=
      summable_doubleTerm_uncurry.prod_symm
    exact ((summable_prod_of_nonneg (fun p => doubleTerm_nonneg p.2 p.1)).mp hsym).1 m
  rw [cAG, A085361]
  simp_rw [← hcol, ← (hasSum_doubleTerm_row _).tsum_eq]
  exact (summable_doubleTerm_uncurry.tsum_comm' summable_doubleTerm_row hcolsum).symm

/-! ## The conjecture -/

/-- **Kotesovec's conjecture (A010786, Vaclav Kotesovec, Oct 03 2018).**

Verbatim: "log(a(n)) ~ c * (n - log(2*Pi*n)/2), where c = 0.7885...
Conjecture: c = A085361."

Here `a(n) = ∏_{k=1}^n ⌊n/k⌋` and `A085361 = Σ_{n≥1} (ζ(n+1) - 1)/n` (the
definition in the name of A085361).  The statement is the `IsEquivalent`
relation `~[atTop]` along `ℕ`; at `n = 0` the junk value `log 0 = 0` is
irrelevant to an asymptotic statement. -/
theorem conjecture_A010786 :
    (fun n : ℕ => Real.log (a n : ℝ)) ~[atTop]
      (fun n : ℕ => A085361 * ((n : ℝ) - Real.log (2 * π * n) / 2)) := by
  rw [← cAG_eq_A085361]
  exact kotesovec_cAG

/-- The limit form of the conjecture: `log a(n) / n → A085361`. -/
theorem tendsto_log_a_div_A085361 :
    Tendsto (fun n : ℕ => Real.log (a n : ℝ) / (n : ℝ)) atTop (𝓝 A085361) := by
  rw [← cAG_eq_A085361]
  exact tendsto_log_a_div

end

end Candidates.A010786ProdFloorKotesovec
