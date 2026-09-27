/-
  Erdős Problem #142 — the unconditional positive-density negative
  square-defect theorem on a fixed square tower.

  For a base `M ≥ 3` put `N k = M ^ (2 ^ k)`, `a k = rothLogDeficit (N k)`
  and `X k = squareScaleDefect (N k) = a (k+1) - 2 * a k`.  The theorem proved
  here is a *density* statement in the tower index `k`:

  for every `β` with `0 < β < 2 - √2`, with `t = 2 - β > √2` and
  `δβ = 1 - log (√2) / log t > 0`, and for every real `δ < δβ`, the negative
  defect inequality `X k ≤ -β * a k` holds at least `δ` fraction of the times
  `k < K`, eventually in `K`.

  The conclusion is expressed *without* any `liminf` API, as the eventual
  `ℝ`-valued lower bound on the cardinality of the filtered range, exactly as
  the informal lower-density statement intends.  A second theorem replaces
  `-β * a k` by an arbitrary fixed negative level `-H`, removing finitely many
  early indices via `tendsto_rothLogDeficit_atTop`.

  The analytic core is a reusable counting lemma about an arbitrary positive,
  nondecreasing sequence `a` with an eventual geometric upper bound `A * s ^ k`
  and a ratio threshold `t > s`: if `cnt K` counts the indices `k < K` with
  `a (k+1) ≤ t * a k`, then `cnt K` grows at least at rate
  `1 - log s / log t`.  The Erdős endpoint instantiates it with `s = √2`, the
  accepted EHPS envelope `eventually_rothLogDeficit_iterated_square_le`, and
  the exact tower recurrence `squareScaleDefect_eq_rothLogDeficit_sub`.

  A second layer takes the endpoint `β ↓ 0` of the density curve.  The
  standalone real lemma `exists_beta_density_gt_of_lt_half` converts any
  `δ < 1/2` into an admissible `β ∈ (0, 2 - √2)` with
  `δ < 1 - log (√2) / log (2 - β)`, using only continuity of `log` at `2`;
  consequently `eventually_card_squareScaleDefect_neg` proves the endpoint
  half-density statement `∀ᶠ K, δ * K ≤ #{k < K : squareScaleDefect (N k) < 0}`
  for every `δ < 1/2`, and `eventually_card_squareScaleDefect_nonpos` is the
  closed-predicate (`≤ 0`) corollary.

  No `sorry`, no `axiom`, no `native_decide`, no `unsafe`.  The axiom audit is
  at the end of the file.
-/

import Erdos.Erdos142.SquareScaleNegative
import Erdos.Erdos142.FixedRadixUpperEnvelope
import Erdos.Erdos142.FixedRadixRecurrence

set_option autoImplicit false

open Filter
open scoped Topology

namespace Erdos142

noncomputable section

/-! ## The counting core -/

/-- The number of indices `k < K` at which `a` does not grow by more than the
factor `t`, i.e. `a (k + 1) ≤ t * a k`.  This is the finite counting functional
from which the lower density is read off. -/
def negRatioCount (a : ℕ → ℝ) (t : ℝ) (K : ℕ) : ℕ :=
  ((Finset.range K).filter (fun k => a (k + 1) ≤ t * a k)).card

/-- Ground-truth check: `negRatioCount` unfolds to the literal filtered range
cardinality. -/
example (a : ℕ → ℝ) (t : ℝ) (K : ℕ) :
    negRatioCount a t K =
      ((Finset.range K).filter (fun k => a (k + 1) ≤ t * a k)).card := rfl

/-- Ground-truth check at `K = 0`: the count is empty. -/
example (a : ℕ → ℝ) (t : ℝ) : negRatioCount a t 0 = 0 := rfl

/-- **Recursion for the counting functional.**  Extending the range by the
single index `K` increases `negRatioCount` by `1` exactly when `a (K+1) ≤ t * a K`
and leaves it unchanged otherwise. -/
theorem negRatioCount_succ (a : ℕ → ℝ) (t : ℝ) (K : ℕ) :
    negRatioCount a t (K + 1) =
      negRatioCount a t K + (if a (K + 1) ≤ t * a K then 1 else 0) := by
  unfold negRatioCount
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases hp : a (K + 1) ≤ t * a K
  · rw [if_pos hp]
    rw [Finset.card_insert_of_notMem (by simp)]
    simp only [if_pos hp]
  · rw [if_neg hp]
    simp only [if_neg hp, add_zero]

/-- **Geometric lower bound.**  For a nondecreasing sequence `a` and a threshold
`t > 1`, the value `a K` dominates `a 0 * t ^ (K - negRatioCount a t K)`: every
index at which the ratio does not exceed `t` contributes at least a factor `1`
(by monotonicity), and every other index contributes strictly more than `t`. -/
theorem geometric_lower_of_card_negRatio (a : ℕ → ℝ) (t : ℝ) (ht : 1 < t)
    (hmono : ∀ k : ℕ, a k ≤ a (k + 1)) :
    ∀ K : ℕ, a 0 * t ^ (K - negRatioCount a t K) ≤ a K := by
  intro K
  induction K with
  | zero => simp [negRatioCount]
  | succ K ih =>
    rw [negRatioCount_succ]
    have hcnt : negRatioCount a t K ≤ K := by
      unfold negRatioCount
      calc ((Finset.range K).filter (fun k => a (k + 1) ≤ t * a k)).card
          ≤ (Finset.range K).card := Finset.card_filter_le _ _
        _ = K := Finset.card_range K
    by_cases hp : a (K + 1) ≤ t * a K
    · rw [if_pos hp]
      have hexp : K + 1 - (negRatioCount a t K + 1) = K - negRatioCount a t K := by
        omega
      rw [hexp]
      exact le_trans ih (hmono K)
    · rw [if_neg hp]
      simp only [add_zero]
      have hlt : t * a K < a (K + 1) := lt_of_not_ge hp
      have hexp : K + 1 - negRatioCount a t K = (K - negRatioCount a t K) + 1 := by
        omega
      rw [hexp, pow_succ]
      have hstep : a 0 * (t ^ (K - negRatioCount a t K) * t) =
          t * (a 0 * t ^ (K - negRatioCount a t K)) := by ring
      rw [hstep]
      exact (lt_of_le_of_lt (mul_le_mul_of_nonneg_left ih (le_of_lt (lt_trans zero_lt_one ht))) hlt).le

/-- **Density from an eventual geometric upper bound.**  Let `a` be a positive
sequence (`a 0 > 0`), nondecreasing, eventually bounded above by `A * s ^ k`
with `A > 0` and `1 < s < t`.  Then for every `δ < 1 - log s / log t` the count
of indices `k < K` with `a (k + 1) ≤ t * a k` is eventually at least `δ * K`.

This is the counting engine: the product of the ratios along `[0, K)` is at
least `t ^ (K - cnt)`, while the endpoint is at most `A * s ^ K`; taking
logarithms and dividing by `log t > 0` yields `cnt ≥ (1 - log s / log t) * K -
(log A - log a 0)/log t`. -/
theorem eventually_card_negRatio_ge_of_geometric_upper
    (a : ℕ → ℝ) (A s t δ : ℝ)
    (ha0 : 0 < a 0) (hmono : ∀ k : ℕ, a k ≤ a (k + 1))
    (hs : 1 < s) (hst : s < t) (hA : 0 < A)
    (hupper : ∀ᶠ k : ℕ in atTop, a k ≤ A * s ^ k)
    (hδ : δ < 1 - Real.log s / Real.log t) :
    ∀ᶠ K : ℕ in atTop, δ * (K : ℝ) ≤ (negRatioCount a t K : ℝ) := by
  have ht : 1 < t := lt_trans hs hst
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hs0 : 0 < s := lt_trans zero_lt_one hs
  have hlogt : 0 < Real.log t := Real.log_pos ht
  have hls_lt : Real.log s < Real.log t := Real.log_lt_log hs0 hst
  have hδpos : 0 < 1 - Real.log s / Real.log t := by
    have : Real.log s / Real.log t < 1 := (div_lt_one hlogt).2 hls_lt
    linarith
  have hlow := geometric_lower_of_card_negRatio a t ht hmono
  obtain ⟨K1, hK1⟩ := eventually_atTop.mp hupper
  have hmain : ∀ᶠ K : ℕ in atTop,
      (1 - Real.log s / Real.log t) * (K : ℝ) - (Real.log A - Real.log (a 0)) / Real.log t
        ≤ (negRatioCount a t K : ℝ) := by
    filter_upwards [eventually_ge_atTop K1] with K hKle
    have hcnt : negRatioCount a t K ≤ K := by
      unfold negRatioCount
      calc ((Finset.range K).filter (fun k => a (k + 1) ≤ t * a k)).card
          ≤ (Finset.range K).card := Finset.card_filter_le _ _
        _ = K := Finset.card_range K
    have hchain : a 0 * t ^ (K - negRatioCount a t K) ≤ A * s ^ K :=
      le_trans (hlow K) (hK1 K hKle)
    have hcombined := Real.log_le_log (mul_pos ha0 (pow_pos ht0 _)) hchain
    rw [Real.log_mul (ne_of_gt ha0) (ne_of_gt (pow_pos ht0 _)), Real.log_pow,
      Real.log_mul (ne_of_gt hA) (ne_of_gt (pow_pos hs0 _)), Real.log_pow,
      Nat.cast_sub hcnt] at hcombined
    set lt := Real.log t
    set ls := Real.log s
    set Kk := (K : ℝ)
    set α := (negRatioCount a t K : ℝ)
    have hlt : 0 < lt := hlogt
    have hlogle' : Real.log (a 0) + (Kk - α) * lt ≤ Real.log A + Kk * ls := hcombined
    have hltX : lt * ((1 - ls / lt) * Kk - (Real.log A - Real.log (a 0)) / lt) =
        (Real.log (a 0) - Real.log A) + Kk * (lt - ls) := by
      field_simp [ne_of_gt hlt]
      ring
    have hltα : (Real.log (a 0) - Real.log A) + Kk * (lt - ls) ≤ lt * α := by
      nlinarith [hlogle']
    have : lt * ((1 - ls / lt) * Kk - (Real.log A - Real.log (a 0)) / lt) ≤ lt * α := by
      rw [hltX]; exact hltα
    exact le_of_mul_le_mul_left this hlt
  rcases lt_or_ge δ 0 with hδlt | hδge
  · filter_upwards [hmain] with K hK
    have h1 : δ * (K : ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hδlt.le (Nat.cast_nonneg K)
    have h2 : (0 : ℝ) ≤ (negRatioCount a t K : ℝ) := Nat.cast_nonneg _
    linarith
  · have hgap : 0 < (1 - Real.log s / Real.log t) - δ := by linarith
    set C : ℝ := (Real.log A - Real.log (a 0)) / Real.log t
    filter_upwards [hmain, eventually_ge_atTop (Nat.ceil (C / (1 - Real.log s / Real.log t - δ)) + 1)]
      with K hK hKge
    have hceil : C / (1 - Real.log s / Real.log t - δ) ≤ (K : ℝ) := by
      have h1 : (Nat.ceil (C / (1 - Real.log s / Real.log t - δ)) : ℝ) ≤ (K : ℝ) := by
        have : Nat.ceil (C / (1 - Real.log s / Real.log t - δ)) ≤ K := by omega
        exact_mod_cast this
      have h2 : C / (1 - Real.log s / Real.log t - δ) ≤
          (Nat.ceil (C / (1 - Real.log s / Real.log t - δ)) : ℝ) := Nat.le_ceil _
      linarith
    have hCK : C ≤ (1 - Real.log s / Real.log t - δ) * (K : ℝ) := by
      rw [div_le_iff₀ hgap] at hceil
      linarith
    linarith

/-! ## Roth-specific inputs -/

/-- **Strict bound on the Roth number.**  For `M ≥ 3` the Roth number is
strictly below `M`: if it equaled `M`, a maximal three-term-progression-free
subset of `range M` would exhaust `range M`, contradicting that `{0, 1, 2}` is
already a nontrivial three-term progression. -/
theorem rothNumberNat_lt_self_of_three_le {M : ℕ} (hM : 3 ≤ M) :
    rothNumberNat M < M := by
  rcases lt_or_eq_of_le (rothNumberNat_le M) with h | h
  · exact h
  · exfalso
    obtain ⟨t, htsub, htcard, htfree⟩ := rothNumberNat_spec M
    have hcard : t.card = (Finset.range M).card := by
      rw [htcard, h, Finset.card_range]
    have hteq : t = Finset.range M :=
      Finset.eq_of_subset_of_card_le htsub (le_of_eq hcard.symm)
    have hfree : ThreeAPFree ((Finset.range M : Finset ℕ) : Set ℕ) := hteq ▸ htfree
    have h0 : (0 : ℕ) ∈ ((Finset.range M : Finset ℕ) : Set ℕ) := by
      rw [Finset.mem_coe, Finset.mem_range]; omega
    have h1 : (1 : ℕ) ∈ ((Finset.range M : Finset ℕ) : Set ℕ) := by
      rw [Finset.mem_coe, Finset.mem_range]; omega
    have h2 : (2 : ℕ) ∈ ((Finset.range M : Finset ℕ) : Set ℕ) := by
      rw [Finset.mem_coe, Finset.mem_range]; omega
    have h01 : (0 : ℕ) = 1 := hfree h0 h1 h2 (by norm_num)
    omega

/-- **Positivity of the log-deficit at the tower base.**  For `M ≥ 3`,
`0 < rothLogDeficit M`, i.e. the Roth number is strictly below `M`, so the
quotient `M / r₃(M)` exceeds one. -/
theorem rothLogDeficit_pos_of_three_le {M : ℕ} (hM : 3 ≤ M) :
    0 < rothLogDeficit M := by
  have hlt := rothNumberNat_lt_self_of_three_le hM
  have h1 : 1 ≤ M := by omega
  have hrpos : (0 : ℝ) < (rothNumberNat M : ℝ) := rothNumberNat_pos_real h1
  rw [rothLogDeficit]
  apply Real.log_pos
  rw [one_lt_div hrpos]
  exact_mod_cast hlt

/-- **Monotonicity along the square tower.**  For `M ≥ 1`,
`rothLogDeficit (M ^ (2 ^ k)) ≤ rothLogDeficit (M ^ (2 ^ (k + 1)))`.  This is
`rothLogDeficit_mono_mul` at `q = N k`, together with `(N k) * (N k) = N (k+1)`. -/
theorem rothLogDeficit_iterated_square_mono (M k : ℕ) (hM : 1 ≤ M) :
    rothLogDeficit (M ^ (2 ^ k)) ≤ rothLogDeficit (M ^ (2 ^ (k + 1))) := by
  have hN : 1 ≤ M ^ (2 ^ k) := one_le_pow₀ hM
  have h := rothLogDeficit_mono_mul (N := M ^ (2 ^ k)) (q := M ^ (2 ^ k)) hN hN
  have hsq : (M ^ (2 ^ k)) * (M ^ (2 ^ k)) = M ^ (2 ^ (k + 1)) := by
    rw [← pow_two]
    symm
    rw [pow_succ, pow_mul]
  simpa only [hsq] using h

/-! ## The main density theorems -/

/-- **Unconditional positive-density negative square-defect theorem.**

Fix `M ≥ 3` and write `N k = M ^ (2 ^ k)`, `a k = rothLogDeficit (N k)` and
`X k = squareScaleDefect (N k) = a (k+1) - 2 * a k`.  For every `β` with
`0 < β < 2 - √2`, with `t = 2 - β > √2` and `δβ = 1 - log (√2) / log t > 0`,
and for every real `δ < δβ`, the negative defect inequality `X k ≤ -β * a k`
holds at least `δ * K` times among `k < K`, eventually in `K`:

`δ * K ≤ #{k < K : squareScaleDefect (N k) ≤ -β * rothLogDeficit (N k)}`.

The conclusion is the tower-index lower-density statement, expressed directly
as an eventual `ℝ`-valued cardinality bound and deliberately avoiding any
`liminf` API.  It is not the known frequent-only statement: it asserts a
positive fraction of all indices.  It says nothing about a density of the
integers `N`.

The proof instantiates the counting engine at `s = √2`, `t = 2 - β`, with
`a 0 = rothLogDeficit M > 0`, tower monotonicity, and the EHPS envelope
`eventually_rothLogDeficit_iterated_square_le`; the identified predicate is
reconciled with `squareScaleDefect` through
`squareScaleDefect_eq_rothLogDeficit_sub`. -/
theorem eventually_card_squareScaleDefect_le_neg_mul_rothLogDeficit
    (M : ℕ) (hM : 3 ≤ M) (β : ℝ) (hβ0 : 0 < β) (hβ : β < 2 - Real.sqrt 2)
    (δ : ℝ) (hδ : δ < 1 - Real.log (Real.sqrt 2) / Real.log (2 - β)) :
    ∀ᶠ K : ℕ in atTop,
      δ * (K : ℝ) ≤
        (((Finset.range K).filter (fun k =>
          squareScaleDefect (M ^ (2 ^ k)) ≤
            -β * rothLogDeficit (M ^ (2 ^ k)))).card : ℝ) := by
  have hM1 : 1 ≤ M := by omega
  have hs : (1 : ℝ) < Real.sqrt 2 := Real.one_lt_sqrt_two
  have hst : Real.sqrt 2 < 2 - β := by
    have := Real.sqrt_nonneg 2
    linarith
  have hA : 0 < (torusLeadingConstant + 1) * Real.sqrt (Real.log (M : ℝ)) := by
    have hc : (0 : ℝ) < torusLeadingConstant + 1 := by linarith [torusLeadingConstant_pos]
    have hl : (0 : ℝ) < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
    positivity
  have ha0 : 0 < rothLogDeficit (M ^ (2 ^ 0)) := by
    simpa using rothLogDeficit_pos_of_three_le hM
  have hmono : ∀ k : ℕ,
      rothLogDeficit (M ^ (2 ^ k)) ≤ rothLogDeficit (M ^ (2 ^ (k + 1))) :=
    fun k => rothLogDeficit_iterated_square_mono M k hM1
  have hgen := eventually_card_negRatio_ge_of_geometric_upper
    (fun k : ℕ => rothLogDeficit (M ^ (2 ^ k)))
    ((torusLeadingConstant + 1) * Real.sqrt (Real.log (M : ℝ))) (Real.sqrt 2) (2 - β) δ
    ha0 hmono hs hst hA (eventually_rothLogDeficit_iterated_square_le M hM) (by simpa using hδ)
  have hiff : ∀ k : ℕ,
      rothLogDeficit (M ^ (2 ^ (k + 1))) ≤ (2 - β) * rothLogDeficit (M ^ (2 ^ k)) ↔
        squareScaleDefect (M ^ (2 ^ k)) ≤ -β * rothLogDeficit (M ^ (2 ^ k)) := by
    intro k
    have hN : 1 ≤ M ^ (2 ^ k) := one_le_pow₀ hM1
    have hsq : (M ^ (2 ^ k)) ^ 2 = M ^ (2 ^ (k + 1)) := by
      symm
      rw [pow_succ, pow_mul]
    rw [squareScaleDefect_eq_rothLogDeficit_sub _ hN, hsq]
    constructor <;> intro hh <;> linarith
  have hcard_eq : ∀ K : ℕ,
      negRatioCount (fun k : ℕ => rothLogDeficit (M ^ (2 ^ k))) (2 - β) K =
        ((Finset.range K).filter (fun k =>
          squareScaleDefect (M ^ (2 ^ k)) ≤
            -β * rothLogDeficit (M ^ (2 ^ k)))).card := by
    intro K
    unfold negRatioCount
    rw [Finset.filter_congr (fun k _ => hiff k)]
  filter_upwards [hgen] with K hK
  rwa [hcard_eq K] at hK

/-- **Fixed-level specialization.**  Under the same hypotheses as the main
theorem, for every fixed threshold `H > 0` and every `δ < δβ`, eventually
`δ * K ≤ #{k < K : squareScaleDefect (N k) ≤ -H}`.

Since `tendsto_rothLogDeficit_atTop` forces `rothLogDeficit (N k) → ∞`, for all
but finitely many `k` one has `β * rothLogDeficit (N k) > H`, so the counted
negative-`β·a` indices are among the indices with defect `≤ -H`; the count then
loses at most a constant `K₀` of early indices, absorbed into the strict gap
`δ < δβ`. -/
theorem eventually_card_squareScaleDefect_le_neg_const
    (M : ℕ) (hM : 3 ≤ M) (H : ℝ) (_hH : 0 < H)
    (β : ℝ) (hβ0 : 0 < β) (hβ : β < 2 - Real.sqrt 2)
    (δ : ℝ) (hδ : δ < 1 - Real.log (Real.sqrt 2) / Real.log (2 - β)) :
    ∀ᶠ K : ℕ in atTop,
      δ * (K : ℝ) ≤
        (((Finset.range K).filter (fun k =>
          squareScaleDefect (M ^ (2 ^ k)) ≤ -H)).card : ℝ) := by
  have hM1 : 1 ≤ M := by omega
  obtain ⟨δ₁, hδδ₁, hδ₁⟩ :
      ∃ δ₁, δ < δ₁ ∧ δ₁ < 1 - Real.log (Real.sqrt 2) / Real.log (2 - β) :=
    ⟨(δ + (1 - Real.log (Real.sqrt 2) / Real.log (2 - β))) / 2,
      by linarith, by linarith⟩
  have hfirst :=
    eventually_card_squareScaleDefect_le_neg_mul_rothLogDeficit M hM β hβ0 hβ δ₁ hδ₁
  have htower : Tendsto (fun k : ℕ => M ^ (2 ^ k)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by omega : 1 < M)).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by omega : 1 < (2 : ℕ)))
  have hbig : ∀ᶠ k : ℕ in atTop, H / β < rothLogDeficit (M ^ (2 ^ k)) :=
    (tendsto_rothLogDeficit_atTop.comp htower).eventually (eventually_gt_atTop (H / β))
  obtain ⟨K0, hK0⟩ := eventually_atTop.mp hbig
  have hK0' : ∀ k : ℕ, K0 ≤ k → H < β * rothLogDeficit (M ^ (2 ^ k)) := by
    intro k hk
    have hk' := hK0 k hk
    rw [div_lt_iff₀ hβ0] at hk'
    linarith
  have hstep : ∀ K : ℕ,
      ((Finset.range K).filter (fun k =>
          squareScaleDefect (M ^ (2 ^ k)) ≤ -β * rothLogDeficit (M ^ (2 ^ k)))).card
        ≤ ((Finset.range K).filter (fun k =>
            squareScaleDefect (M ^ (2 ^ k)) ≤ -H)).card + K0 := by
    intro K
    have hsub : ((Finset.range K).filter (fun k =>
          squareScaleDefect (M ^ (2 ^ k)) ≤ -β * rothLogDeficit (M ^ (2 ^ k))))
        ⊆ ((Finset.range K).filter (fun k =>
            squareScaleDefect (M ^ (2 ^ k)) ≤ -H)) ∪ Finset.range K0 := by
      intro k hk
      rw [Finset.mem_filter, Finset.mem_range] at hk
      obtain ⟨hkK, hkle⟩ := hk
      rw [Finset.mem_union]
      by_cases hk0 : k < K0
      · exact Or.inr (Finset.mem_range.2 hk0)
      · refine Or.inl (Finset.mem_filter.2 ⟨Finset.mem_range.2 hkK, ?_⟩)
        have := hK0' k (by omega)
        linarith
    calc ((Finset.range K).filter (fun k =>
            squareScaleDefect (M ^ (2 ^ k)) ≤ -β * rothLogDeficit (M ^ (2 ^ k)))).card
        ≤ (((Finset.range K).filter (fun k =>
              squareScaleDefect (M ^ (2 ^ k)) ≤ -H)) ∪ Finset.range K0).card :=
          Finset.card_le_card hsub
      _ ≤ ((Finset.range K).filter (fun k =>
              squareScaleDefect (M ^ (2 ^ k)) ≤ -H)).card + (Finset.range K0).card :=
          Finset.card_union_le _ _
      _ = ((Finset.range K).filter (fun k =>
              squareScaleDefect (M ^ (2 ^ k)) ≤ -H)).card + K0 := by
          rw [Finset.card_range]
  have hgap : 0 < δ₁ - δ := by linarith
  filter_upwards [hfirst,
      eventually_ge_atTop (Nat.ceil ((K0 : ℝ) / (δ₁ - δ)) + 1)] with K hK hKge
  have hceil : (K0 : ℝ) / (δ₁ - δ) ≤ (K : ℝ) := by
    have h1 : (Nat.ceil ((K0 : ℝ) / (δ₁ - δ)) : ℝ) ≤ (K : ℝ) := by
      have : Nat.ceil ((K0 : ℝ) / (δ₁ - δ)) ≤ K := by omega
      exact_mod_cast this
    have h2 : (K0 : ℝ) / (δ₁ - δ) ≤ (Nat.ceil ((K0 : ℝ) / (δ₁ - δ)) : ℝ) := Nat.le_ceil _
    linarith
  have hK0le : (K0 : ℝ) ≤ (δ₁ - δ) * (K : ℝ) := by
    rw [div_le_iff₀ hgap] at hceil
    linarith
  have hstep' : ((Finset.range K).filter (fun k =>
        squareScaleDefect (M ^ (2 ^ k)) ≤ -β * rothLogDeficit (M ^ (2 ^ k)))).card
      ≤ ((Finset.range K).filter (fun k =>
          squareScaleDefect (M ^ (2 ^ k)) ≤ -H)).card + K0 := hstep K
  have hstepR : (((Finset.range K).filter (fun k =>
        squareScaleDefect (M ^ (2 ^ k)) ≤ -β * rothLogDeficit (M ^ (2 ^ k)))).card : ℝ)
      ≤ (((Finset.range K).filter (fun k =>
          squareScaleDefect (M ^ (2 ^ k)) ≤ -H)).card : ℝ) + (K0 : ℝ) := by
    exact_mod_cast hstep'
  linarith

/-! ## The endpoint consequence: half-density of nonpositive defects -/

/-- **Endpoint real lemma.**  For every real `δ < 1/2` there is an admissible
slope `β` with `0 < β < 2 - √2` for which the EHPS density
`δβ = 1 - log (√2) / log (2 - β)` already exceeds `δ`.

The point is the limit `δβ → 1/2` as `β ↓ 0`, which holds because
`2 - β → 2` and `log` is continuous at `2 ≠ 0`.  The proof makes the limit
argument concrete: writing `c = log (√2) / (1 - δ)`, one has `c < log 2`
exactly because `1 - δ > 1/2`, and continuity of `β ↦ log (2 - β)` at `0`
furnishes a positive radius on which `c < log (2 - β)`; a `β` inside that
radius and inside `(0, 2 - √2)` is then extracted.  No monotonicity or
derivative argument is required, and no `liminf` API is used. -/
theorem exists_beta_density_gt_of_lt_half (δ : ℝ) (hδ : δ < 1 / 2) :
    ∃ β : ℝ, 0 < β ∧ β < 2 - Real.sqrt 2 ∧
      δ < 1 - Real.log (Real.sqrt 2) / Real.log (2 - β) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogsqrt2 : Real.log (Real.sqrt 2) = Real.log 2 / 2 :=
    Real.log_sqrt (by norm_num)
  have h1δ : (1 : ℝ) / 2 < 1 - δ := by linarith
  have h1δpos : 0 < 1 - δ := by linarith
  have hc_lt : Real.log (Real.sqrt 2) / (1 - δ) < Real.log 2 := by
    rw [hlogsqrt2, div_lt_iff₀ h1δpos]
    nlinarith [hlog2, h1δ]
  have htend : Tendsto (fun β : ℝ => Real.log (2 - β)) (𝓝 0) (𝓝 (Real.log 2)) := by
    have h2 : Tendsto (fun β : ℝ => 2 - β) (𝓝 0) (𝓝 2) := by
      simpa using (tendsto_const_nhds.sub tendsto_id :
        Tendsto (fun β : ℝ => (2 : ℝ) - β) (𝓝 0) (𝓝 (2 - 0)))
    exact (Real.continuousAt_log (x := 2) (by norm_num)).tendsto.comp h2
  have hev : ∀ᶠ β in 𝓝 (0 : ℝ),
      Real.log (Real.sqrt 2) / (1 - δ) < Real.log (2 - β) :=
    htend.eventually (isOpen_Ioi.mem_nhds hc_lt)
  obtain ⟨ε, hεpos, hε⟩ := Metric.eventually_nhds_iff.mp hev
  have hsqrt2lt2 : Real.sqrt 2 < 2 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have hsq1 : (1 : ℝ) < Real.sqrt 2 := Real.one_lt_sqrt_two
  have hpos : 0 < (2 - Real.sqrt 2) / 2 := by linarith
  refine ⟨min (ε / 2) ((2 - Real.sqrt 2) / 2), lt_min (by linarith) hpos, ?_, ?_⟩
  · have hle : min (ε / 2) ((2 - Real.sqrt 2) / 2) ≤ (2 - Real.sqrt 2) / 2 :=
      min_le_right _ _
    linarith
  · set β := min (ε / 2) ((2 - Real.sqrt 2) / 2) with hβdef
    have hβltε : β < ε := by
      have : β ≤ ε / 2 := min_le_left _ _
      linarith
    have hβ2 : β < 2 - Real.sqrt 2 := by
      have : β ≤ (2 - Real.sqrt 2) / 2 := min_le_right _ _
      linarith
    have hdist : dist β 0 < ε := by
      rw [Real.dist_eq, sub_zero,
        abs_of_nonneg (le_of_lt (lt_min (by linarith) hpos))]
      exact hβltε
    have hlog := hε hdist
    have harg1 : 1 < 2 - β := by linarith
    have hlogpos : 0 < Real.log (2 - β) := Real.log_pos harg1
    have hstep : Real.log (Real.sqrt 2) / Real.log (2 - β) < 1 - δ := by
      rw [div_lt_iff₀ hlogpos]
      have hh := (div_lt_iff₀ h1δpos).mp hlog
      linarith
    linarith

/-- **Positivity of the log-deficit at every tower node.**  For `M ≥ 3` and
all `k`, `0 < rothLogDeficit (M ^ (2 ^ k))`; this is the input
`rothLogDeficit_pos_of_three_le` at the base together with tower monotonicity
`rothLogDeficit_iterated_square_mono`. -/
theorem rothLogDeficit_iterated_square_pos {M : ℕ} (hM : 3 ≤ M) (k : ℕ) :
    0 < rothLogDeficit (M ^ (2 ^ k)) := by
  have hM1 : 1 ≤ M := by omega
  induction k with
  | zero => simpa using rothLogDeficit_pos_of_three_le hM
  | succ k ih => exact lt_of_lt_of_le ih (rothLogDeficit_iterated_square_mono M k hM1)

/-- **Endpoint half-density theorem (strict version).**

Fix `M ≥ 3` and write `N k = M ^ (2 ^ k)`, `X k = squareScaleDefect (N k)`.
For every real `δ < 1/2` the strictly negative defect inequality `X k < 0`
holds at least `δ * K` times among `k < K`, eventually in `K`:

`∀ᶠ K, δ * K ≤ #{k < K : squareScaleDefect (N k) < 0}`.

This is the endpoint of the EHPS density curve and is the strongest of the
clean half-density statements, since `X k < 0` is strictly better than the
approved nonpositive alternative.  The proof picks an admissible `β` with
`0 < β < 2 - √2` and `δβ > δ` via `exists_beta_density_gt_of_lt_half` -- this
is the essential step, and it guarantees no fixed sub-`1/2` density is
being smuggled in -- and then uses the accepted counted theorem
`eventually_card_squareScaleDefect_le_neg_mul_rothLogDeficit`, whose counted
predicate `X k ≤ -β * rothLogDeficit (N k)` implies `X k < 0` because
`β > 0` and every tower log-deficit is positive.  Only a monotone `card_le_card`
vacuousness check separates the two filters.  Nothing is assumed about a density
of the integers `N`. -/
theorem eventually_card_squareScaleDefect_neg
    (M : ℕ) (hM : 3 ≤ M) (δ : ℝ) (hδ : δ < 1 / 2) :
    ∀ᶠ K : ℕ in atTop,
      δ * (K : ℝ) ≤
        (((Finset.range K).filter (fun k =>
          squareScaleDefect (M ^ (2 ^ k)) < 0)).card : ℝ) := by
  obtain ⟨β, hβ0, hβlt, hδβ⟩ := exists_beta_density_gt_of_lt_half δ hδ
  have hmain : ∀ᶠ K : ℕ in atTop, δ * (K : ℝ) ≤
      (((Finset.range K).filter (fun k =>
        squareScaleDefect (M ^ (2 ^ k)) ≤
          -β * rothLogDeficit (M ^ (2 ^ k)))).card : ℝ) :=
    eventually_card_squareScaleDefect_le_neg_mul_rothLogDeficit M hM β hβ0 hβlt δ hδβ
  filter_upwards [hmain] with K hK
  have hle : ((Finset.range K).filter (fun k =>
        squareScaleDefect (M ^ (2 ^ k)) ≤
          -β * rothLogDeficit (M ^ (2 ^ k)))).card ≤
      ((Finset.range K).filter (fun k =>
        squareScaleDefect (M ^ (2 ^ k)) < 0)).card :=
    Finset.card_le_card (fun k hk => by
      rw [Finset.mem_filter] at hk
      exact Finset.mem_filter.2 ⟨hk.1, by
        nlinarith [mul_pos hβ0 (rothLogDeficit_iterated_square_pos hM k), hk.2]⟩)
  exact le_trans hK (by exact_mod_cast hle)

/-- **Endpoint half-density theorem (nonpositive version).**

Under the same hypotheses, for every real `δ < 1/2`,
`∀ᶠ K, δ * K ≤ #{k < K : squareScaleDefect (N k) ≤ 0}`.

This is the external-free cardinal conclusion for the closed predicate: it
follows from the strict theorem by the inclusion
`{X < 0} ⊆ {X ≤ 0}` and needs no additional analytic input. -/
theorem eventually_card_squareScaleDefect_nonpos
    (M : ℕ) (hM : 3 ≤ M) (δ : ℝ) (hδ : δ < 1 / 2) :
    ∀ᶠ K : ℕ in atTop,
      δ * (K : ℝ) ≤
        (((Finset.range K).filter (fun k =>
          squareScaleDefect (M ^ (2 ^ k)) ≤ 0)).card : ℝ) := by
  refine (eventually_card_squareScaleDefect_neg M hM δ hδ).mono ?_
  intro K hK
  have hle : ((Finset.range K).filter (fun k =>
        squareScaleDefect (M ^ (2 ^ k)) < 0)).card ≤
      ((Finset.range K).filter (fun k =>
        squareScaleDefect (M ^ (2 ^ k)) ≤ 0)).card :=
    Finset.card_le_card (fun k hk => by
      rw [Finset.mem_filter] at hk
      exact Finset.mem_filter.2 ⟨hk.1, le_of_lt hk.2⟩)
  exact le_trans hK (by exact_mod_cast hle)

/-! ## Non-vacuity and ground-truth checks -/

/-- The admissible-`β` region is nonempty: `β = 1/2` satisfies
`0 < β < 2 - √2`. -/
example : (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 2 - Real.sqrt 2 := by
  have hsq : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hnn : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  constructor
  · norm_num
  · nlinarith

/-- Non-vacuity of the generic counting engine: the constant sequence
`a ≡ 1`, with `s = 2`, `t = 4`, `A = 1` and `δ = 1/4`, satisfies every
hypothesis, and every ratio equals `1 ≤ 4`, so the counted set is all of
`range K`. -/
example : ∀ᶠ K : ℕ in atTop,
      ((1 : ℝ) / 4) * (K : ℝ) ≤
        (negRatioCount (fun _ : ℕ => (1 : ℝ)) 4 K : ℝ) := by
  refine eventually_card_negRatio_ge_of_geometric_upper
    (fun _ : ℕ => (1 : ℝ)) 1 2 4 (1 / 4)
    (by norm_num) (fun _ => le_rfl) (by norm_num) (by norm_num) (by norm_num)
    (Filter.Eventually.of_forall (fun k => by
      rw [one_mul]
      exact one_le_pow₀ (by norm_num))) ?_
  have hlog4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  have h16 : Real.log 2 / Real.log 4 < 3 / 4 := by
    rw [div_lt_iff₀ hlog4]
    have hkey : Real.log ((2 : ℝ) ^ 4) < Real.log ((4 : ℝ) ^ 3) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow, Real.log_pow] at hkey
    norm_num at hkey
    linarith
  linarith

/-- The hypotheses of the main density theorem are jointly satisfiable:
`β = 1/2` lies in `(0, 2 - √2)` and `δβ = 1 - log (√2) / log (3/2) > 0`, so the
conclusion is a genuine lower-density statement about the concrete tower rather
than a vacuous one. -/
example : ∃ β : ℝ, 0 < β ∧ β < 2 - Real.sqrt 2 ∧
    (0 : ℝ) < 1 - Real.log (Real.sqrt 2) / Real.log (2 - β) := by
  refine ⟨1 / 2, by norm_num, ?_, ?_⟩
  · have hsq : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    have hnn : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    nlinarith
  · have hsqrt2lt : Real.sqrt 2 < 3 / 2 := by
      have hsq : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
      have hnn : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
      nlinarith
    have hnum : Real.log (Real.sqrt 2) < Real.log (3 / 2) :=
      Real.log_lt_log (Real.sqrt_pos.2 (by norm_num)) hsqrt2lt
    have hlt1 : Real.log (Real.sqrt 2) / Real.log (3 / 2) < 1 :=
      (div_lt_one (Real.log_pos (by norm_num))).2 hnum
    have h2b : (2 : ℝ) - 1 / 2 = 3 / 2 := by norm_num
    rw [h2b]
    linarith

/-- Non-vacuity with `δ > 0`: at `δ = 1/4` and every `M ≥ 3` the strict
endpoint conclusion holds, so the half-density theorem is not a statement about
the zero density. -/
example (M : ℕ) (hM : 3 ≤ M) :
    ∀ᶠ K : ℕ in atTop,
      ((1 : ℝ) / 4) * (K : ℝ) ≤
        (((Finset.range K).filter (fun k =>
          squareScaleDefect (M ^ (2 ^ k)) < 0)).card : ℝ) :=
  eventually_card_squareScaleDefect_neg M hM (1 / 4) (by norm_num)

/-- The endpoint real lemma is non-vacuous at a concrete positive `δ`: for
`δ = 1/3` there exists an admissible `β` whose EHPS density exceeds `1/3`. -/
example : ∃ β : ℝ, 0 < β ∧ β < 2 - Real.sqrt 2 ∧
    (1 / 3 : ℝ) < 1 - Real.log (Real.sqrt 2) / Real.log (2 - β) :=
  exists_beta_density_gt_of_lt_half (1 / 3) (by norm_num)



end

end Erdos142