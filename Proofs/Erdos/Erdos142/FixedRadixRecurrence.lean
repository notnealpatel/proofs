/-
  Erdős Problem #142 — two-sided recurrent fixed-right-factor threshold
  inequalities for the product defect, and rigidity of any finite limit.

  `FixedRadixDefect.exists_fixed_right_defect_gt` shows, for a generic sequence
  `lam` and defect `D` satisfying the exact identity

      `D N M = lam N + lam M - lam (N * (2 * M - 1)) + log ((2 * M - 1) / M)`

  together with the sub-logarithmic limit `lam N / log N → 0`, that every
  `B` below the threshold `T_M = lam M + log ((2 * M - 1) / M)` is exceeded by
  `D N M` for *some* `N ≥ 1`.  This file strengthens that existential statement
  to a *frequently* one and proves the matching upper-threshold statement.

  The three generic targets are:

  * `frequently_fixed_right_defect_gt`: for every `B < T_M` the inequality
    `B < D N M` holds for `N` arbitrarily large, i.e. `∃ᶠ N in atTop, B < D N M`.
    No value of `lam` at `1` is assumed.  The route is by contradiction from an
    eventual bound `D N M ≤ B`: on the eventual tail the identity turns the bound
    into the affine increment `lam (N * q) ≥ lam N + c` along the radix
    `q = 2 * M - 1`, with `c = T_M - B > 0`.  Iterating from `q ^ K` beyond the
    cutoff gives `lam (q ^ (K + k)) ≥ lam (q ^ K) + k * c`; dividing by
    `log (q ^ (K + k)) = (K + k) log q`, the constant contribution of `lam (q ^ K)`
    vanishes as `k → ∞`, leaving a positive lower bound `c / log q` for the ratio
    `lam (q ^ (K + k)) / log (q ^ (K + k))`, contradicting `lam N / log N → 0`
    along the subsequence of `q`-powers.

  * `frequently_fixed_right_defect_lt`: with the additional sign hypothesis
    `0 ≤ lam N` for `N ≥ 1` and *no* sub-logarithmic limit, for every `T_M < B`
    the inequality `D N M < B` holds for `N` arbitrarily large.  An eventual
    reverse bound `B ≤ D N M` now forces the *decreasing* increment
    `lam (N * q) ≤ lam N - c` with `c = B - T_M > 0`; iterating beyond the cutoff
    drives `lam` negative, contradicting nonnegativity.

  * `tendsto_fixed_right_defect_eq_threshold`: if in addition
    `D N M → L` for a finite real `L`, then `L = T_M`.  The two recurrent
    inequalities pin `L` from below and above by a midpoint argument.

  The Roth instantiations `frequently_fixed_right_rothProductDefect_gt`,
  `frequently_fixed_right_rothProductDefect_lt`, and
  `tendsto_fixed_right_rothProductDefect_eq_threshold` feed these with
  `lam = rothLogDeficit`, `D = rothProductDefect`, the exact identity
  `rothProductDefect_eq_rothLogDeficit`, the unconditional limit
  `tendsto_rothLogDeficit_div_log_zero`, and the nonnegativity of the deficit
  coming from `rothNumberNat N ≤ N`.

  What this does and does not say.  These are two-sided *recurrent* threshold
  inequalities together with a rigidity statement for a *finite* limit: the
  values of `D (·, M)` return arbitrarily often above every level below `T_M`
  and below every level above `T_M`, and any limit that exists must equal `T_M`.
  They do *not* prove that `D (·, M)` converges, that it oscillates essentially,
  or that `limsup_N D N M = T_M` or `liminf_N D N M = T_M`; a constant threshold
  model such as `lam ≡ 0`, `D N M = log ((2 * M - 1) / M)`, in which the defect
  equals `T_M` for every `N`, remains consistent with all hypotheses.  In
  particular nothing here resolves Erdős #142.

  No `sorry`, no `unsafe`, no new axioms, and no existing declaration is edited.
-/

import Erdos.Erdos142.FixedRadixDefect

set_option autoImplicit false

open Filter
open scoped Topology

namespace Erdos142

noncomputable section

/-- **Frequently-exceeded fixed-right-factor threshold (generic).**  Let
`lam : ℕ → ℝ` and `D : ℕ → ℕ → ℝ` satisfy the exact identity

`D N M = lam N + lam M - lam (N * (2 * M - 1)) + log ((2 * M - 1) / M)`

on positive inputs, and let `lam N / log N → 0`.  Then for every fixed `M ≥ 2`
and every real `B` below the threshold `T_M = lam M + log ((2 * M - 1) / M)`
the inequality `B < D N M` holds for `N` arbitrarily large:

`∃ᶠ N : ℕ in atTop, B < D N M`.

No value of `lam` at `1` is required.  Route: assume `D N M ≤ B` on the tail
`N ≥ K`; with `q = 2 * M - 1 ≥ 3` and `c = T_M - B > 0` the identity gives
`lam (N * q) ≥ lam N + c` for `N ≥ K`.  Iterating from `N₀ = q ^ K` yields
`lam (q ^ (K + k)) ≥ lam (q ^ K) + k * c`, and dividing by
`log (q ^ (K + k)) = (K + k) log q` shows the ratios
`lam (q ^ (K + k)) / log (q ^ (K + k))` are eventually bounded below by
`c / (2 log q) > 0`, contradicting the limit `lam N / log N → 0` along the
subsequence of `q`-powers.  This is threshold saturation, not convergence: it
does not assert that `D (·, M)` is unbounded in `N`. -/
theorem frequently_fixed_right_defect_gt
    (lam : ℕ → ℝ) (D : ℕ → ℕ → ℝ)
    (hid : ∀ N M : ℕ, 1 ≤ N → 1 ≤ M →
      D N M = lam N + lam M - lam (N * (2 * M - 1)) +
        Real.log (((2 * M - 1 : ℕ) : ℝ) / (M : ℝ)))
    (hsub : Tendsto (fun N : ℕ => lam N / Real.log (N : ℝ)) atTop (𝓝 0))
    {M : ℕ} (hM : 2 ≤ M) {B : ℝ}
    (hB : B < lam M + Real.log (((2 * M - 1 : ℕ) : ℝ) / (M : ℝ))) :
    ∃ᶠ N : ℕ in atTop, B < D N M := by
  rw [Filter.Frequently]
  intro hcon
  set q : ℕ := 2 * M - 1 with hq
  have hM1 : 1 ≤ M := by omega
  have hq1 : 1 < q := by omega
  have hle : ∀ᶠ N : ℕ in atTop, D N M ≤ B := hcon.mono fun N h => le_of_not_gt h
  obtain ⟨K, hK⟩ := eventually_atTop.mp hle
  let K₀ : ℕ := max K 1
  have hK₀1 : 1 ≤ K₀ := le_max_right K 1
  have hK₀ : ∀ N : ℕ, K₀ ≤ N → D N M ≤ B := fun N hN =>
    hK N (le_trans (le_max_left K 1) hN)
  set c : ℝ := lam M + Real.log ((q : ℝ) / (M : ℝ)) - B with hc
  have hcpos : 0 < c := by rw [hc]; linarith
  have hstep : ∀ N : ℕ, K₀ ≤ N → lam N + c ≤ lam (N * q) := by
    intro N hN
    have hD := hK₀ N hN
    have hidN := hid N M (by omega) hM1
    rw [hc]
    linarith
  have hbase : K₀ ≤ q ^ K₀ := by
    have h2 : 2 ≤ q := by omega
    calc K₀ ≤ 2 ^ K₀ := le_of_lt Nat.lt_two_pow_self
      _ ≤ q ^ K₀ := Nat.pow_le_pow_left h2 K₀
  have hiter : ∀ k : ℕ, lam (q ^ K₀) + (k : ℝ) * c ≤ lam (q ^ (K₀ + k)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hNK : K₀ ≤ q ^ (K₀ + k) :=
        hbase.trans (Nat.pow_le_pow_right (by omega : 0 < q) (Nat.le_add_right K₀ k))
      have hs := hstep (q ^ (K₀ + k)) hNK
      have hpow : q ^ (K₀ + k) * q = q ^ (K₀ + (k + 1)) := by
        rw [← pow_succ]
        congr 1
      rw [hpow] at hs
      have hcast : ((k + 1 : ℕ) : ℝ) * c = (k : ℝ) * c + c := by push_cast; ring
      linarith [ih, hs, hcast]
  set a : ℝ := lam (q ^ K₀) with ha
  have hpow_tendsto : Tendsto (fun k : ℕ => q ^ (K₀ + k)) atTop atTop := by
    simpa [Function.comp_def, Nat.add_comm] using
      (tendsto_pow_atTop_atTop_of_one_lt hq1).comp (tendsto_add_atTop_nat K₀)
  have hlim_sub : Tendsto (fun k : ℕ =>
      lam (q ^ (K₀ + k)) / Real.log (((q ^ (K₀ + k) : ℕ) : ℝ))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using hsub.comp hpow_tendsto
  have hLpos : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq1)
  have hev : ∀ᶠ k : ℕ in atTop,
      c / (2 * Real.log (q : ℝ)) ≤
        lam (q ^ (K₀ + k)) / Real.log (((q ^ (K₀ + k) : ℕ) : ℝ)) := by
    refine eventually_atTop.mpr ⟨max K₀ ⌈(c * (K₀ : ℝ) - 2 * a) / c⌉₊, fun k hk => ?_⟩
    have hkceil : (c * (K₀ : ℝ) - 2 * a) / c ≤ (k : ℝ) :=
      le_trans (Nat.le_ceil _)
        (by exact_mod_cast (le_trans (le_max_right K₀ _) hk))
    have hkey : c * (K₀ : ℝ) - 2 * a ≤ (k : ℝ) * c := (div_le_iff₀ hcpos).mp hkceil
    have hDpos : 0 < ((K₀ : ℝ) + k) * Real.log (q : ℝ) := by
      have hK0r : (1 : ℝ) ≤ (K₀ : ℝ) := by exact_mod_cast hK₀1
      have hkr : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      exact mul_pos (by linarith) hLpos
    have hlog : Real.log (((q ^ (K₀ + k) : ℕ) : ℝ)) =
        ((K₀ : ℝ) + k) * Real.log (q : ℝ) := by
      rw [Nat.cast_pow, Real.log_pow]
      push_cast
      ring
    have hratio : c / (2 * Real.log (q : ℝ)) ≤
        (a + (k : ℝ) * c) / (((K₀ : ℝ) + k) * Real.log (q : ℝ)) := by
      rw [div_le_div_iff₀ (by linarith [hLpos] : (0 : ℝ) < 2 * Real.log (q : ℝ)) hDpos]
      have h2 : c * (((K₀ : ℝ) + k) * Real.log (q : ℝ)) ≤
          (a + (k : ℝ) * c) * (2 * Real.log (q : ℝ)) := by
        nlinarith [hkey, hLpos]
      exact h2
    calc c / (2 * Real.log (q : ℝ))
        ≤ (a + (k : ℝ) * c) / (((K₀ : ℝ) + k) * Real.log (q : ℝ)) := hratio
      _ ≤ lam (q ^ (K₀ + k)) / (((K₀ : ℝ) + k) * Real.log (q : ℝ)) :=
          div_le_div_of_nonneg_right (hiter k) hDpos.le
      _ = lam (q ^ (K₀ + k)) / Real.log (((q ^ (K₀ + k) : ℕ) : ℝ)) := by rw [hlog]
  have hle0 : c / (2 * Real.log (q : ℝ)) ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim_sub hev
  have hpos : 0 < c / (2 * Real.log (q : ℝ)) := div_pos hcpos (by linarith [hLpos])
  linarith

/-- **Frequently-undershot fixed-right-factor threshold (generic).**  Let
`lam : ℕ → ℝ` be nonnegative on positive inputs and let `D : ℕ → ℕ → ℝ` satisfy
the exact identity

`D N M = lam N + lam M - lam (N * (2 * M - 1)) + log ((2 * M - 1) / M)`

on positive inputs.  Then for every fixed `M ≥ 2` and every real `B` above the
threshold `T_M = lam M + log ((2 * M - 1) / M)` the inequality `D N M < B`
holds for `N` arbitrarily large: `∃ᶠ N : ℕ in atTop, D N M < B`.

No sub-logarithmic limit is needed.  Route: assume `B ≤ D N M` on the tail
`N ≥ K`; with `q = 2 * M - 1` and `c = B - T_M > 0` the identity gives
`lam (N * q) ≤ lam N - c` for `N ≥ K`.  Iterating from `N₀ = q ^ K` gives
`lam (q ^ (K + k)) ≤ lam (q ^ K) - k * c`, which is negative for `k` large,
contradicting `0 ≤ lam (q ^ (K + k))`.  This is an arbitrarily-late undershoot,
not convergence: it does not assert that `D (·, M)` tends to `T_M`. -/
theorem frequently_fixed_right_defect_lt
    (lam : ℕ → ℝ) (D : ℕ → ℕ → ℝ)
    (hnonneg : ∀ N : ℕ, 1 ≤ N → 0 ≤ lam N)
    (hid : ∀ N M : ℕ, 1 ≤ N → 1 ≤ M →
      D N M = lam N + lam M - lam (N * (2 * M - 1)) +
        Real.log (((2 * M - 1 : ℕ) : ℝ) / (M : ℝ)))
    {M : ℕ} (hM : 2 ≤ M) {B : ℝ}
    (hB : lam M + Real.log (((2 * M - 1 : ℕ) : ℝ) / (M : ℝ)) < B) :
    ∃ᶠ N : ℕ in atTop, D N M < B := by
  rw [Filter.Frequently]
  intro hcon
  set q : ℕ := 2 * M - 1 with hq
  have hM1 : 1 ≤ M := by omega
  have hq1 : 1 < q := by omega
  have hge : ∀ᶠ N : ℕ in atTop, B ≤ D N M := hcon.mono fun N h => le_of_not_gt h
  obtain ⟨K, hK⟩ := eventually_atTop.mp hge
  let K₀ : ℕ := max K 1
  have hK₀1 : 1 ≤ K₀ := le_max_right K 1
  have hK₀ : ∀ N : ℕ, K₀ ≤ N → B ≤ D N M := fun N hN =>
    hK N (le_trans (le_max_left K 1) hN)
  set c : ℝ := B - (lam M + Real.log ((q : ℝ) / (M : ℝ))) with hc
  have hcpos : 0 < c := by rw [hc]; linarith
  have hstep : ∀ N : ℕ, K₀ ≤ N → lam (N * q) ≤ lam N - c := by
    intro N hN
    have hD := hK₀ N hN
    have hidN := hid N M (by omega) hM1
    rw [hc]
    linarith
  have hbase : K₀ ≤ q ^ K₀ := by
    have h2 : 2 ≤ q := by omega
    calc K₀ ≤ 2 ^ K₀ := le_of_lt Nat.lt_two_pow_self
      _ ≤ q ^ K₀ := Nat.pow_le_pow_left h2 K₀
  have hiter : ∀ k : ℕ, lam (q ^ (K₀ + k)) ≤ lam (q ^ K₀) - (k : ℝ) * c := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hNK : K₀ ≤ q ^ (K₀ + k) :=
        hbase.trans (Nat.pow_le_pow_right (by omega : 0 < q) (Nat.le_add_right K₀ k))
      have hs := hstep (q ^ (K₀ + k)) hNK
      have hpow : q ^ (K₀ + k) * q = q ^ (K₀ + (k + 1)) := by
        rw [← pow_succ]
        congr 1
      rw [hpow] at hs
      have hcast : ((k + 1 : ℕ) : ℝ) * c = (k : ℝ) * c + c := by push_cast; ring
      linarith [ih, hs, hcast]
  obtain ⟨k, hk⟩ := exists_nat_gt (lam (q ^ K₀) / c)
  have hkc : lam (q ^ K₀) < (k : ℝ) * c := by
    have h := (div_lt_iff₀ hcpos).mp hk
    linarith
  have hneg : lam (q ^ (K₀ + k)) < 0 := by
    have h := hiter k
    linarith
  have hge0 : 0 ≤ lam (q ^ (K₀ + k)) := hnonneg _ (Nat.one_le_pow _ q (by omega))
  linarith

/-- **Limit rigidity at the fixed-right-factor threshold (generic).**  Under the
exact identity, the nonnegativity of `lam` on positive inputs, and the
sub-logarithmic limit `lam N / log N → 0`, if `D N M` converges to a finite real
`L` then necessarily

`L = lam M + log ((2 * M - 1) / M)`.

Route: `frequently_fixed_right_defect_gt` gives `B ≤ L` for every `B` below the
threshold, and `frequently_fixed_right_defect_lt` gives `L ≤ B` for every `B`
above it; the two bounds are reconciled by a midpoint contradiction.  This
characterizes any limit that exists; it does *not* prove that the limit exists
and does not assert equality of `limsup` or `liminf` with the threshold. -/
theorem tendsto_fixed_right_defect_eq_threshold
    (lam : ℕ → ℝ) (D : ℕ → ℕ → ℝ)
    (hnonneg : ∀ N : ℕ, 1 ≤ N → 0 ≤ lam N)
    (hid : ∀ N M : ℕ, 1 ≤ N → 1 ≤ M →
      D N M = lam N + lam M - lam (N * (2 * M - 1)) +
        Real.log (((2 * M - 1 : ℕ) : ℝ) / (M : ℝ)))
    (hsub : Tendsto (fun N : ℕ => lam N / Real.log (N : ℝ)) atTop (𝓝 0))
    {M : ℕ} (hM : 2 ≤ M) {L : ℝ}
    (hD : Tendsto (fun N : ℕ => D N M) atTop (𝓝 L)) :
    L = lam M + Real.log (((2 * M - 1 : ℕ) : ℝ) / (M : ℝ)) := by
  have hA : ∀ B : ℝ, B < lam M + Real.log (((2 * M - 1 : ℕ) : ℝ) / (M : ℝ)) →
      ∃ᶠ N : ℕ in atTop, B < D N M := by
    intro B hB
    exact frequently_fixed_right_defect_gt lam D hid hsub hM hB
  have hB' : ∀ B : ℝ, lam M + Real.log (((2 * M - 1 : ℕ) : ℝ) / (M : ℝ)) < B →
      ∃ᶠ N : ℕ in atTop, D N M < B := by
    intro B hB
    exact frequently_fixed_right_defect_lt lam D hnonneg hid hM hB
  have hTL : lam M + Real.log (((2 * M - 1 : ℕ) : ℝ) / (M : ℝ)) ≤ L := by
    by_contra h
    push Not at h
    set B : ℝ := (L + (lam M + Real.log (((2 * M - 1 : ℕ) : ℝ) / (M : ℝ)))) / 2 with hBdef
    have h1 : L < B := by rw [hBdef]; linarith
    have h2 : B < lam M + Real.log (((2 * M - 1 : ℕ) : ℝ) / (M : ℝ)) := by
      rw [hBdef]; linarith
    have hev : ∀ᶠ N : ℕ in atTop, D N M < B := hD.eventually (Iio_mem_nhds h1)
    exact (hA B h2) (hev.mono fun N hlt => not_lt_of_ge (le_of_lt hlt))
  have hLT : L ≤ lam M + Real.log (((2 * M - 1 : ℕ) : ℝ) / (M : ℝ)) := by
    by_contra h
    push Not at h
    set B : ℝ := ((lam M + Real.log (((2 * M - 1 : ℕ) : ℝ) / (M : ℝ))) + L) / 2 with hBdef
    have h1 : lam M + Real.log (((2 * M - 1 : ℕ) : ℝ) / (M : ℝ)) < B := by
      rw [hBdef]; linarith
    have h2 : B < L := by rw [hBdef]; linarith
    have hev : ∀ᶠ N : ℕ in atTop, B < D N M := hD.eventually (Ioi_mem_nhds h2)
    exact (hB' B h1) (hev.mono fun N hlt => not_lt_of_ge (le_of_lt hlt))
  linarith

/-- **Nonnegativity of the Roth log-deficit.**  For `N ≥ 1`,
`0 ≤ rothLogDeficit N`.  This follows from the trivial bound
`rothNumberNat N ≤ N` together with `rothNumberNat N ≥ 1`, which give
`N / rothNumberNat N ≥ 1`, hence `log (N / rothNumberNat N) ≥ 0`. -/
theorem rothLogDeficit_nonneg {N : ℕ} (hN : 1 ≤ N) : 0 ≤ rothLogDeficit N := by
  have hrnN : rothNumberNat N ≤ N := rothNumberNat_le N
  have hrn1 : 1 ≤ rothNumberNat N := one_le_rothNumberNat hN
  have hpos : (0 : ℝ) < (rothNumberNat N : ℝ) := by
    exact_mod_cast (by omega : 0 < rothNumberNat N)
  have h1 : (1 : ℝ) ≤ (N : ℝ) / (rothNumberNat N : ℝ) := by
    rw [le_div_iff₀ hpos]
    simpa using (show (rothNumberNat N : ℝ) ≤ (N : ℝ) from by exact_mod_cast hrnN)
  rw [rothLogDeficit]
  exact Real.log_nonneg h1

/-- **Frequently-exceeded fixed-right-factor threshold for the Roth product
defect.**  For every fixed `M ≥ 2` and every real `B` below
`T_M = rothLogDeficit M + log ((2 * M - 1) / M)` the inequality
`B < rothProductDefect N M` holds for `N` arbitrarily large:
`∃ᶠ N : ℕ in atTop, B < rothProductDefect N M`.

This instantiates `frequently_fixed_right_defect_gt` with `lam = rothLogDeficit`
and `D = rothProductDefect` via `rothProductDefect_eq_rothLogDeficit` and the
unconditional limit `tendsto_rothLogDeficit_div_log_zero`.  It does not prove
that `rothProductDefect (·, M)` is unbounded in `N`, that the supremum equals or
attains `T_M`, or that the defect oscillates, and it does not resolve Erdős
#142. -/
theorem frequently_fixed_right_rothProductDefect_gt
    {M : ℕ} (hM : 2 ≤ M) {B : ℝ}
    (hB : B < rothLogDeficit M + Real.log (((2 * M - 1 : ℕ) : ℝ) / (M : ℝ))) :
    ∃ᶠ N : ℕ in atTop, B < rothProductDefect N M :=
  frequently_fixed_right_defect_gt rothLogDeficit rothProductDefect
    (fun _ _ hN hM => rothProductDefect_eq_rothLogDeficit hN hM)
    tendsto_rothLogDeficit_div_log_zero hM hB

/-- **Frequently-undershot fixed-right-factor threshold for the Roth product
defect.**  For every fixed `M ≥ 2` and every real `B` above
`T_M = rothLogDeficit M + log ((2 * M - 1) / M)` the inequality
`rothProductDefect N M < B` holds for `N` arbitrarily large:
`∃ᶠ N : ℕ in atTop, rothProductDefect N M < B`.

This instantiates `frequently_fixed_right_defect_lt` with `lam = rothLogDeficit`
and `D = rothProductDefect`, using the nonnegativity `rothLogDeficit_nonneg`.
No sub-logarithmic limit is used.  It does not prove convergence or oscillation
of `rothProductDefect (·, M)` and does not resolve Erdős #142. -/
theorem frequently_fixed_right_rothProductDefect_lt
    {M : ℕ} (hM : 2 ≤ M) {B : ℝ}
    (hB : rothLogDeficit M + Real.log (((2 * M - 1 : ℕ) : ℝ) / (M : ℝ)) < B) :
    ∃ᶠ N : ℕ in atTop, rothProductDefect N M < B :=
  frequently_fixed_right_defect_lt rothLogDeficit rothProductDefect
    (fun _ hN => rothLogDeficit_nonneg hN)
    (fun _ _ hN hM => rothProductDefect_eq_rothLogDeficit hN hM)
    hM hB

/-- **Limit rigidity at the Roth fixed-right-factor threshold.**  If for fixed
`M ≥ 2` the Roth product defect `rothProductDefect N M` converges to a finite
real `L` as `N → ∞`, then
`L = rothLogDeficit M + log ((2 * M - 1) / M)`.

This instantiates `tendsto_fixed_right_defect_eq_threshold`.  It characterizes
any limit that exists; it does *not* prove that a limit exists, does not assert
equality of `limsup` or `liminf` with the threshold, and does not resolve
Erdős #142. -/
theorem tendsto_fixed_right_rothProductDefect_eq_threshold
    {M : ℕ} (hM : 2 ≤ M) {L : ℝ}
    (hD : Tendsto (fun N : ℕ => rothProductDefect N M) atTop (𝓝 L)) :
    L = rothLogDeficit M + Real.log (((2 * M - 1 : ℕ) : ℝ) / (M : ℝ)) :=
  tendsto_fixed_right_defect_eq_threshold rothLogDeficit rothProductDefect
    (fun _ hN => rothLogDeficit_nonneg hN)
    (fun _ _ hN hM => rothProductDefect_eq_rothLogDeficit hN hM)
    tendsto_rothLogDeficit_div_log_zero hM hD

/-- **Satisfiability of the generic hypotheses (constant threshold model).**
With `lam ≡ 0` and `D N M = log ((2 * M - 1) / M)` all hypotheses of
`frequently_fixed_right_defect_gt` hold jointly; the conclusion is the true
statement `∃ᶠ N, 0 < log (3 / 2)`.  This witnesses non-vacuity of Target A and
exhibits the constant threshold model in which the defect equals `T_M` for every
`N`, consistent with the docstring's claim that convergence is not proved. -/
example : ∃ᶠ _ : ℕ in atTop, (0 : ℝ) <
    Real.log (((2 * 2 - 1 : ℕ) : ℝ) / (2 : ℝ)) :=
  frequently_fixed_right_defect_gt (lam := fun _ => 0)
    (D := fun _ M => Real.log (((2 * M - 1 : ℕ) : ℝ) / (M : ℝ)))
    (fun _ _ _ _ => by ring)
    (by simpa only [zero_div] using tendsto_const_nhds)
    (M := 2) (by norm_num) (B := 0)
    (by
      have h : (1 : ℝ) < (((2 * 2 - 1 : ℕ) : ℝ)) / (2 : ℝ) := by norm_num
      simpa using Real.log_pos h)

/-- **Satisfiability of the limit-rigidity hypotheses.**  In the same constant
model, `D (·, 2) ≡ log (3 / 2)` converges, and
`tendsto_fixed_right_defect_eq_threshold` identifies its limit with the
threshold.  This witnesses non-vacuity of Target C. -/
example : Real.log (((2 * 2 - 1 : ℕ) : ℝ) / (2 : ℝ)) =
    (0 : ℝ) + Real.log (((2 * 2 - 1 : ℕ) : ℝ) / (2 : ℝ)) :=
  tendsto_fixed_right_defect_eq_threshold (lam := fun _ => 0)
    (D := fun _ M => Real.log (((2 * M - 1 : ℕ) : ℝ) / (M : ℝ)))
    (fun _ _ => le_refl 0)
    (fun _ _ _ _ => by ring)
    (by simpa only [zero_div] using tendsto_const_nhds)
    (M := 2) (by norm_num)
    (L := Real.log (((2 * 2 - 1 : ℕ) : ℝ) / (2 : ℝ)))
    tendsto_const_nhds

end

end Erdos142

-- Axiom audit for the load-bearing declarations.
#print axioms Erdos142.frequently_fixed_right_defect_gt
#print axioms Erdos142.frequently_fixed_right_defect_lt
#print axioms Erdos142.tendsto_fixed_right_defect_eq_threshold
#print axioms Erdos142.rothLogDeficit_nonneg
#print axioms Erdos142.frequently_fixed_right_rothProductDefect_gt
#print axioms Erdos142.frequently_fixed_right_rothProductDefect_lt
#print axioms Erdos142.tendsto_fixed_right_rothProductDefect_eq_threshold