/-
  Erdős Problem #142 — exclusion of finite wrong odd-scale ratios for
  asymptotic comparison functions.

  Fix `M ≥ 2` and write `q = 2 * M - 1` for the odd scale.  The Roth number
  `rothNumberNat N` is the largest cardinality of a three-term-progression-free
  subset of `{0, …, N - 1}`.

  This file studies *asymptotic comparison functions*: real functions `f` with

      `rothNumberNat N / f N → 1`,

  i.e. `f` is any quantity asymptotically equivalent to `N ↦ rothNumberNat N`
  in the ratio sense (the ratio `→ 1` notion, not Mathlib's
  `Asymptotics.IsEquivalent`).  The theorem below says that for such an `f`,
  *if* the fixed-odd-scale dilation ratio has a finite limit,

      `f (N * q) / f N → c`,

  then necessarily `c = q`.  Equivalently, no `f` with `rothNumberNat N / f N → 1`
  can have `f (N * q) / f N → c` for any `c ≠ q`.

  The proof is a transfer of the accepted rigidity of the Roth-number ratio
  `eq_odd_scale_of_tendsto_rothNumberNat_ratio` from `rothNumberNat` to an
  arbitrary asymptotic comparison `f`.  From `rothNumberNat N / f N → 1` and
  eventual `rothNumberNat N > 0` we first derive eventual `f N > 0` (the
  falsifier — loss of eventual nonzeroness — is thereby excluded, and positivity
  is *derived*, never assumed).  The map `N ↦ N * q` tends to `atTop`, so
  composing the first hypothesis with it gives `rothNumberNat (N*q) / f (N*q) → 1`,
  while inverting gives `(rothNumberNat N / f N)⁻¹ → 1`.  On the eventual tail
  where `f N`, `f (N*q)`, and `rothNumberNat N` are nonzero, the field identity

      `rothNumberNat (N*q) / rothNumberNat N
         = (rothNumberNat (N*q) / f (N*q)) * (f (N*q) / f N)
             * (rothNumberNat N / f N)⁻¹`

  writes the Roth-number ratio as a product of the three convergent factors, so
  it tends to `1 * c * 1 = c`.  The accepted classifier then forces `c = q`.

  What this does and does not say.  This is a *universal exclusion*: for the
  whole class of positive asymptotic comparison functions with a finite
  fixed-odd-scale dilation ratio, the only possible finite ratio value is the
  odd scale `q = 2 * M - 1`.  If a candidate comparison `f` satisfies the ratio
  asymptotic `rothNumberNat N / f N → 1` *and* is regularly varying of index
  `α ≠ 1`, then its odd-dilation ratio would tend to `q^α ≠ q`, so this theorem
  rules that candidate out; no assertion is made that such an `f` exists.  The
  theorem does *not* exclude index-one slowly varying candidates, which are the
  boundary model `f N = N * L N` with `L` slowly varying: there the ratio would
  tend to `q` and the theorem is compatible rather than contradictory.  The statement does not claim
  that any particular formula fails, does not assert that any ratio limit exists,
  says nothing about oscillation or `limsup`/`liminf`, and does not resolve
  Erdős #142.

  A note on satisfiability.  The ratio hypothesis `rothNumberNat N / f N → 1` is
  satisfiable — the concrete choice `f = rothNumberNat` makes the ratio
  eventually `1` — and this is checked below.  The dilation-ratio convergence
  hypothesis is the open content and is not witnessed.  The classifiers are
  implications whose antecedent may currently be false; when it holds they carry
  genuine content.

  No `sorry`, no `unsafe`, no `axiom`, no `native_decide`, no existing
  declaration is edited, and the aggregate `Proofs/Erdos.lean` is untouched.
-/

import Erdos.Erdos142.OddScaleRatioRigidity

set_option autoImplicit false

open Filter
open scoped Topology

namespace Erdos142

noncomputable section

/-- **Odd-scale rigidity of any asymptotic comparison function.**  For fixed
`M ≥ 2`, let `q = 2 * M - 1`.  Suppose a real function `f` satisfies
`rothNumberNat N / f N → 1` and its fixed-odd-scale dilation ratio has a finite
limit `f (N * q) / f N → c`.  Then `c = q`.

Route: from `rothNumberNat N / f N → 1` and eventual `rothNumberNat N > 0` we
derive eventual `f N > 0`; the map `N ↦ N * q` tends to `atTop`, so composing
gives `rothNumberNat (N*q) / f (N*q) → 1` and inverting gives
`(rothNumberNat N / f N)⁻¹ → 1`.  On the eventual tail the exact field identity
expresses `rothNumberNat (N*q) / rothNumberNat N` as the product of those three
convergent factors, hence it tends to `1 * c * 1 = c`, and the accepted
classifier `eq_odd_scale_of_tendsto_rothNumberNat_ratio` forces `c = q`. -/
theorem eq_odd_scale_of_asymptotic_comparison {M : ℕ} (hM : 2 ≤ M)
    {f : ℕ → ℝ} {c : ℝ}
    (hf : Tendsto (fun N => (rothNumberNat N : ℝ) / f N) atTop (𝓝 1))
    (hc : Tendsto (fun N => f (N*(2*M-1)) / f N) atTop (𝓝 c)) :
    c = ((2*M-1:ℕ):ℝ) := by
  have hq : Tendsto (fun N : ℕ => N * (2*M-1)) atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    refine ⟨b, fun a ha => ?_⟩
    calc b ≤ a := ha
      _ = a * 1 := (Nat.mul_one a).symm
      _ ≤ a * (2*M-1) := Nat.mul_le_mul_left a (by omega)
  have hev_ratio_gt : ∀ᶠ N : ℕ in atTop,
      (1/2 : ℝ) < (rothNumberNat N : ℝ) / f N :=
    (tendsto_order.1 hf).1 (1/2) (by norm_num)
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
  have hev_fpos_q : ∀ᶠ N : ℕ in atTop, 0 < f (N * (2*M-1)) :=
    hq.eventually hev_fpos
  have hev_rN_ne : ∀ᶠ N : ℕ in atTop, (rothNumberNat N : ℝ) ≠ 0 :=
    eventually_atTop.mpr ⟨1, fun N hN => ne_of_gt (rothNumberNat_pos_real hN)⟩
  have hev_eq : (fun N : ℕ =>
        (rothNumberNat (N * (2*M-1)) : ℝ) / (rothNumberNat N : ℝ))
      =ᶠ[atTop] (fun N : ℕ =>
        ((rothNumberNat (N * (2*M-1)) : ℝ) / f (N * (2*M-1)))
          * (f (N * (2*M-1)) / f N)
          * (((rothNumberNat N : ℝ) / f N)⁻¹)) := by
    filter_upwards [hev_fpos, hev_fpos_q, hev_rN_ne] with N hfN hfNq hrN
    have hfN' : f N ≠ 0 := ne_of_gt hfN
    have hfNq' : f (N * (2*M-1)) ≠ 0 := ne_of_gt hfNq
    field_simp
  have hA : Tendsto (fun N : ℕ =>
      (rothNumberNat (N * (2*M-1)) : ℝ) / f (N * (2*M-1))) atTop (𝓝 1) :=
    hf.comp hq
  have hC : Tendsto (fun N : ℕ =>
      ((rothNumberNat N : ℝ) / f N)⁻¹) atTop (𝓝 (1 : ℝ)) := by
    simpa using hf.inv₀ one_ne_zero
  have hprod : Tendsto (fun N : ℕ =>
      ((rothNumberNat (N * (2*M-1)) : ℝ) / f (N * (2*M-1)))
        * (f (N * (2*M-1)) / f N)
        * (((rothNumberNat N : ℝ) / f N)⁻¹)) atTop (𝓝 c) := by
    simpa using (hA.mul hc).mul hC
  have hlim : Tendsto (fun N : ℕ =>
      (rothNumberNat (N * (2*M-1)) : ℝ) / (rothNumberNat N : ℝ)) atTop (𝓝 c) :=
    Tendsto.congr' hev_eq.symm hprod
  exact eq_odd_scale_of_tendsto_rothNumberNat_ratio hM hlim

/-- **No asymptotic comparison function with a wrong finite odd-scale ratio.**
For fixed `M ≥ 2`, there is no real function `f` with
`rothNumberNat N / f N → 1` and `f (N * (2 * M - 1)) / f N → c` for any
`c ≠ 2 * M - 1`.  This is the nonexistence corollary of
`eq_odd_scale_of_asymptotic_comparison`: the whole class of positive asymptotic
comparison functions with a finite fixed-odd-scale dilation ratio is excluded at
every value other than the odd scale.  It does not assert that any ratio limit
exists. -/
theorem not_exists_asymptotic_comparison_of_ne_odd_scale {M : ℕ}
    (hM : 2 ≤ M) {c : ℝ} (hcq : c ≠ ((2*M-1:ℕ):ℝ)) :
    ¬ ∃ f : ℕ → ℝ,
      Tendsto (fun N => (rothNumberNat N:ℝ)/f N) atTop (𝓝 1) ∧
      Tendsto (fun N => f (N*(2*M-1))/f N) atTop (𝓝 c) := by
  rintro ⟨f, hf, hc⟩
  exact hcq (eq_odd_scale_of_asymptotic_comparison hM hf hc)

/-- Ground-truth satisfiability check of the ratio hypothesis: the concrete
choice `f = rothNumberNat` makes `rothNumberNat N / f N` eventually `1`, hence
tends to `1`.  This witnesses non-vacuity of the first hypothesis of
`eq_odd_scale_of_asymptotic_comparison`; it does not witness the dilation-ratio
hypothesis, whose convergence is the open content. -/
example : Tendsto (fun N : ℕ => (rothNumberNat N : ℝ) / (rothNumberNat N : ℝ))
    atTop (𝓝 1) := by
  apply Tendsto.congr' _ tendsto_const_nhds
  filter_upwards [eventually_atTop.mpr
    ⟨1, fun N hN => rothNumberNat_pos_real hN⟩] with N hN
  exact (div_self (ne_of_gt hN)).symm

/-- Ground-truth check of the excluded value at `M = 2`: the forced odd scale
`((2 * 2 - 1 : ℕ) : ℝ) = 3` is positive and distinct from the wrong
fixed-odd-scale value `1`, so the conclusion of
`eq_odd_scale_of_asymptotic_comparison` is a substantive constraint and the
exclusion hypothesis of `not_exists_asymptotic_comparison_of_ne_odd_scale` is
non-vacuous there. -/
example : ((2 * 2 - 1 : ℕ) : ℝ) = 3 ∧ (0 : ℝ) < ((2 * 2 - 1 : ℕ) : ℝ) ∧
    ((2 * 2 - 1 : ℕ) : ℝ) ≠ 1 := by
  norm_num

end

end Erdos142

-- Axiom audit for every public declaration.
#print axioms Erdos142.eq_odd_scale_of_asymptotic_comparison
#print axioms Erdos142.not_exists_asymptotic_comparison_of_ne_odd_scale