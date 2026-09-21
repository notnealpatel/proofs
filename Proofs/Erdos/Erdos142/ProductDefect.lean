/-
  Erdős Problem #142 — the negative/shared product defect of the Roth number.

  The scale-product lower bound `ScaleProduct.rothNumberNat_mul_le_rothNumberNat_sub`
  says that `rothNumberNat N * rothNumberNat M ≤ rothNumberNat (N * (2 * M - 1))`.
  Taking logarithms, the *product defect*

      `rothProductDefect N M
         = log (rothNumberNat (N * (2 * M - 1))) - log (rothNumberNat N)
             - log (rothNumberNat M)`

  is nonnegative for `N, M ≥ 1`.  The *log-deficit*

      `rothLogDeficit N = log (N / rothNumberNat N)`

  measures how far the Roth number is from the trivial upper bound `N`.

  This file proves:

  * `1 ≤ rothNumberNat N ≤ N` for `N ≥ 1` (`one_le_rothNumberNat`,
    `rothNumberNat_le`);
  * the exact identity relating the two notions
    (`rothProductDefect_eq_rothLogDeficit`), together with the log-quotient
    form `rothProductDefect_eq_log_div` and nonnegativity
    (`rothProductDefect_nonneg`) inherited from the scale-product bound;
  * `rothLogDeficit` is unbounded above (`rothLogDeficit_unbounded`), which
    is a direct consequence of the accepted explicit Roth threshold
    `ExplicitRothThreshold.rothNumberNat_lt_mul_of_explicitRothThreshold_le`;
  * the generic analytic lemma
    `unbounded_product_defect_of_tendsto`: for *any* sequence `lam` vanishing
    at `1`, whose defects satisfy the exact identity, if `lam` is unbounded
    above and `lam N / log N → 0`, then the defects are unbounded above;
  * the conditional structural theorem
    `rothProductDefect_unbounded_of_tendsto`: under the Behrend-class subpower
    hypothesis `Tendsto (fun N => rothLogDeficit N / log N) atTop (𝓝 0)`, the
    product defect is unbounded above;
  * the no-constant-reverse corollary
    `exists_mul_lt_rothNumberNat_of_pos`: for every real `C > 0` there are
    `N, M ≥ 1` with `C * rothNumberNat N * rothNumberNat M <
    rothNumberNat (N * (2 * M - 1))`.

  The single remaining conditional hypothesis is the subpower hypothesis
  `Tendsto (fun N => rothLogDeficit N / log N) atTop (𝓝 0)`, isolated in the
  statement of `rothProductDefect_unbounded_of_tendsto`.  No `sorry`, `axiom`
  or `unsafe` is used; the axiom audit is at the end of the file.
-/

import Erdos.Erdos142.ScaleProduct
import Erdos.Erdos142.ExplicitRothThreshold

set_option autoImplicit false

open Finset Filter
open scoped Topology

namespace Erdos142

noncomputable section

/-- The logarithmic deficit of the Roth number of `N`, namely
`log (N / rothNumberNat N)`.  For `N ≥ 1` this is nonnegative and measures how
far `rothNumberNat N` falls below the trivial bound `N`. -/
def rothLogDeficit (N : ℕ) : ℝ :=
  Real.log ((N : ℝ) / (rothNumberNat N : ℝ))

/-- The product defect of the Roth number: the logarithm of
`rothNumberNat (N * (2 * M - 1))` minus the logarithms of `rothNumberNat N` and
`rothNumberNat M`.  It is nonnegative for `N, M ≥ 1` by the scale-product
lower bound, and it is the quantity whose unboundedness expresses that the Roth
number cannot satisfy a constant reverse supermultiplicativity bound. -/
def rothProductDefect (N M : ℕ) : ℝ :=
  Real.log (rothNumberNat (N * (2 * M - 1)) : ℝ) - Real.log (rothNumberNat N : ℝ) -
    Real.log (rothNumberNat M : ℝ)

/-- Ground-truth check: the Roth number of `1` is `1`. -/
theorem rothNumberNat_one : rothNumberNat 1 = 1 := by
  have h1 : 1 ≤ rothNumberNat 1 := by
    have hle := ThreeAPFree.le_rothNumberNat (n := 1) (k := 1) ({0} : Finset ℕ)
      (by simp) (by intro x hx; simp only [mem_singleton] at hx; omega) (by simp)
    simpa using hle
  have h2 := rothNumberNat_le 1
  omega

/-- The log-deficit vanishes at `N = 1`, where the Roth number attains its
trivial bound. -/
theorem rothLogDeficit_one : rothLogDeficit 1 = 0 := by
  rw [rothLogDeficit, rothNumberNat_one]
  norm_num

/-- Ground-truth check of `rothLogDeficit` at `N = 1`. -/
example : rothLogDeficit 1 = 0 := rothLogDeficit_one

/-- Ground-truth check of `rothProductDefect` at `(N, M) = (1, 1)`. -/
example : rothProductDefect 1 1 = 0 := by
  rw [rothProductDefect, rothNumberNat_one]
  norm_num

/-- **Positivity of the Roth number.**  For `N ≥ 1` the Roth number is at least
`1`, since `{0}` is a three-term-progression-free subset of `range N`. -/
theorem one_le_rothNumberNat {N : ℕ} (hN : 1 ≤ N) : 1 ≤ rothNumberNat N := by
  have hle := ThreeAPFree.le_rothNumberNat (n := N) (k := 1) ({0} : Finset ℕ)
    (by simp) (by intro x hx; simp only [mem_singleton] at hx; omega) (by simp)
  simpa using hle

/-- The Roth number of `N ≥ 1` is a positive real. -/
theorem rothNumberNat_pos_real {N : ℕ} (hN : 1 ≤ N) : 0 < (rothNumberNat N : ℝ) := by
  have h := one_le_rothNumberNat hN
  exact_mod_cast (by omega : 0 < rothNumberNat N)

/-- **Log-deficit as a difference of logarithms.**  For `N ≥ 1`,
`rothLogDeficit N = log N - log (rothNumberNat N)`. -/
theorem rothLogDeficit_eq {N : ℕ} (hN : 1 ≤ N) :
    rothLogDeficit N = Real.log (N : ℝ) - Real.log (rothNumberNat N : ℝ) := by
  rw [rothLogDeficit, Real.log_div]
  · exact Nat.cast_ne_zero.mpr (by omega : N ≠ 0)
  · exact Nat.cast_ne_zero.mpr (by
      have h := one_le_rothNumberNat hN
      omega)

/-- **Nonnegativity of the product defect.**  This is the scale-product lower
bound `rothNumberNat N * rothNumberNat M ≤ rothNumberNat (N * (2 * M - 1))`
after taking logarithms. -/
theorem rothProductDefect_nonneg {N M : ℕ} (hN : 1 ≤ N) (hM : 1 ≤ M) :
    0 ≤ rothProductDefect N M := by
  have hprod : rothNumberNat N * rothNumberNat M ≤ rothNumberNat (N * (2 * M - 1)) := by
    have h := rothNumberNat_mul_le_rothNumberNat_sub N M
    have heq : 2 * N * M - N = N * (2 * M - 1) := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_one]
      ring_nf
    rwa [heq] at h
  have ha : (0 : ℝ) < (rothNumberNat N : ℝ) := rothNumberNat_pos_real hN
  have hb : (0 : ℝ) < (rothNumberNat M : ℝ) := rothNumberNat_pos_real hM
  have hcast : (rothNumberNat N : ℝ) * (rothNumberNat M : ℝ) ≤
      (rothNumberNat (N * (2 * M - 1)) : ℝ) := by exact_mod_cast hprod
  have hmul : Real.log ((rothNumberNat N : ℝ) * (rothNumberNat M : ℝ)) =
      Real.log (rothNumberNat N : ℝ) + Real.log (rothNumberNat M : ℝ) :=
    Real.log_mul (ne_of_gt ha) (ne_of_gt hb)
  have hle : Real.log (rothNumberNat N : ℝ) + Real.log (rothNumberNat M : ℝ) ≤
      Real.log (rothNumberNat (N * (2 * M - 1)) : ℝ) := by
    have := Real.log_le_log (mul_pos ha hb) hcast
    rwa [hmul] at this
  rw [rothProductDefect]
  linarith

/-- **Exact defect/deficit identity.**  For `N, M ≥ 1` the product defect and
the log-deficit are related by
`rothProductDefect N M = rothLogDeficit N + rothLogDeficit M
   - rothLogDeficit (N * (2 * M - 1)) + log ((2 * M - 1) / M)`.

The final term is the price of the radix `2 * M - 1`; it is nonnegative for
`M ≥ 1`, and it is the extra summand that makes the identity an equality. -/
theorem rothProductDefect_eq_rothLogDeficit {N M : ℕ} (hN : 1 ≤ N) (hM : 1 ≤ M) :
    rothProductDefect N M =
      rothLogDeficit N + rothLogDeficit M - rothLogDeficit (N * (2 * M - 1)) +
        Real.log (((2 * M - 1 : ℕ) : ℝ) / (M : ℝ)) := by
  have hNpos : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega : N ≠ 0)
  have hMpos : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega : M ≠ 0)
  have hqpos : ((2 * M - 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega : 2 * M - 1 ≠ 0)
  have hNq : 1 ≤ N * (2 * M - 1) := by
    have hq : 1 ≤ 2 * M - 1 := by omega
    simpa using Nat.mul_le_mul hN hq
  have ha : (rothNumberNat N : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by have h := one_le_rothNumberNat hN; omega)
  have hb : (rothNumberNat M : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by have h := one_le_rothNumberNat hM; omega)
  have hc : (rothNumberNat (N * (2 * M - 1)) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by have h := one_le_rothNumberNat hNq; omega)
  rw [rothProductDefect, rothLogDeficit_eq hN, rothLogDeficit_eq hM,
    rothLogDeficit_eq hNq, Nat.cast_mul,
    Real.log_mul hNpos hqpos, Real.log_div hqpos hMpos]
  ring

/-- **Log-quotient form of the product defect.**  For `N, M ≥ 1`,
`rothProductDefect N M = log (rothNumberNat (N * (2 * M - 1)) /
(rothNumberNat N * rothNumberNat M))`. -/
theorem rothProductDefect_eq_log_div {N M : ℕ} (hN : 1 ≤ N) (hM : 1 ≤ M) :
    rothProductDefect N M =
      Real.log ((rothNumberNat (N * (2 * M - 1)) : ℝ) /
        ((rothNumberNat N : ℝ) * (rothNumberNat M : ℝ))) := by
  have ha : (rothNumberNat N : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by have h := one_le_rothNumberNat hN; omega)
  have hb : (rothNumberNat M : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by have h := one_le_rothNumberNat hM; omega)
  have hNq : 1 ≤ N * (2 * M - 1) := by
    have hq : 1 ≤ 2 * M - 1 := by omega
    simpa using Nat.mul_le_mul hN hq
  have hc : (rothNumberNat (N * (2 * M - 1)) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by have h := one_le_rothNumberNat hNq; omega)
  rw [rothProductDefect, Real.log_div hc (mul_ne_zero ha hb), Real.log_mul ha hb]
  ring

/-- **Unboundedness of the log-deficit from the explicit Roth threshold.**
For every real `B` there is `N ≥ 1` with `B < rothLogDeficit N`.

The proof chooses `δ = min (1/2) (exp (-(B + 1)))`, so that `0 < δ ≤ 1` and
`log δ ≤ -(B + 1)`, i.e. `-log δ > B`.  Taking `N` above the explicit finite
threshold `explicitRothThreshold δ` gives
`rothNumberNat N < δ * N` by
`ExplicitRothThreshold.rothNumberNat_lt_mul_of_explicitRothThreshold_le`, hence
`N / rothNumberNat N > 1 / δ` and `rothLogDeficit N > -log δ > B`. -/
theorem rothLogDeficit_unbounded : ∀ B : ℝ, ∃ N : ℕ, 1 ≤ N ∧ B < rothLogDeficit N := by
  intro B
  let δ : ℝ := min (1 / 2) (Real.exp (-(B + 1)))
  have hδdef : δ = min (1 / 2) (Real.exp (-(B + 1))) := rfl
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact lt_min (by norm_num) (Real.exp_pos _)
  have hδle1 : δ ≤ 1 := by
    rw [hδdef]
    exact (min_le_left _ _).trans (by norm_num)
  have hδleexp : δ ≤ Real.exp (-(B + 1)) := by
    rw [hδdef]
    exact min_le_right _ _
  have hlogδ : Real.log δ ≤ -(B + 1) := by
    have h := Real.log_le_log hδpos hδleexp
    rwa [Real.log_exp] at h
  have hBlt : B < -Real.log δ := by linarith
  let N : ℕ := max 1 ⌈explicitRothThreshold δ⌉₊
  have hNdef : N = max 1 ⌈explicitRothThreshold δ⌉₊ := rfl
  have hN1 : 1 ≤ N := by
    rw [hNdef]
    exact le_max_left _ _
  have hthr : explicitRothThreshold δ ≤ (N : ℝ) := by
    have h1 : explicitRothThreshold δ ≤ (⌈explicitRothThreshold δ⌉₊ : ℝ) :=
      Nat.le_ceil _
    have h2 : ((⌈explicitRothThreshold δ⌉₊ : ℕ) : ℝ) ≤ (N : ℝ) := by
      rw [hNdef]
      exact_mod_cast (le_max_right 1 ⌈explicitRothThreshold δ⌉₊)
    linarith
  refine ⟨N, hN1, ?_⟩
  have hlt := rothNumberNat_lt_mul_of_explicitRothThreshold_le δ N hδpos hδle1 hthr
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hrn : (0 : ℝ) < (rothNumberNat N : ℝ) := rothNumberNat_pos_real hN1
  have hloglt : Real.log (rothNumberNat N : ℝ) < Real.log (δ * (N : ℝ)) :=
    Real.log_lt_log hrn hlt
  have hlogmul : Real.log (δ * (N : ℝ)) = Real.log δ + Real.log (N : ℝ) :=
    Real.log_mul (ne_of_gt hδpos) (ne_of_gt hNr)
  rw [rothLogDeficit_eq hN1]
  linarith

/-- **Generic sub-logarithmic defect lemma.**  Let `lam : ℕ → ℝ` vanish at `1`
and let `D : ℕ → ℕ → ℝ` satisfy the exact identity
`D N M = lam N + lam M - lam (N * (2 * M - 1)) + log ((2 * M - 1) / M)`.
If `lam` is unbounded above and `lam N / log N → 0`, then `D` is unbounded
above.

Route: if `D ≤ B` everywhere, pick `M ≥ 2` with `lam M > B`; with
`q = 2 * M - 1 > 1` and `c = lam M + log (q / M) - B > 0` the identity yields
`lam (N * q) ≥ lam N + c`.  Iterating at `N = q ^ k` gives `lam (q ^ k) ≥ k * c`,
which contradicts `lam N / log N → 0` along `N = q ^ k`. -/
theorem unbounded_product_defect_of_tendsto
    (lam : ℕ → ℝ) (D : ℕ → ℕ → ℝ) (hlam1 : lam 1 = 0)
    (hid : ∀ N M : ℕ, 1 ≤ N → 1 ≤ M →
      D N M = lam N + lam M - lam (N * (2 * M - 1)) +
        Real.log (((2 * M - 1 : ℕ) : ℝ) / (M : ℝ)))
    (hunb : ∀ B : ℝ, ∃ N : ℕ, 1 ≤ N ∧ B < lam N)
    (hsub : Tendsto (fun N : ℕ => lam N / Real.log (N : ℝ)) atTop (𝓝 0)) :
    ∀ B : ℝ, ∃ N M : ℕ, 1 ≤ N ∧ 1 ≤ M ∧ B < D N M := by
  intro B
  by_contra hcon
  have hcon' : ∀ N M : ℕ, 1 ≤ N → 1 ≤ M → D N M ≤ B := by
    intro N M hN hM
    by_contra h
    exact hcon ⟨N, M, hN, hM, lt_of_not_ge h⟩
  obtain ⟨M, hM1, hMB⟩ := hunb (max B 1)
  have hMB' : B < lam M := (le_max_left B 1).trans_lt hMB
  have hMne1 : M ≠ 1 := by
    intro h
    rw [h, hlam1] at hMB
    linarith [le_max_right B 1]
  have hM2 : 2 ≤ M := by omega
  let c : ℝ := lam M + Real.log (((2 * M - 1 : ℕ) : ℝ) / (M : ℝ)) - B
  have hcdef : c = lam M + Real.log (((2 * M - 1 : ℕ) : ℝ) / (M : ℝ)) - B := rfl
  have hcpos : 0 < c := by
    rw [hcdef]
    have hL : 0 ≤ Real.log (((2 * M - 1 : ℕ) : ℝ) / (M : ℝ)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (by exact_mod_cast (by omega : 0 < M))]
      have hMq : (M : ℝ) ≤ ((2 * M - 1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : M ≤ 2 * M - 1)
      simpa using hMq
    linarith
  have hstep : ∀ N : ℕ, 1 ≤ N → lam N + c ≤ lam (N * (2 * M - 1)) := by
    intro N hN
    have hD : D N M ≤ B := hcon' N M hN hM1
    have hidN := hid N M hN hM1
    rw [hcdef]
    linarith
  have hiter : ∀ k : ℕ, (k : ℝ) * c ≤ lam ((2 * M - 1) ^ k) := by
    intro k
    induction k with
    | zero => simp [hlam1]
    | succ k ih =>
      rw [pow_succ]
      have h1 : 1 ≤ (2 * M - 1) ^ k := Nat.one_le_pow k (2 * M - 1) (by omega)
      have hs := hstep ((2 * M - 1) ^ k) h1
      have hkey : ((k : ℝ) + 1) * c ≤ lam ((2 * M - 1) ^ k * (2 * M - 1)) := by
        linarith
      simpa [Nat.cast_succ, add_mul, one_mul] using hkey
  have hq1 : 1 < 2 * M - 1 := by omega
  have hLpos : 0 < Real.log (((2 * M - 1 : ℕ) : ℝ)) := by
    apply Real.log_pos
    exact_mod_cast hq1
  have hlim : Tendsto (fun k : ℕ => lam ((2 * M - 1) ^ k) /
      Real.log ((((2 * M - 1) ^ k : ℕ) : ℝ))) atTop (𝓝 0) :=
    hsub.comp (tendsto_pow_atTop_atTop_of_one_lt hq1)
  have hev : ∀ᶠ k : ℕ in atTop, c / Real.log (((2 * M - 1 : ℕ) : ℝ)) ≤
      lam ((2 * M - 1) ^ k) / Real.log ((((2 * M - 1) ^ k : ℕ) : ℝ)) := by
    refine eventually_atTop.mpr ⟨1, fun k hk => ?_⟩
    have hkne : (k : ℝ) ≠ 0 := by
      exact_mod_cast (by omega : k ≠ 0)
    have hlogpow : Real.log ((((2 * M - 1) ^ k : ℕ) : ℝ)) =
        (k : ℝ) * Real.log (((2 * M - 1 : ℕ) : ℝ)) := by
      rw [Nat.cast_pow, Real.log_pow]
    rw [hlogpow]
    have hnum : (k : ℝ) * c ≤ lam ((2 * M - 1) ^ k) := hiter k
    have hden : 0 ≤ (k : ℝ) * Real.log (((2 * M - 1 : ℕ) : ℝ)) :=
      mul_nonneg (by positivity) hLpos.le
    calc c / Real.log (((2 * M - 1 : ℕ) : ℝ))
        = (k : ℝ) * c / ((k : ℝ) * Real.log (((2 * M - 1 : ℕ) : ℝ))) :=
          (mul_div_mul_left _ _ hkne).symm
      _ ≤ lam ((2 * M - 1) ^ k) / ((k : ℝ) * Real.log (((2 * M - 1 : ℕ) : ℝ))) :=
          div_le_div_of_nonneg_right hnum hden
  have hle : c / Real.log (((2 * M - 1 : ℕ) : ℝ)) ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim hev
  have hpos : 0 < c / Real.log (((2 * M - 1 : ℕ) : ℝ)) := div_pos hcpos hLpos
  linarith

/-- **The negative/shared product-defect theorem (conditional).**  Under the
Behrend-class subpower hypothesis `rothLogDeficit N / log N → 0`, the product
defect of the Roth number is unbounded above: for every real `B` there are
`N, M ≥ 1` with `B < rothProductDefect N M`.

This is `unbounded_product_defect_of_tendsto` instantiated at the Roth number,
using the exact identity `rothProductDefect_eq_rothLogDeficit` and the
unconditional unboundedness `rothLogDeficit_unbounded`. -/
theorem rothProductDefect_unbounded_of_tendsto
    (hsub : Tendsto (fun N : ℕ => rothLogDeficit N / Real.log (N : ℝ)) atTop (𝓝 0)) :
    ∀ B : ℝ, ∃ N M : ℕ, 1 ≤ N ∧ 1 ≤ M ∧ B < rothProductDefect N M :=
  unbounded_product_defect_of_tendsto rothLogDeficit rothProductDefect rothLogDeficit_one
    (fun _ _ hN hM => rothProductDefect_eq_rothLogDeficit hN hM)
    rothLogDeficit_unbounded hsub

/-- Ground-truth check of the identity at `(N, M) = (1, 1)`. -/
example : rothProductDefect 1 1 = rothLogDeficit 1 + rothLogDeficit 1 -
    rothLogDeficit (1 * (2 * 1 - 1)) +
      Real.log (((2 * 1 - 1 : ℕ) : ℝ) / ((1 : ℕ) : ℝ)) :=
  rothProductDefect_eq_rothLogDeficit le_rfl le_rfl

/-- **No-constant-reverse corollary.**  Under the subpower hypothesis, for every
real `C > 0` there are `N, M ≥ 1` with
`C * rothNumberNat N * rothNumberNat M < rothNumberNat (N * (2 * M - 1))`.

Equivalently, the scale-product inequality admits no constant reverse bound:
the ratio `rothNumberNat (N * (2 * M - 1)) / (rothNumberNat N * rothNumberNat M)`
is unbounded. -/
theorem exists_mul_lt_rothNumberNat_of_pos
    (hsub : Tendsto (fun N : ℕ => rothLogDeficit N / Real.log (N : ℝ)) atTop (𝓝 0))
    (C : ℝ) (hC : 0 < C) :
    ∃ N M : ℕ, 1 ≤ N ∧ 1 ≤ M ∧
      C * (rothNumberNat N : ℝ) * (rothNumberNat M : ℝ) <
        (rothNumberNat (N * (2 * M - 1)) : ℝ) := by
  obtain ⟨N, M, hN, hM, hB⟩ := rothProductDefect_unbounded_of_tendsto hsub (Real.log C)
  refine ⟨N, M, hN, hM, ?_⟩
  have hNq : 1 ≤ N * (2 * M - 1) := by
    have hq : 1 ≤ 2 * M - 1 := by omega
    simpa using Nat.mul_le_mul hN hq
  have ha : (0 : ℝ) < (rothNumberNat N : ℝ) := rothNumberNat_pos_real hN
  have hb : (0 : ℝ) < (rothNumberNat M : ℝ) := rothNumberNat_pos_real hM
  have hc : (0 : ℝ) < (rothNumberNat (N * (2 * M - 1)) : ℝ) := rothNumberNat_pos_real hNq
  have hquot : (0 : ℝ) < (rothNumberNat (N * (2 * M - 1)) : ℝ) /
      ((rothNumberNat N : ℝ) * (rothNumberNat M : ℝ)) := div_pos hc (mul_pos ha hb)
  have hlog : Real.log C < Real.log ((rothNumberNat (N * (2 * M - 1)) : ℝ) /
      ((rothNumberNat N : ℝ) * (rothNumberNat M : ℝ))) := by
    rw [← rothProductDefect_eq_log_div hN hM]
    exact hB
  have hlt : C < (rothNumberNat (N * (2 * M - 1)) : ℝ) /
      ((rothNumberNat N : ℝ) * (rothNumberNat M : ℝ)) :=
    (Real.log_lt_log_iff hC hquot).mp hlog
  have hmul := (lt_div_iff₀ (mul_pos ha hb)).mp hlt
  simpa only [mul_assoc] using hmul

end

end Erdos142

-- Axiom audit for the load-bearing declarations.
#print axioms Erdos142.rothNumberNat_one
#print axioms Erdos142.one_le_rothNumberNat
#print axioms Erdos142.rothLogDeficit_eq
#print axioms Erdos142.rothProductDefect_nonneg
#print axioms Erdos142.rothProductDefect_eq_rothLogDeficit
#print axioms Erdos142.rothProductDefect_eq_log_div
#print axioms Erdos142.rothLogDeficit_unbounded
#print axioms Erdos142.unbounded_product_defect_of_tendsto
#print axioms Erdos142.rothProductDefect_unbounded_of_tendsto
#print axioms Erdos142.exists_mul_lt_rothNumberNat_of_pos