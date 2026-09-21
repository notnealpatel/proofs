/-
  Erdős Problem #142 — fixed-right-factor threshold saturation of the product
  defect.

  `ProductDefect.rothProductDefect_unbounded` shows that the product defect
  `rothProductDefect N M` is unbounded above in the two variables jointly: it
  exhibits *some* pair `(N, M)` with `rothProductDefect N M > B`.

  This file localizes such witnesses in the right factor.  For each fixed
  `M ≥ 2` it proves that the left-factor supremum `sup_N rothProductDefect N M`
  is *at least* the threshold

      `T_M = rothLogDeficit M + log ((2 * M - 1) / M)`,

  in the precise sense that every real `B < T_M` is exceeded by
  `rothProductDefect N M` for some `N ≥ 1`.  Since `rothLogDeficit M` is
  unbounded across `M`, this refines the global unboundedness of the defect by
  pinning the failure at chosen right factors `M` with large `λ(M)`.

  The mechanism is that the exact defect/deficit identity

      `rothProductDefect N M
         = rothLogDeficit N + rothLogDeficit M
             - rothLogDeficit (N * (2 * M - 1))
             + log ((2 * M - 1) / M)`

  turns any fixed upper bound `rothProductDefect N M ≤ B` into the affine
  increment `rothLogDeficit (N * q) ≥ rothLogDeficit N + c` along the radix
  `q = 2 * M - 1`, with `c = rothLogDeficit M + log (q / M) - B`.  Iterating
  from `rothLogDeficit 1 = 0` gives `rothLogDeficit (q ^ k) ≥ k * c`, which the
  accepted sub-logarithmic convergence `rothLogDeficit N / log N → 0` forbids
  as soon as `c > 0`.

  The generic statement `exists_fixed_right_defect_gt` isolates this argument
  for an arbitrary sequence `lam` and defect `D` satisfying the identity pattern
  and the sub-logarithmic limit; the instantiation
  `exists_fixed_right_rothProductDefect_gt` applies it to the Roth number via
  the unconditional `tendsto_rothLogDeficit_div_log_zero`.

  What this does and does not say.  This is a *threshold-saturation* statement,
  not an unboundedness statement in `N`.  For a fixed `M` it exhibits values of
  `D(N, M)` above every level below `T_M = lam M + log ((2 * M - 1) / M)`, which
  shows `sup_N D(N, M) ≥ T_M`, but it does *not* show that `D(N, M)` is
  unbounded in `N` for fixed `M`, does *not* show that the supremum equals `T_M`
  or that `T_M` is attained, and does *not* prove oscillation of the defect.
  The `lam ≡ 0` example below shows the threshold is sharp and why fixed-`M`
  unboundedness cannot be deduced from the identity and the limit alone: there
  `D(N, M) = T_M` for every `N`, so the left-factor supremum equals `T_M` and is
  finite.  Nor does any of this resolve Erdős #142.

  No `sorry`, no `unsafe`, no new axioms, and no existing declaration is edited.
-/

import Erdos.Erdos142.ProductDefect
import Erdos.Erdos142.TorusAsymptoticConsequences

set_option autoImplicit false

open Filter
open scoped Topology

namespace Erdos142

noncomputable section

/-- **Generic fixed-right-factor defect lemma.**  Let `lam : ℕ → ℝ` vanish at
`1` and let `D : ℕ → ℕ → ℝ` satisfy the exact identity

`D N M = lam N + lam M - lam (N * (2 * M - 1)) + log ((2 * M - 1) / M)`

on positive inputs.  If `lam N / log N → 0`, then for every fixed `M ≥ 2` and
every real `B` below the threshold `lam M + log ((2 * M - 1) / M)` there is
`N ≥ 1` with `B < D N M`.  Equivalently, for fixed `M` the left-factor supremum
`sup_N D(N, M)` is at least the threshold `lam M + log ((2 * M - 1) / M)`; the
conclusion is threshold saturation, not unboundedness in `N`.

Route: suppose `D N M ≤ B` for all `N ≥ 1`.  With `q = 2 * M - 1 ≥ 3` and
`c = lam M + log (q / M) - B > 0`, the identity yields
`lam (N * q) ≥ lam N + c`.  Iterating from `lam 1 = 0` gives
`lam (q ^ k) ≥ k * c`, hence `lam (q ^ k) / log (q ^ k) ≥ c / log q > 0`, which
contradicts `lam N / log N → 0` along the subsequence `N = q ^ k`. -/
theorem exists_fixed_right_defect_gt
    (lam : ℕ → ℝ) (D : ℕ → ℕ → ℝ) (hlam1 : lam 1 = 0)
    (hid : ∀ N M : ℕ, 1 ≤ N → 1 ≤ M →
      D N M = lam N + lam M - lam (N * (2 * M - 1)) +
        Real.log (((2 * M - 1 : ℕ) : ℝ) / (M : ℝ)))
    (hsub : Tendsto (fun N : ℕ => lam N / Real.log (N : ℝ)) atTop (𝓝 0))
    {M : ℕ} (hM : 2 ≤ M) {B : ℝ}
    (hB : B < lam M + Real.log (((2 * M - 1 : ℕ) : ℝ) / (M : ℝ))) :
    ∃ N : ℕ, 1 ≤ N ∧ B < D N M := by
  by_contra hcon
  have hcon' : ∀ N : ℕ, 1 ≤ N → D N M ≤ B := by
    intro N hN
    by_contra h
    exact hcon ⟨N, hN, lt_of_not_ge h⟩
  have hM1 : 1 ≤ M := by omega
  let c : ℝ := lam M + Real.log (((2 * M - 1 : ℕ) : ℝ) / (M : ℝ)) - B
  have hcdef : c = lam M + Real.log (((2 * M - 1 : ℕ) : ℝ) / (M : ℝ)) - B := rfl
  have hcpos : 0 < c := by
    rw [hcdef]
    linarith
  have hstep : ∀ N : ℕ, 1 ≤ N → lam N + c ≤ lam (N * (2 * M - 1)) := by
    intro N hN
    have hD : D N M ≤ B := hcon' N hN
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

/-- Sharpness check for `exists_fixed_right_defect_gt`.  Take `lam ≡ 0` and
`D N M = log ((2 * M - 1) / M)`, which satisfies the identity because both `lam`
terms vanish.  Here the threshold is `T_M = log ((2 * M - 1) / M)` and the
defect equals it for *every* `N`, so `sup_N D(N, M) = T_M` exactly.  This shows
two things: (i) the condition `B < T_M` is sharp, since `B = T_M` is not
exceeded; and (ii) fixed-`M` unboundedness cannot follow from the identity and
`lam N / log N → 0` alone, because `D(·, M)` is bounded above in this model.  At
`M = 2`, `B = 0` the theorem produces `N ≥ 1` with `0 < log (3 / 2)`. -/
example : ∃ N : ℕ, 1 ≤ N ∧ (0 : ℝ) <
    Real.log (((2 * 2 - 1 : ℕ) : ℝ) / (2 : ℝ)) :=
  exists_fixed_right_defect_gt (lam := fun _ => 0)
    (D := fun _ M => Real.log (((2 * M - 1 : ℕ) : ℝ) / (M : ℝ)))
    rfl
    (fun _ _ _ _ => by ring)
    (by simpa only [zero_div] using tendsto_const_nhds)
    (M := 2) (by norm_num) (B := 0)
    (by
      have h : (1 : ℝ) < (((2 * 2 - 1 : ℕ) : ℝ)) / (2 : ℝ) := by norm_num
      simpa using Real.log_pos h)

/-- **Fixed-right-factor threshold saturation of the Roth product defect.**
For every fixed `M ≥ 2` and every real `B` below the threshold
`T_M = rothLogDeficit M + log ((2 * M - 1) / M)` there is `N ≥ 1` with
`B < rothProductDefect N M`.  Equivalently, `sup_N rothProductDefect N M ≥ T_M`.

Because `rothLogDeficit M` is unbounded across `M`, this localizes arbitrarily
large failure of a constant reverse bound for the accepted scale-product
inequality at chosen right factors `M`.  It does *not* show that
`rothProductDefect N M` is unbounded in `N` for fixed `M`, does *not* show that
the supremum equals or attains `T_M`, and does not prove oscillation of the
defect; nor does it resolve Erdős #142. -/
theorem exists_fixed_right_rothProductDefect_gt
    {M : ℕ} (hM : 2 ≤ M) {B : ℝ}
    (hB : B < rothLogDeficit M + Real.log (((2 * M - 1 : ℕ) : ℝ) / (M : ℝ))) :
    ∃ N : ℕ, 1 ≤ N ∧ B < rothProductDefect N M :=
  exists_fixed_right_defect_gt rothLogDeficit rothProductDefect rothLogDeficit_one
    (fun _ _ hN hM => rothProductDefect_eq_rothLogDeficit hN hM)
    tendsto_rothLogDeficit_div_log_zero hM hB

end

end Erdos142

-- Axiom audit for the load-bearing declarations.
#print axioms Erdos142.exists_fixed_right_defect_gt
#print axioms Erdos142.exists_fixed_right_rothProductDefect_gt