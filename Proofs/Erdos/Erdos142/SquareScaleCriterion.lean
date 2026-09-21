/-
  Erdős Problem #142 — the sharp square-scale criterion for the endpoint.

  `RegularityDiscriminator` isolates the deterministic analytic kernel of the
  #142 endpoint: a nonnegative, bounded-above *normalized deficit* `D` obeying
  the square-scale recurrence `D(N²) = √2 · D(N) + o(1)` must tend to `0`.  This
  module instantiates that kernel at the *actual* Roth number `r₃ = rothNumberNat`
  and shows that the resulting statement is sharp: an exact `iff`, with nothing
  lost in either direction.

  The two quantities compared are

  * the normalized deficit
    `D(N) = normalizedDeficit r₃ N = log (N / r₃ N) / √(log N)`, and
  * the *square-scale defect*
    `X(N) = log (r₃(N)² / r₃(N²)) / √(log N)`,
    the logarithm of the multiplicativity defect of `r₃` at the single scale pair
    `(N, N)`, divided by `√(log N)`.

  The bridge is the exact identity `normalizedDeficit_sq_sub` at `a = r₃`,
  recorded below as `normalizedDeficit_sq_sub_roth`:

      `√2 · (D(N²) - √2 · D(N)) = X(N)`   for `N ≥ 2`.

  * **Forward.**  `D → 0` and `N ↦ N² → ∞` give `D(N²) → 0`, hence
    `√2 · (D(N²) - √2 · D(N)) → 0`; the identity transfers this to `X → 0`.
  * **Backward.**  `X → 0` feeds `tendsto_zero_of_sqrt_two_recurrence` at a
    threshold `N₀ ≥ 2` chosen from the eventual lower bound: eventual
    nonnegativity of `D` comes from `1 ≤ r₃ N ≤ N`, and eventual boundedness
    `D ≤ torusLeadingConstant + 1` comes from
    `TorusAsymptoticLowerBound.eventually_rothNumberNat_lower_bound` at `δ = 1`.
    The identity converts the signed defect `X` into the absolute recurrence
    error `|D(N²) - √2 · D(N)| ≤ |X(N)|`.

  **This is an unconditional characterization, not a resolution of #142.**  It
  asserts neither `D → 0` nor `X → 0`; it only asserts that the two are
  equivalent.  What it does is localize the positive endpoint of #142 to a
  statement about `r₃` alone: `r₃(N) = N^{1-o(1)}` holds exactly when the
  square-scale multiplicativity defect of `r₃` is `o(√(log N))`, i.e. exactly
  when `log (r₃(N)^2 / r₃(N²)) = o(√(log N))`.  (The reverse direction needs
  the accepted unconditional EHPS-shaped lower bound — without it the
  equivalence is false, e.g. at `a ≡ 1` the defect `X` vanishes identically
  while `D` diverges.)

  No `sorry`, no `unsafe`, no new axioms, and no existing declaration is edited;
  the axiom audit is at the end of the file.
-/

import Erdos.Erdos142.TorusAsymptoticLowerBound
import Erdos.Erdos142.RegularityDiscriminator
import Erdos.Erdos142.ProductDefect

set_option autoImplicit false

open Filter
open scoped Topology

namespace Erdos142

noncomputable section

/-! ## Eventual regularity of the normalized deficit of `r₃` -/

/-- The squaring map `N ↦ N ^ 2` tends to infinity on `ℕ`. -/
theorem tendsto_nat_sq_atTop : Tendsto (fun N : ℕ => N ^ 2) atTop atTop := by
  rw [tendsto_atTop_atTop]
  refine fun b => ⟨max b 1, fun a ha => ?_⟩
  have hb : b ≤ a := le_trans (le_max_left b 1) ha
  have h1 : 1 ≤ a := le_trans (le_max_right b 1) ha
  calc b ≤ a := hb
    _ ≤ a * a := Nat.le_mul_self a
    _ = a ^ 2 := (pow_two a).symm

/-- **Eventual nonnegativity of the normalized deficit of `r₃`.**  For `N ≥ 2`
the Roth number satisfies `1 ≤ r₃ N ≤ N`, so `N / r₃ N ≥ 1` and `log N > 0`;
hence `D(N) = log (N / r₃ N) / √(log N) ≥ 0`.

This is one of the two regularity hypotheses of the deterministic kernel
`tendsto_zero_of_sqrt_two_recurrence`; its consumer is
`tendsto_normalizedDeficit_zero_iff_square_defect`. -/
theorem normalizedDeficit_rothNumberNat_nonneg {N : ℕ} (hN : 2 ≤ N) :
    0 ≤ normalizedDeficit rothNumberNat N := by
  have hN1 : 1 ≤ N := by omega
  have hrpos : (0 : ℝ) < (rothNumberNat N : ℝ) := rothNumberNat_pos_real hN1
  have hle : (rothNumberNat N : ℝ) ≤ (N : ℝ) := by exact_mod_cast rothNumberNat_le N
  rw [normalizedDeficit, logDeficit]
  refine div_nonneg (Real.log_nonneg ?_) (Real.sqrt_nonneg _)
  rw [le_div_iff₀ hrpos]
  simpa using hle

/-- **Eventual upper bound on the normalized deficit of `r₃`.**  The accepted
unconditional EHPS-shaped lower bound at `δ = 1`, namely
`N · exp(-(torusLeadingConstant + 1)·√(log N)) ≤ r₃ N` eventually, gives
`log r₃ N ≥ log N - (torusLeadingConstant + 1)·√(log N)` and hence
`D(N) ≤ torusLeadingConstant + 1` eventually.

This is the second regularity hypothesis of the deterministic kernel; its
consumer is `tendsto_normalizedDeficit_zero_iff_square_defect`. -/
theorem eventually_le_normalizedDeficit_rothNumberNat :
    ∀ᶠ N : ℕ in atTop,
      normalizedDeficit rothNumberNat N ≤ torusLeadingConstant + 1 := by
  obtain ⟨N₁, hN₁⟩ :=
    eventually_atTop.mp (eventually_rothNumberNat_lower_bound 1 (by norm_num))
  refine eventually_atTop.2 ⟨max 2 N₁, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_trans (by norm_num : 1 ≤ 2) (le_max_left 2 N₁)) hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hrpos : (0 : ℝ) < (rothNumberNat N : ℝ) := rothNumberNat_pos_real hN1
  have hlogpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hsqrtpos : 0 < Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_pos.2 hlogpos
  have hlow := hN₁ N (le_trans (le_max_right 2 N₁) hN)
  have hlhs : 0 < (N : ℝ) *
      Real.exp (-(torusLeadingConstant + 1) * Real.sqrt (Real.log (N : ℝ))) :=
    mul_pos hNpos (Real.exp_pos _)
  have hlog := Real.log_le_log hlhs hlow
  rw [Real.log_mul (ne_of_gt hNpos) (Real.exp_ne_zero _), Real.log_exp] at hlog
  have hkey : Real.log (N : ℝ) - Real.log (rothNumberNat N : ℝ) ≤
      (torusLeadingConstant + 1) * Real.sqrt (Real.log (N : ℝ)) := by linarith
  have hD : normalizedDeficit rothNumberNat N =
      (Real.log (N : ℝ) - Real.log (rothNumberNat N : ℝ)) /
        Real.sqrt (Real.log (N : ℝ)) := by
    rw [normalizedDeficit, logDeficit, Real.log_div (ne_of_gt hNpos) (ne_of_gt hrpos)]
  rw [hD]
  exact (div_le_iff₀ hsqrtpos).mpr hkey

/-! ## The exact square-scale bridge -/

/-- **The exact square-scale bridge for `r₃`.**  For `N ≥ 2`,

`√2 · (D(N²) - √2 · D(N)) = log (r₃(N)² / r₃(N²)) / √(log N)`,

i.e. the square-scale defect `X(N)` is exactly the `√2`-multiple of the
recurrence difference of `D`.  This is `normalizedDeficit_sq_sub` at
`a = rothNumberNat` together with `√(2 · log N) = √2 · √(log N)`.

Its consumers are both directions of `tendsto_normalizedDeficit_zero_iff_square_defect`. -/
theorem normalizedDeficit_sq_sub_roth (N : ℕ) (hN : 2 ≤ N) :
    Real.sqrt 2 * (normalizedDeficit rothNumberNat (N ^ 2) -
        Real.sqrt 2 * normalizedDeficit rothNumberNat N) =
      Real.log (((rothNumberNat N : ℝ) ^ 2) / (rothNumberNat (N ^ 2) : ℝ)) /
        Real.sqrt (Real.log (N : ℝ)) := by
  rw [normalizedDeficit_sq_sub (N := N) hN (fun M hM => one_le_rothNumberNat hM),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) (Real.log (N : ℝ))]
  have hlogpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hS : Real.sqrt (Real.log (N : ℝ)) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hlogpos)
  have h2 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  field_simp

/-! ## The sharp square-scale criterion -/

/-- **Sharp square-scale criterion for the #142 endpoint.**  The normalized
deficit of the Roth number vanishes,

`D(N) = normalizedDeficit r₃ N → 0`,

**if and only if** the square-scale multiplicativity defect of `r₃` is
`o(√(log N))`:

`log (r₃(N)² / r₃(N²)) / √(log N) → 0`.

The forward implication is purely analytic: `D → 0` and `N ↦ N² → ∞` give
`D(N²) → 0`, so `√2 · (D(N²) - √2 · D(N)) → 0`, and the exact bridge
`normalizedDeficit_sq_sub_roth` transfers the limit to the defect.  The backward
implication invokes the deterministic kernel `tendsto_zero_of_sqrt_two_recurrence`
at a threshold `N₀ ≥ 2` chosen from the eventual lower bound
`eventually_rothNumberNat_lower_bound 1`: `D ≥ 0` from `1 ≤ r₃ N ≤ N`, and
`D ≤ torusLeadingConstant + 1` from `eventually_le_normalizedDeficit_rothNumberNat`;
the bridge turns the signed defect into the absolute recurrence error
`|D(N²) - √2 · D(N)| ≤ |X(N)| → 0`.

**This theorem is an unconditional characterization and is *not* a claim that
either side holds.**  It does not assert `D → 0`, does not assert `X → 0`, and
says nothing about whether `r₃(N) = N^{1-o(1)}`.  Its content is that the
positive endpoint of #142 is *localized* to the single-scale statement
`log (r₃(N)^2 / r₃(N²)) = o(√(log N))`; conversely, the accepted unconditional
EHPS-shaped lower bound makes that square-scale multiplicativity statement
equivalent to the endpoint.  Neither direction of the equivalence is vacuous:
the forward direction holds for every real sequence, while the backward
direction genuinely uses the arithmetic of `r₃` (for the synthetic counting
function `a ≡ 1` the defect vanishes identically but `D` diverges). -/
theorem tendsto_normalizedDeficit_zero_iff_square_defect :
    Tendsto (normalizedDeficit rothNumberNat) atTop (𝓝 0) ↔
    Tendsto (fun N : ℕ =>
      Real.log (((rothNumberNat N : ℝ) ^ 2) /
        (rothNumberNat (N ^ 2) : ℝ)) /
        Real.sqrt (Real.log (N : ℝ))) atTop (𝓝 0) := by
  constructor
  · intro hD
    have hcomp : Tendsto (fun N : ℕ => normalizedDeficit rothNumberNat (N ^ 2))
        atTop (𝓝 0) :=
      hD.comp tendsto_nat_sq_atTop
    have htarget : Tendsto (fun N : ℕ => Real.sqrt 2 *
        (normalizedDeficit rothNumberNat (N ^ 2) -
          Real.sqrt 2 * normalizedDeficit rothNumberNat N)) atTop (𝓝 0) := by
      have hsub := hcomp.sub (hD.const_mul (Real.sqrt 2))
      simpa using hsub.const_mul (Real.sqrt 2)
    refine htarget.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    exact normalizedDeficit_sq_sub_roth N hN
  · intro hX
    obtain ⟨N₁, hN₁⟩ :=
      eventually_atTop.mp (eventually_rothNumberNat_lower_bound 1 (by norm_num))
    obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp eventually_le_normalizedDeficit_rothNumberNat
    refine tendsto_zero_of_sqrt_two_recurrence (normalizedDeficit rothNumberNat)
      (fun N => |Real.log (((rothNumberNat N : ℝ) ^ 2) /
        (rothNumberNat (N ^ 2) : ℝ)) / Real.sqrt (Real.log (N : ℝ))|)
      (max 2 (max N₁ N₂)) ?_ ?_ ?_ ?_
    · intro n hn
      exact normalizedDeficit_rothNumberNat_nonneg (le_trans (le_max_left 2 _) hn)
    · refine ⟨torusLeadingConstant + 1, fun n hn => ?_⟩
      exact hN₂ n (le_trans (le_trans (le_max_right N₁ N₂) (le_max_right 2 _)) hn)
    · simpa using hX.abs
    · intro n hn
      have hn2 : 2 ≤ n := le_trans (le_max_left 2 _) hn
      have hb := normalizedDeficit_sq_sub_roth n hn2
      have hs2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
      have hs2ge1 : (1 : ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.2 (by norm_num)
      rw [← hb, abs_mul, abs_of_nonneg hs2pos.le]
      calc |normalizedDeficit rothNumberNat (n ^ 2) -
            Real.sqrt 2 * normalizedDeficit rothNumberNat n|
          = 1 * |normalizedDeficit rothNumberNat (n ^ 2) -
              Real.sqrt 2 * normalizedDeficit rothNumberNat n| := (one_mul _).symm
        _ ≤ Real.sqrt 2 * |normalizedDeficit rothNumberNat (n ^ 2) -
              Real.sqrt 2 * normalizedDeficit rothNumberNat n| :=
            mul_le_mul_of_nonneg_right hs2ge1 (abs_nonneg _)

/-- Synthetic sanity check of the forward mechanism in the abstract: for an
arbitrary real sequence `D`, the square-scale recurrence expression
`N ↦ √2 · (D(N²) - √2 · D(N))` vanishes whenever `D` does.  This is the analytic
content of the forward implication with the arithmetic of `r₃` removed, so it
can be checked in isolation; it is non-vacuous at `D ≡ 0`. -/
example (D : ℕ → ℝ) (hD : Tendsto D atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => Real.sqrt 2 * (D (N ^ 2) - Real.sqrt 2 * D N))
      atTop (𝓝 0) := by
  have hcomp : Tendsto (fun N : ℕ => D (N ^ 2)) atTop (𝓝 0) := hD.comp tendsto_nat_sq_atTop
  simpa using (hcomp.sub (hD.const_mul (Real.sqrt 2))).const_mul (Real.sqrt 2)

end

#print axioms Erdos142.tendsto_nat_sq_atTop
#print axioms Erdos142.normalizedDeficit_rothNumberNat_nonneg
#print axioms Erdos142.eventually_le_normalizedDeficit_rothNumberNat
#print axioms Erdos142.normalizedDeficit_sq_sub_roth
#print axioms Erdos142.tendsto_normalizedDeficit_zero_iff_square_defect

end Erdos142