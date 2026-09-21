/-
  Erdős Problem #142 — the sharp fixed-right upper envelope of the Roth product
  defect.

  `FixedRadixRecurrence.frequently_fixed_right_rothProductDefect_gt` shows that
  for fixed `M ≥ 2` the Roth product defect `rothProductDefect N M` returns
  arbitrarily often above every level `B` below the threshold

      `T_M = rothLogDeficit M + log ((2 * M - 1) / M)`.

  That is a one-sided *lower* statement: it says the defect is repeatedly pushed
  up toward `T_M`.  This file supplies the matching *upper* envelope and combines
  the two into an arbitrarily-late two-sided approximation of `T_M` from below.

  The mechanism is the block/subadditivity inequality for the Roth number,

      `rothNumberNat (q * N) ≤ q * rothNumberNat N`,

  proved here from the Mathlib subadditivity `rothNumberNat_add_le` by induction
  on `q` (and stated in the commuting orientation `N * q` as well).  Writing
  `rothLogDeficit X = log (X / rothNumberNat X)`, the block inequality is exactly
  what makes `rothLogDeficit` *non-decreasing* along multiplication by a positive
  `q`, i.e. `rothLogDeficit N ≤ rothLogDeficit (N * q)`.  Since the exact defect
  identity (from `ProductDefect`) reads

      `rothProductDefect N M
         = rothLogDeficit N + rothLogDeficit M
             - rothLogDeficit (N * (2 * M - 1)) + log ((2 * M - 1) / M)`,

  the monotonicity cancels the `N`-dependent part, giving the pointwise envelope

      `rothProductDefect N M ≤ rothLogDeficit M + log ((2 * M - 1) / M) = T_M`

  for all `N, M ≥ 1`.  Combining this eventual upper bound with the frequently
  established lower bound yields, for every `M ≥ 2` and `ε > 0`, the arbitrarily
  late one-sided approximation

      `∃ᶠ N in atTop, T_M - ε < rothProductDefect N M ∧ rothProductDefect N M ≤ T_M`.

  Finally, the pointwise envelope plus the existential threshold saturation
  `exists_fixed_right_rothProductDefect_gt` identify `T_M` as the *least upper
  bound* of the positive-input range `{rothProductDefect N M | N ≥ 1}`.

  What this does and does not say.  The envelope is an upper bound and the
  combination is an arbitrarily-late two-sided approximation *from below*: it
  does **not** prove that `T_M` is ever attained, does **not** prove that
  `rothProductDefect (·, M)` converges, and does **not** assert any `liminf`
  claim (indeed `liminf_N rothProductDefect N M` may be strictly below `T_M`, and
  the constant threshold model in which the defect equals `T_M` for every `N`
  remains consistent).  The `IsLUB` statement is about the range as an ordered
  set and says nothing about which values along the sequence are taken, about
  oscillation, or about any limit.  Nothing here resolves Erdős #142.

  No `sorry`, no `unsafe`, no new axioms, and no existing declaration is edited.
-/

import Erdos.Erdos142.FixedRadixRecurrence

set_option autoImplicit false

open Filter
open scoped Topology

namespace Erdos142

noncomputable section

/-- **Block (subadditivity) inequality for the Roth number.**  For all naturals
`q` and `N`,

`rothNumberNat (q * N) ≤ q * rothNumberNat N`.

This is the iterated form of the Mathlib subadditivity
`rothNumberNat (M + N) ≤ rothNumberNat M + rothNumberNat N`: induction on `q`
splits `(q + 1) * N = q * N + N`.  The `q = 0` case is the trivial
`rothNumberNat 0 = 0 ≤ 0`, so no positivity hypothesis is needed. -/
theorem rothNumberNat_mul_le (q N : ℕ) :
    rothNumberNat (q * N) ≤ q * rothNumberNat N := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hsplit : (q + 1) * N = q * N + N := by ring
    rw [hsplit]
    refine (rothNumberNat_add_le (q * N) N).trans ?_
    calc rothNumberNat (q * N) + rothNumberNat N
        ≤ q * rothNumberNat N + rothNumberNat N := add_le_add ih le_rfl
      _ = (q + 1) * rothNumberNat N := by ring

/-- **Block inequality in the commuting orientation.**  For all naturals `N` and
`q`,

`rothNumberNat (N * q) ≤ q * rothNumberNat N`,

the form used downstream where the radix `q = 2 * M - 1` multiplies `N` on the
right.  Immediate from `rothNumberNat_mul_le` and `Nat.mul_comm`. -/
theorem rothNumberNat_mul_le_comm (N q : ℕ) :
    rothNumberNat (N * q) ≤ q * rothNumberNat N := by
  rw [Nat.mul_comm N q]
  exact rothNumberNat_mul_le q N

/-- **Monotonicity of the log-deficit along positive scaling.**
For `N ≥ 1` and `q ≥ 1`,

`rothLogDeficit N ≤ rothLogDeficit (N * q)`.

Writing `rothLogDeficit X = log (X / rothNumberNat X)`, the two arguments of the
outer logarithms are positive, and `log` is monotone, so it suffices to compare
the quotients.  Cross-multiplying reduces this to
`rothNumberNat (N * q) ≤ q * rothNumberNat N`, which is
`rothNumberNat_mul_le_comm`.  Both hypotheses are needed: the statement is only
used at positive inputs and positivity of the two log arguments is what licenses
`Real.log_le_log`. -/
theorem rothLogDeficit_mono_mul {N q : ℕ} (hN : 1 ≤ N) (hq : 1 ≤ q) :
    rothLogDeficit N ≤ rothLogDeficit (N * q) := by
  have hNq : 1 ≤ N * q := by simpa using Nat.mul_le_mul hN hq
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hb : (0 : ℝ) < (rothNumberNat N : ℝ) := rothNumberNat_pos_real hN
  have hd : (0 : ℝ) < (rothNumberNat (N * q) : ℝ) := rothNumberNat_pos_real hNq
  have hsub : rothNumberNat (N * q) ≤ q * rothNumberNat N :=
    rothNumberNat_mul_le_comm N q
  have hcast : (rothNumberNat (N * q) : ℝ) ≤ (q : ℝ) * (rothNumberNat N : ℝ) := by
    exact_mod_cast hsub
  have hle : (N : ℝ) / (rothNumberNat N : ℝ) ≤
      ((N * q : ℕ) : ℝ) / (rothNumberNat (N * q) : ℝ) := by
    rw [div_le_div_iff₀ hb hd]
    have hmul : (N : ℝ) * (rothNumberNat (N * q) : ℝ) ≤
        (N : ℝ) * ((q : ℝ) * (rothNumberNat N : ℝ)) :=
      mul_le_mul_of_nonneg_left hcast (Nat.cast_nonneg N)
    push_cast
    linarith [hmul]
  rw [rothLogDeficit, rothLogDeficit]
  exact Real.log_le_log (div_pos hNpos hb) hle

/-- **Sharp fixed-right upper envelope of the Roth product defect.**  For all
`N, M ≥ 1`,

`rothProductDefect N M ≤ rothLogDeficit M + log ((2 * M - 1) / M)`.

The exact defect identity splits off the `N`-dependence as
`rothLogDeficit N - rothLogDeficit (N * (2 * M - 1))`, which is nonpositive by
the monotonicity `rothLogDeficit_mono_mul` at `q = 2 * M - 1 ≥ 1`.  The remaining
terms depend only on `M`, giving the envelope with
`T_M = rothLogDeficit M + log ((2 * M - 1) / M)`.

All inputs are positive, so the identity is applied strictly off its zero cases.
This is an upper bound only: it does not assert that the bound is attained, and
it does not pin down the limit or `liminf` of `rothProductDefect (·, M)`. -/
theorem rothProductDefect_le_rothLogDeficit_add_log {N M : ℕ} (hN : 1 ≤ N)
    (hM : 1 ≤ M) :
    rothProductDefect N M ≤
      rothLogDeficit M + Real.log (((2 * M - 1 : ℕ) : ℝ) / (M : ℝ)) := by
  have hq1 : 1 ≤ 2 * M - 1 := by omega
  have hmono := rothLogDeficit_mono_mul (N := N) (q := 2 * M - 1) hN hq1
  rw [rothProductDefect_eq_rothLogDeficit hN hM]
  linarith

/-- **Arbitrarily late one-sided approximation of the fixed-right threshold.**
For every `M ≥ 2` and every `ε > 0` the Roth product defect lies eventually,
and arbitrarily often, in the interval `(T_M - ε, T_M]`, where
`T_M = rothLogDeficit M + log ((2 * M - 1) / M)`:

`∃ᶠ N in atTop, T_M - ε < rothProductDefect N M ∧ rothProductDefect N M ≤ T_M`.

The lower bound is the accepted frequently-exceeded threshold
`frequently_fixed_right_rothProductDefect_gt`, applied at the level `T_M - ε`
(which is below `T_M` because `ε > 0`); the upper bound is the eventual pointwise
envelope `rothProductDefect_le_rothLogDeficit_add_log`, valid for all `N ≥ 1`.

This is a two-sided approximation *from below* and no more: it does **not** prove
that `T_M` is attained for any `N`, does **not** prove that
`rothProductDefect (·, M)` converges, and does **not** assert that
`liminf_N rothProductDefect N M = T_M` (that would require lower bounds
approaching `T_M` from below along a full eventual set, which is not shown
here).  Nothing here resolves Erdős #142. -/
theorem frequently_fixed_right_rothProductDefect_envelope
    {M : ℕ} (hM : 2 ≤ M) {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ N : ℕ in atTop,
      rothLogDeficit M + Real.log (((2 * M - 1 : ℕ) : ℝ) / (M : ℝ)) - ε <
          rothProductDefect N M ∧
        rothProductDefect N M ≤
          rothLogDeficit M + Real.log (((2 * M - 1 : ℕ) : ℝ) / (M : ℝ)) := by
  have hM1 : 1 ≤ M := by omega
  have hgt : ∃ᶠ N : ℕ in atTop,
      rothLogDeficit M + Real.log (((2 * M - 1 : ℕ) : ℝ) / (M : ℝ)) - ε <
        rothProductDefect N M :=
    frequently_fixed_right_rothProductDefect_gt hM (by linarith)
  refine hgt.and_eventually ?_
  refine eventually_atTop.mpr ⟨1, fun N hN => ?_⟩
  exact rothProductDefect_le_rothLogDeficit_add_log hN hM1

/-- **The fixed-right threshold is the least upper bound of the positive-input
range.**  For every `M ≥ 2`,

`IsLUB {y : ℝ | ∃ N : ℕ, 1 ≤ N ∧ y = rothProductDefect N M}
   (rothLogDeficit M + log ((2 * M - 1) / M))`.

Being an upper bound is the pointwise envelope
`rothProductDefect_le_rothLogDeficit_add_log`.  Minimality uses the accepted
threshold saturation `exists_fixed_right_rothProductDefect_gt`: any upper bound
`c` with `c < T_M` is contradicted by some value `rothProductDefect N M` with
`N ≥ 1` exceeding `c`.

This is a statement about the range as an ordered set: it does not assert that
the least upper bound is attained, does not identify any limit or `liminf` of
`rothProductDefect (·, M)`, and does not resolve Erdős #142. -/
theorem isLUB_rothProductDefect_positive_range {M : ℕ} (hM : 2 ≤ M) :
    IsLUB {y : ℝ | ∃ N : ℕ, 1 ≤ N ∧ y = rothProductDefect N M}
      (rothLogDeficit M + Real.log (((2 * M - 1 : ℕ) : ℝ) / (M : ℝ))) := by
  have hM1 : 1 ≤ M := by omega
  constructor
  · intro y hy
    obtain ⟨N, hN, rfl⟩ := hy
    exact rothProductDefect_le_rothLogDeficit_add_log hN hM1
  · intro c hc
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨N, hN, hNc⟩ := exists_fixed_right_rothProductDefect_gt hM hlt
    exact not_le_of_gt hNc (hc ⟨N, hN, rfl⟩)

/-- **Non-vacuity of the block inequality.**  The bound at `q = 3`, `N = 4` is
the concrete true statement `rothNumberNat 12 ≤ 3 * rothNumberNat 4`. -/
example : rothNumberNat (3 * 4) ≤ 3 * rothNumberNat 4 := rothNumberNat_mul_le 3 4

/-- **Ground-truth check of the monotonicity at a nontrivial pair.**  The
log-deficit does not decrease when multiplying `N = 3` by `q = 5`. -/
example : rothLogDeficit 3 ≤ rothLogDeficit (3 * 5) :=
  rothLogDeficit_mono_mul (N := 3) (q := 5) (by norm_num) (by norm_num)

/-- **Non-vacuity of the pointwise envelope.**  At `(N, M) = (1, 2)` the
hypotheses `1 ≤ N`, `1 ≤ M` hold and the bound reads
`rothProductDefect 1 2 ≤ rothLogDeficit 2 + log (3 / 2)`. -/
example : rothProductDefect 1 2 ≤
    rothLogDeficit 2 + Real.log (((2 * 2 - 1 : ℕ) : ℝ) / (2 : ℝ)) :=
  rothProductDefect_le_rothLogDeficit_add_log le_rfl (by norm_num)

/-- **Non-vacuity of the one-sided approximation.**  Specializing the envelope
theorem to `M = 2` and `ε = 1` and extracting a witness gives the genuine
existential statement that some `N` has
`rothLogDeficit 2 + log (3 / 2) - 1 < rothProductDefect N 2`. -/
example : ∃ N : ℕ,
    rothLogDeficit 2 + Real.log (((2 * 2 - 1 : ℕ) : ℝ) / (2 : ℝ)) - 1 <
      rothProductDefect N 2 := by
  obtain ⟨N, h⟩ := (frequently_fixed_right_rothProductDefect_envelope
    (M := 2) (by norm_num) (ε := 1) (by norm_num)).exists
  exact ⟨N, h.1⟩

/-- **Non-vacuity of the `IsLUB` statement.**  At `M = 2` the threshold
`rothLogDeficit 2 + log (3 / 2)` is exhibited as the least upper bound of the
positive-input range of `rothProductDefect (·, 2)`. -/
example : IsLUB {y : ℝ | ∃ N : ℕ, 1 ≤ N ∧ y = rothProductDefect N 2}
    (rothLogDeficit 2 + Real.log (((2 * 2 - 1 : ℕ) : ℝ) / (2 : ℝ))) :=
  isLUB_rothProductDefect_positive_range (M := 2) (by norm_num)

end

end Erdos142

-- Axiom audit for the load-bearing declarations.
#print axioms Erdos142.rothNumberNat_mul_le
#print axioms Erdos142.rothNumberNat_mul_le_comm
#print axioms Erdos142.rothLogDeficit_mono_mul
#print axioms Erdos142.rothProductDefect_le_rothLogDeficit_add_log
#print axioms Erdos142.frequently_fixed_right_rothProductDefect_envelope
#print axioms Erdos142.isLUB_rothProductDefect_positive_range