/-
  Erdős Problem #142 — the finite logarithmic kernel of the critical-contraction
  transfer lemma.

  Write `r = rothNumberNat`, `λ N = rothLogDeficit N = log (N / r N)` and
  `h = log 2`.  This file formalizes exactly the two *directed* finite log
  inequalities of `Documents/erdos142-critical-contraction-regularity.md`, with
  no asymptotic hypothesis, no envelope, and no assertion of `P`:

  * `rothLogDeficit_le_add_log_two` — the interval-partition (one-scale
    window-covering) comparison: for `1 ≤ L ≤ M`,
    `λ L ≤ λ M + h`.  It is the logarithmic form of the integer inequality
    `L * r M ≤ 2 * M * r L` (`Erdos142.mul_rothNumberNat_le_two_mul_mul`).

  * `rothLogDeficit_two_mul_mul_le` — the carry-free product comparison: for
    `1 ≤ a` and `1 ≤ b`, `λ (2 * a * b) ≤ h + λ a + λ b`.  It is the logarithmic
    form of `r a * r b ≤ r (2 * a * b)`
    (`Erdos142.rothNumberNat_mul_le_rothNumberNat_two_mul_mul`), with the
    direction preserved through `log`.

  * `criticalContraction_upper` — inequality (1) of the note: for
    `1 ≤ a ≤ x`, `λ a - λ x ≤ h`.

  * `criticalContraction_lower` — inequality (2) of the note: for `1 ≤ x`,
    `1 ≤ a`, `1 ≤ b` and `x ≤ 2 * a * b`,
    `λ x - λ a ≤ λ b + 2 * h`.

  * `criticalContractionTransfer` — the conjunction of the two exact finite
    inequalities under the note's hypotheses `a ≤ x` and `x ≤ 2 * a * b`.

  Direction is preserved throughout: no monotonicity of `λ` for arbitrary
  arguments is used or claimed, so neither `λ x ≥ λ a` nor a fixed sign for
  the difference in (1) is asserted.  Nothing here resolves Erdős #142.

  No `sorry`, no `unsafe`, no new axioms; the axiom audit is at the end.
-/

import Erdos.Erdos142.ScaleProduct
import Erdos.Erdos142.ProductDefect
import Erdos.Erdos142.OneScaleLPObstruction

set_option autoImplicit false

namespace Erdos142

noncomputable section

/-- **Interval-partition comparison for the log-deficit.**  For naturals `L, M`
with `1 ≤ L` and `L ≤ M`,

`rothLogDeficit L ≤ rothLogDeficit M + log 2`.

This is the logarithmic form of the one-scale window-covering bound
`L * rothNumberNat M ≤ 2 * M * rothNumberNat L`
(`mul_rothNumberNat_le_two_mul_mul`): dividing by the positive quantity
`M * rothNumberNat M` turns it into `L / (2 * r L) ≤ M / (r M)`, and `log` is
monotone, with `log (L / (2 * r L)) = λ L - log 2`.  Written additively, the
same statement is `λ M ≥ λ L - log 2`, which is the note's "partitioning"
inequality `x ≥ y ≥ 1 → λ x ≥ λ y - h` at `x = M`, `y = L`.  Only this
*directed* comparison is asserted; no reverse inequality is claimed. -/
theorem rothLogDeficit_le_add_log_two {L M : ℕ} (hL1 : 1 ≤ L) (hLM : L ≤ M) :
    rothLogDeficit L ≤ rothLogDeficit M + Real.log 2 := by
  have hM1 : 1 ≤ M := hL1.trans hLM
  have hrL : (0 : ℝ) < (rothNumberNat L : ℝ) := rothNumberNat_pos_real hL1
  have hrM : (0 : ℝ) < (rothNumberNat M : ℝ) := rothNumberNat_pos_real hM1
  have hcore : L * rothNumberNat M ≤ 2 * M * rothNumberNat L :=
    mul_rothNumberNat_le_two_mul_mul hL1 hLM
  have hcast : (L : ℝ) * (rothNumberNat M : ℝ) ≤
      2 * (M : ℝ) * (rothNumberNat L : ℝ) := by
    exact_mod_cast hcore
  have hdiv : (L : ℝ) / (2 * (rothNumberNat L : ℝ)) ≤
      (M : ℝ) / (rothNumberNat M : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) hrM]
    linarith [hcast]
  have hlog := Real.log_le_log (by positivity) hdiv
  have hsplit : Real.log ((L : ℝ) / (2 * (rothNumberNat L : ℝ))) =
      Real.log ((L : ℝ) / (rothNumberNat L : ℝ)) - Real.log 2 := by
    rw [show (L : ℝ) / (2 * (rothNumberNat L : ℝ)) =
          ((L : ℝ) / (rothNumberNat L : ℝ)) / 2 by ring,
      Real.log_div (by positivity) (by norm_num : (2 : ℝ) ≠ 0)]
  simp only [rothLogDeficit] at hlog ⊢
  linarith [hlog, hsplit]

/-- **Carry-free product comparison for the log-deficit.**  For naturals `a, b`
with `1 ≤ a` and `1 ≤ b`,

`rothLogDeficit (2 * a * b) ≤ log 2 + rothLogDeficit a + rothLogDeficit b`.

This is the logarithmic form of the carry-free product inequality
`rothNumberNat a * rothNumberNat b ≤ rothNumberNat (2 * a * b)`
(`rothNumberNat_mul_le_rothNumberNat_two_mul_mul`).  Dividing the integer
inequality by `rothNumberNat (2 * a * b)` gives
`(2 * a * b) / r (2 * a * b) ≤ 2 * (a / r a) * (b / r b)`, and taking `log`
yields the claim because `log (2 * X * Y) = log 2 + log X + log Y` for positive
`X, Y`.  The direction of the product inequality is preserved by `log`; no
reverse inequality is asserted. -/
theorem rothLogDeficit_two_mul_mul_le {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    rothLogDeficit (2 * a * b) ≤ Real.log 2 + rothLogDeficit a + rothLogDeficit b := by
  have h2ab : 1 ≤ 2 * a * b := by nlinarith [ha, hb]
  have hra : (0 : ℝ) < (rothNumberNat a : ℝ) := rothNumberNat_pos_real ha
  have hrb : (0 : ℝ) < (rothNumberNat b : ℝ) := rothNumberNat_pos_real hb
  have hr2 : (0 : ℝ) < (rothNumberNat (2 * a * b) : ℝ) := rothNumberNat_pos_real h2ab
  have hnum : (0 : ℝ) < ((2 * a * b : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * a * b)
  have hprod : rothNumberNat a * rothNumberNat b ≤ rothNumberNat (2 * a * b) :=
    rothNumberNat_mul_le_rothNumberNat_two_mul_mul a b
  have hcast : (rothNumberNat a : ℝ) * (rothNumberNat b : ℝ) ≤
      (rothNumberNat (2 * a * b) : ℝ) := by
    exact_mod_cast hprod
  have hdiv : ((2 * a * b : ℕ) : ℝ) / (rothNumberNat (2 * a * b) : ℝ) ≤
      ((2 * a * b : ℕ) : ℝ) / ((rothNumberNat a : ℝ) * (rothNumberNat b : ℝ)) := by
    rw [div_le_div_iff₀ hr2 (mul_pos hra hrb)]
    exact mul_le_mul_of_nonneg_left hcast (le_of_lt hnum)
  have hlog := Real.log_le_log (div_pos hnum hr2) hdiv
  have hrhs : Real.log (((2 * a * b : ℕ) : ℝ) /
        ((rothNumberNat a : ℝ) * (rothNumberNat b : ℝ))) =
      Real.log 2 + Real.log ((a : ℝ) / (rothNumberNat a : ℝ)) +
        Real.log ((b : ℝ) / (rothNumberNat b : ℝ)) := by
    have hane : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hbne : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hrane : (rothNumberNat a : ℝ) ≠ 0 := ne_of_gt hra
    have hrbne : (rothNumberNat b : ℝ) ≠ 0 := ne_of_gt hrb
    have hXne : (a : ℝ) / (rothNumberNat a : ℝ) ≠ 0 := div_ne_zero hane hrane
    have hYne : (b : ℝ) / (rothNumberNat b : ℝ) ≠ 0 := div_ne_zero hbne hrbne
    have hprod' : ((2 * a * b : ℕ) : ℝ) /
          ((rothNumberNat a : ℝ) * (rothNumberNat b : ℝ)) =
        2 * ((a : ℝ) / (rothNumberNat a : ℝ)) *
          ((b : ℝ) / (rothNumberNat b : ℝ)) := by
      push_cast
      field_simp
    rw [hprod',
      Real.log_mul (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hXne) hYne,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hXne]
  simp only [rothLogDeficit] at hlog ⊢
  linarith [hlog, hrhs]

/-- **Critical-contraction transfer, first (upper) direction (1).**  For naturals
`a, x` with `1 ≤ a` and `a ≤ x`,

`rothLogDeficit a - rothLogDeficit x ≤ log 2`.

This is inequality (1) of the note, obtained from the interval-partition
comparison `rothLogDeficit_le_add_log_two` at `L = a`, `M = x`.  In particular
no lower bound on `rothLogDeficit x - rothLogDeficit a` is implied; the
difference in (1) has no asserted sign. -/
theorem criticalContraction_upper {x a : ℕ} (ha : 1 ≤ a) (hax : a ≤ x) :
    rothLogDeficit a - rothLogDeficit x ≤ Real.log 2 := by
  have h := rothLogDeficit_le_add_log_two ha hax
  linarith

/-- **Critical-contraction transfer, second (lower) direction (2).**  For naturals
`x, a, b` with `1 ≤ x`, `1 ≤ a`, `1 ≤ b` and `x ≤ 2 * a * b`,

`rothLogDeficit x - rothLogDeficit a ≤ rothLogDeficit b + 2 * log 2`.

This is inequality (2) of the note.  Partitioning at `L = x`, `M = 2 * a * b`
gives `λ x ≤ λ (2 * a * b) + log 2`, and the carry-free product comparison
`rothLogDeficit_two_mul_mul_le` gives
`λ (2 * a * b) ≤ log 2 + λ a + λ b`.  Adding the two `log 2` terms and
subtracting `λ a` yields the claim.  No monotonicity of `λ` is used and the
inequality is one-sided. -/
theorem criticalContraction_lower {x a b : ℕ} (hx : 1 ≤ x) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hx2 : x ≤ 2 * a * b) :
    rothLogDeficit x - rothLogDeficit a ≤ rothLogDeficit b + 2 * Real.log 2 := by
  have hpart : rothLogDeficit x ≤ rothLogDeficit (2 * a * b) + Real.log 2 :=
    rothLogDeficit_le_add_log_two hx hx2
  have hprod : rothLogDeficit (2 * a * b) ≤
      Real.log 2 + rothLogDeficit a + rothLogDeficit b :=
    rothLogDeficit_two_mul_mul_le ha hb
  linarith

/-- **Finite kernel of the critical-contraction transfer.**  For naturals
`x, a, b` with `1 ≤ x`, `1 ≤ a`, `1 ≤ b`, `a ≤ x` and `x ≤ 2 * a * b`, both
directed inequalities hold:

`rothLogDeficit a - rothLogDeficit x ≤ log 2` and
`rothLogDeficit x - rothLogDeficit a ≤ rothLogDeficit b + 2 * log 2`.

These are exactly the concrete finite instances of (1) and (2) in
`Documents/erdos142-critical-contraction-regularity.md` at the parameters
`x = N ^ 2`, `a = rothNumberNat N ^ 2`, `b = ⌈x / a⌉` (where `a ≤ x` and
`x ≤ 2 * a * b` follow from `rothNumberNat N ≤ N` and the ceiling bound), but
the statement is made for arbitrary naturals satisfying the two inequalities so
that it carries no asymptotic or `P`-related hypothesis. -/
theorem criticalContractionTransfer {x a b : ℕ} (hx : 1 ≤ x) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hax : a ≤ x) (hx2 : x ≤ 2 * a * b) :
    rothLogDeficit a - rothLogDeficit x ≤ Real.log 2 ∧
      rothLogDeficit x - rothLogDeficit a ≤ rothLogDeficit b + 2 * Real.log 2 :=
  ⟨criticalContraction_upper ha hax, criticalContraction_lower hx ha hb hx2⟩

/-- **Non-vacuity of the partition comparison at `(L, M) = (1, 1)`.**  Both
hypotheses `1 ≤ L`, `L ≤ M` hold and the bound reads `0 ≤ 0 + log 2`. -/
example : rothLogDeficit 1 ≤ rothLogDeficit 1 + Real.log 2 :=
  rothLogDeficit_le_add_log_two (L := 1) (M := 1) le_rfl le_rfl

/-- **Ground-truth instance of the partition comparison at `(L, M) = (2, 3)`.**
The bound `λ 2 ≤ λ 3 + log 2` is the concrete true statement obtained from the
known values `rothNumberNat 2 = 2`, `rothNumberNat 3 = 2`. -/
example : rothLogDeficit 2 ≤ rothLogDeficit 3 + Real.log 2 :=
  rothLogDeficit_le_add_log_two (L := 2) (M := 3) (by norm_num) (by norm_num)

/-- **Non-vacuity of the product comparison at `(a, b) = (2, 3)`.**  The claim
`λ 12 ≤ log 2 + λ 2 + λ 3` is the concrete instance of the carry-free product
bound, applied without needing the value of `rothNumberNat 12`. -/
example : rothLogDeficit (2 * 2 * 3) ≤
    Real.log 2 + rothLogDeficit 2 + rothLogDeficit 3 :=
  rothLogDeficit_two_mul_mul_le (a := 2) (b := 3) (by norm_num) (by norm_num)

/-- **Non-vacuity of inequality (1) at `(a, x) = (2, 3)`.**  The hypotheses
`1 ≤ a`, `a ≤ x` hold and the direction `λ 2 - λ 3 ≤ log 2` is the claimed
one. -/
example : rothLogDeficit 2 - rothLogDeficit 3 ≤ Real.log 2 :=
  criticalContraction_upper (a := 2) (x := 3) (by norm_num) (by norm_num)

/-- **Non-vacuity of inequality (2) at `(x, a, b) = (3, 2, 1)`.**  The
hypotheses hold, including `3 ≤ 2 * 2 * 1`, so the bound
`λ 3 - λ 2 ≤ λ 1 + 2 * log 2` is the genuine finite inequality. -/
example : rothLogDeficit 3 - rothLogDeficit 2 ≤ rothLogDeficit 1 + 2 * Real.log 2 :=
  criticalContraction_lower (x := 3) (a := 2) (b := 1) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- **Non-vacuity of the combined transfer at `(x, a, b) = (3, 2, 1)`.**  All
five hypotheses hold and the conjunction of (1) and (2) is asserted. -/
example : rothLogDeficit 2 - rothLogDeficit 3 ≤ Real.log 2 ∧
    rothLogDeficit 3 - rothLogDeficit 2 ≤ rothLogDeficit 1 + 2 * Real.log 2 :=
  criticalContractionTransfer (x := 3) (a := 2) (b := 1) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

end

end Erdos142

-- Axiom audit for the load-bearing declarations.
