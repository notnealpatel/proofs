/-
# A002050: eventual periodicity of a weighted Stirling sum

OEIS A002050, Peter Bala (Aug 03 2023); Stirling-sum formula by Vladimir
Kruchinin (Sep 27 2013). For every positive `k`, `φ(k)` is an eventual
period modulo `k`, by the integral weighted-Stirling theorem.
Related source: Poonen (1988), eventual periodicity of Fubini numbers;
Bala's general A000670 weighted-Stirling comment (Jul 08 2022).
The definition uses `a(0) = 0`, matching the DATA and the e.g.f.
`(exp(2x) - exp(x))/(2 - exp(x))`, rather than the formula comment's `a(0) = 1`.
The e.g.f. and coefficient identity are proved; the barycentric-subdivision
counting interpretation is not formalized.
-/
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Data.ZMod.Basic
import Enumerative.OrdinaryIntegralEGFComposition

set_option autoImplicit false

namespace Candidates.A002050SimplicesBarycentricSubdivision

open PowerSeries Finset

/-! ## Definitions -/

/-- Ordinary coefficients of `G(Y) = Y(1+Y)/(1-Y) = Y + 2Y^2 + 2Y^3 + ⋯`,
the outer series with `e.g.f. = G(e^x - 1)`. -/
def g : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | _ + 2 => 2

/-- A002050: `a(n) = Σ_{m=0}^{n} g(m) m! S₂(n,m)`, i.e. Kruchinin's
`a(n) = 1 + 2 Σ_{k=2}^{n} k! S₂(n,k)` for `n > 0`, with `a(0) = 0`. -/
def a (n : ℕ) : ℤ :=
  ∑ m ∈ range (n + 1), g m * (m.factorial : ℤ) * (n.stirlingSecond m : ℤ)

/-- The entry's e.g.f. `(exp(2x) - exp(x)) / (2 - exp(x))` in `ℚ⟦X⟧`. -/
noncomputable def egf : PowerSeries ℚ :=
  (exp ℚ ^ 2 - exp ℚ) * (2 - exp ℚ)⁻¹

-- Example: the first nine DATA terms.
example : (List.range 9).map a = [0, 1, 5, 25, 149, 1081, 9365, 94585, 1091669] := by
  decide

/-! ## Bridge to the e.g.f. -/

/-- `G(Y) (1 - Y) = Y + Y^2` over `ℤ`, i.e. `G = Y(1+Y)/(1-Y)`. -/
theorem mk_g_mul_one_sub_X : PowerSeries.mk g * (1 - X) = X + X ^ 2 := by
  ext n
  rcases n with _ | _ | _ | n
  · simp [g]
  · simp [mul_sub, g]
  · simp [mul_sub, g, coeff_X_pow, coeff_X]
  · simp [mul_sub, g, coeff_X_pow, coeff_X]

/-- The same identity after casting the coefficients to `ℚ`. -/
theorem map_mk_g_mul_one_sub_X :
    PowerSeries.map (Int.castRingHom ℚ) (PowerSeries.mk g) * (1 - X) = X + X ^ 2 := by
  have h := congrArg (PowerSeries.map (Int.castRingHom ℚ)) mk_g_mul_one_sub_X
  simpa only [map_mul, map_sub, map_one, map_X, map_add, map_pow] using h

/-- The entry's e.g.f. is the formal composition `G(exp x - 1)`. -/
theorem egf_eq_subst : egf = PowerSeries.subst (exp ℚ - 1)
    (PowerSeries.map (Int.castRingHom ℚ) (PowerSeries.mk g)) := by
  have hc : constantCoeff (exp ℚ - 1) = 0 := by simp
  have ha : HasSubst (exp ℚ - 1) := HasSubst.of_constantCoeff_zero' hc
  set S : PowerSeries ℚ := PowerSeries.subst (exp ℚ - 1)
    (PowerSeries.map (Int.castRingHom ℚ) (PowerSeries.mk g)) with hS
  have h1 : S * (2 - exp ℚ) = exp ℚ ^ 2 - exp ℚ := by
    have h := congrArg (substAlgHom ha) map_mk_g_mul_one_sub_X
    rw [map_mul, map_sub, map_one, map_add, map_pow, substAlgHom_X,
      coe_substAlgHom] at h
    calc S * (2 - exp ℚ) = S * (1 - (exp ℚ - 1)) := by ring
      _ = (exp ℚ - 1) + (exp ℚ - 1) ^ 2 := h
      _ = exp ℚ ^ 2 - exp ℚ := by ring
  have h2 : constantCoeff (2 - exp ℚ) ≠ 0 := by
    rw [map_sub, map_ofNat, constantCoeff_exp]
    norm_num
  unfold egf
  rw [← h1, mul_assoc, PowerSeries.mul_inv_cancel _ h2, mul_one]

/-- `a n = n! · [xⁿ] (exp(2x) - exp x)/(2 - exp x)`: `a` is the entry's sequence. -/
theorem a_eq_factorial_mul_coeff_egf (n : ℕ) :
    (a n : ℚ) = (n.factorial : ℚ) * coeff n egf := by
  rw [egf_eq_subst, OrdinaryIntegralEGF.factorial_mul_coeff_subst_exp_sub_one]
  simp only [a, OrdinaryIntegralEGF.weightedStirlingTransform, coeff_mk]

-- Example through the e.g.f.: `2! · [x²] egf = 5`.
example : ((Nat.factorial 2 : ℕ) : ℚ) * coeff 2 egf = 5 := by
  rw [← a_eq_factorial_mul_coeff_egf]
  have h : a 2 = 5 := by decide
  rw [h]
  norm_num

/-! ## The conjecture -/

/-- For every positive `k`, `φ(k)` is an eventual period of `a mod k`
(Bala's A002050 conjecture), by the weighted-Stirling theorem with weights `g`. -/
theorem a_mod_eventuallyPeriodic (k : ℕ) (hk : 1 ≤ k) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (a (n + Nat.totient k) : ZMod k) = (a n : ZMod k) :=
  OrdinaryIntegralEGF.weightedStirlingTransform_eventuallyPeriodic g k hk

/-- The conjecture in "period dividing `φ(k)`" form, phrased directly on
the integers `n! · [xⁿ] egf`: some positive `P ∣ φ(k)` is an eventual
period modulo `k`. -/
theorem egf_coeff_mod_eventuallyPeriodic (k : ℕ) (hk : 1 ≤ k) :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = (n.factorial : ℚ) * coeff n egf) ∧
      ∃ N P : ℕ, P ∣ Nat.totient k ∧ 0 < P ∧ ∀ n : ℕ, N ≤ n →
        (b (n + P) : ZMod k) = (b n : ZMod k) := by
  obtain ⟨N, hN⟩ := a_mod_eventuallyPeriodic k hk
  exact ⟨a, a_eq_factorial_mul_coeff_egf, N, Nat.totient k, dvd_rfl,
    Nat.totient_pos.mpr hk, hN⟩

/-! ## Examples -/

-- Bala's example modulo 9 (`φ 9 = 6`): `a 11 ≡ a 5 ≡ 1`.
example : (a (5 + Nat.totient 9) : ZMod 9) = (a 5 : ZMod 9) := by
  have h9 : Nat.totient 9 = 6 := by decide
  rw [h9]
  decide

-- "Eventually" is load-bearing: `a 6 = 9365 ≡ 5 (mod 9)` but `a 0 = 0`.
example : (a (0 + Nat.totient 9) : ZMod 9) ≠ (a 0 : ZMod 9) := by
  have h9 : Nat.totient 9 = 6 := by decide
  rw [h9]
  decide

end Candidates.A002050SimplicesBarycentricSubdivision
