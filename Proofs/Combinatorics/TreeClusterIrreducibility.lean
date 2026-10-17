import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Algebra.Polynomial.Bivariate
set_option autoImplicit false
open Polynomial
namespace TreeCluster
private theorem linear_primitive (q : ℕ) (hq : 2 ≤ q) :
    (C (X ^ q - 1 : ℚ[X]) * X + C (X : ℚ[X])).IsPrimitive := by
  intro r hr
  have hc := (C_dvd_iff_dvd_coeff r _).mp hr
  have h0 : r ∣ (X : ℚ[X]) := by simpa using hc 0
  have h1 : r ∣ (X ^ q - 1 : ℚ[X]) := by
    simpa only [coeff_add, coeff_C_mul, coeff_X_one, mul_one, coeff_C,
      if_neg (show (1 : ℕ) ≠ 0 by decide), add_zero] using hc 1
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show q ≠ 0 by omega)
  have hp : r ∣ (X : ℚ[X]) ^ (n + 1) := by
    rw [pow_succ]
    exact dvd_mul_of_dvd_right h0 _
  have hu : r ∣ (1 : ℚ[X]) := by
    simpa only [Nat.succ_eq_add_one, sub_sub_cancel] using dvd_sub hp h1
  exact isUnit_of_dvd_one hu
private theorem linear_irreducible (q : ℕ) (hq : 2 ≤ q) :
    Irreducible (C (X ^ q - 1 : ℚ[X]) * X + C (X : ℚ[X])) := by
  apply (linear_primitive q hq).irreducible_iff_irreducible_map_fraction_map
      (K := RatFunc ℚ) |>.mpr
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X]
  apply irreducible_of_degree_eq_one
  have hn : algebraMap ℚ[X] (RatFunc ℚ) (X ^ q - 1) ≠ 0 := by
    apply (map_ne_zero_iff _ (IsFractionRing.injective ℚ[X] (RatFunc ℚ))).mpr
    intro he
    have hc := congrArg (fun p : ℚ[X] => p.coeff q) he
    simp only [coeff_sub, coeff_X_pow, coeff_one,
      if_neg (show q ≠ 0 by omega), sub_zero, coeff_zero] at hc
    exact one_ne_zero hc
  rw [degree_add_eq_left_of_degree_lt]
  · rw [degree_mul, degree_C hn, degree_X, zero_add]
  · rw [degree_mul, degree_C hn, degree_X, zero_add,
      degree_C ((map_ne_zero_iff _ (IsFractionRing.injective ℚ[X] (RatFunc ℚ))).mpr X_ne_zero)]
    exact zero_lt_one
private theorem target_primitive (q : ℕ) (hq : 2 ≤ q) :
    (C (X : ℚ[X]) * X ^ q + X - C (X : ℚ[X])).IsPrimitive := by
  intro r hr
  have hc := (C_dvd_iff_dvd_coeff r _).mp hr 1
  have hq1 : 1 ≠ q := by omega
  have hu : r ∣ (1 : ℚ[X]) := by simpa [coeff_X_pow, hq1] using hc
  exact isUnit_of_dvd_one hu
/-- The rational-function polynomial x V^q + V - x is irreducible for q at least two. -/
theorem irreducible (q : ℕ) (hq : 2 ≤ q) :
    Irreducible (C (RatFunc.X : RatFunc ℚ) * X ^ q + X - C (RatFunc.X : RatFunc ℚ)) := by
  have hs := (MulEquiv.irreducible_iff (Bivariate.swap (R := ℚ))).mpr
    (linear_irreducible q hq)
  have he : Bivariate.swap (C (X ^ q - 1 : ℚ[X]) * X + C (X : ℚ[X])) =
      C (X : ℚ[X]) * X ^ q + X - C (X : ℚ[X]) := by
    simp only [map_add, map_mul, map_sub, map_pow, map_one, Bivariate.swap_Y,
      Bivariate.swap_C, Polynomial.map_X]
    ring
  rw [he] at hs
  have hm := (target_primitive q hq).irreducible_iff_irreducible_map_fraction_map
      (K := RatFunc ℚ) |>.mp hs
  simpa only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, RatFunc.X] using hm
example : Irreducible (C (RatFunc.X : RatFunc ℚ) * X ^ 2 + X -
    C (RatFunc.X : RatFunc ℚ)) := irreducible 2 (by decide)
end TreeCluster
