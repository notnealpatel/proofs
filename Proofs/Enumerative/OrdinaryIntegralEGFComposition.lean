import Enumerative.OrdinaryIntegralEGF
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.Data.Nat.Choose.Sum

set_option autoImplicit false

open Finset

namespace OrdinaryIntegralEGF

/-- The powers of `exp X - 1` have factorial-scaled Stirling coefficients,
including degree zero and powers above the diagonal. -/
theorem factorial_mul_coeff_exp_sub_one_pow (n m : ℕ) :
    (n.factorial : ℚ) * PowerSeries.coeff n ((PowerSeries.exp ℚ - 1) ^ m) =
      (m.factorial : ℚ) * (n.stirlingSecond m : ℚ) := by
  have hexpand : (PowerSeries.exp ℚ - 1) ^ m =
      ∑ j ∈ range (m + 1), PowerSeries.exp ℚ ^ j *
        PowerSeries.C ((-1 : ℚ) ^ (m - j) * (m.choose j : ℚ)) := by
    simpa only [sub_eq_add_neg, ← map_neg, ← map_one PowerSeries.C,
      ← map_pow, ← map_natCast PowerSeries.C, mul_assoc, ← map_mul] using
      (add_pow (PowerSeries.exp ℚ) (-1) m)
  rw [hexpand, map_sum, Finset.mul_sum]
  have hsum := congrArg (fun z : ℤ => (z : ℚ))
    (factorial_mul_stirlingSecond n m)
  push_cast at hsum
  rw [hsum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [PowerSeries.coeff_mul_C, PowerSeries.exp_pow_eq_rescale_exp,
    PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
  change (n.factorial : ℚ) * ((j : ℚ) ^ n * (1 / (n.factorial : ℚ)) *
    ((-1 : ℚ) ^ (m - j) * (m.choose j : ℚ))) = _
  have hn : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

/-- Above the diagonal the coefficient of a power of `exp X - 1` vanishes. -/
theorem coeff_exp_sub_one_pow_eq_zero {n m : ℕ} (hnm : n < m) :
    PowerSeries.coeff n ((PowerSeries.exp ℚ - 1) ^ m) = 0 := by
  have h := factorial_mul_coeff_exp_sub_one_pow n m
  rw [Nat.stirlingSecond_eq_zero_of_lt hnm, Nat.cast_zero, mul_zero] at h
  exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast n.factorial_ne_zero)

/-- Genuine substitution has a finite coefficient sum, even for arbitrary
infinite and signed ordinary-integral input. -/
theorem coeff_subst_exp_sub_one (G : PowerSeries ℤ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.subst (PowerSeries.exp ℚ - 1)
      (PowerSeries.map (Int.castRingHom ℚ) G)) =
    ∑ m ∈ range (n + 1), ((PowerSeries.coeff m G : ℤ) : ℚ) *
      PowerSeries.coeff n ((PowerSeries.exp ℚ - 1) ^ m) := by
  have hc : PowerSeries.constantCoeff (PowerSeries.exp ℚ - 1) = 0 := by simp
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' hc)]
  simp only [PowerSeries.coeff_map, Int.castRingHom, smul_eq_mul]
  apply finsum_eq_sum_of_support_subset
  intro m hm
  apply Finset.mem_range.mpr
  by_contra hlt
  have hnm : n < m := by omega
  exact hm (by simp [coeff_exp_sub_one_pow_eq_zero hnm])

/-- The factorial-scaled coefficients of actual formal composition with
`exp X - 1` equal the integer weighted Stirling transform of the ordinary
coefficients, without sign, growth, or support restrictions. -/
theorem factorial_mul_coeff_subst_exp_sub_one (G : PowerSeries ℤ) (n : ℕ) :
    (n.factorial : ℚ) * PowerSeries.coeff n
      (PowerSeries.subst (PowerSeries.exp ℚ - 1)
        (PowerSeries.map (Int.castRingHom ℚ) G)) =
      (weightedStirlingTransform (fun m => PowerSeries.coeff m G) n : ℚ) := by
  rw [coeff_subst_exp_sub_one, Finset.mul_sum]
  unfold weightedStirlingTransform
  push_cast
  apply Finset.sum_congr rfl
  intro m hm
  calc
    (n.factorial : ℚ) * (((PowerSeries.coeff m G : ℤ) : ℚ) *
        PowerSeries.coeff n ((PowerSeries.exp ℚ - 1) ^ m)) =
        ((PowerSeries.coeff m G : ℤ) : ℚ) * ((n.factorial : ℚ) *
          PowerSeries.coeff n ((PowerSeries.exp ℚ - 1) ^ m)) := by ring
    _ = _ := by rw [factorial_mul_coeff_exp_sub_one_pow]; ring

/-- Each actual exponential coefficient has a unique integer representative.
The assertion concerns factorial-scaled, not ordinary, coefficients. -/
theorem existsUnique_int_factorial_mul_coeff_subst (G : PowerSeries ℤ) (n : ℕ) :
    ∃! z : ℤ, (z : ℚ) = (n.factorial : ℚ) * PowerSeries.coeff n
      (PowerSeries.subst (PowerSeries.exp ℚ - 1)
        (PowerSeries.map (Int.castRingHom ℚ) G)) := by
  refine ⟨weightedStirlingTransform (fun m => PowerSeries.coeff m G) n,
    (factorial_mul_coeff_subst_exp_sub_one G n).symm, ?_⟩
  intro z hz
  exact_mod_cast hz.trans (factorial_mul_coeff_subst_exp_sub_one G n)

/-- Integer representatives of actual exponential coefficients are eventually
periodic modulo positive `k`, with period `φ(k)`. No rational-to-`ZMod` cast
is used, and `k = 1` is included. -/
theorem factorial_mul_coeff_subst_eventuallyPeriodic (G : PowerSeries ℤ)
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ b : ℕ → ℤ,
      (∀ n, (b n : ℚ) = (n.factorial : ℚ) * PowerSeries.coeff n
        (PowerSeries.subst (PowerSeries.exp ℚ - 1)
          (PowerSeries.map (Int.castRingHom ℚ) G))) ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        (b (n + Nat.totient k) : ZMod k) = (b n : ZMod k) := by
  refine ⟨weightedStirlingTransform (fun m => PowerSeries.coeff m G), ?_, ?_⟩
  · intro n
    exact (factorial_mul_coeff_subst_exp_sub_one G n).symm
  · exact weightedStirlingTransform_eventuallyPeriodic _ k hk

/-- At degree zero genuine composition preserves the input constant. -/
theorem coeff_zero_subst_exp_sub_one (G : PowerSeries ℤ) :
    PowerSeries.coeff 0 (PowerSeries.subst (PowerSeries.exp ℚ - 1)
      (PowerSeries.map (Int.castRingHom ℚ) G)) = ((PowerSeries.coeff 0 G : ℤ) : ℚ) := by
  simpa [weightedStirlingTransform, Nat.stirlingSecond] using
    factorial_mul_coeff_subst_exp_sub_one G 0

/-- A genuine nonconstant model: `G = X` has scaled coefficient one at degree two. -/
theorem model_X_scaled_two :
    (Nat.factorial 2 : ℚ) * PowerSeries.coeff 2
      (PowerSeries.subst (PowerSeries.exp ℚ - 1)
        (PowerSeries.map (Int.castRingHom ℚ) (PowerSeries.X : PowerSeries ℤ))) = 1 := by
  simpa [weightedStirlingTransform, Finset.sum_range_succ, PowerSeries.coeff_X,
    Nat.stirlingSecond] using
    factorial_mul_coeff_subst_exp_sub_one (PowerSeries.X : PowerSeries ℤ) 2

/-- The same genuine model has ordinary coefficient `1/2`, not an integer. -/
theorem model_X_coeff_two :
    PowerSeries.coeff 2 (PowerSeries.subst (PowerSeries.exp ℚ - 1)
      (PowerSeries.map (Int.castRingHom ℚ) (PowerSeries.X : PowerSeries ℤ))) = 1 / 2 := by
  have h := model_X_scaled_two
  norm_num at h ⊢
  linarith

/-- A signed constant model at degree zero witnesses unrestricted negative input. -/
theorem model_negative_constant_zero :
    PowerSeries.coeff 0 (PowerSeries.subst (PowerSeries.exp ℚ - 1)
      (PowerSeries.map (Int.castRingHom ℚ) (PowerSeries.C (-3 : ℤ)))) = -3 := by
  simpa only [PowerSeries.coeff_C, ite_true, Int.cast_neg, Int.cast_ofNat] using
    coeff_zero_subst_exp_sub_one (PowerSeries.C (-3 : ℤ))

/-- The cutoff hypothesis is inhabited: the first positive power has zero constant. -/
theorem model_cutoff_zero_one :
    PowerSeries.coeff 0 ((PowerSeries.exp ℚ - 1) ^ (1 : ℕ)) = 0 :=
  coeff_exp_sub_one_pow_eq_zero (by decide)

/-- The zero input and modulus one jointly instantiate the periodicity hypotheses. -/
theorem model_zero_mod_one :
    ∃ b : ℕ → ℤ,
      (∀ n, (b n : ℚ) = (n.factorial : ℚ) * PowerSeries.coeff n
        (PowerSeries.subst (PowerSeries.exp ℚ - 1)
          (PowerSeries.map (Int.castRingHom ℚ) (0 : PowerSeries ℤ)))) ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        (b (n + Nat.totient 1) : ZMod 1) = (b n : ZMod 1) :=
  factorial_mul_coeff_subst_eventuallyPeriodic 0 1 (by decide)

end OrdinaryIntegralEGF
