import Combinatorics.PermutationEndpointZeroTwoExact
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

open Filter Topology

namespace PermutationEndpointZeroTwoRate

private theorem sum_identity (m : ℕ) (hm : 1 ≤ m) :
    (∑ k ∈ Finset.Icc 2 m, 1 / (Nat.factorial (k - 1) : ℝ)) =
      (∑ k ∈ Finset.range m, 1 / (Nat.factorial k : ℝ)) - 1 := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]
    simp only [Nat.add_sub_cancel]
    ring

/-- The factorial sum in the exact finite formula converges to `exp 1 - 1`. -/
theorem tendsto_short_sum :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.Icc 2 (n / 2),
      1 / (Nat.factorial (k - 1) : ℝ)) atTop (nhds (Real.exp 1 - 1)) := by
  have hs : HasSum (fun k : ℕ => 1 / (Nat.factorial k : ℝ)) (Real.exp 1) := by
    simpa [← Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (1 : ℝ)
  have ht := (hs.tendsto_sum_nat.comp (Nat.tendsto_div_const_atTop (by decide : 2 ≠ 0))).sub_const 1
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  exact (sum_identity (n / 2) (by omega)).symm

/-- The parity correction in the actual finite formula tends to zero. -/
theorem tendsto_parity_correction :
    Tendsto (fun n : ℕ => if Odd n then
      1 / (Nat.factorial ((n - 3) / 2) : ℝ) else 0) atTop (nhds 0) := by
  have hi : Tendsto (fun n : ℕ => (n - 3) / 2) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (2 * b + 3)] with n hn
    omega
  have hf : Tendsto (fun n : ℕ => 1 / (Nat.factorial ((n - 3) / 2) : ℝ))
      atTop (nhds 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp (factorial_tendsto_atTop.comp hi) :
        Tendsto (fun n : ℕ => (Nat.factorial ((n - 3) / 2) : ℝ)) atTop atTop)
  apply squeeze_zero (fun n => ?_) (fun n => ?_) hf
  · split_ifs <;> positivity
  · split_ifs
    · exact le_rfl
    · positivity

/-- The sharp scaled failure rate for the actual uniform endpoint-zero/two
permutation experiment is `exp 1 - 1`. -/
theorem tendsto_scaled_failure :
    Tendsto (fun n : ℕ => (n : ℝ) * (1 - PermutationSameEdgeLimit.F n 0 2))
      atTop (nhds (Real.exp 1 - 1)) := by
  have hr : Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) - 2)) atTop (nhds 1) := by
    simpa only [sub_eq_add_neg] using tendsto_natCast_div_add_atTop (-2 : ℝ)
  have ht := hr.mul (tendsto_short_sum.add tendsto_parity_correction)
  simp only [add_zero, one_mul] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
  rw [PermutationEndpointZeroTwoExact.one_sub_F_zero_two hn]
  ring

end PermutationEndpointZeroTwoRate
