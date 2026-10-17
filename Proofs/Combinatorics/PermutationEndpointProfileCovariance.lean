import Combinatorics.PermutationJointEndpointProfile
import Combinatorics.PermutationCovarianceConsumer

set_option autoImplicit false

noncomputable section

namespace PermutationEndpointProfileCovariance

open Filter Topology PermutationEndpointProfile PermutationAvoidanceCovariance
open PermutationJointEndpointProfile

/-- The same continuous residual-bearing profile and positive normalizer governing all
actual full-avoidance conditional endpoint limits have coordinate means one half.
Their covariance, centered at these actual profile means, is at least `191/201600`
and strictly greater than `1/1152`. All original profile and limit conclusions are retained. -/
theorem exists_actual_conditional_endpoint_limit_with_covariance :
    ∃ (P : ℝ × ℝ → ℝ) (Z : ℝ),
      ContinuousOn P (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) ∧
      (∀ z ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1, 0 ≤ P z ∧ P z ≤ 1) ∧
      TendstoUniformlyOn profileApprox P atTop
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) ∧
      (∀ K z, z ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 →
        0 ≤ profileApprox K z - P z ∧ profileApprox K z - P z ≤ 6 / ((K + 3) / 3).factorial) ∧
      Z = (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, P (x, y)) ∧
      (16991 / 50400 : ℝ) ≤ Z ∧ 0 < Z ∧
      (∀ n : ℕ, 30 ≤ n → 0 < (avoiding n).card) ∧
      (∀ phi : ℝ × ℝ → ℝ,
        ContinuousOn phi (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) →
        Tendsto (actualConditionalEndpointAverage phi) atTop
          (𝓝 ((∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, phi (x, y) * P (x, y)) / Z))) ∧
      ((∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, x * P (x, y)) / Z = 1 / 2) ∧
      ((∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, y * P (x, y)) / Z = 1 / 2) ∧
      (191 / 201600 : ℝ) ≤
        (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
          (x - (∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, u * P (u, v)) / Z) *
          (y - (∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, v * P (u, v)) / Z) *
          P (x, y)) / Z ∧
      (1 / 1152 : ℝ) <
        (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
          (x - (∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, u * P (u, v)) / Z) *
          (y - (∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, v * P (u, v)) / Z) *
          P (x, y)) / Z := by
  obtain ⟨P, Z, hcont, hunit, hu, hP, hZ, hZlower, hZpos, hcard, hlimit⟩ :=
    exists_actual_conditional_endpoint_limit
  have hfirst :
      (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, x * P (x, y)) / Z = 1 / 2 := by
    have ht := hlimit (fun z => z.1) continuous_fst.continuousOn
    apply tendsto_nhds_unique ht
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 30] with n hn
    have hn2 : 2 ≤ n := by omega
    have hH := (PermutationCovarianceConsumer.actual_endpoint_covariance_lower hn).1
    simpa only [actualConditionalEndpointAverage, dif_pos hn2, mean] using
      (mean_coordinate hn2 hH (⟨0, by omega⟩ : Fin n)).symm
  have hsecond :
      (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, y * P (x, y)) / Z = 1 / 2 := by
    have ht := hlimit (fun z => z.2) continuous_snd.continuousOn
    apply tendsto_nhds_unique ht
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 30] with n hn
    have hn2 : 2 ≤ n := by omega
    have hH := (PermutationCovarianceConsumer.actual_endpoint_covariance_lower hn).1
    simpa only [actualConditionalEndpointAverage, dif_pos hn2, mean] using
      (mean_coordinate hn2 hH (⟨n - 1, by omega⟩ : Fin n)).symm
  have hcentered : (191 / 201600 : ℝ) ≤
      (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
        (x - 1 / 2) * (y - 1 / 2) * P (x, y)) / Z := by
    have ht := hlimit (fun z => (z.1 - 1 / 2) * (z.2 - 1 / 2))
      (by fun_prop)
    apply ge_of_tendsto ht
    filter_upwards [eventually_ge_atTop 30] with n hn
    have hn2 : 2 ≤ n := by omega
    obtain ⟨hH, hcov, _⟩ := PermutationCovarianceConsumer.actual_endpoint_covariance_lower hn
    rw [covariance_eq_centered hn2 hH] at hcov
    simpa only [actualConditionalEndpointAverage, dif_pos hn2, mean] using hcov
  refine ⟨P, Z, hcont, hunit, hu, hP, hZ, hZlower, hZpos, hcard, hlimit,
    hfirst, hsecond, ?_, ?_⟩
  · simpa only [hfirst, hsecond] using hcentered
  · have hstrict : (1 / 1152 : ℝ) < 191 / 201600 := by norm_num
    simpa only [hfirst, hsecond] using hstrict.trans_le hcentered

example : Nonempty (Fin 30) ∧ 0 < (avoiding 30).card ∧
    (⟨0, by omega⟩ : Fin 30) ≠ ⟨30 - 1, by omega⟩ := by
  exact ⟨⟨0⟩, actual_avoiding_card_pos (by decide), by decide⟩

example : ((0 : ℝ), (0 : ℝ)) ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 :=
  ⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl, zero_le_one⟩⟩

end PermutationEndpointProfileCovariance
