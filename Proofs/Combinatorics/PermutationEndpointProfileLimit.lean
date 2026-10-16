import Combinatorics.PermutationEndpointProfileTransfer

set_option autoImplicit false

namespace PermutationEndpointProfile

open Filter
open scoped Topology

/-- The uniform truncation errors tend to zero along the cutoff sequence. -/
theorem profile_tail_tendsto :
    Tendsto (fun K : ℕ => (6:ℝ)/((K+3)/3).factorial) atTop (𝓝 0) := by
  apply PermutationEndpointOverlapTail.tendsto_bound.comp
  apply tendsto_atTop.2
  intro k
  exact eventually_atTop.2 ⟨k,fun j hj => by omega⟩

/-- The actual boundary polynomials form a uniformly Cauchy sequence on the
entire closed square. -/
theorem profileApprox_uniformCauchy :
    UniformCauchySeqOn profileApprox atTop
      (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1) := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  have he := profile_tail_tendsto.eventually_lt tendsto_const_nhds hε
  obtain ⟨N,hN⟩ := eventually_atTop.1 he
  refine ⟨N,fun m hm n hn z hz => ?_⟩
  have hm' := profileApprox_sub_bounds N m hm z hz
  have hn' := profileApprox_sub_bounds N n hn z hz
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [hN N le_rfl]

/-- The actual boundary polynomials have a continuous uniform limit on the
closed square, valued in the unit interval and with the one-sided uniform tail. -/
theorem exists_continuous_profile_limit :
    ∃ P : ℝ × ℝ → ℝ,
      ContinuousOn P (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1) ∧
      (∀ z ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1, 0 ≤ P z ∧ P z ≤ 1) ∧
      TendstoUniformlyOn profileApprox P atTop
        (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1) ∧
      (∀ K z, z ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1 →
        0 ≤ profileApprox K z-P z ∧
          profileApprox K z-P z ≤ 6/((K+3)/3).factorial) := by
  classical
  let S := Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1
  have hc := profileApprox_uniformCauchy
  have hex : ∀ z ∈ S, ∃ l : ℝ, Tendsto (fun K => profileApprox K z) atTop (𝓝 l) := by
    intro z hz
    exact cauchySeq_tendsto_of_complete (hc.cauchySeq hz)
  let P : ℝ × ℝ → ℝ := fun z => if hz : z ∈ S then (hex z hz).choose else 0
  have hp : ∀ z ∈ S, Tendsto (fun K => profileApprox K z) atTop (𝓝 (P z)) := by
    intro z hz
    dsimp only [P]
    rw [dif_pos hz]
    exact (hex z hz).choose_spec
  have hu := hc.tendstoUniformlyOn_of_tendsto hp
  refine ⟨P, hu.continuousOn ?_, ?_, hu, ?_⟩
  · exact Frequently.of_forall (fun K => (continuous_profileApprox K).continuousOn)
  · intro z hz
    exact ⟨ge_of_tendsto (hp z hz)
      (Eventually.of_forall (fun K => (profileApprox_mem_unit K z hz).1)),
      le_of_tendsto (hp z hz)
      (Eventually.of_forall (fun K => (profileApprox_mem_unit K z hz).2))⟩
  · intro K z hz
    have ht : Tendsto (fun J => profileApprox K z-profileApprox J z) atTop
        (𝓝 (profileApprox K z-P z)) := tendsto_const_nhds.sub (hp z hz)
    have hb : ∀ᶠ J in atTop,
        0 ≤ profileApprox K z-profileApprox J z ∧
          profileApprox K z-profileApprox J z ≤ 6/((K+3)/3).factorial := by
      filter_upwards [eventually_ge_atTop K] with J hJ
      exact profileApprox_sub_bounds K J hJ z hz
    exact ⟨ge_of_tendsto ht (hb.mono fun _ h => h.1),
      le_of_tendsto ht (hb.mono fun _ h => h.2)⟩

end PermutationEndpointProfile
