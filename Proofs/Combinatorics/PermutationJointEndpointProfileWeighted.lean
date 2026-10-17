import Combinatorics.PermutationJointEndpointProfileGrid

set_option autoImplicit false

namespace PermutationJointEndpointProfile

open scoped BigOperators
open Filter Topology PermutationEndpointProfile

/-- Actual endpoint normalization stays in the unit interval and differs from left-grid normalization by at most one mesh. -/
theorem endpoint_scale {n : ℕ} (hn : 2 ≤ n) (a : Fin n) :
    (a.val : ℝ) / ((n : ℝ) - 1) ∈ Set.Icc (0 : ℝ) 1 ∧
      dist ((a.val : ℝ) / ((n : ℝ) - 1)) ((a.val : ℝ) / n) ≤ 1 / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have ha : (a.val : ℝ) ≤ (n : ℝ) - 1 := by
    have : (a.val : ℝ) + 1 ≤ n := by exact_mod_cast (by omega : a.val + 1 ≤ n)
    linarith
  have hv : (a.val : ℝ) / ((n : ℝ) - 1) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by positivity, (div_le_one hn1).mpr ha⟩
  refine ⟨hv, ?_⟩
  have hid : (a.val : ℝ) / ((n : ℝ) - 1) - (a.val : ℝ) / n =
      ((a.val : ℝ) / ((n : ℝ) - 1)) * (1 / n) := by
    field_simp
    ring
  rw [Real.dist_eq, hid, abs_of_nonneg (by positivity)]
  exact (mul_le_mul_of_nonneg_right hv.2 (by positivity)).trans_eq (one_mul _)

example : (1 : ℝ) / ((2 : ℝ) - 1) ∈ Set.Icc (0 : ℝ) 1 ∧
    dist ((1 : ℝ) / ((2 : ℝ) - 1)) ((1 : ℝ) / 2) ≤ 1 / 2 :=
by simpa using endpoint_scale (by decide) (1 : Fin 2)

/-- The residual-bearing profile approximates every valid distinct actual fiber uniformly as the size tends to infinity. -/
theorem actual_profile_uniform (P : ℝ × ℝ → ℝ)
    (hP : ∀ K z, z ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 →
      0 ≤ profileApprox K z - P z ∧ profileApprox K z - P z ≤ 6 / ((K + 3) / 3).factorial)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ a b : Fin n, a ≠ b →
      |PermutationSameEdgeLimit.F n a.val b.val -
        P ((a.val : ℝ) / n, (b.val : ℝ) / n)| ≤ ε := by
  obtain ⟨K, hK⟩ := (profile_tail_tendsto.eventually_lt tendsto_const_nhds
    (show (0 : ℝ) < ε / 2 by positivity)).exists
  let C : ℝ := ((2 * (K + 3) - 2).factorial : ℝ) *
    (2 * (2 * (K + 3) - 2 - 2 : ℕ) * ((2 * (K + 3) - 2 - 2 : ℕ) + 2))
  have hc : Tendsto (fun n : ℕ => C / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_natCast_atTop_atTop.const_div_atTop C
  filter_upwards [eventually_ge_atTop 3, eventually_ge_atTop (2 * (K + 3) - 2),
    eventually_ge_atTop ((2 * (K + 3) - 2 - 2) * (2 * (K + 3) - 2 - 2 + 3)),
    hc.eventually_lt tendsto_const_nhds (show (0 : ℝ) < ε / 2 by positivity)]
    with n hn hsize hlarge hcn
  intro a b hab
  have he := actual_profile_error P hP K n a.val b.val hn a.isLt b.isLt
    (fun he => hab (Fin.ext he)) hsize hlarge
  have hid : ((2 * (K + 3) - 2).factorial : ℝ) *
      (2 * (2 * (K + 3) - 2 - 2 : ℕ) * ((2 * (K + 3) - 2 - 2 : ℕ) + 2) / n) = C / n := by
    dsimp [C]
    ring
  rw [hid] at he
  linarith

/-- Every continuous test function has the actual ordered-distinct weighted profile limit, using the actual endpoint normalization. -/
theorem actual_weighted_tendsto (P : ℝ × ℝ → ℝ)
    (hcont : ContinuousOn P (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1))
    (hunit : ∀ z ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1, 0 ≤ P z ∧ P z ≤ 1)
    (hP : ∀ K z, z ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 →
      0 ≤ profileApprox K z - P z ∧ profileApprox K z - P z ≤ 6 / ((K + 3) / 3).factorial)
    (phi : ℝ × ℝ → ℝ)
    (hphi : ContinuousOn phi (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)) :
    Tendsto (fun n : ℕ => (∑ a : Fin n, ∑ b : Fin n with a ≠ b,
      phi ((a.val : ℝ) / ((n : ℝ) - 1), (b.val : ℝ) / ((n : ℝ) - 1)) *
        PermutationSameEdgeLimit.F n a.val b.val) / ((n : ℝ) * ((n : ℝ) - 1)))
      atTop (𝓝 (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, phi (x, y) * P (x, y))) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hphi
  let B : ℝ := max M 1
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hbound : ∀ z ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1, |phi z| ≤ B := by
    intro z hz
    have hm : |phi z| ≤ M := by simpa only [Real.norm_eq_abs] using hM z hz
    exact hm.trans (le_max_left _ _)
  have huc := (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hphi
  have hgrid := distinct_grid_tendsto (fun z => phi z * P z) (hphi.mul hcont)
  have hi : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_natCast_atTop_atTop.const_div_atTop 1
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp huc (ε / 4) (by positivity)
  filter_upwards [eventually_ge_atTop 2,
    actual_profile_uniform P hP (ε / (4 * B)) (by positivity),
    hi.eventually_lt tendsto_const_nhds hδ,
    Metric.tendsto_nhds.mp hgrid (ε / 4) (by positivity)] with n hn hprof hmesh hgr
  have hpair (a : Fin n) (b : {b : Fin n // b ≠ a}) :
      |phi ((a.val : ℝ) / ((n : ℝ) - 1), (b.val.val : ℝ) / ((n : ℝ) - 1)) *
          PermutationSameEdgeLimit.F n a.val b.val.val -
        phi ((a.val : ℝ) / n, (b.val.val : ℝ) / n) *
          P ((a.val : ℝ) / n, (b.val.val : ℝ) / n)| ≤ ε / 2 := by
    let u : ℝ × ℝ := ((a.val : ℝ) / n, (b.val.val : ℝ) / n)
    let v : ℝ × ℝ := ((a.val : ℝ) / ((n : ℝ) - 1), (b.val.val : ℝ) / ((n : ℝ) - 1))
    have hu : u ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 :=
      ⟨grid_mem (by omega) a, grid_mem (by omega) b.val⟩
    have hv : v ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 :=
      ⟨(endpoint_scale hn a).1, (endpoint_scale hn b.val).1⟩
    have hdist : dist v u < δ := by
      rw [Prod.dist_eq, max_lt_iff]
      exact ⟨(endpoint_scale hn a).2.trans_lt hmesh, (endpoint_scale hn b.val).2.trans_lt hmesh⟩
    have hphierr : |phi v - phi u| ≤ ε / 4 :=
      le_of_lt (by simpa only [Real.dist_eq] using hmod v hv u hu hdist)
    have hp : |P u| ≤ 1 := by rw [abs_of_nonneg (hunit u hu).1]; exact (hunit u hu).2
    have hf := hprof a b.val b.property.symm
    change |phi v * PermutationSameEdgeLimit.F n a.val b.val.val - phi u * P u| ≤ ε / 2
    calc
      _ = |phi v * (PermutationSameEdgeLimit.F n a.val b.val.val - P u) +
          (phi v - phi u) * P u| := by congr 1; ring
      _ ≤ |phi v * (PermutationSameEdgeLimit.F n a.val b.val.val - P u)| +
          |(phi v - phi u) * P u| := abs_add_le _ _
      _ ≤ B * (ε / (4 * B)) + (ε / 4) * 1 := by
        simp only [abs_mul]
        exact add_le_add (mul_le_mul (hbound v hv) hf (abs_nonneg _) (le_of_lt hB))
          (mul_le_mul hphierr hp (abs_nonneg _) (by positivity))
      _ = ε / 2 := by field_simp; ring
  rw [filtered_average_eq]
  have herr := distinct_average_abs_le hn (fun a b =>
    phi ((a.val : ℝ) / ((n : ℝ) - 1), (b.val.val : ℝ) / ((n : ℝ) - 1)) *
      PermutationSameEdgeLimit.F n a.val b.val.val -
    phi ((a.val : ℝ) / n, (b.val.val : ℝ) / n) *
      P ((a.val : ℝ) / n, (b.val.val : ℝ) / n)) (ε / 2) hpair
  simp only [Finset.sum_sub_distrib, sub_div] at herr
  rw [Real.dist_eq] at hgr ⊢
  apply lt_of_le_of_lt (abs_sub_le _
    ((∑ a : Fin n, (∑ b : {b : Fin n // b ≠ a},
      phi ((a.val : ℝ) / n, (b.val.val : ℝ) / n) *
        P ((a.val : ℝ) / n, (b.val.val : ℝ) / n)) / ((n : ℝ) - 1)) / n) _)
  linarith only [herr, hgr, hε]

end PermutationJointEndpointProfile
