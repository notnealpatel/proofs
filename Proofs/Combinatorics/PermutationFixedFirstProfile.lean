import Combinatorics.PermutationFixedFirstProfileAnalysis

set_option autoImplicit false

namespace PermutationFixedFirstProfile

open PermutationFixedFirstLimit PermutationEndpointProfile Filter Topology
open scoped BigOperators

/-- For any residual-bearing continuous endpoint profile, actual first-only avoidance converges to its row integral along every admissible macroscopic first-label sequence. -/
theorem actual_moving_first_tendsto (P : ℝ × ℝ → ℝ)
    (hcont : ContinuousOn P (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1))
    (hunit : ∀ z ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1, 0 ≤ P z ∧ P z ≤ 1)
    (hP : ∀ K z, z ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 →
      0 ≤ profileApprox K z - P z ∧ profileApprox K z - P z ≤ 6 / ((K + 3) / 3).factorial)
    (n m : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (hvalid : ∀ᶠ j in atTop, m j < n j)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hr : Tendsto (fun j => (m j : ℝ) / (n j : ℝ)) atTop (𝓝 x)) :
    Tendsto (fun j => A (n j) (m j)) atTop (𝓝 (∫ y in (0 : ℝ)..1, P (x, y))) := by
  have hu : ∀ᶠ j in atTop, (m j : ℝ) / (n j : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [hvalid, hn.eventually_ge_atTop 1] with j hj hnj
    have hnR : (0 : ℝ) < n j := by exact_mod_cast hnj
    exact ⟨by positivity, (div_le_one hnR).mpr (by exact_mod_cast hj.le)⟩
  have hgrid := grid_moving_tendsto P hcont n (fun j => (m j : ℝ) / n j) hn hu x hx hr
  have hden : Tendsto (fun j => (n j : ℝ) - 1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [(tendsto_natCast_atTop_atTop.comp hn).eventually_ge_atTop (b + 1)] with j hj
    change b + 1 ≤ (n j : ℝ) at hj
    linarith
  have hdiag : Tendsto (fun j => 2 / ((n j : ℝ) - 1)) atTop (𝓝 0) :=
    hden.const_div_atTop 2
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨K, hK⟩ := (profile_tail_tendsto.eventually_lt tendsto_const_nhds
    (show (0 : ℝ) < ε / 4 by positivity)).exists
  let C : ℝ := ((2 * (K + 3) - 2).factorial : ℝ) *
    (2 * (2 * (K + 3) - 2 - 2 : ℕ) * ((2 * (K + 3) - 2 - 2 : ℕ) + 2))
  have hc : Tendsto (fun j => C / (n j : ℝ)) atTop (𝓝 0) :=
    (tendsto_natCast_atTop_atTop.comp hn).const_div_atTop C
  have hce := hc.eventually_lt tendsto_const_nhds (show (0 : ℝ) < ε / 4 by positivity)
  have hde := hdiag.eventually_lt tendsto_const_nhds (show (0 : ℝ) < ε / 4 by positivity)
  have hge := Metric.tendsto_nhds.mp hgrid (ε / 4) (by positivity)
  filter_upwards [hvalid, hu, hn.eventually_ge_atTop 3,
    hn.eventually_ge_atTop (2 * (K + 3) - 2),
    hn.eventually_ge_atTop ((2 * (K + 3) - 2 - 2) * (2 * (K + 3) - 2 - 2 + 3)),
    hce, hde, hge] with j hj huj hnj hsize hlarge hcj hdj hgj
  let a : Fin (n j) := ⟨m j, hj⟩
  let g : Fin (n j) → ℝ := fun b => P ((m j : ℝ) / n j, (b.val : ℝ) / n j)
  let B : ℝ := (∑ b : {b : Fin (n j) // b ≠ a}, g b.val) / ((n j : ℝ) - 1)
  let R : ℝ := (∑ b : Fin (n j), g b) / n j
  have hrow : |A (n j) (m j) - B| ≤ C / n j + 6 / ((K + 3) / 3).factorial := by
    have he := actual_row_error P hP K (n j) hnj a hsize hlarge
    change |A (n j) (m j) - B| ≤ _ at he
    convert he using 1
    dsimp [C]
    ring
  have hbr : |B - R| ≤ 2 / ((n j : ℝ) - 1) := by
    apply omitted_diagonal_error (by omega) a g
    intro b
    have hnR : (0 : ℝ) < n j := by exact_mod_cast (by omega : 0 < n j)
    have hb : (b.val : ℝ) / n j ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨by positivity, (div_le_one hnR).mpr (by exact_mod_cast b.isLt.le)⟩
    have hbound := hunit ((m j : ℝ) / n j, (b.val : ℝ) / n j) ⟨huj, hb⟩
    dsimp [g]
    rw [abs_of_nonneg hbound.1]
    exact hbound.2
  have hrJ : |R - ∫ y in (0 : ℝ)..1, P (x, y)| < ε / 4 := by
    simpa only [Real.dist_eq] using hgj
  have hABR := abs_sub_le (A (n j) (m j)) B R
  have hARJ := abs_sub_le (A (n j) (m j)) R (∫ y in (0 : ℝ)..1, P (x, y))
  rw [Real.dist_eq]
  linarith

/-- There is one continuous endpoint profile, selected with its uniform polynomial residual, whose row integral is continuous on the closed interval and is the actual full first-only avoidance limit for every macroscopic moving first label; its zero-endpoint value is the adopted `L0`. -/
theorem exists_actual_continuous_marginal :
    ∃ (P : ℝ × ℝ → ℝ) (J : ℝ → ℝ),
      ContinuousOn P (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) ∧
      (∀ z ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1, 0 ≤ P z ∧ P z ≤ 1) ∧
      TendstoUniformlyOn profileApprox P atTop
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) ∧
      (∀ K z, z ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 →
        0 ≤ profileApprox K z - P z ∧
          profileApprox K z - P z ≤ 6 / ((K + 3) / 3).factorial) ∧
      (∀ x : ℝ, J x = ∫ y in (0 : ℝ)..1, P (x, y)) ∧
      ContinuousOn J (Set.Icc (0 : ℝ) 1) ∧
      (∀ (n m : ℕ → ℕ), Tendsto n atTop atTop →
        (∀ᶠ j in atTop, m j < n j) →
        ∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 →
          Tendsto (fun j => (m j : ℝ) / (n j : ℝ)) atTop (𝓝 x) →
          Tendsto (fun j => A (n j) (m j)) atTop (𝓝 (J x))) ∧
      J 0 = L0 := by
  obtain ⟨P, hcont, hunit, huniform, hres⟩ := exists_continuous_profile_limit
  let J : ℝ → ℝ := fun x => ∫ y in (0 : ℝ)..1, P (x, y)
  have hzero : Tendsto (fun n : ℕ => A n 0) atTop (𝓝 (J 0)) := by
    apply actual_moving_first_tendsto P hcont hunit hres (fun n => n) (fun _ => 0) tendsto_id
    · exact eventually_atTop.mpr ⟨1, by intro n hn; omega⟩
    · exact ⟨le_rfl, by norm_num⟩
    · simp
  refine ⟨P, J, hcont, hunit, huniform, hres, (fun _ => rfl),
    continuousOn_marginal P hcont, ?_, tendsto_nhds_unique hzero (fixed_first_limit 0)⟩
  intro n m hn hvalid x hx hr
  exact actual_moving_first_tendsto P hcont hunit hres n m hn hvalid x hx hr

example : Tendsto (fun j : ℕ => j + 2) atTop atTop ∧
    (∀ j : ℕ, 2 ≤ j + 2 ∧ 0 < j + 2) ∧
    Tendsto (fun j : ℕ => (0 : ℝ) / ((j + 2 : ℕ) : ℝ)) atTop (𝓝 0) ∧
    (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨lattice_size_tendsto, by omega, by simp, by norm_num⟩

example : Tendsto (fun j : ℕ => j + 2) atTop atTop ∧
    (∀ j : ℕ, 2 ≤ j + 2 ∧ j + 1 < j + 2) ∧
    Tendsto (fun j : ℕ => ((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)) atTop (𝓝 1) ∧
    (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨lattice_size_tendsto, by omega, ?_, by norm_num⟩
  have hi := lattice_error_tendsto 1
  have ht : Tendsto (fun j : ℕ => 1 - (1 : ℝ) / ((j + 2 : ℕ) : ℝ)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hi
  apply ht.congr'
  filter_upwards [] with j
  push_cast
  field_simp
  ring

end PermutationFixedFirstProfile
