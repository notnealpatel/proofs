import Combinatorics.PermutationFixedFirstProfileAnalysis

set_option autoImplicit false

namespace PermutationJointEndpointProfile

open scoped BigOperators
open Filter Topology PermutationFixedFirstProfile

/-- Every left-grid coordinate lies in the closed unit interval. -/
theorem grid_mem {n : ℕ} (hn : 0 < n) (a : Fin n) :
    (a.val : ℝ) / n ∈ Set.Icc (0 : ℝ) 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  exact ⟨by positivity, (div_le_one hnR).mpr (by exact_mod_cast a.isLt.le)⟩

/-- A point of a left-grid cell lies in the unit interval and is at distance at most the mesh from its left endpoint. -/
theorem cell_mem_dist {n : ℕ} (hn : 0 < n) (a : Fin n) (x : ℝ)
    (hx : x ∈ Set.Icc ((a.val : ℝ) / n) (((a.val : ℝ) + 1) / n)) :
    x ∈ Set.Icc (0 : ℝ) 1 ∧ dist ((a.val : ℝ) / n) x ≤ 1 / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have htop : ((a.val : ℝ) + 1) / n ≤ 1 := by
    apply (div_le_one hnR).mpr
    exact_mod_cast (by omega : a.val + 1 ≤ n)
  refine ⟨⟨(grid_mem hn a).1.trans hx.1, hx.2.trans htop⟩, ?_⟩
  rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hx.1)]
  linarith [hx.2, show ((a.val : ℝ) + 1) / n = (a.val : ℝ) / n + 1 / n by ring]

/-- Cellwise errors on a square control the full two-dimensional left-grid average against the iterated integral. -/
theorem grid_integral_error (f : ℝ × ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1))
    (n : ℕ) (hn : 0 < n) (g : Fin n → Fin n → ℝ) (e : ℝ)
    (herr : ∀ a b : Fin n, ∀ x ∈ Set.Icc ((a.val : ℝ) / n) (((a.val : ℝ) + 1) / n),
      ∀ y ∈ Set.Icc ((b.val : ℝ) / n) (((b.val : ℝ) + 1) / n),
      |g a b - f (x, y)| ≤ e) :
    |(∑ a : Fin n, (∑ b : Fin n, g a b) / n) / n -
      ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, f (x, y)| ≤ e := by
  apply PermutationFixedFirstProfile.grid_integral_error _ (continuousOn_marginal f hf) n hn
  intro a x hx
  apply PermutationFixedFirstProfile.grid_integral_error
    (fun y => f (x, y))
    (hf.comp (by fun_prop) (fun y hy => ⟨(cell_mem_dist hn a x hx).1, hy⟩)) n hn
  intro b y hy
  exact herr a b x hx y hy

/-- Full square left-grid averages converge to the iterated integral for every function continuous on the closed square. -/
theorem grid_tendsto (f : ℝ × ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)) :
    Tendsto (fun n : ℕ => (∑ a : Fin n, (∑ b : Fin n,
      f ((a.val : ℝ) / n, (b.val : ℝ) / n)) / n) / n) atTop
      (𝓝 (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, f (x, y))) := by
  have huc := (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hf
  have hi : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_natCast_atTop_atTop.const_div_atTop 1
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp huc (ε / 2) (by positivity)
  filter_upwards [eventually_ge_atTop 1, hi.eventually_lt tendsto_const_nhds hδ] with n hn hmesh
  have he := grid_integral_error f hf n hn
    (fun a b => f ((a.val : ℝ) / n, (b.val : ℝ) / n)) (ε / 2) (by
      intro a b x hx y hy
      have hxc := cell_mem_dist hn a x hx
      have hyc := cell_mem_dist hn b y hy
      have hm := hmod ((a.val : ℝ) / n, (b.val : ℝ) / n)
        ⟨grid_mem hn a, grid_mem hn b⟩ (x, y) ⟨hxc.1, hyc.1⟩ (by
          rw [Prod.dist_eq, max_lt_iff]
          exact ⟨hxc.2.trans_lt hmesh, hyc.2.trans_lt hmesh⟩)
      exact le_of_lt (by simpa only [Real.dist_eq] using hm))
  rw [Real.dist_eq]
  linarith

example : Tendsto (fun n : ℕ => (∑ _a : Fin n, (∑ _b : Fin n, (0 : ℝ)) / n) / n)
    atTop (𝓝 (∫ _x in (0 : ℝ)..1, ∫ _y in (0 : ℝ)..1, (0 : ℝ))) :=
  grid_tendsto (fun _ => 0) (by fun_prop)

end PermutationJointEndpointProfile
