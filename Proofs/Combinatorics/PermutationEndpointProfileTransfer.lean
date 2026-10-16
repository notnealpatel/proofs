import Combinatorics.PermutationEndpointProfileLattice
import Mathlib.Topology.UniformSpace.UniformConvergence

set_option autoImplicit false

namespace PermutationEndpointProfile

open Filter
open scoped Topology

/-- The shifted lattice sizes tend to infinity. -/
theorem lattice_size_tendsto : Tendsto (fun j : ℕ => j+2) atTop atTop := by
  apply tendsto_atTop.2
  intro k
  exact eventually_atTop.2 ⟨k, fun j hj => by omega⟩

/-- A constant divided by the shifted lattice size tends to zero. -/
theorem lattice_error_tendsto (C : ℝ) :
    Tendsto (fun j : ℕ => C / (j+2:ℕ)) atTop (𝓝 0) :=
  (tendsto_natCast_atTop_atTop.comp lattice_size_tendsto).const_div_atTop C

/-- Every square point is a limit of actual valid distinct endpoint pairs. -/
theorem exists_distinct_lattice_path (x y : ℝ)
    (hx : x ∈ Set.Icc (0:ℝ) 1) (hy : y ∈ Set.Icc (0:ℝ) 1) :
    ∃ a b : (j : ℕ) → Fin (j+2),
      (∀ j, a j ≠ b j) ∧
      Tendsto (fun j => ((a j).val:ℝ)/(j+2:ℕ)) atTop (𝓝 x) ∧
      Tendsto (fun j => ((b j).val:ℝ)/(j+2:ℕ)) atTop (𝓝 y) := by
  classical
  choose a b hab ha hb using
    (fun j : ℕ => exists_distinct_lattice_endpoints (j+2) (by omega) x y hx hy)
  refine ⟨a,b,hab,?_,?_⟩
  · rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero' (Eventually.of_forall (fun _ => dist_nonneg))
      (Eventually.of_forall (fun j => by simpa only [Real.dist_eq] using ha j))
      (lattice_error_tendsto 2)
  · rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero' (Eventually.of_forall (fun _ => dist_nonneg))
      (Eventually.of_forall (fun j => by simpa only [Real.dist_eq] using hb j))
      (lattice_error_tendsto 2)

/-- Along any valid convergent lattice path the actual truncated fractions
converge to their continuous boundary polynomial. -/
theorem shortFraction_path_tendsto (K : ℕ) (a b : (j : ℕ) → Fin (j+2))
    (hab : ∀ j, a j ≠ b j) (x y : ℝ)
    (ha : Tendsto (fun j => ((a j).val:ℝ)/(j+2:ℕ)) atTop (𝓝 x))
    (hb : Tendsto (fun j => ((b j).val:ℝ)/(j+2:ℕ)) atTop (𝓝 y)) :
    Tendsto (fun j => shortFraction (K+3) (0 : Fin (j+2)).rev (a j) (b j))
      atTop (𝓝 (profileApprox K (x,y))) := by
  have hp := (continuous_profileApprox K).tendsto (x,y) |>.comp (ha.prodMk_nhds hb)
  have he : Tendsto (fun j =>
      shortFraction (K+3) (0 : Fin (j+2)).rev (a j) (b j) -
        profileApprox K (((a j).val:ℝ)/(j+2:ℕ),((b j).val:ℝ)/(j+2:ℕ)))
      atTop (𝓝 0) := by
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall (fun _ => dist_nonneg))
      (g := fun j => ((2*(K+3)-2).factorial:ℝ) *
        (2*(2*(K+3)-2-2:ℕ)*((2*(K+3)-2-2:ℕ)+2)/(j+2:ℕ)))
    · filter_upwards [lattice_size_tendsto.eventually_ge_atTop (2*(K+3)-2),
        lattice_size_tendsto.eventually_ge_atTop
          ((2*(K+3)-2-2)*(2*(K+3)-2-2+3))] with j hj hj'
      simpa only [Real.dist_eq, sub_zero] using
        shortFraction_profileApprox_error K hj hj' (a j) (b j) (hab j)
    · convert (lattice_error_tendsto
        (((2*(K+3)-2).factorial:ℝ)*(2*(2*(K+3)-2-2:ℕ)*((2*(K+3)-2-2:ℕ)+2)))) using 1
      ext j
      ring
  simpa only [Function.comp_apply, zero_add, sub_add_cancel] using he.add hp

/-- All continuous boundary approximations take values in the unit interval on
the closed square, obtained from actual distinct-label fractions. -/
theorem profileApprox_mem_unit (K : ℕ) (z : ℝ × ℝ)
    (hz : z ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1) :
    0 ≤ profileApprox K z ∧ profileApprox K z ≤ 1 := by
  obtain ⟨a,b,hab,ha,hb⟩ := exists_distinct_lattice_path z.1 z.2 hz.1 hz.2
  have ht := shortFraction_path_tendsto K a b hab z.1 z.2 ha hb
  constructor
  · exact ge_of_tendsto ht (Eventually.of_forall (fun j => shortFraction_nonneg _ _ _ _))
  · apply le_of_tendsto ht
    exact Eventually.of_forall (fun j =>
      shortFraction_le_one (by omega) _ _ (by simp) _ _ (hab j))

/-- The polynomial differences inherit the one-sided actual truncation tail on
all square points, including the diagonal and corners. -/
theorem profileApprox_sub_bounds (K J : ℕ) (hKJ : K ≤ J) (z : ℝ × ℝ)
    (hz : z ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1) :
    0 ≤ profileApprox K z - profileApprox J z ∧
      profileApprox K z - profileApprox J z ≤ 6 / ((K+3)/3).factorial := by
  obtain ⟨a,b,hab,ha,hb⟩ := exists_distinct_lattice_path z.1 z.2 hz.1 hz.2
  have ht := (shortFraction_path_tendsto K a b hab z.1 z.2 ha hb).sub
    (shortFraction_path_tendsto J a b hab z.1 z.2 ha hb)
  have hbounds : ∀ᶠ j in atTop,
      0 ≤ shortFraction (K+3) (0 : Fin (j+2)).rev (a j) (b j) -
        shortFraction (J+3) (0 : Fin (j+2)).rev (a j) (b j) ∧
      shortFraction (K+3) (0 : Fin (j+2)).rev (a j) (b j) -
        shortFraction (J+3) (0 : Fin (j+2)).rev (a j) (b j) ≤
          6 / ((K+3)/3).factorial := by
    filter_upwards [eventually_ge_atTop 1] with j hj
    have hk := shortFraction_sub_actual_bounds (by omega : 3 ≤ j+2)
      (K+3) (by omega) (0 : Fin (j+2)).rev (by simp) (a j) (b j) (hab j)
    have hj' := shortFraction_sub_actual_bounds (by omega : 3 ≤ j+2)
      (J+3) (by omega) (0 : Fin (j+2)).rev (by simp) (a j) (b j) (hab j)
    have hm := shortFraction_antitone (by omega : K+3 ≤ J+3)
      (0 : Fin (j+2)).rev (a j) (b j)
    constructor <;> linarith [hk.2, hj'.1]
  exact ⟨ge_of_tendsto ht (hbounds.mono fun _ h => h.1),
    le_of_tendsto ht (hbounds.mono fun _ h => h.2)⟩

example : (0,0) ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1 := by
  constructor <;> constructor <;> norm_num

end PermutationEndpointProfile
