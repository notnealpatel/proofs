import Combinatorics.PermutationEndpointProfileLimit

set_option autoImplicit false

namespace PermutationEndpointProfile

open Filter
open scoped Topology

/-- Every valid actual endpoint fraction differs from the constructed profile
by at most the finite polynomial error plus one factorial tail. -/
theorem actual_profile_error (P : ℝ × ℝ → ℝ)
    (hP : ∀ K z, z ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1 →
      0 ≤ profileApprox K z-P z ∧ profileApprox K z-P z ≤ 6/((K+3)/3).factorial)
    (K n a b : ℕ) (hn : 3 ≤ n) (ha : a < n) (hb : b < n) (hab : a ≠ b)
    (hsize : 2*(K+3)-2 ≤ n)
    (hlarge : (2*(K+3)-2-2)*(2*(K+3)-2-2+3) ≤ n) :
    |PermutationSameEdgeLimit.F n a b-P ((a:ℝ)/n,(b:ℝ)/n)| ≤
      ((2*(K+3)-2).factorial:ℝ) *
        (2*(2*(K+3)-2-2:ℕ)*((2*(K+3)-2-2:ℕ)+2)/n) +
          6/((K+3)/3).factorial := by
  letI : NeZero n := ⟨by omega⟩
  have hnR : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hz : ((a:ℝ)/n,(b:ℝ)/n) ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1 := by
    constructor <;> constructor
    · positivity
    · exact (div_le_one hnR).2 (by exact_mod_cast ha.le)
    · positivity
    · exact (div_le_one hnR).2 (by exact_mod_cast hb.le)
  have hr := hP K _ hz
  have he := shortFraction_profileApprox_error K hsize hlarge
    (⟨a,ha⟩ : Fin n) (⟨b,hb⟩ : Fin n) (fun h => hab (congrArg Fin.val h))
  have ht := shortFraction_sub_F_bounds hn (K+3) (by omega) ha hb hab
  have hrev : (⟨n-1, by omega⟩ : Fin n) = (0 : Fin n).rev := by ext; simp
  rw [hrev] at ht
  rw [abs_le] at he ⊢
  constructor <;> linarith [he.1,he.2,ht.1,ht.2,hr.1,hr.2]

/-- A continuous profile with the established actual polynomial residuals
controls arbitrary moving valid distinct endpoint sequences. -/
theorem actual_moving_tendsto (P : ℝ × ℝ → ℝ)
    (hcont : ContinuousOn P (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1))
    (hP : ∀ K z, z ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1 →
      0 ≤ profileApprox K z-P z ∧ profileApprox K z-P z ≤ 6/((K+3)/3).factorial)
    (n a b : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (hv : ∀ᶠ j in atTop, 2 ≤ n j ∧ a j < n j ∧ b j < n j ∧ a j ≠ b j)
    (x y : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) (hy : y ∈ Set.Icc (0:ℝ) 1)
    (ha : Tendsto (fun j => (a j:ℝ)/(n j:ℝ)) atTop (𝓝 x))
    (hb : Tendsto (fun j => (b j:ℝ)/(n j:ℝ)) atTop (𝓝 y)) :
    Tendsto (fun j => PermutationSameEdgeLimit.F (n j) (a j) (b j))
      atTop (𝓝 (P (x,y))) := by
  let z := fun j => ((a j:ℝ)/(n j:ℝ),(b j:ℝ)/(n j:ℝ))
  have hz : Tendsto z atTop (𝓝 (x,y)) := ha.prodMk_nhds hb
  have hzin : ∀ᶠ j in atTop, z j ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1 := by
    filter_upwards [hv] with j hj
    have hnR : (0:ℝ) < n j := by exact_mod_cast (show 0 < n j by omega)
    constructor <;> constructor
    · positivity
    · exact (div_le_one hnR).2 (by exact_mod_cast hj.2.1.le)
    · positivity
    · exact (div_le_one hnR).2 (by exact_mod_cast hj.2.2.1.le)
  have hpz : Tendsto (fun j => P (z j)) atTop (𝓝 (P (x,y))) :=
    (hcont (x,y) ⟨hx,hy⟩).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hz,hzin⟩)
  rw [Metric.tendsto_nhds]
  intro ε hε
  have heps := profile_tail_tendsto.eventually_lt tendsto_const_nhds
    (show (0:ℝ) < ε/4 by positivity)
  obtain ⟨K,hK⟩ := heps.exists
  let C : ℝ := ((2*(K+3)-2).factorial:ℝ) *
    (2*(2*(K+3)-2-2:ℕ)*((2*(K+3)-2-2:ℕ)+2))
  have hc : Tendsto (fun j => C/(n j:ℝ)) atTop (𝓝 0) :=
    (tendsto_natCast_atTop_atTop.comp hn).const_div_atTop C
  have hc' := hc.eventually_lt tendsto_const_nhds (show (0:ℝ) < ε/4 by positivity)
  have hp' := (Metric.tendsto_nhds.1 hpz) (ε/2) (by positivity)
  filter_upwards [hv,hn.eventually_ge_atTop 3,
    hn.eventually_ge_atTop (2*(K+3)-2),
    hn.eventually_ge_atTop ((2*(K+3)-2-2)*(2*(K+3)-2-2+3)),hc',hp']
      with j hj hn3 hsize hlarge hcj hpj
  have he := actual_profile_error P hP K (n j) (a j) (b j) hn3 hj.2.1
    hj.2.2.1 hj.2.2.2 hsize hlarge
  have hE : ((2*(K+3)-2).factorial:ℝ) *
        (2*(2*(K+3)-2-2:ℕ)*((2*(K+3)-2-2:ℕ)+2)/(n j:ℝ)) = C/(n j:ℝ) := by
    dsimp [C]
    ring
  rw [hE] at he
  rw [Real.dist_eq] at hpj ⊢
  have htri := abs_sub_le (PermutationSameEdgeLimit.F (n j) (a j) (b j))
    (P (z j)) (P (x,y))
  change |PermutationSameEdgeLimit.F (n j) (a j) (b j)-P (z j)| ≤ _ at he
  linarith

/-- There exists a continuous unit-square profile for the actual endpoint-
conditioned avoidance fractions along every moving valid distinct endpoint
sequence. Coincident limiting coordinates and all corners are included. -/
theorem exists_actual_continuous_endpoint_profile :
    ∃ P : ℝ × ℝ → ℝ,
      ContinuousOn P (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1) ∧
      (∀ z ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1, 0 ≤ P z ∧ P z ≤ 1) ∧
      ∀ (n a b : ℕ → ℕ), Tendsto n atTop atTop →
        (∀ᶠ j in atTop, 2 ≤ n j ∧ a j < n j ∧ b j < n j ∧ a j ≠ b j) →
        ∀ x y : ℝ, x ∈ Set.Icc (0:ℝ) 1 → y ∈ Set.Icc (0:ℝ) 1 →
          Tendsto (fun j => (a j:ℝ)/(n j:ℝ)) atTop (𝓝 x) →
          Tendsto (fun j => (b j:ℝ)/(n j:ℝ)) atTop (𝓝 y) →
          Tendsto (fun j => PermutationSameEdgeLimit.F (n j) (a j) (b j))
            atTop (𝓝 (P (x,y))) := by
  obtain ⟨P,hcont,hunit,_hu,hres⟩ := exists_continuous_profile_limit
  exact ⟨P,hcont,hunit,actual_moving_tendsto P hcont hres⟩

example : Tendsto (fun j : ℕ => j+2) atTop atTop ∧
    (∀ j : ℕ, 2 ≤ j+2 ∧ 0 < j+2 ∧ 1 < j+2 ∧ (0:ℕ) ≠ 1) ∧
    Tendsto (fun j : ℕ => (0:ℝ)/(j+2:ℕ)) atTop (𝓝 0) ∧
    Tendsto (fun j : ℕ => (1:ℝ)/(j+2:ℕ)) atTop (𝓝 0) := by
  refine ⟨lattice_size_tendsto, ?_, ?_, lattice_error_tendsto 1⟩
  · intro j
    omega
  · simpa using lattice_error_tendsto 0

end PermutationEndpointProfile
