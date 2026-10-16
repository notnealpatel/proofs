import Combinatorics.PermutationSameEdgeLimit

set_option autoImplicit false

open Filter Topology

namespace PermutationSameEdgeMovingLimit

/-- Sublinear zero-based labels eventually lie in a size-at-least-two experiment.
Together with eventual distinctness, this is exactly the guard of `F`; the
inhabited actual fiber is then supplied by `PermutationSameEdgeLimit.terminal_fiber_nonempty`. -/
theorem eventually_valid (a b : ℕ → ℕ)
    (hsub : Tendsto (fun n => ((max (a n) (b n) : ℕ) : ℝ) / (n : ℝ))
      atTop (𝓝 0)) :
    ∀ᶠ n in atTop, 2 ≤ n ∧ a n < n ∧ b n < n := by
  have hsmall : ∀ᶠ n in atTop,
      ((max (a n) (b n) : ℕ) : ℝ) / (n : ℝ) < 1 :=
    hsub.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hsmall, eventually_ge_atTop 2] with n hs hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hmax : max (a n) (b n) < n := by
    have hm : ((max (a n) (b n) : ℕ) : ℝ) < n := by
      simpa only [one_mul] using (div_lt_iff₀ hnpos).mp hs
    exact_mod_cast hm
  exact ⟨hn, lt_of_le_of_lt (le_max_left _ _) hmax,
    lt_of_le_of_lt (le_max_right _ _) hmax⟩

/-- For eventually distinct sublinear zero-based labels, the actual terminal
same-edge avoidance fractions tend to one, without any separate validity or
bounded-label hypothesis. -/
theorem tendsto_F (a b : ℕ → ℕ) (hab : ∀ᶠ n in atTop, a n ≠ b n)
    (hsub : Tendsto (fun n => ((max (a n) (b n) : ℕ) : ℝ) / (n : ℝ))
      atTop (𝓝 0)) :
    Tendsto (fun n => PermutationSameEdgeLimit.F n (a n) (b n)) atTop (𝓝 1) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨K₀, hK₀⟩ := Metric.tendsto_atTop.mp
    PermutationEndpointOverlapTail.tendsto_bound (ε / 2) (by linarith)
  let K := max K₀ 3
  have hK : 3 ≤ K := le_max_right _ _
  have htail : (6 : ℝ) / (K / 3).factorial < ε / 2 := by
    have ht := hK₀ K (le_max_left _ _)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at ht
    exact ht
  let C : ℝ := 2 * (K : ℝ) - 4
  have hC : 0 < C := by
    have hKr : (3 : ℝ) ≤ K := by exact_mod_cast hK
    dsimp [C]
    linarith
  have hsmall : ∀ᶠ n in atTop,
      ((max (a n) (b n) : ℕ) : ℝ) / (n : ℝ) < ε / (4 * C) :=
    hsub.eventually (eventually_lt_nhds (by positivity))
  have hevent : ∀ᶠ n in atTop,
      dist (PermutationSameEdgeLimit.F n (a n) (b n)) 1 < ε := by
    filter_upwards [eventually_valid a b hsub, hab, hsmall,
      eventually_ge_atTop (max 4 (2 * K))] with n hv hd hs hn
    have hn4 : 4 ≤ n := le_trans (le_max_left _ _) hn
    have hnK : 2 * K ≤ n := le_trans (le_max_right _ _) hn
    have hn4r : (4 : ℝ) ≤ n := by exact_mod_cast hn4
    have hnpos : (0 : ℝ) < n := by linarith
    have hden : (0 : ℝ) < (n : ℝ) - 2 := by linarith
    let M : ℝ := ((max (a n) (b n) : ℕ) : ℝ)
    have hM : 0 ≤ M := by positivity
    have hcompare : (M - 1) / ((n : ℝ) - 2) ≤ 2 * (M / (n : ℝ)) := by
      rw [← mul_div_assoc, div_le_div_iff₀ hden hnpos]
      have hprod : 0 ≤ M * ((n : ℝ) - 4) := mul_nonneg hM (by linarith)
      nlinarith
    have hterm : C * (M - 1) / ((n : ℝ) - 2) < ε / 2 := by
      calc
        C * (M - 1) / ((n : ℝ) - 2) = C * ((M - 1) / ((n : ℝ) - 2)) := by ring
        _ ≤ C * (2 * (M / (n : ℝ))) := mul_le_mul_of_nonneg_left hcompare hC.le
        _ < ε / 2 := by
          have hs' : M / (n : ℝ) * (4 * C) < ε := (lt_div_iff₀ (by positivity)).mp hs
          nlinarith
    have hbound := PermutationSameEdgeLimit.one_sub_F_le hK hnK hv.2.1 hv.2.2 hd
    change 1 - PermutationSameEdgeLimit.F n (a n) (b n) ≤
      C * (M - 1) / ((n : ℝ) - 2) + 6 / (K / 3).factorial at hbound
    rw [Real.dist_eq, abs_of_nonpos
      (sub_nonpos.mpr (PermutationSameEdgeLimit.F_le_one n (a n) (b n)))]
    linarith
  exact eventually_atTop.mp hevent

/-- The fixed distinct labels zero and one jointly satisfy the moving-label
hypotheses, giving a concrete nonvacuous instance of the limit. -/
theorem tendsto_F_zero_one :
    Tendsto (fun n => PermutationSameEdgeLimit.F n 0 1) atTop (𝓝 1) := by
  apply tendsto_F (fun _ => 0) (fun _ => 1)
  · exact Filter.Eventually.of_forall (fun _ => by decide)
  · simpa using (tendsto_one_div_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0))

end PermutationSameEdgeMovingLimit
