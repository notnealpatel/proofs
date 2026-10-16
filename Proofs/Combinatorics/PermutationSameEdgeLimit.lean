import Combinatorics.PermutationSameEdgeAvoidance

set_option autoImplicit false

open Filter Topology

namespace PermutationSameEdgeLimit

open PermutationEndpointCounting PermutationSameEdgeAvoidance

attribute [local instance] Classical.propDecidable

/-- The actual terminal two-endpoint avoidance fraction, extended by zero when
size or label distinctness makes the prescribed experiment invalid. -/
noncomputable def F (n a b : ℕ) : ℝ :=
  if h : 2 ≤ n ∧ a < n ∧ b < n ∧ a ≠ b then
    letI : NeZero n := ⟨by omega⟩
    (Fintype.card (PermutationMixedEndpointBound.AvoidTwo
      (⟨n - 1, by omega⟩ : Fin n) ⟨a, h.2.1⟩ ⟨b, h.2.2.1⟩) : ℝ) /
      Fintype.card (FixedTwo (0 : Fin n) ⟨n - 1, by omega⟩
        ⟨a, h.2.1⟩ ⟨b, h.2.2.1⟩)
  else 0

/-- On the valid guard the totalized fraction is exactly the actual cardinal ratio. -/
theorem F_eq_actual {n a b : ℕ} [NeZero n]
    (hn : 2 ≤ n) (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    F n a b =
      (Fintype.card (PermutationMixedEndpointBound.AvoidTwo
        (⟨n - 1, by omega⟩ : Fin n) ⟨a, ha⟩ ⟨b, hb⟩) : ℝ) /
        Fintype.card (FixedTwo (0 : Fin n) ⟨n - 1, by omega⟩ ⟨a, ha⟩ ⟨b, hb⟩) := by
  have h : 2 ≤ n ∧ a < n ∧ b < n ∧ a ≠ b := ⟨hn, ha, hb, hab⟩
  simp only [F, dif_pos h]

example : F 0 0 1 = 0 := by simp [F]
example (n a : ℕ) : F n a a = 0 := by simp [F]
example : F 6 0 1 =
    (Fintype.card (PermutationMixedEndpointBound.AvoidTwo (5 : Fin 6) 0 1) : ℝ) /
      Fintype.card (FixedTwo (0 : Fin 6) 5 0 1) :=
  F_eq_actual (by decide) (by decide) (by decide) (by decide)

/-- Every valid terminal fiber is inhabited: both positions and labels are distinct. -/
theorem terminal_fiber_nonempty {n a b : ℕ} [NeZero n]
    (hn : 2 ≤ n) (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    Nonempty (FixedTwo (0 : Fin n) ⟨n - 1, by omega⟩ ⟨a, ha⟩ ⟨b, hb⟩) := by
  apply fixedTwo_nonempty
  · intro he
    have hv := congrArg Fin.val he
    change 0 = n - 1 at hv
    omega
  · intro he
    exact hab (congrArg Fin.val he)

example : Nonempty (FixedTwo (0 : Fin 6) 5 0 1) :=
  terminal_fiber_nonempty (by decide) (by decide) (by decide) (by decide)

/-- The totalized actual fraction is always nonnegative. -/
theorem F_nonneg (n a b : ℕ) : 0 ≤ F n a b := by
  unfold F
  split_ifs <;> positivity

/-- The actual avoidance event is a subset of its prescribed fiber, so its
fraction (including the invalid zero extension) never exceeds one. -/
theorem F_le_one (n a b : ℕ) : F n a b ≤ 1 := by
  classical
  by_cases h : 2 ≤ n ∧ a < n ∧ b < n ∧ a ≠ b
  · letI : NeZero n := ⟨by omega⟩
    rw [F_eq_actual h.1 h.2.1 h.2.2.1 h.2.2.2]
    letI := terminal_fiber_nonempty h.1 h.2.1 h.2.2.1 h.2.2.2
    have hp : (0 : ℝ) < Fintype.card (FixedTwo (0 : Fin n)
        ⟨n - 1, by omega⟩ ⟨a, h.2.1⟩ ⟨b, h.2.2.1⟩) := by
      exact_mod_cast Fintype.card_pos
    apply (div_le_one hp).mpr
    exact_mod_cast (Nat.le.intro (card_avoidTwo_add_card_overlap
      (⟨n - 1, by omega⟩ : Fin n) ⟨a, h.2.1⟩ ⟨b, h.2.2.1⟩))
  · simp [F, h]

/-- The finite actual same-edge bound specializes to the totalized fraction
whenever the size is separated from the fixed cutoff. -/
theorem one_sub_F_le {n a b K : ℕ} (hK : 3 ≤ K) (hn : 2 * K ≤ n)
    (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    1 - F n a b ≤
      (2 * (K : ℝ) - 4) * (((max a b : ℕ) : ℝ) - 1) / ((n : ℝ) - 2) +
        6 / (K / 3).factorial := by
  letI : NeZero n := ⟨by omega⟩
  rw [F_eq_actual (by omega) ha hb hab]
  exact actualAvoid_fraction_bound K hK hn ⟨n - 1, by omega⟩
    (by dsimp; omega) ⟨a, ha⟩ ⟨b, hb⟩ (fun he => hab (congrArg Fin.val he))

/-- For any two fixed distinct natural labels, the full sequence of actual
terminal avoidance fractions tends to one. The cutoff is fixed before size grows. -/
theorem tendsto_F (a b : ℕ) (hab : a ≠ b) :
    Tendsto (fun n => F n a b) atTop (𝓝 1) := by
  have hmax : 1 ≤ max a b := by omega
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
  have hsmall : Tendsto (fun n : ℕ =>
      (2 * (K : ℝ) - 4) * (((max a b : ℕ) : ℝ) - 1) / ((n : ℝ) - 2))
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (by
      apply tendsto_atTop.mpr
      intro r
      filter_upwards [(tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually
          (eventually_ge_atTop (r + 2))] with n hn
      linarith)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hsmall (ε / 2) (by linarith)
  refine ⟨max N (max (2 * K) (max (a + 1) (b + 1))), ?_⟩
  intro n hn
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hnK : 2 * K ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have ha : a < n := by omega
  have hb : b < n := by omega
  have hterm := hN n hnN
  rw [Real.dist_eq, sub_zero] at hterm
  have hterm' :
      (2 * (K : ℝ) - 4) * (((max a b : ℕ) : ℝ) - 1) / ((n : ℝ) - 2) < ε / 2 :=
    lt_of_le_of_lt (le_abs_self _) hterm
  have hbound := one_sub_F_le hK hnK ha hb hab
  rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (F_le_one n a b))]
  linarith

end PermutationSameEdgeLimit
