import Combinatorics.PermutationMixedEndpointBound
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

open Filter Topology

namespace PermutationOppositeEdgeLimit

open PermutationMixedEndpointBound PermutationEndpointCounting

attribute [local instance] Classical.propDecidable

/-- The actual fraction of permutations avoiding every proper overlap of length at
least two, conditional on the first label being `m t` and the last being `l t`.
The dimension is `N t + 3`; distinct labels make the conditioning fiber nonempty. -/
noncomputable def actualAvoidFraction (N : ℕ → ℕ)
    (m l : (t : ℕ) → Fin (N t + 3)) : ℕ → ℝ :=
  fun t => (Fintype.card (AvoidTwo (⟨N t + 2, by omega⟩ : Fin (N t + 3))
    (m t) (l t)) : ℝ) /
    Fintype.card (FixedTwo (0 : Fin (N t + 3)) ⟨N t + 2, by omega⟩ (m t) (l t))

example (N : ℕ → ℕ) (m l : (t : ℕ) → Fin (N t + 3)) (t : ℕ) :
    actualAvoidFraction N m l t =
      (Fintype.card (AvoidTwo (⟨N t + 2, by omega⟩ : Fin (N t + 3)) (m t) (l t)) : ℝ) /
        Fintype.card (FixedTwo (0 : Fin (N t + 3)) ⟨N t + 2, by omega⟩ (m t) (l t)) := rfl

/-- Distinct prescribed labels give a positive denominator in the actual fraction. -/
theorem fixedTwo_card_pos (N : ℕ → ℕ)
    (m l : (t : ℕ) → Fin (N t + 3)) (hml : ∀ t, m t ≠ l t) (t : ℕ) :
    0 < Fintype.card
      (FixedTwo (0 : Fin (N t + 3)) ⟨N t + 2, by omega⟩ (m t) (l t)) := by
  have hpq : (0 : Fin (N t + 3)) ≠ ⟨N t + 2, by omega⟩ := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_zero] at hv
    omega
  letI := fixedTwo_nonempty (0 : Fin (N t + 3)) ⟨N t + 2, by omega⟩
    (m t) (l t) hpq (hml t)
  exact Fintype.card_pos

/-- The actual fraction is nonnegative. -/
theorem actualAvoidFraction_nonneg (N : ℕ → ℕ)
    (m l : (t : ℕ) → Fin (N t + 3)) (t : ℕ) :
    0 ≤ actualAvoidFraction N m l t := by
  unfold actualAvoidFraction
  positivity

/-- The mixed-endpoint finite bound, specialized to dimension `N t + 3`. -/
theorem actualAvoidFraction_le (N : ℕ → ℕ)
    (m l : (t : ℕ) → Fin (N t + 3)) (hml : ∀ t, m t ≠ l t) (t : ℕ) :
    actualAvoidFraction N m l t ≤
      ((m t).val + (N t + 2 - (l t).val : ℕ) : ℝ) / ((N t : ℝ) + 1) := by
  have h := avoidTwo_fraction_le (by omega : 3 ≤ N t + 3)
    (⟨N t + 2, by omega⟩ : Fin (N t + 3)) (by simp)
    (m t) (l t) (hml t)
  have hn : N t + 3 - 1 = N t + 2 := by omega
  rw [hn] at h
  unfold actualAvoidFraction
  convert h using 1
  push_cast
  ring

/-- If the mixed finite majorant tends to zero, so does the actual avoidance fraction. -/
theorem tendsto_actualAvoidFraction_zero_of_majorant (N : ℕ → ℕ)
    (m l : (t : ℕ) → Fin (N t + 3)) (hml : ∀ t, m t ≠ l t)
    (hbound : Tendsto (fun t =>
      ((m t).val + (N t + 2 - (l t).val : ℕ) : ℝ) / ((N t : ℝ) + 1))
      atTop (𝓝 0)) :
    Tendsto (actualAvoidFraction N m l) atTop (𝓝 0) :=
  squeeze_zero (actualAvoidFraction_nonneg N m l)
    (actualAvoidFraction_le N m l hml) hbound

/-- The correction from the dimension denominator to the mixed-bound denominator
converges to one along any size function tending to infinity. -/
theorem tendsto_sizeRatio_one (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) :
    Tendsto (fun t => ((N t : ℝ) + 3) / ((N t : ℝ) + 1)) atTop (𝓝 1) := by
  have hD : Tendsto (fun t => (N t : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.comp hN)
  have hsmall : Tendsto (fun t => (2 : ℝ) / ((N t : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hD
  have hsum := (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add hsmall
  have heq (t : ℕ) : ((N t : ℝ) + 3) / ((N t : ℝ) + 1) =
      1 + 2 / ((N t : ℝ) + 1) := by
    have hp : (0 : ℝ) < (N t : ℝ) + 1 := by positivity
    field_simp
    ring
  simpa only [heq, add_zero] using hsum

/-- Moving lower labels and upper codistances that are sublinear in the dimension
force the actual all-length avoidance fraction to tend to zero. -/
theorem tendsto_actualAvoidFraction_zero (N : ℕ → ℕ)
    (hN : Tendsto N atTop atTop) (m l : (t : ℕ) → Fin (N t + 3))
    (hml : ∀ t, m t ≠ l t)
    (hm : Tendsto (fun t => ((m t).val : ℝ) / ((N t : ℝ) + 3)) atTop (𝓝 0))
    (hl : Tendsto (fun t => ((N t + 2 - (l t).val : ℕ) : ℝ) /
      ((N t : ℝ) + 3)) atTop (𝓝 0)) :
    Tendsto (actualAvoidFraction N m l) atTop (𝓝 0) := by
  apply tendsto_actualAvoidFraction_zero_of_majorant N m l hml
  have hprod := (hm.add hl).mul (tendsto_sizeRatio_one N hN)
  have heq (t : ℕ) :
      (((m t).val : ℝ) / ((N t : ℝ) + 3) +
        ((N t + 2 - (l t).val : ℕ) : ℝ) / ((N t : ℝ) + 3)) *
        (((N t : ℝ) + 3) / ((N t : ℝ) + 1)) =
      ((m t).val + (N t + 2 - (l t).val : ℕ) : ℝ) / ((N t : ℝ) + 1) := by
    have h3 : (0 : ℝ) < (N t : ℝ) + 3 := by positivity
    have h1 : (0 : ℝ) < (N t : ℝ) + 1 := by positivity
    field_simp
  simpa only [heq, add_zero, zero_mul] using hprod

private theorem tendsto_bounded_div_size_zero (N f : ℕ → ℕ)
    (hN : Tendsto N atTop atTop) (A : ℕ) (hf : ∀ᶠ t in atTop, f t ≤ A) :
    Tendsto (fun t => (f t : ℝ) / ((N t : ℝ) + 3)) atTop (𝓝 0) := by
  have hD : Tendsto (fun t => (N t : ℝ) + 3) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.comp hN)
  apply squeeze_zero' (Eventually.of_forall (fun t => by positivity)) _
    (tendsto_const_nhds.div_atTop hD :
      Tendsto (fun t => (A : ℝ) / ((N t : ℝ) + 3)) atTop (𝓝 0))
  filter_upwards [hf] with t ht
  exact div_le_div_of_nonneg_right (by exact_mod_cast ht) (by positivity)

/-- Uniformly bounded lower distance and upper codistance eventually suffice for
vanishing of the actual avoidance fraction. -/
theorem tendsto_actualAvoidFraction_zero_of_bounded_distance (N : ℕ → ℕ)
    (hN : Tendsto N atTop atTop) (m l : (t : ℕ) → Fin (N t + 3))
    (hml : ∀ t, m t ≠ l t)
    (hbounded : ∃ A B : ℕ, ∀ᶠ t in atTop,
      (m t).val ≤ A ∧ N t + 2 - (l t).val ≤ B) :
    Tendsto (actualAvoidFraction N m l) atTop (𝓝 0) := by
  obtain ⟨A, B, hAB⟩ := hbounded
  exact tendsto_actualAvoidFraction_zero N hN m l hml
    (tendsto_bounded_div_size_zero N (fun t => (m t).val) hN A
      (hAB.mono (fun _ ht => ht.1)))
    (tendsto_bounded_div_size_zero N (fun t => N t + 2 - (l t).val) hN B
      (hAB.mono (fun _ ht => ht.2)))

/-- With lower label zero and upper codistance one in dimension `t + 3`, the
actual avoidance fraction tends to zero. -/
theorem tendsto_actualAvoidFraction_zero_fixed_distance :
    Tendsto (actualAvoidFraction (fun t => t) (fun _ => 0)
      (fun t => ⟨t + 1, by omega⟩)) atTop (𝓝 0) := by
  apply tendsto_actualAvoidFraction_zero_of_bounded_distance _ tendsto_id
  · intro t he
    have hv := congrArg Fin.val he
    simp only [Fin.val_zero] at hv
    omega
  · exact ⟨0, 1, Eventually.of_forall (fun t => by simp)⟩

example :
    Tendsto (fun t : ℕ => t) atTop atTop ∧
    (∀ t : ℕ, (0 : Fin (t + 3)) ≠ ⟨t + 1, by omega⟩) ∧
    Tendsto (fun t : ℕ => ((0 : Fin (t + 3)).val : ℝ) / ((t : ℝ) + 3))
      atTop (𝓝 0) ∧
    Tendsto (fun t : ℕ => ((t + 2 - (t + 1) : ℕ) : ℝ) / ((t : ℝ) + 3))
      atTop (𝓝 0) := by
  refine ⟨tendsto_id, ?_, ?_, ?_⟩
  · intro t he
    have hv := congrArg Fin.val he
    simp only [Fin.val_zero] at hv
    omega
  · simp
  · exact tendsto_bounded_div_size_zero (fun t => t) (fun t => t + 2 - (t + 1))
      tendsto_id 1 (Eventually.of_forall (fun t => by omega))

end PermutationOppositeEdgeLimit
