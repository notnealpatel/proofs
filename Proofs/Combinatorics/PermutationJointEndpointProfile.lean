import Combinatorics.PermutationJointEndpointProfileWeighted
import Combinatorics.PermutationJointEndpointCounting

set_option autoImplicit false
noncomputable section

namespace PermutationJointEndpointProfile

open scoped BigOperators
open Filter Topology PermutationEndpointProfile PermutationAvoidanceCovariance

/-- The full-avoidance endpoint numerator, averaged over all permutations. Sizes below two are assigned zero; all endpoint coordinates otherwise use the positive denominator `n - 1`. -/
def actualEndpointNumerator (phi : ℝ × ℝ → ℝ) (n : ℕ) : ℝ :=
  if hn : 2 ≤ n then
    (∑ π ∈ avoiding n,
      phi (coordinate (⟨0, by omega⟩ : Fin n) π,
        coordinate (⟨n - 1, by omega⟩ : Fin n) π)) /
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ)
  else 0

/-- The uniform average of an endpoint test over the actual full-avoidance set. Sizes below two are assigned zero; for sizes at least thirty the conditioning set has positive cardinality. -/
def actualConditionalEndpointAverage (phi : ℝ × ℝ → ℝ) (n : ℕ) : ℝ :=
  if hn : 2 ≤ n then
    (∑ π ∈ avoiding n,
      phi (coordinate (⟨0, by omega⟩ : Fin n) π,
        coordinate (⟨n - 1, by omega⟩ : Fin n) π)) /
      ((avoiding n).card : ℝ)
  else 0

example (phi : ℝ × ℝ → ℝ) : actualEndpointNumerator phi 0 = 0 := rfl
example (phi : ℝ × ℝ → ℝ) : actualConditionalEndpointAverage phi 1 = 0 := rfl

/-- At size two the numerator for the constant test is one: there are no proper overlap lengths to exclude. -/
theorem actualEndpointNumerator_one_two : actualEndpointNumerator (fun _ => 1) 2 = 1 := by
  have hH : avoiding 2 = Finset.univ := by
    ext π
    simp only [mem_avoiding, Finset.mem_univ, iff_true]
    intro k hk hkn
    omega
  simp [actualEndpointNumerator, hH]

/-- At size two the conditional average of the constant test is one. -/
theorem actualConditionalEndpointAverage_one_two :
    actualConditionalEndpointAverage (fun _ => 1) 2 = 1 := by
  have hH : avoiding 2 = Finset.univ := by
    ext π
    simp only [mem_avoiding, Finset.mem_univ, iff_true]
    intro k hk hkn
    omega
  simp [actualConditionalEndpointAverage, hH]

/-- The actual numerator is the weighted distinct-fiber sum for every size at least two. -/
theorem actualEndpointNumerator_eq {n : ℕ} (hn : 2 ≤ n) (phi : ℝ × ℝ → ℝ) :
    actualEndpointNumerator phi n =
      (∑ a : Fin n, ∑ b : Fin n with a ≠ b,
        phi ((a.val : ℝ) / ((n : ℝ) - 1), (b.val : ℝ) / ((n : ℝ) - 1)) *
          PermutationSameEdgeLimit.F n a.val b.val) / ((n : ℝ) * ((n : ℝ) - 1)) := by
  rw [actualEndpointNumerator, dif_pos hn]
  exact PermutationJointEndpointCounting.weighted_actual_disintegration hn (fun x y => phi (x, y))

/-- The constant test numerator is exactly the probability of actual full avoidance. -/
theorem actualEndpointNumerator_one {n : ℕ} (hn : 2 ≤ n) :
    actualEndpointNumerator (fun _ => 1) n =
      ((avoiding n).card : ℝ) / (Fintype.card (Equiv.Perm (Fin n)) : ℝ) := by
  simp [actualEndpointNumerator, hn]

/-- The actual conditional average is the actual numerator divided by the full-avoidance probability. -/
theorem actualConditionalEndpointAverage_eq {n : ℕ} (hn : 2 ≤ n)
    (phi : ℝ × ℝ → ℝ) :
    actualConditionalEndpointAverage phi n =
      actualEndpointNumerator phi n /
        (((avoiding n).card : ℝ) / (Fintype.card (Equiv.Perm (Fin n)) : ℝ)) := by
  have hp : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt Fintype.card_pos)
  simp only [actualConditionalEndpointAverage, actualEndpointNumerator, dif_pos hn]
  exact (div_div_div_cancel_right₀ hp _ _).symm

/-- The weighted profile limit is the actual unconditional full-avoidance numerator limit. -/
theorem actualEndpointNumerator_tendsto (P : ℝ × ℝ → ℝ)
    (hcont : ContinuousOn P (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1))
    (hunit : ∀ z ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1, 0 ≤ P z ∧ P z ≤ 1)
    (hP : ∀ K z, z ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 →
      0 ≤ profileApprox K z - P z ∧ profileApprox K z - P z ≤ 6 / ((K + 3) / 3).factorial)
    (phi : ℝ × ℝ → ℝ)
    (hphi : ContinuousOn phi (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)) :
    Tendsto (actualEndpointNumerator phi) atTop
      (𝓝 (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, phi (x, y) * P (x, y))) := by
  apply (actual_weighted_tendsto P hcont hunit hP phi hphi).congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  exact (actualEndpointNumerator_eq hn phi).symm

/-- Actual full avoidance has positive cardinality at every size at least thirty. -/
theorem actual_avoiding_card_pos {n : ℕ} (hn : 30 ≤ n) : 0 < (avoiding n).card := by
  have hp : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin n)) := by
    exact_mod_cast Fintype.card_pos
  have hb := (le_div_iff₀ hp).mp
    (PermutationJointEndpointCounting.avoiding_probability_lower hn)
  have hc : (0 : ℝ) < (avoiding n).card :=
    lt_of_lt_of_le (mul_pos (by norm_num : (0 : ℝ) < 16991 / 50400) hp) hb
  exact_mod_cast hc

/-- The mass of actual full avoidance tends to the integral of the same residual-bearing profile. -/
theorem actual_avoiding_probability_tendsto (P : ℝ × ℝ → ℝ)
    (hcont : ContinuousOn P (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1))
    (hunit : ∀ z ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1, 0 ≤ P z ∧ P z ≤ 1)
    (hP : ∀ K z, z ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 →
      0 ≤ profileApprox K z - P z ∧ profileApprox K z - P z ≤ 6 / ((K + 3) / 3).factorial) :
    Tendsto (fun n : ℕ => ((avoiding n).card : ℝ) /
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ)) atTop
      (𝓝 (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, P (x, y))) := by
  have ht := actualEndpointNumerator_tendsto P hcont hunit hP (fun _ => 1)
    continuousOn_const
  simp only [one_mul] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  exact actualEndpointNumerator_one hn

/-- The residual-bearing profile has integral at least the uniform actual avoidance lower bound. -/
theorem profile_integral_lower (P : ℝ × ℝ → ℝ)
    (hcont : ContinuousOn P (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1))
    (hunit : ∀ z ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1, 0 ≤ P z ∧ P z ≤ 1)
    (hP : ∀ K z, z ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 →
      0 ≤ profileApprox K z - P z ∧ profileApprox K z - P z ≤ 6 / ((K + 3) / 3).factorial) :
    (16991 / 50400 : ℝ) ≤ ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, P (x, y) := by
  apply ge_of_tendsto (actual_avoiding_probability_tendsto P hcont hunit hP)
  filter_upwards [eventually_ge_atTop 30] with n hn
  exact PermutationJointEndpointCounting.avoiding_probability_lower hn

/-- Uniform full-avoidance conditional endpoint averages converge for every continuous square test, with the same profile as the boundary-polynomial uniform limit and its strictly positive integral normalizer. No profile, fiber, or Riemann-limit premise is assumed. -/
theorem exists_actual_conditional_endpoint_limit :
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
          (𝓝 ((∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, phi (x, y) * P (x, y)) / Z))) := by
  obtain ⟨P, hcont, hunit, hu, hP⟩ := exists_continuous_profile_limit
  let Z : ℝ := ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, P (x, y)
  have hZlower : (16991 / 50400 : ℝ) ≤ Z := profile_integral_lower P hcont hunit hP
  have hZpos : 0 < Z := lt_of_lt_of_le (by norm_num) hZlower
  refine ⟨P, Z, hcont, hunit, hu, hP, rfl, hZlower, hZpos,
    fun n hn => actual_avoiding_card_pos hn, ?_⟩
  intro phi hphi
  have hnum := actualEndpointNumerator_tendsto P hcont hunit hP phi hphi
  have hmass := actual_avoiding_probability_tendsto P hcont hunit hP
  apply (hnum.div hmass (ne_of_gt hZpos)).congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  exact (actualConditionalEndpointAverage_eq hn phi).symm

example : Nonempty (Fin 30) ∧ 0 < (avoiding 30).card :=
  ⟨⟨0⟩, actual_avoiding_card_pos (by decide)⟩

example : ((0 : ℝ), (0 : ℝ)) ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 :=
  ⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl, zero_le_one⟩⟩

end PermutationJointEndpointProfile
