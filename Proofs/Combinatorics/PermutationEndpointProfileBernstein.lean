import Combinatorics.PermutationFiniteIidEndpointLaw
import Combinatorics.PermutationEndpointProfileTransfer

set_option autoImplicit false
noncomputable section
namespace PermutationEndpointProfile
open Filter
open scoped Topology BigOperators

/-- The factorial-normalized Bernstein monomial for an anchor of rank `r`. -/
def anchorBasis (k : ℕ) (r : Fin k) (t : ℝ) : ℝ :=
  t ^ r.val * (1 - t) ^ (k - 1 - r.val) /
    ((r.val.factorial : ℝ) * ((k - 1 - r.val).factorial : ℝ))

example : anchorBasis 2 (0 : Fin 2) 0 = 1 := by norm_num [anchorBasis]
example : anchorBasis 2 (1 : Fin 2) 1 = 1 := by norm_num [anchorBasis]

/-- The two endpoint Bernstein weight of a pattern, zero for the empty pattern. -/
def bernsteinPatternWeight {k : ℕ} (σ : Equiv.Perm (Fin k)) (x y : ℝ) : ℝ :=
  if hk : 0 < k then
    anchorBasis k (σ ⟨0, hk⟩) x * anchorBasis k (σ ⟨k - 1, by omega⟩) y
  else 0

example : bernsteinPatternWeight (Equiv.refl (Fin 0)) 0 1 = 0 := by
  simp [bernsteinPatternWeight]
example : bernsteinPatternWeight (Equiv.refl (Fin 2)) 0 1 = 1 := by
  norm_num [bernsteinPatternWeight, anchorBasis]

/-- The global polynomial obtained by summing the avoiding-pattern Bernstein weights. -/
def bernsteinProfile (K : ℕ) (x y : ℝ) : ℝ :=
  1 - ∑ k ∈ Finset.Icc 2 (K + 2),
    ∑ σ ∈ PermutationAvoidanceCovariance.avoiding k, bernsteinPatternWeight σ x y

example (K : ℕ) (x y : ℝ) : bernsteinProfile K x y =
    1 - ∑ k ∈ Finset.Icc 2 (K + 2),
      ∑ σ ∈ PermutationAvoidanceCovariance.avoiding k, bernsteinPatternWeight σ x y := rfl

/-- Scaled descending factorials converge to powers along any bounded population path. -/
theorem descFactorial_path_tendsto (s : ℕ) (p : ℕ → ℕ) (hp : ∀ j, p j ≤ j + 2)
    (x : ℝ) (hx : Tendsto (fun j => (p j : ℝ) / (j + 2 : ℕ)) atTop (𝓝 x)) :
    Tendsto (fun j => ((p j).descFactorial s : ℝ) / (j + 2 : ℕ) ^ s)
      atTop (𝓝 (x ^ s)) := by
  have he : Tendsto (fun j => ((p j).descFactorial s : ℝ) / (j + 2 : ℕ) ^ s -
      ((p j : ℝ) / (j + 2 : ℕ)) ^ s) atTop (𝓝 0) := by
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall (fun _ => dist_nonneg))
      (Eventually.of_forall (fun j => ?_)) (lattice_error_tendsto ((s : ℝ) ^ 2))
    simpa only [Real.dist_eq, sub_zero] using
      descFactorial_div_pow_error (p j) s (j + 2) (by omega) (hp j)
  simpa only [sub_add_cancel, zero_add] using he.add (hx.pow s)

/-- Complementary anchor populations have limiting density `1-x`, including the boundary. -/
theorem complement_path_tendsto (a : (j : ℕ) → Fin (j + 2)) (x : ℝ)
    (ha : Tendsto (fun j => ((a j).val : ℝ) / (j + 2 : ℕ)) atTop (𝓝 x)) :
    Tendsto (fun j => ((j + 2 - 1 - (a j).val : ℕ) : ℝ) / (j + 2 : ℕ))
      atTop (𝓝 (1 - x)) := by
  have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have h := (hc.sub (lattice_error_tendsto 1)).sub ha
  simp only [sub_zero] at h
  convert h using 1
  ext j
  have hj : (0 : ℝ) < (j + 2 : ℕ) := by positivity
  rw [Nat.cast_sub (by have hlt := (a j).isLt; omega),
    Nat.cast_sub (by omega : 1 ≤ j + 2), Nat.cast_one]
  field_simp

/-- The finite binomial anchor weight is a product of scaled descending factorials. -/
theorem anchorWeight_eq_desc {n k : ℕ} (hn : 0 < n) (a : Fin n) (r : Fin k) :
    PermutationFiniteIidEndpointLaw.anchorWeight a r =
      (((a.val.descFactorial r.val : ℝ) / (n : ℝ) ^ r.val) *
        (((n - 1 - a.val).descFactorial (k - 1 - r.val) : ℝ) /
          (n : ℝ) ^ (k - 1 - r.val))) /
        ((r.val.factorial : ℝ) * ((k - 1 - r.val).factorial : ℝ)) := by
  have hr : r.val + (k - 1 - r.val) = k - 1 := by have h := r.isLt; omega
  rw [PermutationFiniteIidEndpointLaw.anchorWeight,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  rw [show (n : ℝ) ^ (k - 1) = (n : ℝ) ^ r.val * (n : ℝ) ^ (k - 1 - r.val) by
    rw [← pow_add, hr]]
  have hnR : (n : ℝ) ≠ 0 := by positivity
  have hf : (r.val.factorial : ℝ) ≠ 0 := by positivity
  have hg : ((k - 1 - r.val).factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- Binomial anchor weights tend to their Bernstein monomial on every lattice path. -/
theorem anchorWeight_path_tendsto {k : ℕ} (r : Fin k)
    (a : (j : ℕ) → Fin (j + 2)) (x : ℝ)
    (ha : Tendsto (fun j => ((a j).val : ℝ) / (j + 2 : ℕ)) atTop (𝓝 x)) :
    Tendsto (fun j => PermutationFiniteIidEndpointLaw.anchorWeight (a j) r)
      atTop (𝓝 (anchorBasis k r x)) := by
  have hl := descFactorial_path_tendsto r.val (fun j => (a j).val)
    (fun j => (a j).isLt.le) x ha
  have hr := descFactorial_path_tendsto (k - 1 - r.val)
    (fun j => j + 2 - 1 - (a j).val) (fun j => by omega) (1 - x)
    (complement_path_tendsto a x ha)
  have heq : (fun j => PermutationFiniteIidEndpointLaw.anchorWeight (a j) r) =
      (fun j => (((a j).val.descFactorial r.val : ℝ) / (j + 2 : ℕ) ^ r.val *
        (((j + 2 - 1 - (a j).val).descFactorial (k - 1 - r.val) : ℝ) /
          (j + 2 : ℕ) ^ (k - 1 - r.val))) /
          ((r.val.factorial : ℝ) * ((k - 1 - r.val).factorial : ℝ))) := by
    funext j
    exact anchorWeight_eq_desc (by omega) (a j) r
  rw [heq]
  exact (hl.mul hr).div_const
    ((r.val.factorial : ℝ) * ((k - 1 - r.val).factorial : ℝ))

/-- Every finite iid pattern weight converges to its two-anchor Bernstein weight. -/
theorem patternWeight_path_tendsto {k : ℕ} (σ : Equiv.Perm (Fin k))
    (a b : (j : ℕ) → Fin (j + 2)) (x y : ℝ)
    (ha : Tendsto (fun j => ((a j).val : ℝ) / (j + 2 : ℕ)) atTop (𝓝 x))
    (hb : Tendsto (fun j => ((b j).val : ℝ) / (j + 2 : ℕ)) atTop (𝓝 y)) :
    Tendsto (fun j => PermutationFiniteIidEndpointLaw.patternWeight (a j) (b j) σ)
      atTop (𝓝 (bernsteinPatternWeight σ x y)) := by
  by_cases hk : 0 < k
  · simpa only [PermutationFiniteIidEndpointLaw.patternWeight, bernsteinPatternWeight,
      dif_pos hk] using
      (anchorWeight_path_tendsto (σ ⟨0, hk⟩) a x ha).mul
        (anchorWeight_path_tendsto (σ ⟨k - 1, by omega⟩) b y hb)
  · simpa only [PermutationFiniteIidEndpointLaw.patternWeight, bernsteinPatternWeight,
      dif_neg hk] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

/-- Finite iid avoiding-pattern sums converge to the global Bernstein polynomial. -/
theorem patternSum_path_tendsto (K : ℕ) (a b : (j : ℕ) → Fin (j + 2)) (x y : ℝ)
    (ha : Tendsto (fun j => ((a j).val : ℝ) / (j + 2 : ℕ)) atTop (𝓝 x))
    (hb : Tendsto (fun j => ((b j).val : ℝ) / (j + 2 : ℕ)) atTop (𝓝 y)) :
    Tendsto (fun j => PermutationFiniteIidEndpointLaw.patternSum (K + 2) (a j) (b j))
      atTop (𝓝 (bernsteinProfile K x y)) := by
  apply Tendsto.const_sub
  apply tendsto_finsetSum
  intro k _
  apply tendsto_finsetSum
  intro σ _
  exact patternWeight_path_tendsto σ a b x y ha hb

/-- On the entire closed square, the production approximation equals the explicit
finite avoiding-pattern Bernstein polynomial. -/
theorem profileApprox_eq_bernsteinProfile (K : ℕ) (x y : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    profileApprox K (x, y) = bernsteinProfile K x y := by
  obtain ⟨a, b, hab, ha, hb⟩ := exists_distinct_lattice_path x y hx hy
  have hs := shortFraction_path_tendsto K a b hab x y ha hb
  have hp := patternSum_path_tendsto K a b x y ha hb
  have he : Tendsto (fun j =>
      shortFraction (K + 3) (0 : Fin (j + 2)).rev (a j) (b j) -
        PermutationFiniteIidEndpointLaw.patternSum (K + 2) (a j) (b j)) atTop (𝓝 0) := by
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall (fun _ => dist_nonneg))
      (g := fun j => ((Nat.choose (2 * (K + 2) - 2) 2 : ℝ) +
        2 * (2 * (K + 2) - 2 : ℕ)) / (j + 2 : ℕ))
    · filter_upwards [lattice_size_tendsto.eventually_ge_atTop (2 * (K + 2))] with j hj
      simpa only [Real.dist_eq, sub_zero, PermutationFiniteIidEndpointLaw.patternSum,
        show K + 2 + 1 = K + 3 by omega] using
        PermutationFiniteIidEndpointLaw.actual_finite_iid_endpoint_error
          (by omega : 2 ≤ K + 2) hj (0 : Fin (j + 2)).rev (a j) (b j)
          (by simp) (hab j)
    · exact lattice_error_tendsto _
  have hzero : profileApprox K (x, y) - bernsteinProfile K x y = 0 :=
    tendsto_nhds_unique (hs.sub hp) he
  exact sub_eq_zero.mp hzero

example : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 ∧ (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  norm_num

example : profileApprox 0 (0, 1) = bernsteinProfile 0 0 1 :=
  profileApprox_eq_bernsteinProfile 0 0 1 (by norm_num) (by norm_num)

example : (∀ j : ℕ, (0 : Fin (j + 2)) ≠ 1) ∧
    Tendsto (fun j : ℕ => (((0 : Fin (j + 2)).val : ℝ) / (j + 2 : ℕ)))
      atTop (𝓝 0) ∧
    Tendsto (fun j : ℕ => (((1 : Fin (j + 2)).val : ℝ) / (j + 2 : ℕ)))
      atTop (𝓝 0) := by
  refine ⟨fun j => by simp, ?_, ?_⟩
  · simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  · simpa using lattice_error_tendsto 1

end PermutationEndpointProfile
