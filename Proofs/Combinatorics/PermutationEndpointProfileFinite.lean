import Combinatorics.PermutationEndpointProfilePolynomial

set_option autoImplicit false

namespace PermutationEndpointProfile

attribute [local instance] Classical.propDecidable

/-- The actual short-event cardinal equals the filtered fiber cardinal used by
the truncation estimates. -/
theorem shortFraction_eq_kernel {n : ℕ} [NeZero n] (K : ℕ) (a b : Fin n) :
    shortFraction K (0 : Fin n).rev a b =
      (Fintype.card {π : PermutationEndpointCounting.FixedTwo
        (0 : Fin n) (0 : Fin n).rev a b //
        PermutationBoundaryStandardization.ShortAvoid K π.val} : ℝ) /
        Fintype.card (PermutationEndpointCounting.FixedTwo
          (0 : Fin n) (0 : Fin n).rev a b) := by
  unfold shortFraction
  congr 1
  apply Nat.cast_inj.mpr
  rw [← Fintype.card_coe]
  apply Fintype.card_congr
  exact Equiv.subtypeEquivRight (fun π => by
    simp only [shortAvoidFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl)

/-- For increasing labels the actual truncated fraction approximates the
boundary polynomial with the explicit factorial uniform error. -/
theorem shortFraction_polynomial_error {n : ℕ} [NeZero n]
    (K : ℕ) (hK : 2 ≤ K) (hn : 2*K-2 ≤ n)
    (hlarge : (2*K-2-2)*(2*K-2-2+3) ≤ n) (a b : Fin n) (hab : a < b) :
    |shortFraction K (0 : Fin n).rev a b -
      patternPolynomial K (2*K-2) ⟨0, by omega⟩ ⟨2*K-2-1, by omega⟩
        ((a.val : ℝ)/n) ((b.val : ℝ)/n)| ≤
      ((2*K-2).factorial : ℝ) *
        (2 * (2*K-2-2 : ℕ) * ((2*K-2-2 : ℕ)+2) / n) := by
  rw [shortFraction_eq_kernel]
  have hrev : (0 : Fin n).rev = ⟨n-1, by omega⟩ := by ext; simp
  rw [hrev]
  have hz : (0 : Fin n) = ⟨0, by omega⟩ := by ext; simp
  rw [hz]
  rw [PermutationTwoAnchorKernel.shortAvoid_twoAnchor_fraction K n hK hn a b hab]
  exact binomial_sum_error K (2*K-2) n (by omega) hn hlarge _ _ a b hab

/-- Symmetric continuous boundary approximation at cutoff `K+3`. The min/max
extension retains the limiting diagonal rather than using invalid equal labels. -/
noncomputable def profileApprox (K : ℕ) (z : ℝ × ℝ) : ℝ :=
  patternPolynomial (K+3) (2*(K+3)-2) ⟨0, by omega⟩ ⟨2*(K+3)-2-1, by omega⟩
    (min z.1 z.2) (max z.1 z.2)

example (K : ℕ) (x y : ℝ) : profileApprox K (x,y) = profileApprox K (y,x) := by
  simp only [profileApprox, min_comm x y, max_comm x y]

/-- All boundary approximations are continuous on the plane. -/
theorem continuous_profileApprox (K : ℕ) : Continuous (profileApprox K) :=
  continuous_patternPolynomial_min_max (K+3) (2*(K+3)-2) _ _

/-- Every actual distinct-label truncated fraction, in either order, has the
same uniform continuous-polynomial approximation. -/
theorem shortFraction_profileApprox_error {n : ℕ} [NeZero n]
    (K : ℕ) (hn : 2*(K+3)-2 ≤ n)
    (hlarge : (2*(K+3)-2-2)*(2*(K+3)-2-2+3) ≤ n)
    (a b : Fin n) (hab : a ≠ b) :
    |shortFraction (K+3) (0 : Fin n).rev a b -
      profileApprox K ((a.val : ℝ)/n, (b.val : ℝ)/n)| ≤
      ((2*(K+3)-2).factorial : ℝ) *
        (2 * (2*(K+3)-2-2 : ℕ) * ((2*(K+3)-2-2 : ℕ)+2) / n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · have hle : (a.val : ℝ)/n ≤ (b.val : ℝ)/n :=
      div_le_div_of_nonneg_right (by exact_mod_cast hlt.le) hnR.le
    simpa only [profileApprox, min_eq_left hle, max_eq_right hle] using
      shortFraction_polynomial_error (K+3) (by omega) hn hlarge a b hlt
  · have hle : (b.val : ℝ)/n ≤ (a.val : ℝ)/n :=
      div_le_div_of_nonneg_right (by exact_mod_cast hgt.le) hnR.le
    rw [shortFraction_symm]
    simpa only [profileApprox, min_eq_right hle, max_eq_left hle] using
      shortFraction_polynomial_error (K+3) (by omega) hn hlarge b a hgt

example : (0 : Fin 10) ≠ 1 ∧ 2*(0+3)-2 ≤ 10 ∧
    (2*(0+3)-2-2)*(2*(0+3)-2-2+3) ≤ 10 := by decide

end PermutationEndpointProfile
