import Combinatorics.AffineRetainedFourier

set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace AffineRetainedDual
open AffineRetainedVariance
variable {p : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
private theorem indicator_sum (C : Finset (ZMod p)) (y : ZMod p) :
    indicator C y = ∑ x ∈ C, if x = y then (1 : ℝ) else 0 := by
  simp [indicator, eq_comm]

/-- Reversing an affine incidence exchanges the two actual sets. -/
theorem Y_swap (C J : Finset (ZMod p)) (a b : ZMod p) (ha : a ≠ 0) :
    Y C J a b = Y J C a⁻¹ (-a⁻¹ * b) := by
  have he (x j : ZMod p) : x = a * j + b ↔ j = a⁻¹ * x + -a⁻¹ * b := by
    constructor
    · intro hx
      rw [hx]
      field_simp
      ring
    · intro hj
      rw [hj]
      field_simp
      ring
  unfold Y
  simp_rw [indicator_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro j hj
  simp only [he]

/-- The exact mean is symmetric in the two sets. -/
theorem mean_swap (C J : Finset (ZMod p)) : mean C J = mean J C := by
  unfold mean
  rw [mul_comm (C.card : ℝ)]

/-- Translation reparametrization preserves the actual variance. -/
theorem S_swap (C J : Finset (ZMod p)) (a : ZMod p) (ha : a ≠ 0) :
    S C J a = S J C a⁻¹ := by
  unfold S
  simp_rw [Y_swap C J a _ ha, mean_swap C J]
  congr 1
  exact Equiv.sum_comp (Equiv.mulLeft₀ (-a⁻¹) (neg_ne_zero.mpr (inv_ne_zero ha)))
    (fun b : ZMod p => (Y J C a⁻¹ b - mean J C) ^ 2)

/-- Translation reparametrization preserves the actual fourth moment. -/
theorem F4_swap (C J : Finset (ZMod p)) (a : ZMod p) (ha : a ≠ 0) :
    AffineRetainedFourier.F4 C J a = AffineRetainedFourier.F4 J C a⁻¹ := by
  unfold AffineRetainedFourier.F4
  simp_rw [Y_swap C J a _ ha, mean_swap C J]
  congr 1
  exact Equiv.sum_comp (Equiv.mulLeft₀ (-a⁻¹) (neg_ne_zero.mpr (inv_ne_zero ha)))
    (fun b : ZMod p => (Y J C a⁻¹ b - mean J C) ^ 4)

/-- The exact nonzero-direction average variance is symmetric. -/
theorem avgS_swap (C J : Finset (ZMod p)) : avgS C J = avgS J C := by
  rw [avgS_eq, avgS_eq]
  ring

/-- Inversion transports the actual variance filter, with zero excluded. -/
theorem mem_retained_swap (C J : Finset (ZMod p)) (a : ZMod p) :
    a ∈ retained C J ↔ a⁻¹ ∈ retained J C := by
  by_cases ha : a = 0
  · simp [ha, retained, directions]
  · simp [retained, directions, ha, S_swap C J a ha, avgS_swap C J]

/-- Inversion identifies the actual retained sets. -/
theorem retained_image_inv (C J : Finset (ZMod p)) :
    (retained C J).image (fun a => a⁻¹) = retained J C := by
  ext a
  constructor
  · intro ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    exact (mem_retained_swap C J b).mp hb
  · intro ha
    exact Finset.mem_image.mpr ⟨a⁻¹, (mem_retained_swap J C a).mp ha, inv_inv a⟩

/-- The same original retained mean equals the reversed-set retained mean. -/
theorem retained_fourth_mean_swap (C J : Finset (ZMod p)) :
    (∑ a ∈ retained C J, AffineRetainedFourier.F4 C J a) /
        ((retained C J).card : ℝ) =
    (∑ a ∈ retained J C, AffineRetainedFourier.F4 J C a) /
        ((retained J C).card : ℝ) := by
  rw [← retained_image_inv C J, Finset.card_image_of_injective _ inv_injective,
    Finset.sum_image (fun a _ b _ h => inv_injective h)]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  exact F4_swap C J a (Finset.mem_erase.mp (retained_subset C J ha)).1

/-- Arbitrary sets satisfy the actual retained fourth-moment bound using the
Fourier weight of the first set, including empty and full sets. -/
theorem retained_fourth_mean_le (C J : Finset (ZMod p)) (hp : 3 ≤ p) :
    (∑ a ∈ retained C J, AffineRetainedFourier.F4 C J a) /
        ((retained C J).card : ℝ) ≤
    (4 * (C.card : ℝ) * ((p : ℝ) - C.card) * (J.card : ℝ)^2 *
      ((p : ℝ) - J.card)^2 / ((p : ℝ)^2 * ((p : ℝ) - 1)^2)) *
        (AffineRetainedFourier.L C)^2 := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hq : (J.card : ℝ) ≤ p := by exact_mod_cast (show J.card ≤ p by simpa using Finset.card_le_univ J)
  have hT : 0 ≤ (J.card : ℝ) * ((p : ℝ) - J.card) :=
    mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hq)
  have hA : 0 ≤ avgS C J := avgS_nonneg C J
  have hR : 0 < ((retained C J).card : ℝ) := by
    exact_mod_cast (retained_nonempty C J).card_pos
  have hcard : ((p : ℝ) - 1) / 2 ≤ ((retained C J).card : ℝ) := by
    simpa using half_le_card_retained C J
  have hactual := RetainedMoment.retained_fourth_mean_le
    (directions (ZMod p)) (retained C J) (directions (ZMod p))
    (fun k => ‖AffineRetainedFourier.hatC C k‖)
    (fun a k => ‖AffineRetainedFourier.DJ J (a * k)‖)
    (AffineRetainedFourier.F4 C J) (2 * avgS C J)
    ((J.card : ℝ) * ((p : ℝ) - J.card))
    (retained_subset C J) (retained_nonempty C J)
    (fun _ _ => norm_nonneg _) (by positivity)
    (fun k hk => (AffineRetainedFourier.DJ_nonzero_energy J k
      (Finset.mem_erase.mp hk).1).le)
    (fun a ha => (AffineRetainedFourier.F4_le_S C J a).trans
      (mul_le_mul_of_nonneg_right (S_le_two_avgS C J a ha) (sq_nonneg _)))
  have hcoef : (2 * avgS C J * ((J.card : ℝ) * ((p : ℝ) - J.card))) /
        ((retained C J).card : ℝ) ≤
      (2 * avgS C J * ((J.card : ℝ) * ((p : ℝ) - J.card))) /
        (((p : ℝ) - 1) / 2) :=
    div_le_div_of_nonneg_left (by positivity) (by linarith) hcard
  refine hactual.trans ((mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)).trans_eq ?_)
  change _ * (AffineRetainedFourier.L C)^2 = _
  rw [avgS_eq, ZMod.card]
  field_simp
  ring

/-- The actual original retained mean also obeys the dual Fourier-weight bound. -/
theorem retained_fourth_mean_le_swapped (C J : Finset (ZMod p)) (hp : 3 ≤ p) :
    (∑ a ∈ retained C J, AffineRetainedFourier.F4 C J a) /
        ((retained C J).card : ℝ) ≤
    (4 * (C.card : ℝ)^2 * ((p : ℝ) - C.card)^2 * (J.card : ℝ) *
      ((p : ℝ) - J.card) / ((p : ℝ)^2 * ((p : ℝ) - 1)^2)) *
        (AffineRetainedFourier.L J)^2 := by
  rw [retained_fourth_mean_swap C J]
  convert retained_fourth_mean_le J C hp using 1
  ring

/-- The actual retained fourth mean is bounded by the better of the two explicit
Fourier-weight coefficients, with the same original retained set in both bounds. -/
theorem retained_fourth_mean_le_min (C J : Finset (ZMod p)) (hp : 3 ≤ p) :
    (∑ a ∈ retained C J, AffineRetainedFourier.F4 C J a) /
        ((retained C J).card : ℝ) ≤ min
    ((4 * (C.card : ℝ) * ((p : ℝ) - C.card) * (J.card : ℝ)^2 *
      ((p : ℝ) - J.card)^2 / ((p : ℝ)^2 * ((p : ℝ) - 1)^2)) *
        (AffineRetainedFourier.L C)^2)
    ((4 * (C.card : ℝ)^2 * ((p : ℝ) - C.card)^2 * (J.card : ℝ) *
      ((p : ℝ) - J.card) / ((p : ℝ)^2 * ((p : ℝ) - 1)^2)) *
        (AffineRetainedFourier.L J)^2) :=
  le_min (retained_fourth_mean_le C J hp) (retained_fourth_mean_le_swapped C J hp)

end AffineRetainedDual
