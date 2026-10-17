import Combinatorics.AffineRetainedFourier
import Combinatorics.HalfIntervalFourierWeight

set_option autoImplicit false

open scoped BigOperators

noncomputable section

namespace HalfIntervalRetainedFourthMoment

/-- Reduction modulo `p` preserves the cardinality of an initial window of length at most `p`. -/
theorem window_card (p q : ℕ) (hqp : q ≤ p) :
    ((Finset.range q).image (fun n : ℕ => (n : ZMod p))).card = q := by
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb hab
  have ha' : a < p := lt_of_lt_of_le (Finset.mem_range.mp ha) hqp
  have hb' : b < p := lt_of_lt_of_le (Finset.mem_range.mp hb) hqp
  simpa only [ZMod.val_natCast_of_lt ha', ZMod.val_natCast_of_lt hb'] using
    congrArg ZMod.val hab

/-- The two production Fourier coefficients use exactly the same normalization and sign. -/
theorem hatC_eq (p : ℕ) [Fact p.Prime] (C : Finset (ZMod p)) (k : ZMod p) :
    AffineRetainedFourier.hatC C k = HalfIntervalFourierWeight.hatC C k := rfl

/-- The actual consumer's nonzero-frequency weight is the half-interval leaf's weight. -/
theorem L_eq_weight (p : ℕ) [Fact p.Prime] :
    AffineRetainedFourier.L (HalfIntervalFourierWeight.halfInterval p) =
      HalfIntervalFourierWeight.weight p := rfl

/-- At an odd prime, the initial half interval has twice its cardinality equal to `p + 1`. -/
theorem halfInterval_twice_card (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) :
    2 * ((HalfIntervalFourierWeight.halfInterval p).card : ℝ) = (p : ℝ) + 1 := by
  have hp0 : 0 < p := by omega
  have hodd : p % 2 = 1 :=
    (Fact.out : p.Prime).eq_two_or_odd.resolve_left (by omega)
  have ph : p = 2 * ((p - 1) / 2) + 1 := by omega
  rw [HalfIntervalFourierWeight.halfInterval_card p hp0]
  exact_mod_cast (show 2 * ((p - 1) / 2 + 1) = p + 1 by omega)

/-- The original half-interval affine variance, for the actual initial window. -/
theorem avgS_eq (p q : ℕ) [Fact p.Prime] (hp : 3 ≤ p) (hqp : q ≤ p) :
    let C := HalfIntervalFourierWeight.halfInterval p
    let J := (Finset.range q).image (fun n : ℕ => (n : ZMod p))
    AffineRetainedVariance.avgS C J =
      ((p : ℝ) + 1) * q * ((p : ℝ) - q) / (4 * (p : ℝ) ^ 2) := by
  dsimp only
  have h := AffineRetainedVariance.two_mul_avgS_eq
    (HalfIntervalFourierWeight.halfInterval p)
    ((Finset.range q).image (fun n : ℕ => (n : ZMod p)))
    (by simpa only [ZMod.card] using halfInterval_twice_card p hp)
  rw [ZMod.card, window_card p q hqp] at h
  have hpR : (p : ℝ) ≠ 0 := by positivity
  field_simp [hpR] at h ⊢
  nlinarith [h]

/-- At least `(p - 1) / 2` directions pass the actual variance filter. -/
theorem half_le_card_retained (p q : ℕ) [Fact p.Prime] :
    let C := HalfIntervalFourierWeight.halfInterval p
    let J := (Finset.range q).image (fun n : ℕ => (n : ZMod p))
    ((p : ℝ) - 1) / 2 ≤ ((AffineRetainedVariance.retained C J).card : ℝ) := by
  simpa only [ZMod.card] using AffineRetainedVariance.half_le_card_retained
    (HalfIntervalFourierWeight.halfInterval p)
    ((Finset.range q).image (fun n : ℕ => (n : ZMod p)))

/-- The actual retained set is nonempty, including for a full window of zero variance. -/
theorem retained_nonempty (p q : ℕ) [Fact p.Prime] :
    let C := HalfIntervalFourierWeight.halfInterval p
    let J := (Finset.range q).image (fun n : ℕ => (n : ZMod p))
    (AffineRetainedVariance.retained C J).Nonempty :=
  AffineRetainedVariance.retained_nonempty _ _

/-- For every nonempty initial window of length at most an odd prime, the actual
retained fourth-moment mean is bounded by the squared harmonic weight, and then
by the squared logarithmic weight. No Fourier assumptions are required. -/
theorem retained_fourth_mean_le_harmonic_le_log (p q : ℕ) [Fact p.Prime]
    (hp : 3 ≤ p) (hq : 1 ≤ q) (hqp : q ≤ p) :
    let C := HalfIntervalFourierWeight.halfInterval p
    let J := (Finset.range q).image (fun n : ℕ => (n : ZMod p))
    let R := AffineRetainedVariance.retained C J
    (∑ a ∈ R, AffineRetainedFourier.F4 C J a) / (R.card : ℝ) ≤
        (q : ℝ) ^ 2 * (harmonic ((p - 1) / 2) : ℝ) ^ 2 ∧
      (q : ℝ) ^ 2 * (harmonic ((p - 1) / 2) : ℝ) ^ 2 ≤
        (q : ℝ) ^ 2 * (1 + Real.log ((p - 1) / 2 : ℕ)) ^ 2 := by
  let C := HalfIntervalFourierWeight.halfInterval p
  let J := (Finset.range q).image (fun n : ℕ => (n : ZMod p))
  have hJ : J.card = q := window_card p q hqp
  have hm : 2 * (C.card : ℝ) = (p : ℝ) + 1 := halfInterval_twice_card p hp
  have hactual := AffineRetainedFourier.retained_fourth_mean_le C J hp
    (by rw [hJ]; exact hq) hm
  rw [hJ] at hactual
  have hbounds := HalfIntervalFourierWeight.weight_le_harmonic_le_log p hp
  have hL : 0 ≤ AffineRetainedFourier.L C :=
    Finset.sum_nonneg (fun k hk => norm_nonneg _)
  have hLH : AffineRetainedFourier.L C ≤ (harmonic ((p - 1) / 2) : ℝ) := by
    simpa only [C, L_eq_weight] using hbounds.1
  have hH : 0 ≤ (harmonic ((p - 1) / 2) : ℝ) := hL.trans hLH
  have hlog : 0 ≤ 1 + Real.log ((p - 1) / 2 : ℕ) := hH.trans hbounds.2
  have hsq := (sq_le_sq₀ hL hH).mpr hLH
  have hlogsq := (sq_le_sq₀ hH hlog).mpr hbounds.2
  exact ⟨hactual.trans (mul_le_mul_of_nonneg_left hsq (sq_nonneg (q : ℝ))),
    mul_le_mul_of_nonneg_left hlogsq (sq_nonneg (q : ℝ))⟩

example : 3 ≤ (3 : ℕ) ∧ 1 ≤ (1 : ℕ) ∧ (1 : ℕ) ≤ 3 := by decide
example : 3 ≤ (3 : ℕ) ∧ 1 ≤ (3 : ℕ) ∧ (3 : ℕ) ≤ 3 := by decide

example :
    let C := HalfIntervalFourierWeight.halfInterval 3
    let J := (Finset.range 1).image (fun n : ℕ => (n : ZMod 3))
    let R := AffineRetainedVariance.retained C J
    (∑ a ∈ R, AffineRetainedFourier.F4 C J a) / (R.card : ℝ) ≤
      (1 : ℝ) ^ 2 * (harmonic 1 : ℝ) ^ 2 ∧
    (1 : ℝ) ^ 2 * (harmonic 1 : ℝ) ^ 2 ≤
      (1 : ℝ) ^ 2 * (1 + Real.log 1) ^ 2 := by
  simpa using retained_fourth_mean_le_harmonic_le_log 3 1 (by decide) (by decide) (by decide)

example :
    let C := HalfIntervalFourierWeight.halfInterval 3
    let J := (Finset.range 3).image (fun n : ℕ => (n : ZMod 3))
    let R := AffineRetainedVariance.retained C J
    (∑ a ∈ R, AffineRetainedFourier.F4 C J a) / (R.card : ℝ) ≤
      (3 : ℝ) ^ 2 * (harmonic 1 : ℝ) ^ 2 ∧
    (3 : ℝ) ^ 2 * (harmonic 1 : ℝ) ^ 2 ≤
      (3 : ℝ) ^ 2 * (1 + Real.log 1) ^ 2 := by
  simpa using retained_fourth_mean_le_harmonic_le_log 3 3 (by decide) (by decide) (by decide)

end HalfIntervalRetainedFourthMoment
