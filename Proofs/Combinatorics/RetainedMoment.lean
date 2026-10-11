import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace RetainedMoment

/-- Weighted Cauchy–Schwarz for real amplitudes and nonnegative weights. -/
theorem weighted_sq_le {κ : Type*} (K : Finset κ) (c d : κ → ℝ)
    (hc : ∀ k ∈ K, 0 ≤ c k) :
    (∑ k ∈ K, c k * d k) ^ 2 ≤
      (∑ k ∈ K, c k) * ∑ k ∈ K, c k * d k ^ 2 := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul K hc
    (fun k hk ↦ mul_nonneg (hc k hk) (sq_nonneg (d k)))
  intro k hk
  exact le_of_eq (by ring)

/-- Restricting a nonnegative quadratic energy to retained directions cannot increase it. -/
theorem retained_energy_le {α : Type*} (D R : Finset α) (d : α → ℝ) (T : ℝ)
    (hRD : R ⊆ D) (henergy : ∑ a ∈ D, d a ^ 2 ≤ T) :
    ∑ a ∈ R, d a ^ 2 ≤ T := by
  exact (Finset.sum_le_sum_of_subset_of_nonneg hRD
    (fun a _ _ ↦ sq_nonneg (d a))).trans henergy

/-- Each mode's uniform retained mean energy is at most total energy divided by
retained cardinality, regardless of how retention was chosen. -/
theorem retained_energy_mean_le {α : Type*} (D R : Finset α) (d : α → ℝ) (T : ℝ)
    (hRD : R ⊆ D) (hR : R.Nonempty) (henergy : ∑ a ∈ D, d a ^ 2 ≤ T) :
    (∑ a ∈ R, d a ^ 2) / (R.card : ℝ) ≤ T / (R.card : ℝ) := by
  have hcard : 0 < (R.card : ℝ) := by exact_mod_cast hR.card_pos
  exact div_le_div_of_nonneg_right (retained_energy_le D R d T hRD henergy) hcard.le

/-- Per-mode total quadratic energy controls the retained sum of squared weighted
amplitudes by `T` times the square of the total weight. -/
theorem retained_weighted_sq_sum_le {α κ : Type*} (D R : Finset α) (K : Finset κ)
    (c : κ → ℝ) (d : α → κ → ℝ) (T : ℝ)
    (hRD : R ⊆ D) (hc : ∀ k ∈ K, 0 ≤ c k)
    (henergy : ∀ k ∈ K, ∑ a ∈ D, d a k ^ 2 ≤ T) :
    ∑ a ∈ R, (∑ k ∈ K, c k * d a k) ^ 2 ≤ T * (∑ k ∈ K, c k) ^ 2 := by
  have hL : 0 ≤ ∑ k ∈ K, c k := Finset.sum_nonneg hc
  have hrestricted : ∀ k ∈ K, ∑ a ∈ R, d a k ^ 2 ≤ T := by
    intro k hk
    exact retained_energy_le D R (fun a ↦ d a k) T hRD (henergy k hk)
  calc
    ∑ a ∈ R, (∑ k ∈ K, c k * d a k) ^ 2
        ≤ ∑ a ∈ R, (∑ k ∈ K, c k) * ∑ k ∈ K, c k * d a k ^ 2 :=
      Finset.sum_le_sum (fun a _ ↦ weighted_sq_le K c (d a) hc)
    _ = (∑ k ∈ K, c k) * ∑ k ∈ K, c k * ∑ a ∈ R, d a k ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp_rw [Finset.mul_sum]
    _ ≤ (∑ k ∈ K, c k) * ∑ k ∈ K, c k * T := by
      apply mul_le_mul_of_nonneg_left _ hL
      exact Finset.sum_le_sum (fun k hk ↦ mul_le_mul_of_nonneg_left
        (hrestricted k hk) (hc k hk))
    _ = T * (∑ k ∈ K, c k) ^ 2 := by rw [← Finset.sum_mul]; ring

/-- The full retained variance filter `F4 ≤ s B²`, together with per-mode quadratic
energy, bounds the retained fourth-moment sum without a fourth-amplitude estimate. -/
theorem retained_fourth_sum_le {α κ : Type*} (D R : Finset α) (K : Finset κ)
    (c : κ → ℝ) (d : α → κ → ℝ) (F4 : α → ℝ) (s T : ℝ)
    (hRD : R ⊆ D) (hc : ∀ k ∈ K, 0 ≤ c k) (hs : 0 ≤ s)
    (henergy : ∀ k ∈ K, ∑ a ∈ D, d a k ^ 2 ≤ T)
    (hfilter : ∀ a ∈ R, F4 a ≤ s * (∑ k ∈ K, c k * d a k) ^ 2) :
    ∑ a ∈ R, F4 a ≤ s * T * (∑ k ∈ K, c k) ^ 2 := by
  calc
    ∑ a ∈ R, F4 a ≤ ∑ a ∈ R, s * (∑ k ∈ K, c k * d a k) ^ 2 :=
      Finset.sum_le_sum hfilter
    _ = s * ∑ a ∈ R, (∑ k ∈ K, c k * d a k) ^ 2 := (Finset.mul_sum ..).symm
    _ ≤ s * (T * (∑ k ∈ K, c k) ^ 2) :=
      mul_le_mul_of_nonneg_left (retained_weighted_sq_sum_le D R K c d T hRD hc henergy) hs
    _ = s * T * (∑ k ∈ K, c k) ^ 2 := by ring

/-- For a nonempty retained set, the uniform fourth-moment mean is bounded by
`(s T / |R|) L²`; no independence of modes or of retention is required. -/
theorem retained_fourth_mean_le {α κ : Type*} (D R : Finset α) (K : Finset κ)
    (c : κ → ℝ) (d : α → κ → ℝ) (F4 : α → ℝ) (s T : ℝ)
    (hRD : R ⊆ D) (hR : R.Nonempty) (hc : ∀ k ∈ K, 0 ≤ c k) (hs : 0 ≤ s)
    (henergy : ∀ k ∈ K, ∑ a ∈ D, d a k ^ 2 ≤ T)
    (hfilter : ∀ a ∈ R, F4 a ≤ s * (∑ k ∈ K, c k * d a k) ^ 2) :
    (∑ a ∈ R, F4 a) / (R.card : ℝ) ≤
      (s * T / (R.card : ℝ)) * (∑ k ∈ K, c k) ^ 2 := by
  have hcard : 0 < (R.card : ℝ) := by exact_mod_cast hR.card_pos
  calc
    (∑ a ∈ R, F4 a) / (R.card : ℝ)
        ≤ (s * T * (∑ k ∈ K, c k) ^ 2) / (R.card : ℝ) :=
      div_le_div_of_nonneg_right
        (retained_fourth_sum_le D R K c d F4 s T hRD hc hs henergy hfilter) hcard.le
    _ = _ := by ring

/-- The half-interval variance and retention constants give a coefficient at most
`q²`, including `q = p`; all divisions have positive denominators. -/
theorem half_interval_factor_le (p q r : ℝ) (hp : 3 ≤ p) (hq : 1 ≤ q)
    (hqp : q ≤ p) (hr : (p - 1) / 2 ≤ r) :
    (((p + 1) * q * (p - q) / (2 * p ^ 2)) * (q * (p - q)) / r) ≤ q ^ 2 := by
  have hp0 : 0 < p := by linarith
  have hr0 : 0 < r := by linarith
  have hdiff : 0 ≤ p - q := sub_nonneg.mpr hqp
  have hsq : (p - q) ^ 2 ≤ (p - 1) ^ 2 := by nlinarith
  have hcoef : (p + 1) * (p - q) ^ 2 ≤ 2 * p ^ 2 * r := by
    have h1 := mul_le_mul_of_nonneg_left hsq (show 0 ≤ p + 1 by linarith)
    have h2 := mul_le_mul_of_nonneg_left hr (sq_nonneg p)
    nlinarith
  apply (div_le_iff₀ hr0).mpr
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (show 0 < 2 * p ^ 2 by positivity)).mpr
  have hfinal := mul_le_mul_of_nonneg_left hcoef (sq_nonneg q)
  nlinarith

/-- Numerical half-interval consumer: the exact per-mode energy, full variance
filter, retained cardinality bound, and total Fourier weight bound imply a
retained fourth-moment mean at most `q² H²`. These are conditional inputs, not
assertions that the finite-field Fourier bridges have already been formalized. -/
theorem half_interval_fourth_mean_le {α κ : Type*} (D R : Finset α) (K : Finset κ)
    (c : κ → ℝ) (d : α → κ → ℝ) (F4 : α → ℝ) (p q H : ℝ)
    (hp : 3 ≤ p) (hq : 1 ≤ q) (hqp : q ≤ p)
    (hRD : R ⊆ D) (hc : ∀ k ∈ K, 0 ≤ c k)
    (hcard : (p - 1) / 2 ≤ (R.card : ℝ))
    (henergy : ∀ k ∈ K, ∑ a ∈ D, d a k ^ 2 ≤ q * (p - q))
    (hfilter : ∀ a ∈ R, F4 a ≤
      ((p + 1) * q * (p - q) / (2 * p ^ 2)) * (∑ k ∈ K, c k * d a k) ^ 2)
    (hweight : ∑ k ∈ K, c k ≤ H) :
    (∑ a ∈ R, F4 a) / (R.card : ℝ) ≤ q ^ 2 * H ^ 2 := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 ≤ q := by linarith
  have hdiff : 0 ≤ p - q := sub_nonneg.mpr hqp
  have hs : 0 ≤ (p + 1) * q * (p - q) / (2 * p ^ 2) := by positivity
  have hcard0 : 0 < (R.card : ℝ) := by linarith
  have hR : R.Nonempty := Finset.card_pos.mp (by exact_mod_cast hcard0)
  have hL : 0 ≤ ∑ k ∈ K, c k := Finset.sum_nonneg hc
  have hH : 0 ≤ H := hL.trans hweight
  have hweight_sq : (∑ k ∈ K, c k) ^ 2 ≤ H ^ 2 := by nlinarith
  calc
    (∑ a ∈ R, F4 a) / (R.card : ℝ)
        ≤ (((p + 1) * q * (p - q) / (2 * p ^ 2)) *
          (q * (p - q)) / (R.card : ℝ)) * (∑ k ∈ K, c k) ^ 2 :=
      retained_fourth_mean_le D R K c d F4 _ _ hRD hR hc hs henergy hfilter
    _ ≤ q ^ 2 * (∑ k ∈ K, c k) ^ 2 :=
      mul_le_mul_of_nonneg_right
        (half_interval_factor_le p q (R.card : ℝ) hp hq hqp hcard) (sq_nonneg _)
    _ ≤ q ^ 2 * H ^ 2 := mul_le_mul_of_nonneg_left hweight_sq (sq_nonneg q)

-- One nonempty concrete model jointly satisfies all generic consumer hypotheses.
example : (∑ _a ∈ ({0} : Finset ℕ), (1 : ℝ)) / (({0} : Finset ℕ).card : ℝ) ≤
    (1 * 1 / (({0} : Finset ℕ).card : ℝ)) * (∑ _k ∈ ({0} : Finset ℕ), (1 : ℝ)) ^ 2 := by
  exact retained_fourth_mean_le {0} {0} {0} (fun _ : ℕ ↦ 1)
    (fun _ _ ↦ 1) (fun _ ↦ 1) 1 1
    (by simp) (by simp) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

-- The specialized hypotheses also coexist, with p=3, q=1, and singleton supports.
example : (∑ _a ∈ ({0} : Finset ℕ), (4 / 9 : ℝ)) /
    (({0} : Finset ℕ).card : ℝ) ≤ (1 : ℝ) ^ 2 * 1 ^ 2 := by
  exact half_interval_fourth_mean_le {0} {0} {0} (fun _ : ℕ ↦ 1)
    (fun _ _ ↦ 1) (fun _ ↦ 4 / 9) 3 1 1
    (by norm_num) (by norm_num) (by norm_num) (by simp) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : (((3 + 1 : ℝ) * 1 * (3 - 1) / (2 * 3 ^ 2)) *
    (1 * (3 - 1)) / 1) ≤ 1 ^ 2 := by
  exact half_interval_factor_le 3 1 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

end RetainedMoment
