import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.NumberTheory.Harmonic.Bounds

set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace HalfIntervalFourierWeight

/-- The initial half interval, including zero. -/
def halfInterval (p : ℕ) : Finset (ZMod p) :=
  (Finset.range ((p - 1) / 2 + 1)).image (fun n : ℕ => (n : ZMod p))

example : halfInterval 3 = {0, 1} := by decide

/-- For positive modulus, reduction modulo `p` identifies no two points of the
initial half interval, which therefore has exactly `(p - 1) / 2 + 1` elements. -/
theorem halfInterval_card (p : ℕ) (hp : 0 < p) :
    (halfInterval p).card = (p - 1) / 2 + 1 := by
  rw [halfInterval, Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb hab
  have ha0 := Finset.mem_range.mp ha
  have hb0 := Finset.mem_range.mp hb
  have ha' : a < p := by omega
  have hb' : b < p := by omega
  simpa [ZMod.val_natCast_of_lt ha', ZMod.val_natCast_of_lt hb'] using congrArg ZMod.val hab

/-- Fourier transform with normalized counting measure and negative sign. -/
def hatC {p : ℕ} [NeZero p] (C : Finset (ZMod p)) (k : ZMod p) : ℂ :=
  (p : ℂ)⁻¹ * ∑ x ∈ C, ZMod.stdAddChar (-(k * x))

example {p : ℕ} [NeZero p] (k : ZMod p) : hatC ∅ k = 0 := by simp [hatC]

/-- The nonconstant Fourier weight of the initial half interval. -/
def weight (p : ℕ) [NeZero p] : ℝ :=
  ∑ k ∈ Finset.univ.erase 0, ‖hatC (halfInterval p) k‖

example {p : ℕ} [NeZero p] : weight p =
    ∑ k ∈ Finset.univ.erase 0, ‖hatC (halfInterval p) k‖ := rfl

private lemma denominator_bound {p j : ℕ} [NeZero p]
    (hp : 0 < p) (hj : 1 ≤ j) (hjp : 2 * j ≤ p) :
    4 * (j : ℝ) / p ≤ ‖ZMod.stdAddChar (j : ZMod p) - 1‖ := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hjR : (0 : ℝ) ≤ j := by positivity
  have hjpR : 2 * (j : ℝ) ≤ p := by exact_mod_cast hjp
  have hx : 0 ≤ Real.pi * j / p := by positivity
  have hx' : Real.pi * j / p ≤ Real.pi / 2 := by
    apply (div_le_iff₀ hpR).2
    nlinarith [Real.pi_pos]
  have hs := Real.mul_le_sin hx hx'
  have he : ZMod.stdAddChar (j : ZMod p) =
      Complex.exp (Complex.I * (2 * Real.pi * j / p : ℝ)) := by
    rw [← Int.cast_natCast j, ZMod.stdAddChar_coe]
    push_cast
    congr 1
    ring
  rw [he, Complex.norm_exp_I_mul_ofReal_sub_one]
  have hh : (2 * Real.pi * (j : ℝ) / p) / 2 = Real.pi * j / p := by ring
  rw [hh, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num) (Real.sin_nonneg_of_nonneg_of_le_pi hx (by linarith [Real.pi_pos])))]
  have hid : 2 / Real.pi * (Real.pi * j / p) = 2 * j / p := by
    field_simp
  rw [hid] at hs
  calc
    4 * (j : ℝ) / p = 2 * (2 * j / p) := by ring
    _ ≤ 2 * Real.sin (Real.pi * j / p) := mul_le_mul_of_nonneg_left hs (by norm_num)

private lemma norm_hat_neg {p : ℕ} [NeZero p] (C : Finset (ZMod p))
    (k : ZMod p) : ‖hatC C (-k)‖ = ‖hatC C k‖ := by
  have hc : hatC C (-k) = (starRingEnd ℂ) (hatC C k) := by
    simp only [hatC, map_mul, map_inv₀, map_sum, map_natCast]
    congr 1
    apply Finset.sum_congr rfl
    intro x hx
    rw [← AddChar.map_neg_eq_conj]
    congr 1
    ring
  rw [hc, Complex.norm_conj]

private lemma interval_coefficient_bound {p j r : ℕ} [NeZero p]
    (hrp : r ≤ p)
    (hp : 0 < p) (hj : 1 ≤ j) (hjp : 2 * j ≤ p) :
    ‖hatC (((Finset.range r).image (fun n : ℕ => (n : ZMod p)))) (j : ZMod p)‖ ≤ (2 * (j : ℝ))⁻¹ := by
  let q : ℂ := ZMod.stdAddChar (-(j : ZMod p))
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have hd : 4 * (j : ℝ) / p ≤ ‖q - 1‖ := by
    dsimp [q]
    rw [AddChar.map_neg_eq_conj, ← map_one (starRingEnd ℂ), ← map_sub,
      Complex.norm_conj]
    exact denominator_bound hp hj hjp
  have hq : ‖q‖ = 1 := by simp [q, AddChar.norm_apply]
  have hsum : (∑ x ∈ ((Finset.range r).image (fun n : ℕ => (n : ZMod p))), ZMod.stdAddChar (-((j : ZMod p) * x))) =
      ∑ r ∈ Finset.range r, q ^ r := by
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro r hr
      dsimp [q]
      rw [← AddChar.map_nsmul_eq_pow]
      congr 1
      simp only [nsmul_eq_mul, mul_neg]
      ring
    · intro a ha b hb hab
      have ha0 := Finset.mem_range.mp ha
      have hb0 := Finset.mem_range.mp hb
      have ha' : a < p := by omega
      have hb' : b < p := by omega
      have hv := congrArg ZMod.val hab
      simpa [ZMod.val_natCast_of_lt ha', ZMod.val_natCast_of_lt hb'] using hv
  let S : ℂ := ∑ r ∈ Finset.range r, q ^ r
  have hn : ‖S‖ * ‖q - 1‖ ≤ 2 := by
    rw [← norm_mul, geom_sum_mul]
    calc
      ‖q ^ r - 1‖ ≤ ‖q ^ r‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hq]; norm_num
  have hs : ‖S‖ * (4 * (j : ℝ) / p) ≤ 2 :=
    (mul_le_mul_of_nonneg_left hd (norm_nonneg S)).trans hn
  rw [hatC, hsum, norm_mul, norm_inv, Complex.norm_natCast]
  change (p : ℝ)⁻¹ * ‖S‖ ≤ _
  simp only [inv_eq_one_div]
  apply (le_div_iff₀ (by positivity : 0 < 2 * (j : ℝ))).2
  have hs' : ‖S‖ * (4 * (j : ℝ)) ≤ 2 * p := (div_le_iff₀ hpR).1 (by simpa [mul_div_assoc] using hs)
  field_simp
  nlinarith

/-- Every initial interval of length at most the odd prime has nonconstant Fourier
weight at most the harmonic number at the half-frequency endpoint. -/
theorem interval_weight_le_harmonic (p r : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    (hrp : r ≤ p) :
    (∑ k ∈ Finset.univ.erase (0 : ZMod p),
      ‖hatC ((Finset.range r).image (fun n : ℕ => (n : ZMod p))) k‖) ≤ (harmonic ((p - 1) / 2) : ℝ) := by
  let h := (p - 1) / 2
  have hp0 : 0 < p := by omega
  have hodd : p % 2 = 1 := (Fact.out : p.Prime).eq_two_or_odd.resolve_left (by omega)
  have ph : p = 2 * h + 1 := by dsimp [h]; omega
  let T := Finset.Icc 1 h
  let A : Finset (ZMod p) := T.image (fun j : ℕ => (j : ZMod p))
  let B : Finset (ZMod p) := A.image (fun k => -k)
  have hinj : Set.InjOn (fun j : ℕ => (j : ZMod p)) T := by
    intro a ha b hb hab
    have ha0 := Finset.mem_Icc.mp ha
    have hb0 := Finset.mem_Icc.mp hb
    have ha' : a < p := by omega
    have hb' : b < p := by omega
    simpa [ZMod.val_natCast_of_lt ha', ZMod.val_natCast_of_lt hb'] using congrArg ZMod.val hab
  have hnz : ∀ k ∈ A, k ≠ 0 := by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    have hj' : 1 ≤ j ∧ j ≤ h := Finset.mem_Icc.mp hj
    have hjp : j < p := by omega
    intro hz
    have hv := congrArg ZMod.val hz
    simp only [ZMod.val_natCast_of_lt hjp, ZMod.val_zero] at hv
    omega
  have hd : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro k hk hk'
    obtain ⟨b, hb, hbk⟩ := Finset.mem_image.mp hk'
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hb
    have ha' := Finset.mem_Icc.mp ha
    have hc' := Finset.mem_Icc.mp hc
    have hs : a + c < p := by omega
    have hz : ((a + c : ℕ) : ZMod p) = 0 := by push_cast; rw [← hbk]; ring
    have hv := congrArg ZMod.val hz
    rw [ZMod.val_natCast_of_lt hs, ZMod.val_zero] at hv
    omega
  have hu : Finset.univ.erase (0 : ZMod p) = A ∪ B := by
    ext k
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union]
    constructor
    · intro hk
      have hv := ZMod.val_lt k
      have hv0 : 0 < k.val := by
        by_contra hz
        have hh : k.val = 0 := by omega
        have he := ZMod.natCast_zmod_val k
        rw [hh] at he
        exact hk (by simpa using he.symm)
      by_cases hkh : k.val ≤ h
      · exact Or.inl (Finset.mem_image.mpr ⟨k.val, Finset.mem_Icc.mpr ⟨hv0, hkh⟩, ZMod.natCast_zmod_val k⟩)
      · right
        apply Finset.mem_image.mpr
        refine ⟨((p - k.val : ℕ) : ZMod p), ?_, ?_⟩
        · apply Finset.mem_image.mpr
          exact ⟨p - k.val, Finset.mem_Icc.mpr (by omega), rfl⟩
        · rw [Nat.cast_sub (by omega : k.val ≤ p), ZMod.natCast_self, zero_sub, neg_neg,
            ZMod.natCast_zmod_val]
    · intro hk
      rcases hk with hk | hk
      · exact hnz k hk
      · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hk
        exact neg_ne_zero.mpr (hnz b hb)
  have heq : (∑ k ∈ Finset.univ.erase (0 : ZMod p),
      ‖hatC ((Finset.range r).image (fun n : ℕ => (n : ZMod p))) k‖) = 2 * ∑ j ∈ T, ‖hatC (((Finset.range r).image (fun n : ℕ => (n : ZMod p)))) (j : ZMod p)‖ := by
    rw [hu, Finset.sum_union hd]
    have hb : (∑ k ∈ B, ‖hatC (((Finset.range r).image (fun n : ℕ => (n : ZMod p)))) k‖) =
        ∑ k ∈ A, ‖hatC (((Finset.range r).image (fun n : ℕ => (n : ZMod p)))) k‖ := by
      dsimp only [B]
      rw [Finset.sum_image]
      · exact Finset.sum_congr rfl (fun k hk => norm_hat_neg _ k)
      · intro a ha b hb hab
        exact neg_injective hab
    rw [hb]
    dsimp only [A]
    rw [Finset.sum_image hinj]
    ring
  rw [heq, harmonic_eq_sum_Icc, Rat.cast_sum]
  calc
    2 * ∑ j ∈ T, ‖hatC (((Finset.range r).image (fun n : ℕ => (n : ZMod p)))) (j : ZMod p)‖ ≤
        2 * ∑ j ∈ T, (2 * (j : ℝ))⁻¹ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro j hj
      have hj' := Finset.mem_Icc.mp hj
      exact interval_coefficient_bound hrp hp0 hj'.1 (by omega)
    _ = ∑ j ∈ Finset.Icc 1 ((p - 1) / 2), (((j : ℚ)⁻¹ : ℚ) : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      push_cast
      rw [mul_inv_rev]
      ring

/-- For an odd prime, the half-interval Fourier weight is at most the harmonic
number at its positive endpoint. -/
theorem weight_le_harmonic (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) :
    weight p ≤ (harmonic ((p - 1) / 2) : ℝ) := by
  exact interval_weight_le_harmonic p ((p - 1) / 2 + 1) hp (by omega)

/-- The half-interval Fourier weight is bounded by the harmonic and logarithmic bounds. -/
theorem weight_le_harmonic_le_log (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) :
    weight p ≤ (harmonic ((p - 1) / 2) : ℝ) ∧
      (harmonic ((p - 1) / 2) : ℝ) ≤ 1 + Real.log ((p - 1) / 2 : ℕ) :=
  ⟨weight_le_harmonic p hp, harmonic_le_one_add_log _⟩

example : weight 3 ≤ (harmonic 1 : ℝ) ∧
    (harmonic 1 : ℝ) ≤ 1 + Real.log 1 := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  simpa only [show (3 - 1) / 2 = (1 : ℕ) from rfl, Nat.cast_one] using
    weight_le_harmonic_le_log 3 (by decide)

example : 1 ≤ (3 - 1) / 2 := by decide

end HalfIntervalFourierWeight
