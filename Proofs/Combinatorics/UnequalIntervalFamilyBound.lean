import Combinatorics.AffineRetainedDual
import Combinatorics.HalfIntervalRetainedFourthMoment

set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace UnequalIntervalFamilyBound
open AffineRetainedVariance AffineRetainedFourier

/-- The logarithmic interval bound is strictly smaller than half the square-root
interval length, beyond the literal threshold in the family. -/
theorem log_square_lt_half_sqrt (p : ℕ) (hp : 2^20 ≤ p) :
    (1 + Real.log (((p - 1) / 2 : ℕ) : ℝ)) ^ 2 < (Nat.sqrt p : ℝ) / 2 := by
  let t : ℝ := Real.sqrt p
  let u : ℝ := t / 1024
  let w : ℝ := Real.sqrt u
  let m : ℝ := Nat.sqrt p
  let h : ℝ := ((p - 1) / 2 : ℕ)
  have hpR : (1048576 : ℝ) ≤ p := by exact_mod_cast hp
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have ht2 : t^2 = (p : ℝ) := Real.sq_sqrt (Nat.cast_nonneg p)
  have ht : 1024 ≤ t := by nlinarith
  have hu : 1 ≤ u := by dsimp [u]; linarith
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _
  have hw2 : w^2 = u := Real.sq_sqrt (by linarith)
  have hw : 1 ≤ w := by nlinarith
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  have hm2 : m^2 ≤ (p : ℝ) := by
    dsimp [m]
    simpa only [pow_two] using (show (Nat.sqrt p : ℝ) * Nat.sqrt p ≤ p by exact_mod_cast Nat.sqrt_le p)
  have hmnext : (p : ℝ) < (m+1)^2 := by
    dsimp [m]
    simpa only [pow_two, Nat.cast_add, Nat.cast_one, Nat.succ_eq_add_one] using
      (show (p : ℝ) < ((Nat.sqrt p + 1 : ℕ) : ℝ) * (Nat.sqrt p + 1 : ℕ) by exact_mod_cast Nat.lt_succ_sqrt p)
  have htm : t < m + 1 := by nlinarith
  have hmlower : 1020 * u ≤ m := by dsimp [u]; nlinarith
  have hh1 : 1 ≤ h := by
    dsimp [h]
    exact_mod_cast (show 1 ≤ (p-1)/2 by omega)
  have hhupper : h ≤ (p : ℝ) / 2 := by
    have hn : 2 * ((p-1)/2) ≤ p := by omega
    have hr : 2 * h ≤ (p : ℝ) := by dsimp [h]; exact_mod_cast hn
    linarith
  have hU0 : 0 ≤ 1 + Real.log h := by
    have hl := Real.log_nonneg hh1
    linarith
  have hlog : Real.log h ≤ Real.log ((p : ℝ)/2) :=
    Real.log_le_log (by linarith) hhupper
  have hscale : (p : ℝ) / 2 = (2 : ℝ)^19 * w^4 := by
    dsimp [u] at hw2
    nlinarith [sq_nonneg (w^2 - t/1024)]
  have hlogscale : Real.log ((p : ℝ)/2) = 19 * Real.log 2 + 4 * Real.log w := by
    rw [hscale, Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow]
    norm_num
  have hlog2 : Real.log 2 < 1 := by
    have hb := Real.log_lt_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num) (by norm_num : (2 : ℝ) ≠ 1)
    linarith
  have hlogw : Real.log w ≤ w - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hU : 1 + Real.log h < 20 * w := by rw [hlogscale] at hlog; nlinarith
  have hUsq : (1 + Real.log h)^2 < 400 * u := by nlinarith
  change (1 + Real.log h)^2 < m / 2
  nlinarith

/-- The actual two interval cardinalities give the exact average variance in the
square-root versus one-third family. -/
theorem family_avgS_eq (p : ℕ) [Fact p.Prime] :
    let C := (Finset.range (Nat.sqrt p)).image (fun n : ℕ => (n : ZMod p))
    let J := (Finset.range (p / 3)).image (fun n : ℕ => (n : ZMod p))
    avgS C J = (Nat.sqrt p : ℝ) * ((p : ℝ) - Nat.sqrt p) * (p / 3 : ℕ) *
      ((p : ℝ) - (p / 3 : ℕ)) / ((p : ℝ)^2 * ((p : ℝ) - 1)) := by
  dsimp only
  rw [avgS_eq, ZMod.card,
    HalfIntervalRetainedFourthMoment.window_card p (Nat.sqrt p) (Nat.sqrt_le_self p),
    HalfIntervalRetainedFourthMoment.window_card p (p/3) (Nat.div_le_self p 3)]

/-- For every prime at least `2^20`, the actual unchanged retained fourth moment
of the square-root and one-third intervals obeys the explicit logarithmic bound,
which is strictly sharper than twice the square-root length squared times the
actual average variance. -/
theorem family_bound (p : ℕ) [Fact p.Prime] (hp : 2^20 ≤ p) :
    let m := Nat.sqrt p
    let q := p / 3
    let C := (Finset.range m).image (fun n : ℕ => (n : ZMod p))
    let J := (Finset.range q).image (fun n : ℕ => (n : ZMod p))
    let R := retained C J
    let U := 1 + Real.log (((p - 1) / 2 : ℕ) : ℝ)
    let A := (m : ℝ) * ((p : ℝ) - m) * q * ((p : ℝ) - q) /
      ((p : ℝ)^2 * ((p : ℝ) - 1))
    let E := 4 * (m : ℝ)^2 * ((p : ℝ) - m)^2 * q * ((p : ℝ) - q) /
      ((p : ℝ)^2 * ((p : ℝ) - 1)^2) * U^2
    (∑ a ∈ R, F4 C J a) / (R.card : ℝ) ≤ E ∧ E < 2 * (m : ℝ)^2 * A := by
  let m := Nat.sqrt p
  let q := p / 3
  let C := (Finset.range m).image (fun n : ℕ => (n : ZMod p))
  let J := (Finset.range q).image (fun n : ℕ => (n : ZMod p))
  let U := 1 + Real.log (((p - 1) / 2 : ℕ) : ℝ)
  let A := (m : ℝ) * ((p : ℝ) - m) * q * ((p : ℝ) - q) /
    ((p : ℝ)^2 * ((p : ℝ) - 1))
  let K := 4 * (m : ℝ)^2 * ((p : ℝ) - m)^2 * q * ((p : ℝ) - q) /
    ((p : ℝ)^2 * ((p : ℝ) - 1)^2)
  change (∑ a ∈ retained C J, F4 C J a) / ((retained C J).card : ℝ) ≤
    K * U^2 ∧ K * U^2 < 2 * (m : ℝ)^2 * A
  have hp3 : 3 ≤ p := by omega
  have hpR : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hmpos : 0 < (m : ℝ) := by
    exact_mod_cast (Nat.sqrt_pos.mpr (show 0 < p by omega))
  have hmlt : (m : ℝ) < p := by
    exact_mod_cast (Nat.sqrt_lt_self (show 1 < p by omega))
  have hqpos : 0 < (q : ℝ) := by
    exact_mod_cast (show 0 < p / 3 by omega)
  have hqlt : (q : ℝ) < p := by
    exact_mod_cast (show p / 3 < p by omega)
  have hC : C.card = m :=
    HalfIntervalRetainedFourthMoment.window_card p m (Nat.sqrt_le_self p)
  have hJ : J.card = q :=
    HalfIntervalRetainedFourthMoment.window_card p q (Nat.div_le_self p 3)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hL : 0 ≤ L J := Finset.sum_nonneg (fun k hk => norm_nonneg _)
  have hLU : L J ≤ U := by
    calc
      L J ≤ (harmonic ((p - 1) / 2) : ℝ) :=
        HalfIntervalFourierWeight.interval_weight_le_harmonic p q hp3 (Nat.div_le_self p 3)
      _ ≤ U := harmonic_le_one_add_log _
  constructor
  · have hspectral := AffineRetainedDual.retained_fourth_mean_le_swapped C J hp3
    rw [hC, hJ] at hspectral
    exact hspectral.trans (mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ hL (hL.trans hLU)).mpr hLU) hK)
  · have hUsq : U^2 < (m : ℝ) / 2 := log_square_lt_half_sqrt p hp
    have hm1 : (1 : ℝ) ≤ m := by
      have hmNat : 0 < m := Nat.sqrt_pos.mpr (by omega)
      exact_mod_cast hmNat
    have hfactor : (p : ℝ) - m ≤ (p : ℝ) - 1 := by linarith
    have hstrict : 2 * ((p : ℝ) - m) * U^2 < (m : ℝ) * ((p : ℝ) - 1) := by
      have hh := mul_lt_mul_of_pos_left hUsq (show 0 < (p : ℝ) - m by linarith)
      nlinarith
    have hmult := mul_lt_mul_of_pos_left hstrict
      (show 0 < 2 * (m : ℝ)^2 * ((p : ℝ) - m) * q * ((p : ℝ) - q) by positivity)
    have hnum : 4 * (m : ℝ)^2 * ((p : ℝ)-m)^2 * q * ((p : ℝ)-q) * U^2 <
        (2 * (m : ℝ)^2 * ((m : ℝ) * ((p : ℝ)-m) * q * ((p : ℝ)-q))) * ((p : ℝ)-1) := by
      nlinarith only [hmult]
    have hdiv := (div_lt_div_iff_of_pos_right
      (show 0 < (p : ℝ)^2 * ((p : ℝ)-1)^2 by positivity)).mpr hnum
    calc
      K * U^2 = (4 * (m : ℝ)^2 * ((p : ℝ)-m)^2 * q * ((p : ℝ)-q) * U^2) /
          ((p : ℝ)^2 * ((p : ℝ)-1)^2) := by dsimp [K]; ring
      _ < _ := hdiv
      _ = 2 * (m : ℝ)^2 * A := by
        dsimp [A]
        field_simp

/-- The actual variance filter in this family always retains a nonzero slope. -/
theorem family_retained_nonempty (p : ℕ) [Fact p.Prime] :
    (retained
      ((Finset.range (Nat.sqrt p)).image (fun n : ℕ => (n : ZMod p)))
      ((Finset.range (p / 3)).image (fun n : ℕ => (n : ZMod p)))).Nonempty :=
  retained_nonempty _ _

example : Nat.Prime 1048583 ∧ 2^20 ≤ (1048583 : ℕ) ∧
    Nat.sqrt 1048583 = 1024 ∧ 1048583 / 3 = 349527 ∧
    0 < (1024 : ℕ) ∧ 1024 < 349527 ∧
    2 * 1024 < 1048583 + 1 ∧ 2 * 349527 < 1048583 + 1 := by
  norm_num

example :
    let C := (Finset.range (Nat.sqrt 1048583)).image (fun n : ℕ => (n : ZMod 1048583))
    let J := (Finset.range (1048583 / 3)).image (fun n : ℕ => (n : ZMod 1048583))
    C.card = 1024 ∧ J.card = 349527 := by
  dsimp only
  rw [HalfIntervalRetainedFourthMoment.window_card _ _ (Nat.sqrt_le_self _),
    HalfIntervalRetainedFourthMoment.window_card _ _ (Nat.div_le_self _ _)]
  norm_num

end UnequalIntervalFamilyBound
