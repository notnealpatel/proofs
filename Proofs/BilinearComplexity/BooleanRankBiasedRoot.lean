import BilinearComplexity.BooleanRankBiasedCounting
import BilinearComplexity.BooleanRankBiasedLower
import BilinearComplexity.BooleanRankDeficitRoot

set_option autoImplicit false

open Filter Topology

namespace BilinearComplexity

/-- A polynomial envelope with geometrically shrinking excess base gives every
strictly larger exponential bound eventually. -/
theorem biased_envelope_eventually_le_pow
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (D : ℕ → ℝ)
    (hupper : ∀ K : ℕ, 1 ≤ K → ∀ n : ℕ, K + 1 ≤ n →
      D n ≤ ((K : ℝ) * (n : ℝ) ^ K + (n : ℝ) ^ (K + 1)) *
        (max p (1 - p) + (1 - p) ^ (K + 1)) ^ n)
    {b : ℝ} (hb : max p (1 - p) < b) :
    ∀ᶠ n : ℕ in atTop, D n ≤ b ^ n := by
  have hq0 : 0 ≤ 1 - p := by linarith
  have hq1 : 1 - p < 1 := by linarith
  have hb0 : 0 < b := lt_trans (lt_of_lt_of_le hp (le_max_left _ _)) hb
  have hgeom : Tendsto (fun K : ℕ => (1 - p) ^ K) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have hbase : Tendsto (fun K : ℕ => max p (1 - p) + (1 - p) ^ (K + 1))
      atTop (nhds (max p (1 - p))) := by
    simpa only [pow_succ, mul_zero, zero_mul, add_zero] using
      (hgeom.mul_const (1 - p)).const_add (max p (1 - p))
  obtain ⟨K, hK, hKb⟩ := ((eventually_ge_atTop 1).and
    (hbase.eventually_lt_const hb)).exists
  let a : ℝ := max p (1 - p) + (1 - p) ^ (K + 1)
  have ha0 : 0 ≤ a := add_nonneg (le_trans hp.le (le_max_left _ _)) (pow_nonneg hq0 _)
  have hab : a < b := hKb
  have hr0 : 0 ≤ a / b := div_nonneg ha0 hb0.le
  have hr1 : a / b < 1 := (div_lt_one hb0).mpr hab
  have hdecay : Tendsto (fun n : ℕ =>
      (K : ℝ) * ((n : ℝ) ^ K * (a / b) ^ n) +
        (n : ℝ) ^ (K + 1) * (a / b) ^ n) atTop (nhds 0) := by
    simpa using ((tendsto_pow_const_mul_const_pow_of_lt_one K hr0 hr1).const_mul
      (K : ℝ)).add (tendsto_pow_const_mul_const_pow_of_lt_one (K + 1) hr0 hr1)
  filter_upwards [eventually_ge_atTop (K + 1),
    hdecay.eventually_lt_const (by norm_num : (0 : ℝ) < 1)] with n hn hsmall
  refine (hupper K hK n hn).trans ?_
  change ((K : ℝ) * (n : ℝ) ^ K + (n : ℝ) ^ (K + 1)) * a ^ n ≤ b ^ n
  apply (div_le_one (pow_pos hb0 n)).mp
  have heq : (((K : ℝ) * (n : ℝ) ^ K + (n : ℝ) ^ (K + 1)) * a ^ n) / b ^ n =
      (K : ℝ) * ((n : ℝ) ^ K * (a / b) ^ n) +
        (n : ℝ) ^ (K + 1) * (a / b) ^ n := by
    rw [show (a / b) ^ n = a ^ n / b ^ n from div_pow a b n]
    ring
  rw [heq]
  exact hsmall.le

/-- Abstract biased deficit bounds imply the maximum-bias root limit.
The positive-dimension restrictions exclude the totalized zeroth root. -/
theorem biased_root_tendsto_of_bounds
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (D : ℕ → ℝ)
    (hD : ∀ n, 0 ≤ D n)
    (hlowq : ∀ n : ℕ, 1 ≤ n → (1 - p) ^ n ≤ D n)
    (hlowp : ∀ n : ℕ, 1 ≤ n → (p * (1 - (1 - p) ^ (n - 1))) ^ n ≤ D n)
    (hupper : ∀ K : ℕ, 1 ≤ K → ∀ n : ℕ, K + 1 ≤ n →
      D n ≤ ((K : ℝ) * (n : ℝ) ^ K + (n : ℝ) ^ (K + 1)) *
        (max p (1 - p) + (1 - p) ^ (K + 1)) ^ n) :
    Tendsto (fun n : ℕ => Real.rpow (D n) (1 / (n : ℝ)))
      atTop (nhds (max p (1 - p))) := by
  have hq0 : 0 < 1 - p := by linarith
  have hq1 : 1 - p < 1 := by linarith
  have hgeom : Tendsto (fun n : ℕ => (1 - p) ^ n / (1 - p)) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1).div_const (1 - p)
  have hplim : Tendsto (fun n : ℕ => p * (1 - (1 - p) ^ n / (1 - p)))
      atTop (nhds p) := by
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).sub hgeom).const_mul p
  apply tendsto_order.mpr
  constructor
  · intro c hc
    rcases lt_max_iff.mp hc with hcp | hcq
    · filter_upwards [eventually_ge_atTop 1, hplim.eventually_const_lt hcp] with n hn hcn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hpow : (1 - p) ^ n / (1 - p) = (1 - p) ^ (n - 1) := by
        conv_lhs => rw [← Nat.sub_add_cancel hn, pow_succ]
        exact mul_div_cancel_right₀ _ hq0.ne'
      have hbase0 : 0 ≤ p * (1 - (1 - p) ^ (n - 1)) :=
        mul_nonneg hp.le (sub_nonneg.mpr (pow_le_one₀ hq0.le hq1.le))
      have hroot : p * (1 - (1 - p) ^ (n - 1)) ≤ Real.rpow (D n) (n : ℝ)⁻¹ := by
        apply (Real.le_rpow_inv_iff_of_pos hbase0 (hD n) hnpos).mpr
        rw [Real.rpow_natCast]
        exact hlowp n hn
      rw [hpow] at hcn
      simpa only [one_div] using hcn.trans_le hroot
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hroot : 1 - p ≤ Real.rpow (D n) (n : ℝ)⁻¹ := by
        apply (Real.le_rpow_inv_iff_of_pos hq0.le (hD n) hnpos).mpr
        rw [Real.rpow_natCast]
        exact hlowq n hn
      simpa only [one_div] using hcq.trans_le hroot
  · intro c hc
    obtain ⟨b, hb, hbc⟩ := exists_between hc
    filter_upwards [eventually_ge_atTop 1,
      biased_envelope_eventually_le_pow p hp hp1 D hupper hb] with n hn hbound
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hb0 : 0 ≤ b := (hp.le.trans (le_max_left _ _)).trans hb.le
    have hroot : Real.rpow (D n) (n : ℝ)⁻¹ ≤ b := by
      apply (Real.rpow_inv_le_iff_of_pos (hD n) hb0 hnpos).mpr
      rw [Real.rpow_natCast]
      exact hbound
    simpa only [one_div] using hroot.trans_lt hbc

namespace BooleanRankProbability

/-- The actual biased displayed-row OR deficit has a fixed-degree polynomial
upper envelope with exponential base tending to the larger Bernoulli atom. -/
theorem deficitMass_le_envelope (p : ℝ) (n K : ℕ)
    (hp : 0 < p) (hp1 : p < 1) (hK : 1 ≤ K) (hn : K + 1 ≤ n) :
    deficitMass p n ≤
      ((K : ℝ) * (n : ℝ) ^ K + (n : ℝ) ^ (K + 1)) *
        (max p (1 - p) + (1 - p) ^ (K + 1)) ^ n := by
  let a : ℝ := max p (1 - p) + (1 - p) ^ (K + 1)
  have hn1 : 1 ≤ n := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hq0 : 0 ≤ 1 - p := by linarith
  have hmax0 : 0 ≤ max p (1 - p) := hp.le.trans (le_max_left _ _)
  have hmax : max p (1 - p) ≤ a := le_add_of_nonneg_right (pow_nonneg hq0 _)
  have ha : 0 ≤ a := hmax0.trans hmax
  have hpbase : p + (1 - p) ^ (K + 1) ≤ a :=
    add_le_add (le_max_left p (1 - p)) le_rfl
  have hchoose (k : ℕ) : (Nat.choose (n - 1) k : ℝ) ≤ (n : ℝ) ^ k := by
    exact_mod_cast (Nat.choose_le_pow (n - 1) k).trans
      (Nat.pow_le_pow_left (Nat.sub_le n 1) k)
  have hsum : (∑ k ∈ Finset.range K, (Nat.choose (n - 1) k : ℝ)) ≤
      (K : ℝ) * (n : ℝ) ^ (K - 1) := by
    calc
      _ ≤ ∑ k ∈ Finset.range K, (n : ℝ) ^ (K - 1) := by
        apply Finset.sum_le_sum
        intro k hk
        exact (hchoose k).trans (pow_le_pow_right₀ hnR (by
          have hk' := Finset.mem_range.mp hk
          omega))
      _ = _ := by simp
  have hpowers : (n : ℝ) * ((K : ℝ) * (n : ℝ) ^ (K - 1)) =
      (K : ℝ) * (n : ℝ) ^ K := by
    have he : K - 1 + 1 = K := Nat.sub_add_cancel hK
    have hpow : (n : ℝ) ^ K = (n : ℝ) ^ (K - 1) * n := by
      calc
        (n : ℝ) ^ K = (n : ℝ) ^ (K - 1 + 1) := by rw [he]
        _ = _ := pow_succ _ _
    rw [hpow]
    ring
  calc
    _ ≤ _ := deficitMass_le_twoScale_max p n K hp hp1 hK hn
    _ ≤ (n : ℝ) * ((K : ℝ) * (n : ℝ) ^ (K - 1)) * a ^ n +
        n * (n : ℝ) ^ K * a ^ n := by
      apply add_le_add
      · exact mul_le_mul
          (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg n))
          (pow_le_pow_left₀ hmax0 hmax n) (pow_nonneg hmax0 n) (by positivity)
      · exact mul_le_mul
          (mul_le_mul_of_nonneg_left (hchoose K) (Nat.cast_nonneg n))
          (pow_le_pow_left₀ (add_nonneg hp.le (pow_nonneg hq0 _)) hpbase n)
          (pow_nonneg (add_nonneg hp.le (pow_nonneg hq0 _)) n) (by positivity)
    _ = _ := by rw [hpowers, pow_succ]; ring

/-- For each fixed Bernoulli parameter strictly between zero and one, the
positive nth root of the actual deficient displayed-row OR-rank mass tends
to the larger atom. The empty OR convention is unchanged; dimension zero
is irrelevant to the limit at infinity. -/
theorem deficitMass_root_tendsto (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun n : ℕ => Real.rpow (deficitMass p n) (1 / (n : ℝ)))
      atTop (nhds (max p (1 - p))) := by
  apply biased_root_tendsto_of_bounds p hp hp1 (deficitMass p)
  · exact fun n => deficitMass_nonneg p n hp hp1
  · exact fun n hn => zero_row_pow_le_deficit_sum n hn p hp hp1
  · exact fun n hn => full_row_or_pow_le_deficit_sum n hn p hp hp1
  · exact fun K hK n hn => deficitMass_le_envelope p n K hp hp1 hK hn

example : 0 < (1 / 2 : ℝ) ∧ (1 / 2 : ℝ) < 1 ∧
    1 ≤ (1 : ℕ) ∧ 1 + 1 ≤ (2 : ℕ) ∧ Nonempty (Fin 2) ∧
    Nonempty (BoolMatrix 2 2) := by
  exact ⟨by norm_num, by norm_num, by decide, by decide, ⟨0⟩, ⟨0⟩⟩

end BooleanRankProbability

end BilinearComplexity
