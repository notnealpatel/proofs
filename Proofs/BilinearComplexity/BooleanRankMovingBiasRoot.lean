import BilinearComplexity.BooleanRankBiasedRoot

set_option autoImplicit false

open Filter Topology

namespace BilinearComplexity.BooleanRankProbability

private theorem moving_complement_pow_tendsto
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (t : ℕ → ℝ)
    (ht : Tendsto t atTop (nhds p)) :
    Tendsto (fun n : ℕ => (1 - t n) ^ (n - 1)) atTop (nhds 0) := by
  have hq : Tendsto (fun n => 1 - t n) atTop (nhds (1 - p)) :=
    tendsto_const_nhds.sub ht
  obtain ⟨r, hqr, hr1⟩ := exists_between (show 1 - p < 1 by linarith)
  have hr0 : 0 < r := by linarith
  have hgeom : Tendsto (fun n : ℕ => r ^ n / r) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1).div_const r
  have hvalid : ∀ᶠ n in atTop, 0 ≤ 1 - t n := by
    filter_upwards [ht.eventually_lt_const hp1] with n hn
    linarith
  apply squeeze_zero' (hvalid.mono (fun n hn => pow_nonneg hn _)) ?_ hgeom
  filter_upwards [eventually_ge_atTop 1, hvalid, hq.eventually_lt_const hqr] with n hn hqn hnr
  have heq : r ^ n / r = r ^ (n - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hn, pow_succ]
    exact mul_div_cancel_right₀ _ hr0.ne'
  rw [heq]
  exact pow_le_pow_left₀ hqn hnr.le _

private theorem moving_envelope_eventually_le_pow
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (t : ℕ → ℝ)
    (ht : Tendsto t atTop (nhds p))
    {b : ℝ} (hb : max p (1 - p) < b) :
    ∀ᶠ n : ℕ in atTop, deficitMass (t n) n ≤ b ^ n := by
  have hq0 : 0 ≤ 1 - p := by linarith
  have hq1 : 1 - p < 1 := by linarith
  have hq : Tendsto (fun n => 1 - t n) atTop (nhds (1 - p)) :=
    tendsto_const_nhds.sub ht
  have hb0 : 0 < b := lt_trans (lt_of_lt_of_le hp (le_max_left _ _)) hb
  have hgeom : Tendsto (fun K : ℕ => (1 - p) ^ K) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have hbase : Tendsto (fun K : ℕ => max p (1 - p) + (1 - p) ^ (K + 1))
      atTop (nhds (max p (1 - p))) := by
    simpa only [pow_succ, mul_zero, zero_mul, add_zero] using
      (hgeom.mul_const (1 - p)).const_add (max p (1 - p))
  obtain ⟨K, hK, hKb⟩ := ((eventually_ge_atTop 1).and
    (hbase.eventually_lt_const hb)).exists
  obtain ⟨a, hca, hab⟩ := exists_between hKb
  have ha0 : 0 ≤ a := (add_nonneg (hp.le.trans (le_max_left _ _))
    (pow_nonneg hq0 _)).trans hca.le
  have hvar : Tendsto (fun n => max (t n) (1 - t n) + (1 - t n) ^ (K + 1))
      atTop (nhds (max p (1 - p) + (1 - p) ^ (K + 1))) :=
    (ht.max hq).add (hq.pow (K + 1))
  have hr0 : 0 ≤ a / b := div_nonneg ha0 hb0.le
  have hr1 : a / b < 1 := (div_lt_one hb0).mpr hab
  have hdecay : Tendsto (fun n : ℕ =>
      (K : ℝ) * ((n : ℝ) ^ K * (a / b) ^ n) +
        (n : ℝ) ^ (K + 1) * (a / b) ^ n) atTop (nhds 0) := by
    simpa using ((tendsto_pow_const_mul_const_pow_of_lt_one K hr0 hr1).const_mul
      (K : ℝ)).add (tendsto_pow_const_mul_const_pow_of_lt_one (K + 1) hr0 hr1)
  filter_upwards [eventually_ge_atTop (K + 1), ht.eventually_const_lt hp,
    ht.eventually_lt_const hp1, hvar.eventually_lt_const hca,
    hdecay.eventually_lt_const (by norm_num : (0 : ℝ) < 1)] with n hn htn0 htn1 hna hsmall
  have hvar0 : 0 ≤ max (t n) (1 - t n) + (1 - t n) ^ (K + 1) :=
    add_nonneg (htn0.le.trans (le_max_left _ _)) (pow_nonneg (by linarith) _)
  calc
    deficitMass (t n) n ≤
        ((K : ℝ) * (n : ℝ) ^ K + (n : ℝ) ^ (K + 1)) *
          (max (t n) (1 - t n) + (1 - t n) ^ (K + 1)) ^ n :=
      deficitMass_le_envelope (t n) n K htn0 htn1 hK hn
    _ ≤ ((K : ℝ) * (n : ℝ) ^ K + (n : ℝ) ^ (K + 1)) * a ^ n :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hvar0 hna.le n) (by positivity)
    _ ≤ b ^ n := by
      apply (div_le_one (pow_pos hb0 n)).mp
      have heq : (((K : ℝ) * (n : ℝ) ^ K + (n : ℝ) ^ (K + 1)) * a ^ n) / b ^ n =
          (K : ℝ) * ((n : ℝ) ^ K * (a / b) ^ n) +
            (n : ℝ) ^ (K + 1) * (a / b) ^ n := by
        rw [show (a / b) ^ n = a ^ n / b ^ n from div_pow a b n]
        ring
      rw [heq]
      exact hsmall.le

/-- If the Bernoulli bias converges to an interior parameter, the positive nth
root of the actual displayed-row OR-rank deficit mass converges to the larger
limiting atom. Only eventual interiority is needed: the totalized mass at
invalid early biases and at dimension zero does not affect this limit. -/
theorem deficitMass_moving_bias_root_tendsto
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (t : ℕ → ℝ)
    (ht : Tendsto t atTop (nhds p)) :
    Tendsto (fun n : ℕ => Real.rpow (deficitMass (t n) n) (1 / (n : ℝ)))
      atTop (nhds (max p (1 - p))) := by
  have hvalid : ∀ᶠ n in atTop, 0 < t n ∧ t n < 1 :=
    (ht.eventually_const_lt hp).and (ht.eventually_lt_const hp1)
  have hq : Tendsto (fun n => 1 - t n) atTop (nhds (1 - p)) :=
    tendsto_const_nhds.sub ht
  have hplim : Tendsto (fun n : ℕ => t n * (1 - (1 - t n) ^ (n - 1)))
      atTop (nhds p) := by
    simpa using ht.mul ((tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).sub
      (moving_complement_pow_tendsto p hp hp1 t ht))
  apply tendsto_order.mpr
  constructor
  · intro c hc
    rcases lt_max_iff.mp hc with hcp | hcq
    · filter_upwards [eventually_ge_atTop 1, hvalid,
        hplim.eventually_const_lt hcp] with n hn htn hcn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hD : 0 ≤ deficitMass (t n) n := deficitMass_nonneg (t n) n htn.1 htn.2
      have hbase0 : 0 ≤ t n * (1 - (1 - t n) ^ (n - 1)) :=
        mul_nonneg htn.1.le (sub_nonneg.mpr (pow_le_one₀ (by linarith [htn.2])
          (by linarith [htn.1])))
      have hroot : t n * (1 - (1 - t n) ^ (n - 1)) ≤
          Real.rpow (deficitMass (t n) n) (n : ℝ)⁻¹ := by
        apply (Real.le_rpow_inv_iff_of_pos hbase0 hD hnpos).mpr
        rw [Real.rpow_natCast]
        exact full_row_or_pow_le_deficit_sum n hn (t n) htn.1 htn.2
      simpa only [one_div] using hcn.trans_le hroot
    · filter_upwards [eventually_ge_atTop 1, hvalid,
        hq.eventually_const_lt hcq] with n hn htn hcn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hD : 0 ≤ deficitMass (t n) n := deficitMass_nonneg (t n) n htn.1 htn.2
      have hq0 : 0 ≤ 1 - t n := by linarith [htn.2]
      have hroot : 1 - t n ≤ Real.rpow (deficitMass (t n) n) (n : ℝ)⁻¹ := by
        apply (Real.le_rpow_inv_iff_of_pos hq0 hD hnpos).mpr
        rw [Real.rpow_natCast]
        exact zero_row_pow_le_deficit_sum n hn (t n) htn.1 htn.2
      simpa only [one_div] using hcn.trans_le hroot
  · intro c hc
    obtain ⟨b, hb, hbc⟩ := exists_between hc
    filter_upwards [eventually_ge_atTop 1, hvalid,
      moving_envelope_eventually_le_pow p hp hp1 t ht hb] with n hn htn hbound
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hD : 0 ≤ deficitMass (t n) n := deficitMass_nonneg (t n) n htn.1 htn.2
    have hb0 : 0 ≤ b := (hp.le.trans (le_max_left _ _)).trans hb.le
    have hroot : Real.rpow (deficitMass (t n) n) (n : ℝ)⁻¹ ≤ b := by
      apply (Real.rpow_inv_le_iff_of_pos hD hb0 hnpos).mpr
      rw [Real.rpow_natCast]
      exact hbound
    simpa only [one_div] using hroot.trans_lt hbc

example : Tendsto (fun n : ℕ => Real.rpow (deficitMass (1 / 2) n) (1 / (n : ℝ)))
    atTop (nhds (1 / 2 : ℝ)) := by
  convert deficitMass_moving_bias_root_tendsto (1 / 2) (by norm_num)
    (by norm_num) (fun _ => 1 / 2) tendsto_const_nhds using 1 <;> norm_num

end BilinearComplexity.BooleanRankProbability
