import BilinearComplexity.BooleanRankCounting
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

open Filter Topology

namespace BilinearComplexity

/-- The fraction of Boolean matrices whose displayed-row OR rank is deficient.
The denominator is strictly positive for every natural dimension. -/
noncomputable def fullRowRankDeficitFraction (n : ℕ) : ℝ :=
  ((2 ^ (n * n) - fullRowRankCount n : ℕ) : ℝ) / (2 : ℝ) ^ (n * n)

/-- The deficit fraction is the complement of the full-rank fraction. -/
theorem fullRowRankDeficitFraction_eq_one_sub (n : ℕ) :
    fullRowRankDeficitFraction n = 1 - fullRowRankFraction n := by
  unfold fullRowRankDeficitFraction fullRowRankFraction
  rw [Nat.cast_sub (fullRowRankCount_le_total n)]
  push_cast
  field_simp

example : fullRowRankDeficitFraction 1 = 1 / 2 := by
  have h : fullRowRankCount 1 = 1 := by
    rw [fullRowRankCount_eq_card_filter_not le_rfl]
    decide
  norm_num [fullRowRankDeficitFraction, h]

/-- Prescribing a zero first row injects all assignments to the other rows
into the rank-deficient matrices, including in dimension one. -/
theorem two_pow_le_total_sub_fullRowRankCount {n : ℕ} (hn : 1 ≤ n) :
    2 ^ (n * (n - 1)) ≤ 2 ^ (n * n) - fullRowRankCount n := by
  classical
  let i : Fin n := ⟨0, by omega⟩
  let f := fun (B : {j : Fin n // j ≠ i} → Fin n → BoolSemiring)
    (j : Fin n) => if h : j = i then 0 else B ⟨j, h⟩
  have hcard : Fintype.card {j : Fin n // j ≠ i} = n - 1 := by
    rw [Fintype.card_subtype]
    have heq : (Finset.univ.filter fun j : Fin n => j ≠ i) = Finset.univ.erase i := by
      ext j
      simp
    rw [heq]
    simp
  have hBS : Fintype.card BoolSemiring = 2 := rfl
  rw [total_sub_fullRowRankCount_eq]
  calc
    2 ^ (n * (n - 1)) =
        (Finset.univ : Finset ({j : Fin n // j ≠ i} → Fin n → BoolSemiring)).card := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fun, hBS,
        Fintype.card_fin, hcard, ← pow_mul]
    _ ≤ _ := by
      apply Finset.card_le_card_of_injOn f
      · intro B hB
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, (boolRowRank_lt_iff_redundant _).mpr ?_⟩
        exact ⟨i, ∅, by simp, by funext c; simp [f, rowsSum]⟩
      · intro B hB C hC hBC
        funext j c
        have hj := congrFun (congrFun hBC j.1) c
        simpa [f, j.2] using hj

/-- The zero-row event gives the exponential lower bound on the deficit. -/
theorem half_pow_le_fullRowRankDeficitFraction {n : ℕ} (hn : 1 ≤ n) :
    (1 / 2 : ℝ) ^ n ≤ fullRowRankDeficitFraction n := by
  have hcount : (2 : ℝ) ^ (n * (n - 1)) ≤
      ((2 ^ (n * n) - fullRowRankCount n : ℕ) : ℝ) := by
    exact_mod_cast two_pow_le_total_sub_fullRowRankCount hn
  have hexp : n * (n - 1) + n = n * n := by
    calc
      n * (n - 1) + n = n * (n - 1 + 1) := by ring
      _ = n * n := by rw [Nat.sub_add_cancel hn]
  have hsplit : (2 : ℝ) ^ (n * n) = 2 ^ (n * (n - 1)) * 2 ^ n := by
    rw [← pow_add, hexp]
  unfold fullRowRankDeficitFraction
  apply (le_div_iff₀ (by positivity)).mpr
  rw [hsplit, div_pow]
  calc
    (1 ^ n / (2 : ℝ) ^ n) * (2 ^ (n * (n - 1)) * 2 ^ n)
        = 2 ^ (n * (n - 1)) := by field_simp; ring
    _ ≤ _ := hcount

/-- Normalizing the two-scale counting bound preserves both exponential bases. -/
theorem fullRowRankDeficitFraction_le_normalized (n K : ℕ)
    (hK : 1 ≤ K) (hn : K + 1 ≤ n) :
    fullRowRankDeficitFraction n ≤
      (n : ℝ) * (1 / 2 : ℝ) ^ n *
        (∑ k ∈ Finset.range K, (Nat.choose (n - 1) k : ℝ)) +
      n * (Nat.choose (n - 1) K : ℝ) *
        (((2 : ℝ) ^ K + 1) / 2 ^ (K + 1)) ^ n := by
  have hc := total_sub_fullRowRankCount_le n K hK (by omega)
  have hcR : ((2 ^ (n * n) - fullRowRankCount n : ℕ) : ℝ) ≤
      (n : ℝ) * 2 ^ (n * (n - 1)) *
        (∑ k ∈ Finset.range K, (Nat.choose (n - 1) k : ℝ)) +
      n * (Nat.choose (n - 1) K : ℝ) * ((2 : ℝ) ^ K + 1) ^ n *
        2 ^ (n * (n - K - 1)) := by exact_mod_cast hc
  have e1 : n * (n - 1) + n = n * n := by
    have he : n - 1 + 1 = n := by omega
    nlinarith
  have e2 : n * (n - K - 1) + (K + 1) * n = n * n := by
    have he : n - K - 1 + (K + 1) = n := by omega
    nlinarith
  have p1 : (2 : ℝ) ^ (n * n) = 2 ^ (n * (n - 1)) * 2 ^ n := by
    rw [← pow_add, e1]
  have p2 : (2 : ℝ) ^ (n * n) = 2 ^ (n * (n - K - 1)) * (2 ^ (K + 1)) ^ n := by
    rw [← pow_mul, ← pow_add, e2]
  unfold fullRowRankDeficitFraction
  refine (div_le_div_of_nonneg_right hcR (by positivity)).trans_eq ?_
  rw [add_div]
  congr 1
  · rw [p1, div_pow]
    field_simp
    simp
  · rw [p2, div_pow]
    field_simp

/-- A fixed-degree polynomial envelope for the normalized deficit bound. -/
theorem fullRowRankDeficitFraction_le_envelope (n K : ℕ)
    (hK : 1 ≤ K) (hn : K + 1 ≤ n) :
    fullRowRankDeficitFraction n ≤
      ((K : ℝ) * (n : ℝ) ^ K + (n : ℝ) ^ (K + 1)) *
        (((2 : ℝ) ^ K + 1) / 2 ^ (K + 1)) ^ n := by
  let a : ℝ := ((2 : ℝ) ^ K + 1) / 2 ^ (K + 1)
  have hn1 : 1 ≤ n := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
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
  have hhalf : (1 / 2 : ℝ) ≤ a := by
    dsimp [a]
    rw [pow_succ]
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) K]
  have hp : (n : ℝ) * ((K : ℝ) * (n : ℝ) ^ (K - 1)) =
      (K : ℝ) * (n : ℝ) ^ K := by
    have he : K - 1 + 1 = K := Nat.sub_add_cancel hK
    have hpow : (n : ℝ) ^ K = (n : ℝ) ^ (K - 1) * n := by
      calc
        (n : ℝ) ^ K = (n : ℝ) ^ (K - 1 + 1) := by rw [he]
        _ = _ := pow_succ _ _
    rw [hpow]
    ring
  have ha : 0 ≤ a := le_trans (by norm_num) hhalf
  calc
    _ ≤ _ := fullRowRankDeficitFraction_le_normalized n K hK hn
    _ ≤ (n : ℝ) * a ^ n * ((K : ℝ) * (n : ℝ) ^ (K - 1)) +
        n * (n : ℝ) ^ K * a ^ n := by
      apply add_le_add
      · exact mul_le_mul (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by norm_num) hhalf n) (by positivity)) hsum
          (Finset.sum_nonneg fun k hk => Nat.cast_nonneg _) 
          (mul_nonneg (by positivity) (pow_nonneg ha n))
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hchoose K) (by positivity)) (pow_nonneg ha n)
    _ = _ := by
      calc
        _ = ((n : ℝ) * ((K : ℝ) * (n : ℝ) ^ (K - 1)) +
            n * (n : ℝ) ^ K) * a ^ n := by ring
        _ = _ := by rw [hp, pow_succ]; ring

/-- Any base strictly above one half eventually bounds the deficit exponentially. -/
theorem fullRowRankDeficitFraction_eventually_le_pow {b : ℝ} (hb : 1 / 2 < b) :
    ∀ᶠ n : ℕ in atTop, fullRowRankDeficitFraction n ≤ b ^ n := by
  have hb0 : 0 < b := lt_trans (by norm_num) hb
  have hgeom : Tendsto (fun K : ℕ => (1 / 2 : ℝ) ^ K) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hbase : Tendsto (fun K : ℕ => (1 / 2 : ℝ) + (1 / 2 : ℝ) ^ K / 2)
      atTop (nhds (1 / 2)) := by
    simpa using (hgeom.div_const 2).const_add (1 / 2 : ℝ)
  obtain ⟨K, hK, hKb⟩ := ((eventually_ge_atTop 1).and
    (hbase.eventually_lt_const hb)).exists
  let a : ℝ := ((2 : ℝ) ^ K + 1) / 2 ^ (K + 1)
  have haeq : a = (1 / 2 : ℝ) + (1 / 2 : ℝ) ^ K / 2 := by
    dsimp [a]
    rw [pow_succ, div_pow]
    field_simp
    ring
  have ha0 : 0 ≤ a := by rw [haeq]; positivity
  have hab : a < b := by rw [haeq]; exact hKb
  have hr0 : 0 ≤ a / b := div_nonneg ha0 hb0.le
  have hr1 : a / b < 1 := (div_lt_one hb0).mpr hab
  have hdecay : Tendsto (fun n : ℕ =>
      (K : ℝ) * ((n : ℝ) ^ K * (a / b) ^ n) +
        (n : ℝ) ^ (K + 1) * (a / b) ^ n) atTop (nhds 0) := by
    simpa using ((tendsto_pow_const_mul_const_pow_of_lt_one K hr0 hr1).const_mul
      (K : ℝ)).add (tendsto_pow_const_mul_const_pow_of_lt_one (K + 1) hr0 hr1)
  filter_upwards [eventually_ge_atTop (K + 1),
    hdecay.eventually_lt_const (by norm_num : (0 : ℝ) < 1)] with n hn hsmall
  refine (fullRowRankDeficitFraction_le_envelope n K hK hn).trans ?_
  change ((K : ℝ) * (n : ℝ) ^ K + (n : ℝ) ^ (K + 1)) * a ^ n ≤ b ^ n
  apply (div_le_one (pow_pos hb0 n)).mp
  have heq : (((K : ℝ) * (n : ℝ) ^ K + (n : ℝ) ^ (K + 1)) * a ^ n) / b ^ n =
      (K : ℝ) * ((n : ℝ) ^ K * (a / b) ^ n) +
        (n : ℝ) ^ (K + 1) * (a / b) ^ n := by
    rw [show (a / b) ^ n = a ^ n / b ^ n from div_pow a b n]
    ring
  rw [heq]
  exact hsmall.le

/-- The positive nth root of the displayed-row OR-rank deficit fraction
converges to one half. Dimension zero does not affect the limit. -/
theorem fullRowRankDeficitFraction_root_tendsto_half :
    Tendsto (fun n : ℕ => Real.rpow (fullRowRankDeficitFraction n) (1 / (n : ℝ)))
      atTop (nhds (1 / 2)) := by
  have hnonneg (n : ℕ) : 0 ≤ fullRowRankDeficitFraction n := by
    unfold fullRowRankDeficitFraction
    positivity
  apply tendsto_order.mpr
  constructor
  · intro c hc
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hroot : (1 / 2 : ℝ) ≤ Real.rpow (fullRowRankDeficitFraction n) (n : ℝ)⁻¹ := by
      apply (Real.le_rpow_inv_iff_of_pos (by norm_num) (hnonneg n) hnpos).mpr
      rw [Real.rpow_natCast]
      exact half_pow_le_fullRowRankDeficitFraction hn
    simpa only [one_div] using hc.trans_le hroot
  · intro c hc
    obtain ⟨b, hb, hbc⟩ := exists_between hc
    filter_upwards [eventually_ge_atTop 1,
      fullRowRankDeficitFraction_eventually_le_pow hb] with n hn hbound
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hb0 : 0 ≤ b := le_trans (by norm_num) hb.le
    have hroot : Real.rpow (fullRowRankDeficitFraction n) (n : ℝ)⁻¹ ≤ b := by
      apply (Real.rpow_inv_le_iff_of_pos (hnonneg n) hb0 hnpos).mpr
      rw [Real.rpow_natCast]
      exact hbound
    simpa only [one_div] using hroot.trans_lt hbc

example : 1 ≤ (1 : ℕ) ∧ 1 + 1 ≤ (2 : ℕ) := by decide

end BilinearComplexity
