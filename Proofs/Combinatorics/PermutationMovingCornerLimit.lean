import Combinatorics.PermutationOppositeCornerLimit

set_option autoImplicit false

open Filter Topology

namespace PermutationMovingCornerLimit

open PermutationCornerStandardization PermutationOppositeCornerLimit

attribute [local instance] Classical.propDecidable

/-- Subtracting a fixed real offset from size does not change its asymptotic ratio. -/
theorem tendsto_ratio_sub (c : ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) - c)) atTop (𝓝 1) := by
  have hs : Tendsto (fun n : ℕ => c / ((n : ℝ) - c)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (by
      apply tendsto_atTop.mpr
      intro z
      filter_upwards [(tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually (eventually_ge_atTop (z + c))]
        with n hn
      linarith)
  have ht : Tendsto (fun n : ℕ => (1 : ℝ) + c / ((n : ℝ) - c)) atTop (𝓝 1) := by
    simpa only [add_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add hs
  apply ht.congr'
  filter_upwards [(tendsto_natCast_atTop_atTop :
    Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually (eventually_gt_atTop c)] with n hn
  have hne : (n : ℝ) - c ≠ 0 := by linarith
  field_simp [hne]
  <;> ring

/-- Sublinear moving label mass makes the finite standardization error vanish. -/
theorem tendsto_moving_error (a b : ℕ → ℕ)
    (hm : Tendsto (fun n : ℕ => ((a n + b n : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 0)) (K : ℕ) :
    Tendsto (fun n : ℕ => ((2 * K : ℝ) - 3) * ((a n : ℝ) + b n - 1) /
      ((n : ℝ) - 3)) atTop (𝓝 0) := by
  have hi : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have ht := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 * K : ℝ) - 3)
    atTop (𝓝 ((2 * K : ℝ) - 3))).mul (hm.sub hi)).mul (tendsto_ratio_sub 3)
  simp only [sub_self, mul_zero, zero_mul] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 4] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hn3 : (n : ℝ) - 3 ≠ 0 := by
    have hnr : (4 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  simp only [Nat.cast_add]
  field_simp [hn0, hn3]
  <;> ring

/-- A single finite cutoff and tail bound controls every low label uniformly. -/
theorem lowFraction_uniform_bound {n a r b K D : ℕ}
    (hK : 3 ≤ K) (hD : 2 ≤ D) (hnK : 4 * K ≤ n) (hnD : 2 * D < n)
    (hm : 2 * (a + b) ≤ n) (hr : r < a) :
    |lowFraction n a r b - canonicalFraction K hK| ≤
      ((2 * K : ℝ) - 3) * ((a : ℝ) + b - 1) / ((n : ℝ) - 3) +
      (2 / (K.factorial : ℝ) + (2 * (D - 1) : ℝ) / (((n - 3) / D).factorial : ℝ) +
        2 / ((D + 1).factorial : ℝ)) := by
  have hn : 3 ≤ n := by omega
  have ha : a < n - 1 - b := by omega
  rw [lowFraction_eq hn hr ha]
  have hf := finiteConsumer_proof K n a b r hK (by omega) hr ha (by omega) 2 (by simp)
  have ht := actualTripleFraction_truncation hK (by omega) hD hnD
    (⟨a, by omega⟩ : Fin n) ⟨r, by omega⟩ ⟨n - 1 - b, by omega⟩ hr ha
  have hp := actualTripleFraction_le hn (⟨a, by omega⟩ : Fin n) ⟨r, by omega⟩
    ⟨n - 1 - b, by omega⟩ K
  have hDR : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hDm : (0 : ℝ) ≤ (D : ℝ) - 1 := by linarith
  have htn : 0 ≤ 2 / (K.factorial : ℝ) +
      (2 * (D - 1) : ℝ) / (((n - 3) / D).factorial : ℝ) + 2 / ((D + 1).factorial : ℝ) := by
    positivity
  have hfb := abs_le.mp hf
  apply abs_le.mpr
  constructor <;> linarith

example : 3 ≤ 3 ∧ 2 ≤ 2 ∧ 4 * 3 ≤ 24 ∧ 2 * 2 < 24 ∧
    2 * (2 + 1) ≤ 24 ∧ 0 < 2 := by decide

/-- Sublinear natural endpoint mass is eventually at most half of size. -/
theorem eventually_mass_small (a b : ℕ → ℕ)
    (hm : Tendsto (fun n : ℕ => ((a n + b n : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, 2 * (a n + b n) ≤ n := by
  filter_upwards [Metric.tendsto_nhds.mp hm (1 / 2) (by norm_num),
    eventually_ge_atTop 1] with n hn hn1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hr : ((a n + b n : ℕ) : ℝ) / (n : ℝ) < 1 / 2 :=
    lt_of_le_of_lt (le_abs_self _) (by simpa only [Real.dist_eq, sub_zero] using hn)
  have ht := (div_lt_iff₀ hnR).mp hr
  have htwo : (2 : ℝ) * (a n + b n : ℕ) ≤ n := by linarith
  exact_mod_cast htwo

/-- All low-branch fractions converge uniformly over the moving finite label ranges; cutoffs precede size. -/
theorem eventually_lowFraction_close {C : ℝ}
    (hC : Tendsto (fun K : ℕ => canonicalFraction (K + 3) (by omega)) atTop (𝓝 C))
    (a b : ℕ → ℕ)
    (hm : Tendsto (fun n : ℕ => ((a n + b n : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ r : ℕ, r < a n → |lowFraction n (a n) r (b n) - C| ≤ ε := by
  have hfac (c : ℝ) : Tendsto (fun j : ℕ => c / (j.factorial : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp factorial_tendsto_atTop)
  have he : 0 < ε / 6 := by linarith
  obtain ⟨J, hJc, hJf⟩ := ((Metric.tendsto_nhds.mp hC (ε / 6) he).and
    (Metric.tendsto_nhds.mp ((hfac 2).comp (tendsto_add_atTop_nat 3)) (ε / 6) he)).exists
  let K := J + 3
  have hK : 3 ≤ K := by omega
  have hcan : |canonicalFraction K hK - C| < ε / 6 := hJc
  have htailK : 2 / (K.factorial : ℝ) < ε / 6 :=
    lt_of_le_of_lt (le_abs_self _)
      (by simpa only [Real.dist_eq, sub_zero, Function.comp_def] using hJf)
  obtain ⟨D, hD, hDf⟩ := ((eventually_ge_atTop 2).and
    (Metric.tendsto_nhds.mp ((hfac 2).comp (tendsto_add_atTop_nat 1)) (ε / 6) he)).exists
  have htailD : 2 / ((D + 1).factorial : ℝ) < ε / 6 :=
    lt_of_le_of_lt (le_abs_self _)
      (by simpa only [Real.dist_eq, sub_zero, Function.comp_def] using hDf)
  have hsub : Tendsto (fun n : ℕ => n - 3) atTop atTop := by
    apply tendsto_atTop.mpr
    intro N
    filter_upwards [eventually_ge_atTop (N + 3)] with n hn
    omega
  have hmiddle := (hfac (2 * (D - 1))).comp
    ((Nat.tendsto_div_const_atTop (by omega : D ≠ 0)).comp hsub)
  filter_upwards [eventually_mass_small a b hm,
    eventually_ge_atTop (4 * K + 2 * D + 10),
    Metric.tendsto_nhds.mp hmiddle (ε / 6) he,
    Metric.tendsto_nhds.mp (tendsto_moving_error a b hm K) (ε / 6) he]
    with n hmass hn hmid herr
  intro r hr
  have hb := lowFraction_uniform_bound hK hD (by omega) (by omega) hmass hr
  have hmid' : (2 * (D - 1) : ℝ) / (((n - 3) / D).factorial : ℝ) < ε / 6 :=
    lt_of_le_of_lt (le_abs_self _)
      (by simpa only [Real.dist_eq, sub_zero, Function.comp_def] using hmid)
  have herr' : ((2 * K : ℝ) - 3) * ((a n : ℝ) + b n - 1) / ((n : ℝ) - 3) < ε / 6 :=
    lt_of_le_of_lt (le_abs_self _) (by simpa only [Real.dist_eq, sub_zero] using herr)
  have htri : |lowFraction n (a n) r (b n) - C| ≤
      |lowFraction n (a n) r (b n) - canonicalFraction K hK| +
        |canonicalFraction K hK - C| := by
    simpa only [sub_add_sub_cancel] using
      abs_add_le (lowFraction n (a n) r (b n) - canonicalFraction K hK)
        (canonicalFraction K hK - C)
  linarith

/-- Uniform error over a finite branch bounds the error of its genuine sum, including an empty branch. -/
theorem branch_sum_bound (n a b : ℕ) (C U : ℝ)
    (hu : ∀ r : Fin a, |lowFraction n a r.val b - C| ≤ U) :
    |(∑ r : Fin a, lowFraction n a r.val b) - (a : ℝ) * C| ≤ (a : ℝ) * U := by
  calc
    _ = |∑ r : Fin a, (lowFraction n a r.val b - C)| := by
      simp [Finset.sum_sub_distrib]
    _ ≤ ∑ r : Fin a, |lowFraction n a r.val b - C| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r : Fin a, U := Finset.sum_le_sum (fun r _ => hu r)
    _ = (a : ℝ) * U := by simp

/-- Positive total branch mass converts uniform branch errors into an average error. -/
theorem branch_average_bound (n a b : ℕ) (C U : ℝ) (hm : 0 < a + b)
    (ha : ∀ r : Fin a, |lowFraction n a r.val b - C| ≤ U)
    (hb : ∀ r : Fin b, |lowFraction n b r.val a - C| ≤ U) :
    |((∑ r : Fin a, lowFraction n a r.val b) +
      (∑ s : Fin b, lowFraction n b s.val a)) / ((a + b : ℕ) : ℝ) - C| ≤ U := by
  have hmR : (0 : ℝ) < ((a + b : ℕ) : ℝ) := by exact_mod_cast hm
  have hsa := branch_sum_bound n a b C U ha
  have hsb := branch_sum_bound n b a C U hb
  have htri := abs_add_le
    ((∑ r : Fin a, lowFraction n a r.val b) - (a : ℝ) * C)
    ((∑ s : Fin b, lowFraction n b s.val a) - (b : ℝ) * C)
  have hsum : |((∑ r : Fin a, lowFraction n a r.val b) +
      (∑ s : Fin b, lowFraction n b s.val a)) - ((a + b : ℕ) : ℝ) * C| ≤
      ((a + b : ℕ) : ℝ) * U := by
    simp only [Nat.cast_add]
    have heq : ((∑ r : Fin a, lowFraction n a r.val b) +
        (∑ s : Fin b, lowFraction n b s.val a)) - ((a : ℝ) + b) * C =
        ((∑ r : Fin a, lowFraction n a r.val b) - (a : ℝ) * C) +
        ((∑ s : Fin b, lowFraction n b s.val a) - (b : ℝ) * C) := by ring
    rw [heq]
    linarith
  rw [div_sub' (ne_of_gt hmR), abs_div, abs_of_pos hmR]
  exact (div_le_iff₀ hmR).mpr (by simpa only [mul_comm] using hsum)

/-- The actual two-branch average converges for all positive sublinear moving endpoint masses. -/
theorem tendsto_branch_average {C : ℝ}
    (hC : Tendsto (fun K : ℕ => canonicalFraction (K + 3) (by omega)) atTop (𝓝 C))
    (a b : ℕ → ℕ) (hmpos : ∀ᶠ n in atTop, 0 < a n + b n)
    (hm : Tendsto (fun n : ℕ => ((a n + b n : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ((∑ r : Fin (a n), lowFraction n (a n) r.val (b n)) +
      (∑ s : Fin (b n), lowFraction n (b n) s.val (a n))) /
        ((a n + b n : ℕ) : ℝ)) atTop (𝓝 C) := by
  have hms : Tendsto (fun n : ℕ => ((b n + a n : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [Nat.add_comm] using hm
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hmpos, eventually_lowFraction_close hC a b hm (ε / 2) (by linarith),
    eventually_lowFraction_close hC b a hms (ε / 2) (by linarith)] with n hn ha hb
  have hav := branch_average_bound n (a n) (b n) C (ε / 2) hn
    (fun r => ha r.val r.isLt) (fun s => hb s.val s.isLt)
  rw [Real.dist_eq]
  linarith

/-- The actual endpoint avoidance fraction has the universal moving-corner limit whenever total positive offset mass is sublinear. -/
theorem tendsto_moving_corner {C : ℝ}
    (hC : Tendsto (fun K : ℕ => canonicalFraction (K + 3) (by omega)) atTop (𝓝 C))
    (a b : ℕ → ℕ) (hmpos : ∀ᶠ n in atTop, 0 < a n + b n)
    (hm : Tendsto (fun n : ℕ => ((a n + b n : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (n : ℝ) / ((a n + b n : ℕ) : ℝ) *
      PermutationSameEdgeLimit.F n (a n) (n - 1 - b n)) atTop (𝓝 C) := by
  have ht := tendsto_normalization.mul (tendsto_branch_average hC a b hmpos hm)
  simp only [one_mul] at ht
  apply ht.congr'
  filter_upwards [eventually_mass_small a b hm, eventually_ge_atTop 4] with n hm' hn
  rw [F_eq_low_sums (by omega) (by omega)]
  ring

/-- A single positive canonical limit governs every positive sublinear moving-corner sequence. -/
theorem exists_moving_corner_limit : ∃ C : ℝ, (1 / 8 : ℝ) ≤ C ∧
    Tendsto (fun K : ℕ => canonicalFraction (K + 3) (by omega)) atTop (𝓝 C) ∧
    ∀ a b : ℕ → ℕ, (∀ᶠ n in atTop, 0 < a n + b n) →
      Tendsto (fun n : ℕ => ((a n + b n : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 0) →
      Tendsto (fun n : ℕ => (n : ℝ) / ((a n + b n : ℕ) : ℝ) *
        PermutationSameEdgeLimit.F n (a n) (n - 1 - b n)) atTop (𝓝 C) := by
  obtain ⟨C, hpos, hC, _⟩ := exists_opposite_corner_limit
  exact ⟨C, hpos, hC, fun a b hmpos hm => tendsto_moving_corner hC a b hmpos hm⟩

example : ∀ᶠ n : ℕ in atTop, 0 < (fun _ : ℕ => 1) n + (fun _ : ℕ => 0) n :=
  Filter.Eventually.of_forall (fun _ => by norm_num)
example : Tendsto (fun n : ℕ => (((fun _ : ℕ => 1) n + (fun _ : ℕ => 0) n : ℕ) : ℝ) /
    (n : ℝ)) atTop (𝓝 0) := by
  simpa using (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
    Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0))

end PermutationMovingCornerLimit
