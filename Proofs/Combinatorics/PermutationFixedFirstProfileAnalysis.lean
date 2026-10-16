import Combinatorics.PermutationFixedFirstProfileFinite
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false

namespace PermutationFixedFirstProfile

open scoped BigOperators
open Filter Topology

private theorem clamp_mem (x : ℝ) : max 0 (min 1 x) ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

private theorem clamp_eq (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    max 0 (min 1 x) = x := by rw [min_eq_right hx.2, max_eq_right hx.1]

/-- Integrating a continuous square profile along its second coordinate gives a continuous marginal on the closed unit interval. -/
theorem continuousOn_marginal (P : ℝ × ℝ → ℝ)
    (hP : ContinuousOn P (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)) :
    ContinuousOn (fun x => ∫ y in (0 : ℝ)..1, P (x, y)) (Set.Icc (0 : ℝ) 1) := by
  let Q : ℝ → ℝ → ℝ := fun x y => P (max 0 (min 1 x), max 0 (min 1 y))
  have hQ : Continuous Q.uncurry := by
    exact hP.comp_continuous (by fun_prop) (fun z => ⟨clamp_mem z.1, clamp_mem z.2⟩)
  have hJ : Continuous (fun x => ∫ y in (0 : ℝ)..1, Q x y) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hQ 0 1
  apply hJ.continuousOn.congr
  intro x hx
  apply intervalIntegral.integral_congr
  intro y hy
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hy
  simp only [Q, clamp_eq x hx, clamp_eq y hy]

example : ContinuousOn (fun x : ℝ => ∫ y in (0 : ℝ)..1, x * y) (Set.Icc (0 : ℝ) 1) :=
  continuousOn_marginal (fun z => z.1 * z.2) (by fun_prop)

/-- Cellwise uniform errors bound the error of the left grid average on the unit interval. -/
theorem grid_integral_error (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (n : ℕ) (hn : 0 < n) (g : Fin n → ℝ) (e : ℝ)
    (herr : ∀ b : Fin n, ∀ y ∈ Set.Icc ((b.val : ℝ) / n) (((b.val : ℝ) + 1) / n),
      |g b - f y| ≤ e) :
    |(∑ b : Fin n, g b) / n - ∫ y in (0 : ℝ)..1, f y| ≤ e := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let a : ℕ → ℝ := fun k => (k : ℝ) / n
  have hcell (k : ℕ) (hk : k < n) : Set.uIcc (a k) (a (k + 1)) ⊆ Set.Icc (0 : ℝ) 1 := by
    rw [Set.uIcc_of_le (by dsimp [a]; push_cast; exact div_le_div_of_nonneg_right (by linarith) hnR.le)]
    intro y hy
    constructor
    · exact (div_nonneg (Nat.cast_nonneg k) hnR.le).trans hy.1
    · apply hy.2.trans
      apply (div_le_one hnR).mpr
      exact_mod_cast (by omega : k + 1 ≤ n)
  have hi (k : ℕ) (hk : k < n) : IntervalIntegrable f MeasureTheory.volume (a k) (a (k + 1)) :=
    (hf.mono (hcell k hk)).intervalIntegrable
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (fun k hk => hi k hk)
  have hend : a 0 = 0 ∧ a n = 1 := by simp [a, ne_of_gt hnR]
  rw [hend.1, hend.2] at hsum
  have hpiece (k : ℕ) (hk : k < n) :
      |g ⟨k, hk⟩ / n - ∫ y in a k..a (k + 1), f y| ≤ e / n := by
    have hconst : g ⟨k, hk⟩ / n = ∫ _y in a k..a (k + 1), g ⟨k, hk⟩ := by
      rw [intervalIntegral.integral_const]
      dsimp [a]
      push_cast
      ring
    rw [hconst, ← intervalIntegral.integral_sub intervalIntegrable_const (hi k hk), ← Real.norm_eq_abs]
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a k) (b := a (k + 1)) (C := e) (f := fun y => g ⟨k, hk⟩ - f y) (by
        intro y hy
        rw [Set.uIoc_of_le (by dsimp [a]; push_cast; exact div_le_div_of_nonneg_right (by linarith) hnR.le)] at hy
        exact herr ⟨k, hk⟩ y ⟨hy.1.le, by simpa [a, Nat.cast_add, Nat.cast_one] using hy.2⟩)
    have hlen : |a (k + 1) - a k| = 1 / n := by
      dsimp [a]
      push_cast
      rw [show ((k : ℝ) + 1) / n - k / n = 1 / n by ring, abs_of_pos (by positivity)]
    simpa only [hlen, mul_one_div] using hbound
  have hsumF : (∑ b : Fin n, ∫ y in a b.val..a (b.val + 1), f y) =
      ∫ y in (0 : ℝ)..1, f y := by
    simpa only [← Fin.sum_univ_eq_sum_range] using hsum
  rw [Finset.sum_div, ← hsumF, ← Finset.sum_sub_distrib]
  calc
    |∑ b : Fin n, (g b / (n : ℝ) - ∫ y in a b.val..a (b.val + 1), f y)| ≤
        ∑ b : Fin n, |g b / (n : ℝ) - ∫ y in a b.val..a (b.val + 1), f y| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _b : Fin n, e / n := Finset.sum_le_sum (fun b _ => hpiece b.val b.isLt)
    _ = e := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp

/-- Removing one diagonal sample and renormalizing changes a bounded row average by at most two over the remaining row size. -/
theorem omitted_diagonal_error {n : ℕ} (hn : 2 ≤ n) (m : Fin n) (g : Fin n → ℝ)
    (hg : ∀ b, |g b| ≤ 1) :
    |(∑ b : {b : Fin n // b ≠ m}, g b.val) / ((n : ℝ) - 1) -
      (∑ b : Fin n, g b) / n| ≤ 2 / ((n : ℝ) - 1) := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hsplit : (∑ b : {b : Fin n // b ≠ m}, g b.val) + g m = ∑ b : Fin n, g b := by
    rw [← Finset.sum_subtype (Finset.univ.erase m) (by simp : ∀ b : Fin n,
      b ∈ Finset.univ.erase m ↔ b ≠ m) g]
    exact Finset.sum_erase_add _ _ (Finset.mem_univ m)
  have havg : |(∑ b : Fin n, g b) / n| ≤ 1 := by
    rw [abs_div, abs_of_pos hnR]
    apply (div_le_one hnR).mpr
    calc
      |∑ b : Fin n, g b| ≤ ∑ b : Fin n, |g b| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _b : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun b _ => hg b)
      _ = n := by simp
  have hid : (∑ b : {b : Fin n // b ≠ m}, g b.val) / ((n : ℝ) - 1) -
      (∑ b : Fin n, g b) / n =
      ((∑ b : Fin n, g b) / n - g m) / ((n : ℝ) - 1) := by
    rw [← hsplit]
    field_simp
    ring
  rw [hid, abs_div, abs_of_pos hn1]
  apply (div_le_div_iff_of_pos_right hn1).mpr
  exact (abs_sub _ _).trans (by linarith [hg m])

example : |(∑ b : {b : Fin 2 // b ≠ 0}, (1 : ℝ)) / ((2 : ℝ) - 1) -
    (∑ _b : Fin 2, (1 : ℝ)) / 2| ≤ 2 / ((2 : ℝ) - 1) :=
  omitted_diagonal_error (by decide) (0 : Fin 2) (fun _ => 1) (by intro _b; norm_num)

/-- Left grid averages of a continuous square profile converge along arbitrary moving rows, including boundary rows. -/
theorem grid_moving_tendsto (P : ℝ × ℝ → ℝ)
    (hP : ContinuousOn P (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1))
    (n : ℕ → ℕ) (u : ℕ → ℝ) (hn : Tendsto n atTop atTop)
    (hu : ∀ᶠ j in atTop, u j ∈ Set.Icc (0 : ℝ) 1)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) (hux : Tendsto u atTop (𝓝 x)) :
    Tendsto (fun j => (∑ b : Fin (n j), P (u j, (b.val : ℝ) / n j)) / n j)
      atTop (𝓝 (∫ y in (0 : ℝ)..1, P (x, y))) := by
  have huc := (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hP
  have hf : ContinuousOn (fun y => P (x, y)) (Set.Icc (0 : ℝ) 1) :=
    hP.comp (by fun_prop) (fun y hy => ⟨hx, hy⟩)
  have hi : Tendsto (fun j => 1 / (n j : ℝ)) atTop (𝓝 0) :=
    (tendsto_natCast_atTop_atTop.comp hn).const_div_atTop 1
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp huc (ε / 2) (by positivity)
  have hgrid := hi.eventually_lt tendsto_const_nhds hδ
  have hrow := Metric.tendsto_nhds.mp hux δ hδ
  filter_upwards [hu, hn.eventually_ge_atTop 1, hgrid, hrow] with j huj hnj hgj hrj
  have hnR : (0 : ℝ) < n j := by exact_mod_cast hnj
  have he := grid_integral_error (fun y => P (x, y)) hf (n j) (by omega)
    (fun b => P (u j, (b.val : ℝ) / n j)) (ε / 2) (by
      intro b y hy
      have hb0 : (0 : ℝ) ≤ (b.val : ℝ) / n j := by positivity
      have hb1 : ((b.val : ℝ) + 1) / n j ≤ 1 := by
        apply (div_le_one hnR).mpr
        exact_mod_cast (by omega : b.val + 1 ≤ n j)
      have hbmem : (b.val : ℝ) / n j ∈ Set.Icc (0 : ℝ) 1 := by
        refine ⟨hb0, ?_⟩
        have : (b.val : ℝ) / n j ≤ ((b.val : ℝ) + 1) / n j :=
          div_le_div_of_nonneg_right (by linarith) hnR.le
        exact this.trans hb1
      have hymem : y ∈ Set.Icc (0 : ℝ) 1 := ⟨hb0.trans hy.1, hy.2.trans hb1⟩
      have hdist : dist ((b.val : ℝ) / n j) y < δ := by
        rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hy.1)]
        have hstep : ((b.val : ℝ) + 1) / n j = (b.val : ℝ) / n j + 1 / n j := by ring
        rw [hstep] at hy
        linarith [hy.2]
      have hm := hmod (u j, (b.val : ℝ) / n j) ⟨huj, hbmem⟩ (x, y) ⟨hx, hymem⟩
        (by simpa only [Prod.dist_eq, max_lt_iff] using And.intro hrj hdist)
      exact le_of_lt (by simpa only [Real.dist_eq] using hm))
  rw [Real.dist_eq]
  linarith

example : |(∑ _b : Fin 2, (0 : ℝ)) / 2 - ∫ _y in (0 : ℝ)..1, (0 : ℝ)| ≤ 0 :=
  grid_integral_error (fun _ => 0) (by fun_prop) 2 (by decide) (fun _ => 0) 0
    (by intro b y hy; norm_num)

end PermutationFixedFirstProfile
