import Combinatorics.PermutationJointEndpointProfileAnalysis

set_option autoImplicit false

namespace PermutationJointEndpointProfile

open scoped BigOperators
open Filter Topology

/-- A uniform pointwise absolute bound controls a finite average with positive sample size. -/
theorem average_abs_le {α : Type*} [Fintype α] (d : ℝ) (hd : 0 < d)
    (hcard : (Fintype.card α : ℝ) = d) (g : α → ℝ) (e : ℝ)
    (hg : ∀ a, |g a| ≤ e) : |(∑ a, g a) / d| ≤ e := by
  rw [abs_div, abs_of_pos hd]
  apply (div_le_iff₀ hd).mpr
  calc
    |∑ a, g a| ≤ ∑ a, |g a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : α, e := Finset.sum_le_sum (fun a _ => hg a)
    _ = e * d := by simp [hcard, mul_comm]

/-- The number of allowed second labels is exactly one less than the ambient size. -/
theorem distinct_card {n : ℕ} (hn : 1 ≤ n) (a : Fin n) :
    (Fintype.card {b : Fin n // b ≠ a} : ℝ) = (n : ℝ) - 1 := by
  have hc : Fintype.card {b : Fin n // b ≠ a} = n - 1 := by
    simpa only [Fintype.card_fin, Fintype.card_subtype_eq] using
      (Fintype.card_subtype_compl (fun b : Fin n => b = a))
  rw [hc, Nat.cast_sub hn, Nat.cast_one]

/-- Uniform errors on ordered distinct labels control their normalized square average. -/
theorem distinct_average_abs_le {n : ℕ} (hn : 2 ≤ n)
    (g : (a : Fin n) → {b : Fin n // b ≠ a} → ℝ) (e : ℝ)
    (hg : ∀ a b, |g a b| ≤ e) :
    |(∑ a : Fin n, (∑ b : {b : Fin n // b ≠ a}, g a b) / ((n : ℝ) - 1)) / n| ≤ e := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  apply average_abs_le (n : ℝ) hnR (by simp)
  intro a
  exact average_abs_le _ hn1 (distinct_card (by omega) a) _ e (hg a)

/-- Omitting a diagonal sample changes a bounded row average by at most twice its bound divided by the remaining size. -/
theorem omitted_diagonal_error {n : ℕ} (hn : 2 ≤ n) (a : Fin n) (g : Fin n → ℝ)
    (M : ℝ) (hg : ∀ b, |g b| ≤ M) :
    |(∑ b : {b : Fin n // b ≠ a}, g b.val) / ((n : ℝ) - 1) -
      (∑ b : Fin n, g b) / n| ≤ 2 * M / ((n : ℝ) - 1) := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hsplit : (∑ b : {b : Fin n // b ≠ a}, g b.val) + g a = ∑ b : Fin n, g b := by
    rw [← Finset.sum_subtype (Finset.univ.erase a) (by simp : ∀ b : Fin n,
      b ∈ Finset.univ.erase a ↔ b ≠ a) g]
    exact Finset.sum_erase_add _ _ (Finset.mem_univ a)
  have havg := average_abs_le (n : ℝ) hnR (by simp) g M hg
  have hid : (∑ b : {b : Fin n // b ≠ a}, g b.val) / ((n : ℝ) - 1) -
      (∑ b : Fin n, g b) / n =
      ((∑ b : Fin n, g b) / n - g a) / ((n : ℝ) - 1) := by
    rw [← hsplit]
    field_simp
    ring
  rw [hid, abs_div, abs_of_pos hn1]
  apply (div_le_div_iff_of_pos_right hn1).mpr
  exact (abs_sub _ _).trans (by linarith [hg a])

/-- Removing the diagonal and using ordered-distinct normalization has vanishing error for bounded square samples. -/
theorem square_omitted_diagonal_error {n : ℕ} (hn : 2 ≤ n) (g : Fin n → Fin n → ℝ)
    (M : ℝ) (hg : ∀ a b, |g a b| ≤ M) :
    |(∑ a : Fin n, (∑ b : {b : Fin n // b ≠ a}, g a b.val) / ((n : ℝ) - 1)) / n -
      (∑ a : Fin n, (∑ b : Fin n, g a b) / n) / n| ≤ 2 * M / ((n : ℝ) - 1) := by
  rw [← sub_div, ← Finset.sum_sub_distrib]
  apply average_abs_le (n : ℝ) (by exact_mod_cast (by omega : 0 < n)) (by simp)
  intro a
  exact omitted_diagonal_error hn a (g a) M (hg a)

example : |(∑ a : Fin 2, (∑ _b : {b : Fin 2 // b ≠ a}, (3 : ℝ)) / (2 - 1)) / 2| ≤ 3 :=
  distinct_average_abs_le (by decide) (fun _ _ => 3) 3 (by intros; norm_num)

/-- Ordered-distinct left-grid averages have the same integral limit as full square grids. -/
theorem distinct_grid_tendsto (f : ℝ × ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)) :
    Tendsto (fun n : ℕ => (∑ a : Fin n, (∑ b : {b : Fin n // b ≠ a},
      f ((a.val : ℝ) / n, (b.val.val : ℝ) / n)) / ((n : ℝ) - 1)) / n) atTop
      (𝓝 (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, f (x, y))) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hf
  have hden : Tendsto (fun n : ℕ => (n : ℝ) - 1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro c
    filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (c + 1)] with n hn
    change c + 1 ≤ (n : ℝ) at hn
    linarith
  have he : Tendsto (fun n : ℕ => 2 * M / ((n : ℝ) - 1)) atTop (𝓝 0) :=
    hden.const_div_atTop (2 * M)
  have hd : Tendsto (fun n : ℕ =>
      (∑ a : Fin n, (∑ b : {b : Fin n // b ≠ a},
        f ((a.val : ℝ) / n, (b.val.val : ℝ) / n)) / ((n : ℝ) - 1)) / n -
      (∑ a : Fin n, (∑ b : Fin n, f ((a.val : ℝ) / n, (b.val : ℝ) / n)) / n) / n)
      atTop (𝓝 0) := by
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall (fun _ => dist_nonneg)) _ he
    filter_upwards [eventually_ge_atTop 2] with n hn
    simpa only [Real.dist_eq, sub_zero] using
      square_omitted_diagonal_error hn
        (fun a b => f ((a.val : ℝ) / n, (b.val : ℝ) / n)) M (fun a b => by
          simpa only [Real.norm_eq_abs] using
            hM _ ⟨grid_mem (by omega) a, grid_mem (by omega) b⟩)
  simpa only [zero_add, sub_add_cancel] using hd.add (grid_tendsto f hf)

/-- Rewriting filtered distinct-label sums as subtype sums matches successive normalized averaging. -/
theorem filtered_average_eq {n : ℕ} (g : Fin n → Fin n → ℝ) :
    (∑ a : Fin n, ∑ b : Fin n with a ≠ b, g a b) / ((n : ℝ) * ((n : ℝ) - 1)) =
    (∑ a : Fin n, (∑ b : {b : Fin n // b ≠ a}, g a b.val) / ((n : ℝ) - 1)) / n := by
  classical
  have hs (a : Fin n) : (∑ b : Fin n with a ≠ b, g a b) =
      ∑ b : {b : Fin n // b ≠ a}, g a b.val := by
    exact Finset.sum_subtype (Finset.univ.filter (fun b => a ≠ b))
      (by intro b; simp [ne_comm]) (g a)
  simp_rw [hs]
  rw [← Finset.sum_div, div_div]
  congr 1
  ring

end PermutationJointEndpointProfile
