import Combinatorics.NoncommutingDenseMaximal

set_option autoImplicit false

namespace NoncommutingDense
noncomputable section
open scoped BigOperators

/-- The actual finite rectangle halo, with nonempty integer interval witnesses
contained in the ambient box and nonstrict density threshold. -/
def rectangleHalo (X Y : Finset ℤ) (E : Finset (ℤ × ℤ)) (α : ℝ) :
    Finset (ℤ × ℤ) := by
  classical
  exact (X ×ˢ Y).filter (fun p => ∃ l ∈ X, ∃ r ∈ X, ∃ s ∈ Y, ∃ t ∈ Y,
    l ≤ r ∧ s ≤ t ∧ Finset.Icc l r ⊆ X ∧ Finset.Icc s t ⊆ Y ∧
    p.1 ∈ Finset.Icc l r ∧ p.2 ∈ Finset.Icc s t ∧
    α * (Finset.Icc l r).card * (Finset.Icc s t).card ≤
      ((E ∩ (Finset.Icc l r ×ˢ Finset.Icc s t)).card : ℝ))

example : rectangleHalo {0} {0} {(0,0)} 1 = {(0,0)} := by
  ext p
  by_cases hp : p = (0,0)
  · subst p
    simp [rectangleHalo]
  · simp [rectangleHalo, hp]

example : rectangleHalo ∅ ∅ ∅ 1 = ∅ := by simp [rectangleHalo]

/-- Indicator mass in a finite box equals the cardinality of its intersection. -/
theorem rectangle_indicator_mass (E : Finset (ℤ × ℤ)) (I J : Finset ℤ) :
    (∑ u ∈ I, ∑ v ∈ J, if (u,v) ∈ E then (1 : ℝ) else 0) =
      ((E ∩ (I ×ˢ J)).card : ℝ) := by
  classical
  rw [← Finset.sum_product' I J (fun u v => if (u,v) ∈ E then (1 : ℝ) else 0)]
  simp only [Finset.sum_boole]
  congr 1
  congr 1
  ext p
  simp [and_comm]

/-- A rectangle of density at least `α` has enough vertically good columns
at every height of the rectangle. -/
theorem rectangle_good_columns (E : Finset (ℤ × ℤ)) (Y : Finset ℤ)
    (l r s t y : ℤ) (hs : s ∈ Y) (ht : t ∈ Y) (hst : s ≤ t)
    (hy : y ∈ Finset.Icc s t) (hyY : y ∈ Y) (α : ℝ) (_hα : 0 < α) (_hα1 : α ≤ 1)
    (hd : α * (Finset.Icc l r).card * (Finset.Icc s t).card ≤
      ((E ∩ (Finset.Icc l r ×ˢ Finset.Icc s t)).card : ℝ)) :
    α * (Finset.Icc l r).card ≤ (2 - α) *
      ∑ u ∈ Finset.Icc l r,
        if y ∈ intervalMaximalHalo Y (fun v => if (u,v) ∈ E then 1 else 0) (α/2)
        then (1 : ℝ) else 0 := by
  classical
  let I := Finset.Icc l r
  let J := Finset.Icc s t
  let g : ℤ → ℝ := fun u =>
    if y ∈ intervalMaximalHalo Y (fun v => if (u,v) ∈ E then 1 else 0) (α/2)
    then 1 else 0
  have hcol (u : ℤ) : (∑ v ∈ J, if (u,v) ∈ E then (1 : ℝ) else 0) ≤
      (α/2 + (1-α/2)*g u) * J.card := by
    by_cases hu : y ∈ intervalMaximalHalo Y (fun v => if (u,v) ∈ E then 1 else 0) (α/2)
    · have hm : (∑ v ∈ J, if (u,v) ∈ E then (1 : ℝ) else 0) ≤ J.card := by
        calc
          _ ≤ ∑ _v ∈ J, (1 : ℝ) := Finset.sum_le_sum (by intros; split_ifs <;> norm_num)
          _ = _ := by simp
      simpa [g, hu] using hm
    · have hn : ¬ (α/2 * J.card ≤ ∑ v ∈ J, if (u,v) ∈ E then (1 : ℝ) else 0) := by
        intro hm
        apply hu
        exact Finset.mem_filter.mpr ⟨hyY, s, hs, t, ht, hst, hy, hm⟩
      simpa [g, hu] using (lt_of_not_ge hn).le
  have hsum := Finset.sum_le_sum (fun u (_hu : u ∈ I) => hcol u)
  have hmass : α * (I.card : ℝ) * J.card ≤
      (α/2 * I.card + (1-α/2) * ∑ u ∈ I, g u) * J.card := by
    calc
      _ ≤ ∑ u ∈ I, ∑ v ∈ J, if (u,v) ∈ E then (1 : ℝ) else 0 := by
        rw [rectangle_indicator_mass]
        exact hd
      _ ≤ _ := by
        calc
          _ ≤ ∑ u ∈ I, (α/2 + (1-α/2)*g u) * J.card := hsum
          _ = _ := by rw [← Finset.sum_mul, Finset.sum_add_distrib, Finset.mul_sum]; simp [mul_comm]
  have hJ : (0 : ℝ) < J.card := by
    exact_mod_cast Finset.card_pos.mpr (show J.Nonempty from ⟨s, Finset.mem_Icc.mpr ⟨le_rfl, hst⟩⟩)
  have hc := (mul_le_mul_iff_left₀ hJ).mp hmass
  change α * (I.card : ℝ) ≤ (2-α) * ∑ u ∈ I, g u
  linarith

example : (0 : ℤ) ∈ ({0} : Finset ℤ) ∧ (0 : ℤ) ≤ 0 ∧
    (0 : ℤ) ∈ Finset.Icc (0 : ℤ) 0 ∧ (0 : ℝ) < 1 ∧ (1 : ℝ) ≤ 1 ∧
    (1 : ℝ) * (Finset.Icc (0 : ℤ) 0).card * (Finset.Icc (0 : ℤ) 0).card ≤
      (({(0,0)} ∩ (Finset.Icc (0 : ℤ) 0 ×ˢ Finset.Icc (0 : ℤ) 0) :
        Finset (ℤ × ℤ)).card : ℝ) := by norm_num

/-- The two-dimensional finite integer rectangle halo obeys the sharp-for-this-
argument constant `18 * (2 - α)` after multiplication by `α²`. -/
theorem rectangleHalo_weak_bound (a b c d : ℤ) (hab : a ≤ b) (hcd : c ≤ d)
    (E : Finset (ℤ × ℤ)) (hE : E ⊆ Finset.Icc a b ×ˢ Finset.Icc c d)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    α^2 * (rectangleHalo (Finset.Icc a b) (Finset.Icc c d) E α).card ≤
      18 * (2-α) * E.card := by
  classical
  let X := Finset.Icc a b
  let Y := Finset.Icc c d
  let H := rectangleHalo X Y E α
  let f : ℤ → ℤ → ℝ := fun u v => if (u,v) ∈ E then 1 else 0
  let V := fun u => intervalMaximalHalo Y (f u) (α/2)
  let g : ℤ → ℤ → ℝ := fun v u => if v ∈ V u then 1 else 0
  let W := fun v => intervalMaximalHalo X (g v) (α/(2-α))
  have htwo : 0 < 2-α := by linarith
  have hsub (p : ℤ × ℤ) (hp : p ∈ H) : p.1 ∈ W p.2 := by
    obtain ⟨hpXY, l, hl, r, hr, s, hs, t, ht, hlr, hst, hIX, hJY, hpl, hps, hd⟩ :=
      Finset.mem_filter.mp hp
    have hpY := (Finset.mem_product.mp hpXY).2
    have hg := rectangle_good_columns E Y l r s t p.2 hs ht hst hps hpY α hα hα1 hd
    apply Finset.mem_filter.mpr
    refine ⟨(Finset.mem_product.mp hpXY).1, l, hl, r, hr, hlr, hpl, ?_⟩
    change α / (2-α) * (Finset.Icc l r).card ≤ ∑ u ∈ Finset.Icc l r, g p.2 u
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ htwo).mpr (by simpa [g, V, f, mul_comm] using hg)
  have hrow (v : ℤ) :
      α * (∑ u ∈ X, if (u,v) ∈ H then (1 : ℝ) else 0) ≤
        3 * (2-α) * ∑ u ∈ X, g v u := by
    have hc : (∑ u ∈ X, if (u,v) ∈ H then (1 : ℝ) else 0) ≤ (W v).card := by
      calc
        _ ≤ ∑ u ∈ X, if u ∈ W v then (1 : ℝ) else 0 := by
          apply Finset.sum_le_sum
          intro u hu
          split_ifs with hh hw hw
          · norm_num
          · exact False.elim (hw (hsub (u,v) hh))
          · norm_num
          · norm_num
        _ = (W v).card := by
          have hW : W v ⊆ X := Finset.filter_subset _ _
          simp only [Finset.sum_boole]
          rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hW]
    have hw := intervalMaximalHalo_weak_bound a b hab (g v)
      (by intro u hu; simp only [g]; split_ifs <;> norm_num) (α/(2-α)) (div_pos hα htwo)
    have hc' := mul_le_mul_of_nonneg_left hc hα.le
    have hw' := (div_le_iff₀ htwo).mp (show
        α * ((W v).card : ℝ) / (2-α) ≤ 3 * ∑ u ∈ X, g v u by
      simpa [W, X, div_mul_eq_mul_div] using hw)
    nlinarith
  have hvert (u : ℤ) : α * (V u).card ≤ 6 * ∑ v ∈ Y, f u v := by
    have hv := intervalMaximalHalo_weak_bound c d hcd (f u)
      (by intro v hv; simp only [f]; split_ifs <;> norm_num) (α/2) (by linarith)
    change α * (V u).card ≤ 6 * ∑ v ∈ Y, f u v
    change α/2 * (V u).card ≤ 3 * ∑ v ∈ Y, f u v at hv
    linarith
  have hH : α * (H.card : ℝ) ≤
      3 * (2-α) * ∑ u ∈ X, ((V u).card : ℝ) := by
    have hh := Finset.sum_le_sum (fun v (_hv : v ∈ Y) => hrow v)
    rw [← Finset.mul_sum, ← Finset.mul_sum] at hh
    have hcount : (∑ v ∈ Y, ∑ u ∈ X, if (u,v) ∈ H then (1 : ℝ) else 0) = H.card := by
      rw [Finset.sum_comm, rectangle_indicator_mass]
      have hHX : H ⊆ X ×ˢ Y := Finset.filter_subset _ _
      rw [Finset.inter_eq_left.mpr hHX]
    rw [hcount] at hh
    have hvcount : (∑ v ∈ Y, ∑ u ∈ X, g v u) = ∑ u ∈ X, ((V u).card : ℝ) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u hu
      have hV : V u ⊆ Y := Finset.filter_subset _ _
      simp only [g, Finset.sum_boole]
      rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hV]
    rwa [hvcount] at hh
  have hV : α * (∑ u ∈ X, ((V u).card : ℝ)) ≤ 6 * E.card := by
    have hv := Finset.sum_le_sum (fun u (_hu : u ∈ X) => hvert u)
    rw [← Finset.mul_sum, ← Finset.mul_sum] at hv
    have hm : (∑ u ∈ X, ∑ v ∈ Y, f u v) = (E.card : ℝ) := by
      change (∑ u ∈ X, ∑ v ∈ Y, if (u,v) ∈ E then (1 : ℝ) else 0) = _
      rw [rectangle_indicator_mass, Finset.inter_eq_left.mpr hE]
    rwa [hm] at hv
  have hh := mul_le_mul_of_nonneg_left hH hα.le
  have hv := mul_le_mul_of_nonneg_left hV (show 0 ≤ 3*(2-α) by positivity)
  change α^2 * (H.card : ℝ) ≤ 18*(2-α)*E.card
  nlinarith

/-- Dividing the rectangle estimate by the positive squared density. -/
theorem rectangleHalo_card_le (a b c d : ℤ) (hab : a ≤ b) (hcd : c ≤ d)
    (E : Finset (ℤ × ℤ)) (hE : E ⊆ Finset.Icc a b ×ˢ Finset.Icc c d)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ((rectangleHalo (Finset.Icc a b) (Finset.Icc c d) E α).card : ℝ) ≤
      18 * (2-α) / α^2 * E.card := by
  have hb := rectangleHalo_weak_bound a b c d hab hcd E hE α hα hα1
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (sq_pos_of_pos hα)).mpr
  simpa [mul_comm] using hb

/-- At density one third the actual rectangle halo has cardinality at most
270 times the number of input points. -/
theorem rectangleHalo_third_bound (a b c d : ℤ) (hab : a ≤ b) (hcd : c ≤ d)
    (E : Finset (ℤ × ℤ)) (hE : E ⊆ Finset.Icc a b ×ˢ Finset.Icc c d) :
    (rectangleHalo (Finset.Icc a b) (Finset.Icc c d) E (1/3)).card ≤ 270 * E.card := by
  have hb := rectangleHalo_card_le a b c d hab hcd E hE (1/3) (by norm_num) (by norm_num)
  norm_num at hb
  exact_mod_cast hb

example : (0 : ℤ) ≤ 0 ∧ (0 : ℤ) ≤ 0 ∧
    ({(0,0)} : Finset (ℤ × ℤ)) ⊆ Finset.Icc 0 0 ×ˢ Finset.Icc 0 0 ∧
    (0 : ℝ) < 1 ∧ (1 : ℝ) ≤ 1 := by norm_num

example : (0 : ℤ) ≤ 0 ∧ (0 : ℤ) ≤ 0 ∧
    (∅ : Finset (ℤ × ℤ)) ⊆ Finset.Icc 0 0 ×ˢ Finset.Icc 0 0 ∧
    (0 : ℝ) < 1/3 ∧ (1/3 : ℝ) ≤ 1 := by norm_num

end
end NoncommutingDense
