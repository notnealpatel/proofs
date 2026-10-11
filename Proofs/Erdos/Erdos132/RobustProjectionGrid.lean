import Mathlib

set_option autoImplicit false

namespace Erdos132.RobustProjectionGrid

/-- An index is matched when its chord projection lies in the affine image of the
value grid, with an actual grid index in `range m`. -/
def Matched (m : ℕ) (t : ℤ) (r : ℝ) (ell : ℕ) : Prop :=
  ∃ j ∈ Finset.range m, Real.cos (2 * Real.pi * (ell : ℝ) / (m : ℝ)) =
    (1 - r ^ 2) / 2 + r * Real.cos ((2 * (j : ℝ) - (t : ℝ)) * Real.pi / (m : ℝ))

/-- The strict nonmaximal chord indices not matched by the affine projection grid.
The upper endpoint uses natural division and subtraction, for both parities. -/
noncomputable def unmatched (m : ℕ) (t : ℤ) (r : ℝ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 (m / 2 - 1)).filter (fun ell => ¬ Matched m t r ell)

example (m : ℕ) (t : ℤ) (r : ℝ) (ell : ℕ) :
    Matched m t r ell ↔ ∃ j ∈ Finset.range m,
      Real.cos (2 * Real.pi * (ell : ℝ) / (m : ℝ)) = (1 - r ^ 2) / 2 +
        r * Real.cos ((2 * (j : ℝ) - (t : ℝ)) * Real.pi / (m : ℝ)) := Iff.rfl

example : unmatched 2 0 (1 / 2) = ∅ := by
  simp [unmatched]

private theorem one_sub_cos_le (b : ℝ) : 1 - Real.cos b ≤ b ^ 2 / 2 := by
  have hsq := Real.sin_sq_le_sq (x := b / 2)
  have hid := Real.cos_two_mul (b / 2)
  have hunit := Real.sin_sq_add_cos_sq (b / 2)
  rw [show 2 * (b / 2) = b by ring] at hid
  nlinarith

private theorem tail_radius (k m ell : ℕ) (t : ℤ) (r : ℝ)
    (hk : 2 ≤ k) (hm : 1000 * (k + 1) ^ 2 ≤ m)
    (hr0 : 0 < r) (hr1 : r < 1)
    (hlo : m / 2 - 1 - (k - 2) / 2 ≤ ell) (hhi : ell ≤ m / 2 - 1)
    (hmatch : Matched m t r ell) :
    1 - r < 1 / (300 * (m : ℝ)) := by
  have hsmall : 12 * ((k - 2) / 2 + 2) ≤ m := by
    have hs : (k - 2) / 2 + 2 ≤ k + 1 := by omega
    have hK : k + 1 ≤ (k + 1) ^ 2 := by nlinarith
    omega
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hnlo : m ≤ 2 * ell + k + 1 := by omega
  have hnhi : 2 * ell < m := by omega
  have hrlo : (m : ℝ) ≤ 2 * (ell : ℝ) + (k + 1 : ℕ) := by exact_mod_cast hnlo
  have hrhi : 2 * (ell : ℝ) < m := by exact_mod_cast hnhi
  let b : ℝ := Real.pi - 2 * Real.pi * (ell : ℝ) / (m : ℝ)
  have hb0 : 0 < b := by dsimp [b]; apply (sub_pos.mpr); apply (div_lt_iff₀ hmpos).mpr; nlinarith [Real.pi_pos]
  have hbK : b ≤ (k + 1 : ℕ) * Real.pi / (m : ℝ) := by
    dsimp [b]
    apply (le_div_iff₀ hmpos).mpr
    field_simp
    nlinarith [Real.pi_pos]
  obtain ⟨j, hj, heq⟩ := hmatch
  have hc := Real.neg_one_le_cos ((2 * (j : ℝ) - (t : ℝ)) * Real.pi / (m : ℝ))
  have hcos : Real.cos b = -Real.cos (2 * Real.pi * (ell : ℝ) / (m : ℝ)) :=
    Real.cos_pi_sub _
  have hend : (1 - r) * (2 - (1 - r) / 2) ≤ 1 - Real.cos b := by
    nlinarith [mul_nonneg (le_of_lt hr0) (by linarith : 0 ≤ Real.cos ((2 * (j : ℝ) - (t : ℝ)) * Real.pi / (m : ℝ)) + 1)]
  have hdelta : 3 * (1 - r) < b ^ 2 := by
    have hbound := one_sub_cos_le b
    nlinarith [sq_pos_of_pos (sub_pos.mpr hr1)]
  have hbSq : b ^ 2 ≤ ((k + 1 : ℕ) * Real.pi / (m : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (le_of_lt hb0) hbK 2
  have hpi : Real.pi ^ 2 < 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hmR : 1000 * ((k + 1 : ℕ) : ℝ) ^ 2 ≤ m := by exact_mod_cast hm
  have hnum : 300 * (1 - r) * (m : ℝ) ^ 2 < (m : ℝ) := by
    have hscaled : 3 * (1 - r) * (m : ℝ) ^ 2 < ((k + 1 : ℕ) : ℝ) ^ 2 * Real.pi ^ 2 := by
      have hsqden : 0 < (m : ℝ) ^ 2 := sq_pos_of_pos hmpos
      have hx := mul_lt_mul_of_pos_right (lt_of_lt_of_le hdelta hbSq) hsqden
      field_simp at hx
      nlinarith [hx]
    have hKpos : 0 < ((k + 1 : ℕ) : ℝ) ^ 2 := by positivity
    nlinarith [mul_lt_mul_of_pos_left hpi hKpos]
  apply (lt_div_iff₀ (by positivity : 0 < 300 * (m : ℝ))).mpr
  nlinarith [mul_pos hmpos (by positivity : 0 < (m : ℝ)), hnum]

private theorem exists_matched (m : ℕ) (t : ℤ) (r : ℝ) (s : ℕ)
    (hbudget : (unmatched m t r).card ≤ s) (B : Finset ℕ)
    (hsub : B ⊆ Finset.Icc 1 (m / 2 - 1)) (hcard : s < B.card) :
    ∃ ell ∈ B, Matched m t r ell := by
  classical
  by_contra hnone
  have hB : B ⊆ unmatched m t r := by
    intro ell hell
    simp only [unmatched, Finset.mem_filter]
    exact ⟨hsub hell, fun hmatch => hnone ⟨ell, hell, hmatch⟩⟩
  have hle := Finset.card_le_card hB
  omega

private theorem fold_grid (m : ℕ) (q : ℤ) (hm : 0 < (m : ℝ)) :
    ∃ a : ℤ, 0 ≤ (a : ℝ) * Real.pi / (m : ℝ) ∧
      (a : ℝ) * Real.pi / (m : ℝ) ≤ Real.pi ∧
      Real.cos ((a : ℝ) * Real.pi / (m : ℝ)) =
        Real.cos ((q : ℝ) * Real.pi / (m : ℝ)) := by
  let y := Real.arccos (Real.cos ((q : ℝ) * Real.pi / (m : ℝ)))
  have hycos : Real.cos y = Real.cos ((q : ℝ) * Real.pi / (m : ℝ)) :=
    Real.cos_arccos (Real.neg_one_le_cos _) (Real.cos_le_one _)
  obtain ⟨z, hz | hz⟩ := Real.cos_eq_cos_iff.mp hycos
  · refine ⟨q - 2 * z * (m : ℤ), ?_⟩
    have heq : ((q - 2 * z * (m : ℤ) : ℤ) : ℝ) * Real.pi / (m : ℝ) = y := by
      push_cast
      apply (div_eq_iff (ne_of_gt hm)).mpr
      have hz' := (div_eq_iff (ne_of_gt hm)).mp hz
      nlinarith [hz']
    rw [heq]
    exact ⟨Real.arccos_nonneg _, Real.arccos_le_pi _, hycos⟩
  · refine ⟨2 * z * (m : ℤ) - q, ?_⟩
    have heq : ((2 * z * (m : ℤ) - q : ℤ) : ℝ) * Real.pi / (m : ℝ) = y := by
      push_cast
      apply (div_eq_iff (ne_of_gt hm)).mpr
      have hz' := (div_eq_iff (ne_of_gt hm)).mp hz
      nlinarith [hz']
    rw [heq]
    exact ⟨Real.arccos_nonneg _, Real.arccos_le_pi _, hycos⟩

private theorem sin_half_le (u : ℝ) (hlo : Real.pi / 3 ≤ u)
    (hhi : u ≤ 5 * Real.pi / 6) : 1 / 2 ≤ Real.sin u := by
  have hp := Real.pi_pos
  by_cases hmid : u ≤ Real.pi / 2
  · have hs := Real.strictMonoOn_sin.monotoneOn
      (show -(Real.pi / 2) ≤ Real.pi / 6 ∧ Real.pi / 6 ≤ Real.pi / 2 by constructor <;> linarith)
      (show -(Real.pi / 2) ≤ u ∧ u ≤ Real.pi / 2 by constructor <;> linarith)
      (show Real.pi / 6 ≤ u by linarith)
    rw [Real.sin_pi_div_six] at hs
    exact hs
  · have hs := Real.strictMonoOn_sin.monotoneOn
      (show -(Real.pi / 2) ≤ Real.pi / 6 ∧ Real.pi / 6 ≤ Real.pi / 2 by constructor <;> linarith)
      (show -(Real.pi / 2) ≤ Real.pi - u ∧ Real.pi - u ≤ Real.pi / 2 by constructor <;> linarith)
      (show Real.pi / 6 ≤ Real.pi - u by linarith)
    rw [Real.sin_pi_div_six, Real.sin_pi_sub] at hs
    exact hs

private theorem cosine_step (m : ℕ) (theta : ℝ) (hm : 3 ≤ m)
    (hlo : Real.pi / 3 ≤ theta) (hhi : theta ≤ Real.pi / 2) :
    Real.pi / (2 * (m : ℝ)) ≤ Real.cos theta - Real.cos (theta + Real.pi / (m : ℝ)) := by
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : 0 < (m : ℝ) := by linarith
  have hstep : 0 < Real.pi / (m : ℝ) := div_pos Real.pi_pos hmpos
  obtain ⟨u, hu, hslope⟩ := exists_hasDerivAt_eq_slope Real.cos (fun x => -Real.sin x)
    (show theta < theta + Real.pi / (m : ℝ) by linarith)
    Real.continuous_cos.continuousOn (fun x _ => Real.hasDerivAt_cos x)
  have hupper : theta + Real.pi / (m : ℝ) ≤ 5 * Real.pi / 6 := by
    have hdiv : Real.pi / (m : ℝ) ≤ Real.pi / 3 :=
      div_le_div_of_nonneg_left (le_of_lt Real.pi_pos) (by norm_num) hmR
    linarith
  have hsin := sin_half_le u (by linarith [hu.1]) (by linarith [hu.2])
  have hslope' := (eq_div_iff (ne_of_gt (by linarith : 0 < theta + Real.pi / (m : ℝ) - theta))).mp hslope
  have hmul := mul_le_mul_of_nonneg_right hsin (le_of_lt hstep)
  have hid : Real.pi / (2 * (m : ℝ)) = (1 / 2) * (Real.pi / (m : ℝ)) := by ring
  rw [hid]
  nlinarith [hslope', hmul]

private theorem grid_spacing (m ell : ℕ) (q : ℤ) (hm : 3 ≤ m)
    (hlo : Real.pi / 3 ≤ 2 * Real.pi * (ell : ℝ) / (m : ℝ))
    (hhi : 2 * Real.pi * (ell : ℝ) / (m : ℝ) ≤ Real.pi / 2)
    (hlt : Real.cos ((q : ℝ) * Real.pi / (m : ℝ)) <
      Real.cos (2 * Real.pi * (ell : ℝ) / (m : ℝ))) :
    1 / (m : ℝ) < Real.cos (2 * Real.pi * (ell : ℝ) / (m : ℝ)) -
      Real.cos ((q : ℝ) * Real.pi / (m : ℝ)) := by
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  obtain ⟨a, ha0, hapi, hacos⟩ := fold_grid m q hmpos
  have htheta0 : 0 ≤ 2 * Real.pi * (ell : ℝ) / (m : ℝ) := by positivity
  have hang : 2 * Real.pi * (ell : ℝ) / (m : ℝ) < (a : ℝ) * Real.pi / (m : ℝ) := by
    by_contra h
    have hc := Real.cos_le_cos_of_nonneg_of_le_pi ha0
      (show 2 * Real.pi * (ell : ℝ) / (m : ℝ) ≤ Real.pi by linarith [Real.pi_pos]) (le_of_not_gt h)
    rw [hacos] at hc
    linarith
  have hintR : 2 * (ell : ℝ) < (a : ℝ) := by
    have hx := (div_lt_div_iff_of_pos_right hmpos).mp hang
    nlinarith [Real.pi_pos]
  have hint : 2 * (ell : ℤ) + 1 ≤ a := by
    have hx : 2 * (ell : ℤ) < a := by exact_mod_cast hintR
    omega
  have hintR' : 2 * (ell : ℝ) + 1 ≤ (a : ℝ) := by exact_mod_cast hint
  have hnext : 2 * Real.pi * (ell : ℝ) / (m : ℝ) + Real.pi / (m : ℝ) ≤
      (a : ℝ) * Real.pi / (m : ℝ) := by
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (le_of_lt hmpos)
    nlinarith [Real.pi_pos]
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi
    (show 0 ≤ 2 * Real.pi * (ell : ℝ) / (m : ℝ) + Real.pi / (m : ℝ) by positivity)
    hapi hnext
  rw [hacos] at hc
  have hstep := cosine_step m (2 * Real.pi * (ell : ℝ) / (m : ℝ)) hm hlo hhi
  have hpi : 2 < Real.pi := by linarith [Real.pi_gt_three]
  have hdiv : 1 / (m : ℝ) < Real.pi / (2 * (m : ℝ)) := by
    apply (div_lt_div_iff₀ hmpos (by positivity : 0 < 2 * (m : ℝ))).mpr
    nlinarith
  linarith

private theorem middle_not_matched (m ell : ℕ) (t : ℤ) (r : ℝ)
    (hm : 3 ≤ m) (hr0 : 0 < r) (hr1 : r < 1)
    (hradius : 1 - r < 1 / (300 * (m : ℝ)))
    (hlo : Real.pi / 3 ≤ 2 * Real.pi * (ell : ℝ) / (m : ℝ))
    (hhi : 2 * Real.pi * (ell : ℝ) / (m : ℝ) ≤ Real.pi / 2) :
    ¬ Matched m t r ell := by
  intro hmatch
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : 0 < (m : ℝ) := by linarith
  have hhalf : 1 / 2 < r := by
    have hdiv : 1 / (300 * (m : ℝ)) ≤ 1 / 2 := by
      apply (div_le_div_iff₀ (by positivity : 0 < 300 * (m : ℝ)) (by norm_num : (0 : ℝ) < 2)).mpr
      linarith
    linarith
  let x := Real.cos (2 * Real.pi * (ell : ℝ) / (m : ℝ))
  have hx0 : 0 ≤ x := by
    have hc := Real.cos_le_cos_of_nonneg_of_le_pi
      (show 0 ≤ 2 * Real.pi * (ell : ℝ) / (m : ℝ) by positivity)
      (show Real.pi / 2 ≤ Real.pi by linarith [Real.pi_pos]) hhi
    rw [Real.cos_pi_div_two] at hc
    exact hc
  have hxhalf : x ≤ 1 / 2 := by
    have hc := Real.cos_le_cos_of_nonneg_of_le_pi
      (show 0 ≤ Real.pi / 3 by positivity)
      (show 2 * Real.pi * (ell : ℝ) / (m : ℝ) ≤ Real.pi by linarith [Real.pi_pos]) hlo
    rw [Real.cos_pi_div_three] at hc
    exact hc
  obtain ⟨j, hj, heq⟩ := hmatch
  let c := Real.cos ((2 * (j : ℝ) - (t : ℝ)) * Real.pi / (m : ℝ))
  have halgebra : r * (x - c) = (1 - r) * ((1 + r) / 2 - x) := by
    dsimp [x, c]
    nlinarith [heq]
  have hfactor0 : 0 < (1 + r) / 2 - x := by linarith
  have hfactor1 : (1 + r) / 2 - x < 1 := by linarith
  have hgap0 : 0 < x - c := by
    have hprod := mul_pos (sub_pos.mpr hr1) hfactor0
    rw [← halgebra] at hprod
    nlinarith
  have hgapupper : x - c < 2 * (1 - r) := by
    have hprod := mul_lt_mul_of_pos_left hfactor1 (sub_pos.mpr hr1)
    rw [← halgebra] at hprod
    nlinarith
  have hgapSmall : x - c < 1 / (m : ℝ) := by
    have hdiv : 2 * (1 / (300 * (m : ℝ))) < 1 / (m : ℝ) := by
      field_simp
      nlinarith
    linarith
  have hqcast : ((2 * (j : ℤ) - t : ℤ) : ℝ) = 2 * (j : ℝ) - (t : ℝ) := by push_cast; rfl
  have hgapLarge := grid_spacing m ell (2 * (j : ℤ) - t) hm hlo hhi (by
    rw [hqcast]
    change c < x
    linarith)
  rw [hqcast] at hgapLarge
  change 1 / (m : ℝ) < x - c at hgapLarge
  linarith

/-- At the exact quadratic threshold, more than the natural half-budget of the
strict nonmaximal chord indices are absent from the affine projection value grid.
This includes every parity of the polygon order and the integer axis parameter. -/
theorem more_than_budget_unmatched (k m : ℕ) (t : ℤ) (r : ℝ)
    (hk : 2 ≤ k) (hm : 1000 * (k + 1) ^ 2 ≤ m)
    (hr0 : 0 < r) (hr1 : r < 1) :
    (k - 2) / 2 < (unmatched m t r).card := by
  classical
  by_contra hnot
  have hbudget : (unmatched m t r).card ≤ (k - 2) / 2 := le_of_not_gt hnot
  have hsK : (k - 2) / 2 + 2 ≤ k + 1 := by omega
  have hKsq : k + 1 ≤ (k + 1) ^ 2 := by nlinarith
  have hsmall : 12 * ((k - 2) / 2 + 2) ≤ m := by omega
  have hm3 : 3 ≤ m := by omega
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  let Btail := Finset.Icc (m / 2 - 1 - (k - 2) / 2) (m / 2 - 1)
  have htailSub : Btail ⊆ Finset.Icc 1 (m / 2 - 1) := by
    intro ell hell
    simp only [Btail, Finset.mem_Icc] at hell ⊢
    constructor <;> omega
  have htailCard : (k - 2) / 2 < Btail.card := by
    rw [show Btail = Finset.Icc (m / 2 - 1 - (k - 2) / 2) (m / 2 - 1) from rfl, Nat.card_Icc]
    omega
  obtain ⟨ell, hell, hmatch⟩ := exists_matched m t r ((k - 2) / 2) hbudget Btail htailSub htailCard
  have htail := Finset.mem_Icc.mp hell
  have hradius := tail_radius k m ell t r hk hm hr0 hr1 htail.1 htail.2 hmatch
  let Bmid := Finset.Icc ((m + 5) / 6) (m / 4)
  have hmidSub : Bmid ⊆ Finset.Icc 1 (m / 2 - 1) := by
    intro ell hell
    simp only [Bmid, Finset.mem_Icc] at hell ⊢
    constructor <;> omega
  have hmidCard : (k - 2) / 2 < Bmid.card := by
    rw [show Bmid = Finset.Icc ((m + 5) / 6) (m / 4) from rfl, Nat.card_Icc]
    omega
  obtain ⟨ellmid, hellmid, hmatchmid⟩ := exists_matched m t r ((k - 2) / 2) hbudget Bmid hmidSub hmidCard
  have hmid := Finset.mem_Icc.mp hellmid
  have hloN : m ≤ 6 * ellmid := by omega
  have hhiN : 4 * ellmid ≤ m := by omega
  have hloR : (m : ℝ) ≤ 6 * (ellmid : ℝ) := by exact_mod_cast hloN
  have hhiR : 4 * (ellmid : ℝ) ≤ m := by exact_mod_cast hhiN
  have hlo : Real.pi / 3 ≤ 2 * Real.pi * (ellmid : ℝ) / (m : ℝ) := by
    apply (le_div_iff₀ hmpos).mpr
    nlinarith [Real.pi_pos]
  have hhi : 2 * Real.pi * (ellmid : ℝ) / (m : ℝ) ≤ Real.pi / 2 := by
    apply (div_le_iff₀ hmpos).mpr
    nlinarith [Real.pi_pos]
  exact middle_not_matched m ellmid t r hm3 hr0 hr1 hradius hlo hhi hmatchmid

end Erdos132.RobustProjectionGrid
