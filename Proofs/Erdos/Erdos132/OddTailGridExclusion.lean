import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

set_option maxHeartbeats 800000

set_option autoImplicit false

namespace Erdos132.OddTailGridExclusion

/-- An integral cosine lattice can be folded to integral levels between zero and π,
including when its original index is negative. -/
theorem fold_integral_grid (m : ℕ) (hm : 0 < m) (z : ℤ) :
    ∃ n : ℕ, n ≤ m ∧ Real.cos ((z : ℝ) * Real.pi / (m : ℝ)) =
      Real.cos ((n : ℝ) * Real.pi / (m : ℝ)) := by
  have hmi : (0 : ℤ) < m := by exact_mod_cast hm
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  let u : ℤ := z % (2 * (m : ℤ))
  have hu0 : 0 ≤ u := Int.emod_nonneg _ (by omega)
  have hu2 : u < 2 * (m : ℤ) := Int.emod_lt_of_pos _ (by omega)
  have hz : z = u + (2 * (m : ℤ)) * (z / (2 * (m : ℤ))) := by
    exact (Int.emod_add_mul_ediv z (2 * (m : ℤ))).symm
  have hperiod : Real.cos ((z : ℝ) * Real.pi / (m : ℝ)) =
      Real.cos ((u : ℝ) * Real.pi / (m : ℝ)) := by
    have hzr : (z : ℝ) = (u : ℝ) + (2 * (m : ℝ)) *
        ((z / (2 * (m : ℤ)) : ℤ) : ℝ) := by exact_mod_cast hz
    rw [hzr]
    convert Real.cos_add_int_mul_two_pi ((u : ℝ) * Real.pi / (m : ℝ))
      (z / (2 * (m : ℤ))) using 1
    field_simp
  by_cases hum : u ≤ (m : ℤ)
  · refine ⟨u.toNat, ?_, ?_⟩
    · omega
    · have hu : ((u.toNat : ℕ) : ℝ) = (u : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hu0
      simpa only [hu] using hperiod
  · let v : ℤ := 2 * (m : ℤ) - u
    have hv0 : 0 ≤ v := by dsimp [v]; omega
    have hvm : v ≤ (m : ℤ) := by dsimp [v]; omega
    refine ⟨v.toNat, by omega, ?_⟩
    rw [hperiod]
    have hv : ((v.toNat : ℕ) : ℝ) = 2 * (m : ℝ) - (u : ℝ) := by
      exact_mod_cast (show (v.toNat : ℤ) = 2 * (m : ℤ) - u from
        Int.toNat_of_nonneg hv0)
    rw [hv]
    have heq : (2 * (m : ℝ) - (u : ℝ)) * Real.pi / (m : ℝ) =
        2 * Real.pi - (u : ℝ) * Real.pi / (m : ℝ) := by
      field_simp
    rw [heq, Real.cos_two_pi_sub]

example : ∃ n : ℕ, n ≤ 15 ∧ Real.cos ((-3 : ℝ) * Real.pi / 15) =
    Real.cos ((n : ℝ) * Real.pi / 15) := by
  simpa only [Nat.cast_ofNat, Int.cast_neg, Int.cast_ofNat] using
    fold_integral_grid 15 (by norm_num) (-3)

private theorem pi_sq_lt_ten : Real.pi ^ 2 < 10 := by
  have hp := Real.pi_pos
  have hb := Real.pi_lt_d2
  nlinarith

private theorem endpoint_radius_bound (M r c : ℝ) (hM : 15 ≤ M)
    (hr : 0 < r) (hr1 : r < 1) (hc : -1 ≤ c)
    (he : (1 - r ^ 2) / 2 + r * c ≤ -Real.cos (3 * Real.pi / M)) :
    4 / 5 < r ∧ 1 - r < 24 / M ^ 2 := by
  have hMp : 0 < M := by linarith
  have hM2 : 225 ≤ M ^ 2 := by nlinarith
  let b : ℝ := 3 * Real.pi / M
  have hb : b ^ 2 * M ^ 2 = 9 * Real.pi ^ 2 := by
    dsimp [b]
    field_simp
    ring
  have hb2 : b ^ 2 < 2 / 5 := by
    nlinarith [pi_sq_lt_ten, sq_nonneg b]
  have hcos : 1 - b ^ 2 / 2 ≤ Real.cos b := Real.one_sub_sq_div_two_le_cos
  have hrc : -r ≤ r * c := by nlinarith
  have hd0 : 0 < 1 - r := by linarith
  have hd1 : 1 - r < 1 := by linarith
  have hbase : (1 - r) * (2 - (1 - r) / 2) ≤ b ^ 2 / 2 := by
    dsimp [b] at hcos
    nlinarith
  have hd : 1 - r < 1 / 5 := by nlinarith
  have hsmall : (19 / 10) * (1 - r) < b ^ 2 / 2 := by nlinarith
  have hmul := mul_lt_mul_of_pos_right hsmall (sq_pos_of_pos hMp)
  have hfinal : (1 - r) * M ^ 2 < 24 := by nlinarith [pi_sq_lt_ten]
  refine ⟨by linarith, ?_⟩
  exact (lt_div_iff₀ (sq_pos_of_pos hMp)).2 hfinal

private theorem grid_below_le_next (m k : ℕ) (hm : 0 < m) (z : ℤ)
    (hnext : 2 * Real.pi * (k : ℝ) / (m : ℝ) + Real.pi / (m : ℝ) ≤ Real.pi)
    (hlt : Real.cos ((z : ℝ) * Real.pi / (m : ℝ)) <
      Real.cos (2 * Real.pi * (k : ℝ) / (m : ℝ))) :
    Real.cos ((z : ℝ) * Real.pi / (m : ℝ)) ≤
      Real.cos (2 * Real.pi * (k : ℝ) / (m : ℝ) + Real.pi / (m : ℝ)) := by
  obtain ⟨n, hnm, hfold⟩ := fold_integral_grid m hm z
  have hM : (0 : ℝ) < m := by exact_mod_cast hm
  have hnpi : (n : ℝ) * Real.pi / (m : ℝ) ≤ Real.pi := by
    apply (div_le_iff₀ hM).2
    have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
    nlinarith [Real.pi_pos]
  have htheta0 : 0 ≤ 2 * Real.pi * (k : ℝ) / (m : ℝ) := by positivity
  have hnk : 2 * k < n := by
    by_contra hbad
    have hn : n ≤ 2 * k := by omega
    have hnr : (n : ℝ) ≤ 2 * (k : ℝ) := by exact_mod_cast hn
    have hang : (n : ℝ) * Real.pi / (m : ℝ) ≤
        2 * Real.pi * (k : ℝ) / (m : ℝ) := by
      apply (div_le_div_iff_of_pos_right hM).2
      nlinarith [Real.pi_pos]
    have hmono := Real.cos_le_cos_of_nonneg_of_le_pi
      (show 0 ≤ (n : ℝ) * Real.pi / (m : ℝ) by positivity)
      (show 2 * Real.pi * (k : ℝ) / (m : ℝ) ≤ Real.pi by
        linarith [div_pos Real.pi_pos hM]) hang
    rw [hfold] at hlt
    linarith
  have hnr : 2 * (k : ℝ) + 1 ≤ (n : ℝ) := by
    exact_mod_cast (show 2 * k + 1 ≤ n by omega)
  rw [hfold]
  apply Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hnpi
  apply (le_div_iff₀ hM).2
  have heq : (2 * Real.pi * (k : ℝ) / (m : ℝ) + Real.pi / (m : ℝ)) *
      (m : ℝ) = (2 * (k : ℝ) + 1) * Real.pi := by
    field_simp
  rw [heq]
  nlinarith [Real.pi_pos]

private theorem middle_gap_bound (M θ : ℝ) (hM : 15 ≤ M)
    (hlo : Real.pi / 2 - 2 * Real.pi / M ≤ θ) (hhi : θ ≤ Real.pi / 2) :
    (2 / M) * (1 - 20 / M ^ 2) <
      Real.cos θ - Real.cos (θ + Real.pi / M) := by
  have hMp : 0 < M := by linarith
  have hM2 : 225 ≤ M ^ 2 := by nlinarith
  let h : ℝ := Real.pi / M
  have hh : 0 < h := div_pos Real.pi_pos hMp
  have hhpi : 2 * h ≤ Real.pi := by
    dsimp [h]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hMp).2
    nlinarith [Real.pi_pos]
  have hs : 1 / M ≤ Real.sin (h / 2) := by
    have harg : h / 2 ≤ Real.pi / 2 := by linarith
    have hj := Real.mul_le_sin (le_of_lt (half_pos hh)) harg
    have heq : 2 / Real.pi * (h / 2) = 1 / M := by
      dsimp [h]
      field_simp
    rwa [heq] at hj
  have hcos : 1 - 20 / M ^ 2 < Real.cos (2 * h) := by
    have ht : (2 * h) ^ 2 * M ^ 2 = 4 * Real.pi ^ 2 := by
      dsimp [h]
      field_simp
      ring
    have hb : (2 * h) ^ 2 / 2 < 20 / M ^ 2 := by
      apply (lt_div_iff₀ (sq_pos_of_pos hMp)).2
      nlinarith [pi_sq_lt_ten]
    have hc : 1 - (2 * h) ^ 2 / 2 ≤ Real.cos (2 * h) :=
      Real.one_sub_sq_div_two_le_cos
    linarith
  have hcospos : 0 < Real.cos (2 * h) := by
    have h20 : 20 / M ^ 2 < 1 := (div_lt_one (sq_pos_of_pos hMp)).2 (by linarith)
    linarith
  have hmid : Real.cos (2 * h) ≤ Real.sin (θ + h / 2) := by
    rw [← Real.cos_pi_div_two_sub]
    have hu : -(2 * h) ≤ Real.pi / 2 - (θ + h / 2) := by linarith
    have hv : Real.pi / 2 - (θ + h / 2) ≤ 2 * h := by
      have hlo' : Real.pi / 2 - 2 * h ≤ θ := by
        simpa only [h, mul_div_assoc] using hlo
      linarith
    by_cases hz : 0 ≤ Real.pi / 2 - (θ + h / 2)
    · exact Real.cos_le_cos_of_nonneg_of_le_pi hz hhpi hv
    · rw [← Real.cos_neg (Real.pi / 2 - (θ + h / 2))]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) hhpi (by linarith)
  have hid : Real.cos θ - Real.cos (θ + Real.pi / M) =
      2 * Real.sin (h / 2) * Real.sin (θ + h / 2) := by
    rw [Real.cos_sub_cos]
    change -2 * Real.sin ((θ + (θ + h)) / 2) * Real.sin ((θ - (θ + h)) / 2) = _
    have he1 : (θ + (θ + h)) / 2 = θ + h / 2 := by ring
    have he2 : (θ - (θ + h)) / 2 = -(h / 2) := by ring
    rw [he1, he2, Real.sin_neg]
    ring
  rw [hid]
  have hprod : (1 / M) * Real.cos (2 * h) ≤
      Real.sin (h / 2) * Real.sin (θ + h / 2) :=
    mul_le_mul hs hmid (le_of_lt hcospos)
      (le_trans (show 0 ≤ 1 / M by positivity) hs)
  have hstrict := mul_lt_mul_of_pos_left hcos (show 0 < 2 / M by positivity)
  have hprod2 := mul_le_mul_of_nonneg_left hprod (show (0 : ℝ) ≤ 2 by norm_num)
  calc
    (2 / M) * (1 - 20 / M ^ 2) < (2 / M) * Real.cos (2 * h) := hstrict
    _ = 2 * (1 / M * Real.cos (2 * h)) := by ring
    _ ≤ 2 * (Real.sin (h / 2) * Real.sin (θ + h / 2)) := hprod2
    _ = 2 * Real.sin (h / 2) * Real.sin (θ + h / 2) := by ring

private theorem numerical_gap (M : ℝ) (hM : 15 ≤ M) :
    24 / (M ^ 2 - 24) < (2 / M) * (1 - 20 / M ^ 2) := by
  have hMp : 0 < M := by linarith
  have hM2 : 225 ≤ M ^ 2 := by nlinarith
  have hd : 0 < M ^ 2 - 24 := by linarith
  have hquadratic : 1 ≤ M ^ 2 - 12 * M - 44 := by
    have hp : 0 ≤ (M - 15) * (M + 3) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hpoly : 0 < M ^ 4 - 12 * M ^ 3 - 44 * M ^ 2 + 480 := by
    have hp := mul_le_mul_of_nonneg_left hquadratic (sq_nonneg M)
    nlinarith
  have hid : ((2 / M) * (1 - 20 / M ^ 2) * (M ^ 2 - 24) - 24) * M ^ 3 =
      2 * (M ^ 4 - 12 * M ^ 3 - 44 * M ^ 2 + 480) := by
    field_simp
    ring
  apply (div_lt_iff₀ hd).2
  have hM3 : 0 < M ^ 3 := pow_pos hMp 3
  nlinarith

private theorem middle_preimage (M r x c : ℝ) (hM : 15 ≤ M)
    (hr : 0 < r) (hr1 : r < 1) (hr4 : 4 / 5 < r)
    (hd : 1 - r < 24 / M ^ 2) (hx0 : 0 ≤ x) (hx1 : x < 1 / 2)
    (he : x = (1 - r ^ 2) / 2 + r * c) :
    c < x ∧ x - c < 24 / (M ^ 2 - 24) := by
  have hMp : 0 < M := by linarith
  have hM2 : 225 ≤ M ^ 2 := by nlinarith
  have hden : 0 < M ^ 2 - 24 := by linarith
  have hident : r * (x - c) = (1 - r) * ((1 + r) / 2 - x) := by
    nlinarith [he]
  have hdiff : 0 < x - c := by
    have hp : 0 < (1 - r) * ((1 + r) / 2 - x) := mul_pos (by linarith) (by linarith)
    nlinarith
  have hupper : r * (x - c) ≤ 1 - r := by
    have hp : 0 ≤ (1 - r) * (1 - ((1 + r) / 2 - x)) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hdelta : (1 - r) * M ^ 2 < 24 :=
    (lt_div_iff₀ (sq_pos_of_pos hMp)).1 hd
  have hratio : (1 - r) / r < 24 / (M ^ 2 - 24) := by
    apply (div_lt_div_iff₀ hr hden).2
    nlinarith
  refine ⟨by linarith, lt_of_le_of_lt ?_ hratio⟩
  exact (le_div_iff₀ hr).2 (by nlinarith)

/-- For every completion size at least fifteen, no strict interior radius can
send all nonmaximal chord cosines into any integer-shifted polygon projection grid.
The required indices are exactly `1 ≤ k < m / 2`, with natural floor division. -/
theorem odd_tail_grid_exclusion (m : ℕ) (hm : 15 ≤ m) (t : ℤ) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1) :
    ¬ (∀ k : ℕ, 1 ≤ k → k < m / 2 → ∃ j : ℕ, j < m ∧
      Real.cos (2 * Real.pi * (k : ℝ) / (m : ℝ)) =
        (1 - r ^ 2) / 2 + r *
          Real.cos ((2 * (j : ℝ) - (t : ℝ)) * Real.pi / (m : ℝ))) := by
  intro hcontain
  have hm0 : 0 < m := by omega
  have hM : (15 : ℝ) ≤ m := by exact_mod_cast hm
  have hMp : (0 : ℝ) < m := by exact_mod_cast hm0
  let L : ℕ := m / 2 - 1
  have hL1 : 1 ≤ L := by dsimp [L]; omega
  have hL2 : L < m / 2 := by dsimp [L]; omega
  have hLm : 2 * L ≤ m := by dsimp [L]; omega
  have hmL : m ≤ 2 * L + 3 := by dsimp [L]; omega
  have hLm' : 2 * (L : ℝ) ≤ m := by exact_mod_cast hLm
  have hmL' : (m : ℝ) ≤ 2 * (L : ℝ) + 3 := by exact_mod_cast hmL
  obtain ⟨jL, hjL, heL⟩ := hcontain L hL1 hL2
  have hβ0 : 0 ≤ Real.pi - 3 * Real.pi / (m : ℝ) := by
    have hb : 3 * Real.pi / (m : ℝ) ≤ Real.pi := by
      apply (div_le_iff₀ hMp).2
      nlinarith [Real.pi_pos]
    linarith
  have hLpi : 2 * Real.pi * (L : ℝ) / (m : ℝ) ≤ Real.pi := by
    apply (div_le_iff₀ hMp).2
    nlinarith [Real.pi_pos]
  have hLlow : Real.pi - 3 * Real.pi / (m : ℝ) ≤
      2 * Real.pi * (L : ℝ) / (m : ℝ) := by
    apply (le_div_iff₀ hMp).2
    rw [sub_mul, div_mul_cancel₀ _ hMp.ne']
    nlinarith [Real.pi_pos]
  have hend := Real.cos_le_cos_of_nonneg_of_le_pi hβ0 hLpi hLlow
  rw [Real.cos_pi_sub] at hend
  obtain ⟨hr4, hdelta⟩ := endpoint_radius_bound (m : ℝ) r
    (Real.cos ((2 * (jL : ℝ) - (t : ℝ)) * Real.pi / (m : ℝ))) hM hr hr1
    (Real.neg_one_le_cos _) (by rw [← heL]; exact hend)
  let k : ℕ := m / 4
  have hk1 : 1 ≤ k := by dsimp [k]; omega
  have hk2 : k < m / 2 := by dsimp [k]; omega
  have hkupper : 4 * k ≤ m := by dsimp [k]; omega
  have hklower : m ≤ 4 * k + 4 := by dsimp [k]; omega
  have hkupper' : 4 * (k : ℝ) ≤ m := by exact_mod_cast hkupper
  have hklower' : (m : ℝ) ≤ 4 * (k : ℝ) + 4 := by exact_mod_cast hklower
  let θ : ℝ := 2 * Real.pi * (k : ℝ) / (m : ℝ)
  have hθ0 : 0 ≤ θ := by dsimp [θ]; positivity
  have hθhi : θ ≤ Real.pi / 2 := by
    dsimp [θ]
    apply (div_le_iff₀ hMp).2
    nlinarith [Real.pi_pos]
  have hθlo : Real.pi / 2 - 2 * Real.pi / (m : ℝ) ≤ θ := by
    dsimp [θ]
    apply (le_div_iff₀ hMp).2
    rw [sub_mul, div_mul_cancel₀ _ hMp.ne']
    nlinarith [Real.pi_pos]
  have hhhalf : Real.pi / (m : ℝ) ≤ Real.pi / 2 := by
    apply (div_le_iff₀ hMp).2
    nlinarith [Real.pi_pos]
  have hnext : θ + Real.pi / (m : ℝ) ≤ Real.pi := by linarith
  have hx0 : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hθhi⟩
  have hu : 0 ≤ 2 * Real.pi / (m : ℝ) := by positivity
  have huhalf : 2 * Real.pi / (m : ℝ) < 1 / 2 := by
    apply (div_lt_iff₀ hMp).2
    nlinarith [Real.pi_lt_d2]
  have hx1 : Real.cos θ < 1 / 2 := by
    have hstart : 0 ≤ Real.pi / 2 - 2 * Real.pi / (m : ℝ) := by
      have hh : 2 * Real.pi / (m : ℝ) ≤ Real.pi / 2 := by
        apply (div_le_iff₀ hMp).2
        nlinarith [Real.pi_pos]
      linarith
    have hmono := Real.cos_le_cos_of_nonneg_of_le_pi hstart
      (show θ ≤ Real.pi by linarith [Real.pi_pos]) hθlo
    rw [Real.cos_pi_div_two_sub] at hmono
    exact lt_of_le_of_lt (hmono.trans (Real.sin_le hu)) huhalf
  obtain ⟨j, hj, he⟩ := hcontain k hk1 hk2
  let c : ℝ := Real.cos ((2 * (j : ℝ) - (t : ℝ)) * Real.pi / (m : ℝ))
  have heq : Real.cos θ = (1 - r ^ 2) / 2 + r * c := he
  obtain ⟨hcx, hsmall⟩ := middle_preimage (m : ℝ) r (Real.cos θ) c
    hM hr hr1 hr4 hdelta hx0 hx1 heq
  let z : ℤ := 2 * (j : ℤ) - t
  have hzc : Real.cos ((z : ℝ) * Real.pi / (m : ℝ)) = c := by
    dsimp [z, c]
    push_cast
    rfl
  have hgrid := grid_below_le_next m k hm0 z hnext (by rw [hzc]; exact hcx)
  rw [hzc] at hgrid
  have hgap := middle_gap_bound (m : ℝ) θ hM hθlo hθhi
  have hnum := numerical_gap (m : ℝ) hM
  change c ≤ Real.cos (θ + Real.pi / (m : ℝ)) at hgrid
  linarith

/-- The exclusion applies at the boundary size fifteen, shift zero and radius
one half; all parameter hypotheses hold simultaneously and the index domain is nonempty. -/
theorem parameter_fixture :
    15 ≤ (15 : ℕ) ∧ 0 < (1 / 2 : ℝ) ∧ (1 / 2 : ℝ) < 1 ∧
    (1 ≤ (3 : ℕ) ∧ 3 < (15 : ℕ) / 2) ∧
    ¬ (∀ k : ℕ, 1 ≤ k → k < (15 : ℕ) / 2 → ∃ j : ℕ, j < 15 ∧
      Real.cos (2 * Real.pi * (k : ℝ) / 15) =
        (1 - (1 / 2 : ℝ) ^ 2) / 2 + (1 / 2 : ℝ) *
          Real.cos ((2 * (j : ℝ) - (0 : ℝ)) * Real.pi / 15)) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  simpa only [Nat.cast_ofNat, Int.cast_zero] using
    odd_tail_grid_exclusion 15 (by norm_num) 0 (1 / 2) (by norm_num) (by norm_num)

end Erdos132.OddTailGridExclusion
