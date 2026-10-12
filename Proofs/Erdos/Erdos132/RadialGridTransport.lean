import Erdos.Erdos132.CircleRotation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

set_option autoImplicit false

open Erdos132.TwoInteriorCircle Erdos132.CircleRotation
open scoped Real

namespace Erdos132.RadialGridTransport

private theorem exp_re (a : ℝ) : ((Circle.exp a : Circle) : ℂ).re = Real.cos a := by
  simp [Circle.coe_exp, Complex.exp_re]

private theorem exp_im (a : ℝ) : ((Circle.exp a : Circle) : ℂ).im = Real.sin a := by
  simp [Circle.coe_exp, Complex.exp_im]

private theorem radial_sq (v : Plane) (s a b : ℝ) :
    dist (s • rotate (Circle.exp a) v) (rotate (Circle.exp b) v) ^ 2 =
      ‖v‖ ^ 2 * (s ^ 2 + 1 - 2 * s * Real.cos (b - a)) := by
  rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_two, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
    rotate, Matrix.cons_val_zero, Matrix.cons_val_one,
    exp_re, exp_im, Real.cos_sub]
  calc
    _ = (v 0 ^ 2 + v 1 ^ 2) *
        (s ^ 2 * (Real.sin a ^ 2 + Real.cos a ^ 2) +
          (Real.sin b ^ 2 + Real.cos b ^ 2) -
          2 * s * (Real.cos b * Real.cos a + Real.sin b * Real.sin a)) := by ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq, Real.sin_sq_add_cos_sq]; ring

/-- The actual canonical vertex with angle `2πj/m` relative to the arbitrary base `v`. -/
noncomputable def canonicalVertex (m : ℕ) (v : Plane) (j : Fin m) : Plane :=
  rotate (Circle.exp (2 * π * (j : ℝ) / (m : ℝ))) v

example (m : ℕ) (v : Plane) (j : Fin m) :
    canonicalVertex m v j = rotate (Circle.exp (2 * π * (j : ℝ) / (m : ℝ))) v := rfl

example (v : Plane) : canonicalVertex 4 v 0 = v := by
  simp [canonicalVertex]

private theorem polar_relative (R : ℝ) (hR : 0 < R) (v p : Plane)
    (hv : ‖v‖ = R) (hp : 0 < ‖p‖) :
    ∃ theta : ℝ, p = (‖p‖ / R) • rotate (Circle.exp theta) v := by
  let q : Plane := (R / ‖p‖) • p
  have hq : ‖q‖ = R := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hR hp), div_mul_cancel₀]
    exact ne_of_gt hp
  obtain ⟨g, hg⟩ := exists_rotation_map hR hv hq
  obtain ⟨theta, htheta⟩ := Circle.exp_surjective g
  refine ⟨theta, ?_⟩
  rw [htheta, hg]
  dsimp only [q]
  rw [smul_smul]
  have hr : ‖p‖ / R * (R / ‖p‖) = 1 := by
    field_simp
  rw [hr, one_smul]

/-- A genuine double radial fiber at distinct canonical vertices pins the direction
of the same nonzero strict interior point to an integer multiple of `π/m`.
This asserts no reflection symmetry of an occupied hull. -/
theorem axis_pinning (m : ℕ) (hm : 3 ≤ m) (R : ℝ) (hR : 0 < R)
    (v p : Plane) (hv : ‖v‖ = R) (hp : 0 < ‖p‖) (_hpR : ‖p‖ < R)
    (i j : Fin m) (hne : canonicalVertex m v i ≠ canonicalVertex m v j)
    (heq : dist p (canonicalVertex m v i) = dist p (canonicalVertex m v j)) :
    ∃ t : ℤ, p = (‖p‖ / R) • rotate (Circle.exp ((t : ℝ) * π / (m : ℝ))) v := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  let r : ℝ := ‖p‖ / R
  have hr : 0 < r := div_pos hp hR
  obtain ⟨theta, htheta⟩ := polar_relative R hR v p hv hp
  have hi := radial_sq v r theta (2 * π * (i : ℝ) / (m : ℝ))
  have hj := radial_sq v r theta (2 * π * (j : ℝ) / (m : ℝ))
  have hd : dist (r • rotate (Circle.exp theta) v) (rotate (Circle.exp (2 * π * (i : ℝ) / (m : ℝ))) v) =
      dist (r • rotate (Circle.exp theta) v) (rotate (Circle.exp (2 * π * (j : ℝ) / (m : ℝ))) v) := by
    change dist ((‖p‖ / R) • rotate (Circle.exp theta) v) _ =
      dist ((‖p‖ / R) • rotate (Circle.exp theta) v) _
    rw [← htheta]
    exact heq
  rw [hd, hv] at hi
  rw [hv] at hj
  have hcos : Real.cos (2 * π * (i : ℝ) / (m : ℝ) - theta) =
      Real.cos (2 * π * (j : ℝ) / (m : ℝ) - theta) := by
    have hc : r ^ 2 + 1 - 2 * r * Real.cos (2 * π * (i : ℝ) / (m : ℝ) - theta) =
        r ^ 2 + 1 - 2 * r * Real.cos (2 * π * (j : ℝ) / (m : ℝ) - theta) :=
      mul_left_cancel₀ (pow_ne_zero 2 (ne_of_gt hR)) (hi.symm.trans hj)
    nlinarith only [hc, hr]
  obtain ⟨k, hk | hk⟩ := Real.cos_eq_cos_iff.mp hcos
  · exfalso
    apply hne
    unfold canonicalVertex
    congr 1
    apply Circle.exp_eq_exp.mpr
    refine ⟨-k, ?_⟩
    push_cast
    linarith
  · let t : ℤ := (i.val : ℤ) + (j.val : ℤ) - k * (m : ℤ)
    have ht : theta = (t : ℝ) * π / (m : ℝ) := by
      dsimp only [t]
      push_cast
      apply (eq_div_iff (ne_of_gt hmR)).mpr
      have hk' := (sub_eq_iff_eq_add).mp hk
      field_simp at hk'
      nlinarith only [hk']
    exact ⟨t, ht ▸ htheta⟩

/-- With a specified radial representation, actual vertex-distance equality is
exactly the cosine-grid equation. The half-range ensures a nonnegative chord,
including the zero chord and the maximum in either parity. -/
theorem distance_eq_chord_iff (m : ℕ) (hm : 3 ≤ m) (R : ℝ) (hR : 0 < R)
    (v p : Plane) (hv : ‖v‖ = R) (r : ℝ) (t : ℤ)
    (hpin : p = r • rotate (Circle.exp ((t : ℝ) * π / (m : ℝ))) v)
    (j : Fin m) (ell : ℕ) (hell : ell ≤ m / 2) :
    dist p (canonicalVertex m v j) = 2 * R * Real.sin (π * (ell : ℝ) / (m : ℝ)) ↔
      Real.cos (2 * π * (ell : ℝ) / (m : ℝ)) =
        (1 - r ^ 2) / 2 + r * Real.cos ((2 * (j : ℝ) - (t : ℝ)) * π / (m : ℝ)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hellR : (2 : ℝ) * ell ≤ m := by
    exact_mod_cast (show 2 * ell ≤ m by omega)
  have hangle0 : 0 ≤ π * (ell : ℝ) / (m : ℝ) := by positivity
  have hanglepi : π * (ell : ℝ) / (m : ℝ) ≤ π := by
    apply (div_le_iff₀ hmR).mpr
    nlinarith only [hellR, Real.pi_pos]
  have hchord0 : 0 ≤ 2 * R * Real.sin (π * (ell : ℝ) / (m : ℝ)) :=
    mul_nonneg (by positivity) (Real.sin_nonneg_of_nonneg_of_le_pi hangle0 hanglepi)
  have hphase : 2 * π * (j : ℝ) / (m : ℝ) - (t : ℝ) * π / (m : ℝ) =
      (2 * (j : ℝ) - (t : ℝ)) * π / (m : ℝ) := by ring
  have hd : dist p (canonicalVertex m v j) ^ 2 =
      R ^ 2 * (r ^ 2 + 1 - 2 * r * Real.cos ((2 * (j : ℝ) - (t : ℝ)) * π / (m : ℝ))) := by
    rw [hpin, canonicalVertex, radial_sq, hv, hphase]
  have hdouble : 2 * π * (ell : ℝ) / (m : ℝ) = 2 * (π * (ell : ℝ) / (m : ℝ)) := by ring
  have hc : (2 * R * Real.sin (π * (ell : ℝ) / (m : ℝ))) ^ 2 =
      R ^ 2 * (2 * (1 - Real.cos (2 * π * (ell : ℝ) / (m : ℝ)))) := by
    rw [hdouble, Real.cos_two_mul]
    have hs := Real.sin_sq_add_cos_sq (π * (ell : ℝ) / (m : ℝ))
    calc
      _ = R ^ 2 * (4 * Real.sin (π * (ell : ℝ) / (m : ℝ)) ^ 2) := by ring
      _ = _ := by congr 1; nlinarith only [hs]
  rw [← (sq_eq_sq₀ dist_nonneg hchord0), hd, hc]
  rw [mul_right_inj' (pow_ne_zero 2 (ne_of_gt hR))]
  constructor <;> intro h <;> linarith only [h]

/-- The same actual double fiber derives one integer axis, a strict normalized
radius, and the distance/cosine equivalence for every actual canonical vertex.
No axis certificate or occupied-hull reflection is an input. -/
theorem radial_grid_transport (m : ℕ) (hm : 3 ≤ m) (R : ℝ) (hR : 0 < R)
    (v p : Plane) (hv : ‖v‖ = R) (hp : 0 < ‖p‖) (hpR : ‖p‖ < R)
    (i j : Fin m) (hne : canonicalVertex m v i ≠ canonicalVertex m v j)
    (heq : dist p (canonicalVertex m v i) = dist p (canonicalVertex m v j)) :
    ∃ t : ℤ,
      p = (‖p‖ / R) • rotate (Circle.exp ((t : ℝ) * π / (m : ℝ))) v ∧
      0 < ‖p‖ / R ∧ ‖p‖ / R < 1 ∧
      ∀ (j : Fin m) (ell : ℕ), ell ≤ m / 2 →
        (dist p (canonicalVertex m v j) = 2 * R * Real.sin (π * (ell : ℝ) / (m : ℝ)) ↔
          Real.cos (2 * π * (ell : ℝ) / (m : ℝ)) =
            (1 - (‖p‖ / R) ^ 2) / 2 +
              (‖p‖ / R) * Real.cos ((2 * (j : ℝ) - (t : ℝ)) * π / (m : ℝ))) := by
  obtain ⟨t, hpin⟩ := axis_pinning m hm R hR v p hv hp hpR i j hne heq
  refine ⟨t, hpin, div_pos hp hR, (div_lt_one hR).mpr hpR, ?_⟩
  intro j ell hell
  exact distance_eq_chord_iff m hm R hR v p hv (‖p‖ / R) t hpin j ell hell

/-- An occupied subset of the canonical completion consumes the original actual
endpoints of a double fiber without requiring an indexing certificate for them. -/
theorem occupied_radial_grid_transport (m : ℕ) (hm : 3 ≤ m) (R : ℝ) (hR : 0 < R)
    (v p : Plane) (hv : ‖v‖ = R) (hp : 0 < ‖p‖) (hpR : ‖p‖ < R)
    (H : Finset Plane) (hH : ∀ h ∈ H, ∃ j : Fin m, canonicalVertex m v j = h)
    (a b : Plane) (ha : a ∈ H) (hb : b ∈ H) (hab : a ≠ b) (heq : dist p a = dist p b) :
    ∃ t : ℤ,
      p = (‖p‖ / R) • rotate (Circle.exp ((t : ℝ) * π / (m : ℝ))) v ∧
      0 < ‖p‖ / R ∧ ‖p‖ / R < 1 ∧
      ∀ (j : Fin m) (ell : ℕ), ell ≤ m / 2 →
        (dist p (canonicalVertex m v j) = 2 * R * Real.sin (π * (ell : ℝ) / (m : ℝ)) ↔
          Real.cos (2 * π * (ell : ℝ) / (m : ℝ)) =
            (1 - (‖p‖ / R) ^ 2) / 2 +
              (‖p‖ / R) * Real.cos ((2 * (j : ℝ) - (t : ℝ)) * π / (m : ℝ))) := by
  obtain ⟨i, hi⟩ := hH a ha
  obtain ⟨j, hj⟩ := hH b hb
  apply radial_grid_transport m hm R hR v p hv hp hpR i j
  · simpa only [hi, hj] using hab
  · simpa only [hi, hj] using heq

private theorem canonical_rotate (m : ℕ) (g : Rotation) (v : Plane) (j : Fin m) :
    canonicalVertex m (rotate g v) j = rotate g (canonicalVertex m v j) := by
  unfold canonicalVertex
  rw [← rotate_mul, mul_comm, rotate_mul]

/-- For every base rotation, the unit square and its strict radial point at half
radius simultaneously satisfy every double-fiber hypothesis. The combined theorem
is applied to those same objects, yielding the full same-axis transport conclusion. -/
theorem rotated_square_application (g : Rotation) :
    ∃ v p : Plane,
      3 ≤ (4 : ℕ) ∧ 0 < (1 : ℝ) ∧ ‖v‖ = (1 : ℝ) ∧ 0 < ‖p‖ ∧ ‖p‖ < 1 ∧
      canonicalVertex 4 v 1 ≠ canonicalVertex 4 v 3 ∧
      dist p (canonicalVertex 4 v 1) = dist p (canonicalVertex 4 v 3) ∧
      ∃ t : ℤ,
        p = (‖p‖ / 1) • rotate (Circle.exp ((t : ℝ) * π / (4 : ℝ))) v ∧
        0 < ‖p‖ / 1 ∧ ‖p‖ / 1 < 1 ∧
        ∀ (j : Fin 4) (ell : ℕ), ell ≤ 4 / 2 →
          (dist p (canonicalVertex 4 v j) = 2 * 1 * Real.sin (π * (ell : ℝ) / (4 : ℝ)) ↔
            Real.cos (2 * π * (ell : ℝ) / (4 : ℝ)) =
              (1 - (‖p‖ / 1) ^ 2) / 2 +
                (‖p‖ / 1) * Real.cos ((2 * (j : ℝ) - (t : ℝ)) * π / (4 : ℝ))) := by
  let w : Plane := WithLp.toLp 2 ![1, 0]
  let q : Plane := (1 / 2 : ℝ) • w
  let v : Plane := rotate g w
  let p : Plane := rotate g q
  have hw : ‖w‖ = (1 : ℝ) := by
    norm_num [w, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  have hv : ‖v‖ = (1 : ℝ) := by rw [norm_rotate, hw]
  have hq : ‖q‖ = (1 / 2 : ℝ) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num), hw, mul_one]
  have hp : ‖p‖ = (1 / 2 : ℝ) := by rw [norm_rotate, hq]
  have htop : canonicalVertex 4 w 1 = WithLp.toLp 2 ![0, 1] := by
    have ha : 2 * π * (1 : ℝ) / 4 = π / 2 := by ring
    norm_num only [canonicalVertex, Fin.val_one, Nat.cast_one, Nat.cast_ofNat]
    rw [ha]
    ext i
    fin_cases i <;>
      simp only [rotate, w, Matrix.cons_val_zero, Matrix.cons_val_one, exp_re, exp_im,
        Real.cos_pi_div_two, Real.sin_pi_div_two] <;> norm_num
  have hbottom : canonicalVertex 4 w 3 = WithLp.toLp 2 ![0, -1] := by
    have ha : 2 * π * (3 : ℝ) / 4 = π / 2 + π := by ring
    have h3 : ((3 : Fin 4) : ℝ) = 3 := by norm_num
    simp only [canonicalVertex, h3, Nat.cast_ofNat]
    rw [ha]
    ext i
    fin_cases i <;>
      simp only [rotate, w, Matrix.cons_val_zero, Matrix.cons_val_one, exp_re, exp_im,
        Real.cos_add_pi, Real.sin_add_pi, Real.cos_pi_div_two, Real.sin_pi_div_two] <;>
        norm_num
  have hne0 : canonicalVertex 4 w 1 ≠ canonicalVertex 4 w 3 := by
    rw [htop, hbottom]
    intro he
    have he1 := congrArg (fun x : Plane => x 1) he
    norm_num at he1
  have hne : canonicalVertex 4 v 1 ≠ canonicalVertex 4 v 3 := by
    rw [canonical_rotate, canonical_rotate]
    exact (rotate_isometry g).injective.ne hne0
  have hd0 : dist q (canonicalVertex 4 w 1) = dist q (canonicalVertex 4 w 3) := by
    rw [htop, hbottom]
    apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
    norm_num [q, w, dist_eq_norm, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  have hd : dist p (canonicalVertex 4 v 1) = dist p (canonicalVertex 4 v 3) := by
    rw [canonical_rotate, canonical_rotate, (rotate_isometry g).dist_eq,
      (rotate_isometry g).dist_eq]
    exact hd0
  have hp0 : 0 < ‖p‖ := by rw [hp]; norm_num
  have hp1 : ‖p‖ < 1 := by rw [hp]; norm_num
  exact ⟨v, p, by decide, by norm_num, hv, hp0, hp1, hne, hd,
    radial_grid_transport 4 (by decide) 1 (by norm_num) v p hv hp0 hp1 1 3 hne hd⟩

end Erdos132.RadialGridTransport
