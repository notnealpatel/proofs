import Erdos.Erdos132.TwoInteriorCircle

set_option autoImplicit false

namespace Erdos132.DoubleEndpoint

open Erdos132.TwoInteriorCircle

/-- Distinct common points of two equal-radius circles in the plane are reflected
through the midpoint of their distinct centers. -/
theorem common_points_sum {a b z w : Plane} {L : ℝ}
    (hab : a ≠ b) (hzw : z ≠ w)
    (hza : dist z a = L) (hzb : dist z b = L)
    (hwa : dist w a = L) (hwb : dist w b = L) :
    z + w = a + b := by
  let c := a + b - z
  have hca : dist c a = L := by
    rw [dist_eq_norm]
    have he : c - a = -(z - b) := by dsimp [c]; abel
    rw [he, norm_neg, ← dist_eq_norm, hzb]
  have hcb : dist c b = L := by
    rw [dist_eq_norm]
    have he : c - b = -(z - a) := by dsimp [c]; abel
    rw [he, norm_neg, ← dist_eq_norm, hza]
  by_cases hcz : c = z
  · have hmid : a + b = z + z := (sub_eq_iff_eq_add).mp hcz
    let x := w - z
    let v := z - a
    have hxa : x + v = w - a := by dsimp [x, v]; abel
    have hxb : x - v = w - b := by
      dsimp [x, v]
      calc
        (w - z) - (z - a) = w - (z + z) + a := by abel
        _ = w - b := by rw [← hmid]; abel
    have hna : ‖x + v‖ = ‖v‖ := by
      rw [hxa, ← dist_eq_norm, hwa]
      exact hza.symm
    have hnb : ‖x - v‖ = ‖v‖ := by
      rw [hxb, ← dist_eq_norm, hwb]
      exact hza.symm
    have hzero : ‖x‖ = 0 := by
      have hp := norm_add_sq_real x v
      have hm := norm_sub_sq_real x v
      rw [hna] at hp
      rw [hnb] at hm
      nlinarith [norm_nonneg x]
    have hwz : w = z := sub_eq_zero.mp (norm_eq_zero.mp hzero)
    exact False.elim (hzw hwz.symm)
  · have he := EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two
      (V := Plane) (by simp [finrank_euclideanSpace]) hab (Ne.symm hcz)
      hza hca hwa hzb hcb hwb
    rcases he with hwz | hwc
    · exact False.elim (hzw hwz.symm)
    · rw [hwc]
      dsimp [c]
      abel

/-- A nonzero linear inner-product functional is strictly above its uniform
lower bound at every ambient interior point. -/
theorem inner_lt_of_mem_interior {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {K : Set E} {u z : E} {c : ℝ}
    (hu : u ≠ 0) (hbound : ∀ x ∈ K, c ≤ inner ℝ u x)
    (hz : z ∈ interior K) : c < inner ℝ u z := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hz)
  have hnorm : 0 < ‖u‖ := norm_pos_iff.mpr hu
  let t := ε / (2 * ‖u‖)
  have ht : 0 < t := div_pos hε (by positivity)
  let q := z - t • u
  have hqdist : dist q z = t * ‖u‖ := by
    rw [dist_eq_norm]
    have he : q - z = -(t • u) := by dsimp [q]; abel
    rw [he, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  have hq : q ∈ K := by
    apply hball
    rw [Metric.mem_ball, hqdist]
    dsimp [t]
    field_simp
    linarith
  have hlow := hbound q hq
  dsimp [q] at hlow
  rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq] at hlow
  have hpositive : 0 < t * ‖u‖ ^ 2 := mul_pos ht (sq_pos_of_pos hnorm)
  linarith

/-- On a centered circle, a distance upper bound relative to a circle vertex
becomes a lower bound for the associated inner-product functional on the hull. -/
theorem inner_le_on_hull (H : Finset Plane) {R : ℝ} {a z : Plane}
    (ha : a ∈ H) (hcircle : ∀ h ∈ H, ‖h‖ = R)
    (hbound : ∀ h ∈ H, dist z h ≤ dist z a) :
    ∀ x ∈ convexHull ℝ (H : Set Plane), inner ℝ z a ≤ inner ℝ z x := by
  apply convexHull_min
  · intro h hh
    change inner ℝ z a ≤ inner ℝ z h
    have hdist := hbound h hh
    have hsquare : dist z h ^ 2 ≤ dist z a ^ 2 :=
      pow_le_pow_left₀ dist_nonneg hdist 2
    rw [dist_eq_norm, dist_eq_norm, norm_sub_sq_real, norm_sub_sq_real,
      hcircle h hh, hcircle a ha] at hsquare
    linarith
  · change Convex ℝ {x : Plane | inner ℝ z a ≤ inner ℝ z x}
    exact convex_halfSpace_ge
      { map_add := fun x y => inner_add_right z x y
        map_smul := fun t x => inner_smul_right z x t } _

/-- At most one ambient interior point can be equally distant from two distinct
circle vertices while all its distances to the circle hull are no larger.
The center and nonantipodal endpoint cases are included. -/
theorem double_endpoint_unique (H : Finset Plane) {R L : ℝ} {a b z w : Plane}
    (hR : 0 < R) (hcircle : ∀ h ∈ H, ‖h‖ = R)
    (ha : a ∈ H) (hb : b ∈ H) (hab : a ≠ b) (hL : 0 < L)
    (hz : z ∈ interior (convexHull ℝ (H : Set Plane)))
    (hw : w ∈ interior (convexHull ℝ (H : Set Plane)))
    (hza : dist z a = L) (hzb : dist z b = L)
    (hwa : dist w a = L) (hwb : dist w b = L)
    (hzbound : ∀ h ∈ H, dist z h ≤ L)
    (hwbound : ∀ h ∈ H, dist w h ≤ L) : z = w := by
  by_contra hzw
  have hsum := common_points_sum hab hzw hza hzb hwa hwb
  have contradiction_of_nonzero : ∀ (u v : Plane), u ≠ 0 →
      u ∈ interior (convexHull ℝ (H : Set Plane)) →
      v ∈ interior (convexHull ℝ (H : Set Plane)) →
      dist u a = L → dist u b = L →
      (∀ h ∈ H, dist u h ≤ L) → u + v = a + b → False := by
    intro u v hu hui hvi hua hub hubound huv
    have hlower := inner_le_on_hull H ha hcircle
      (fun h hh => by rw [hua]; exact hubound h hh)
    have hstrictu := inner_lt_of_mem_interior hu hlower hui
    have hstrictv := inner_lt_of_mem_interior hu hlower hvi
    have habinner : inner ℝ u a = inner ℝ u b := by
      have he : ‖u - a‖ ^ 2 = ‖u - b‖ ^ 2 := by
        rw [← dist_eq_norm, ← dist_eq_norm, hua, hub]
      rw [norm_sub_sq_real, norm_sub_sq_real, hcircle a ha, hcircle b hb] at he
      linarith
    have hinner := congrArg (fun x => inner ℝ u x) huv
    rw [inner_add_right, inner_add_right, ← habinner] at hinner
    linarith
  by_cases hz0 : z = 0
  · have hw0 : w ≠ 0 := by intro hw0; exact hzw (hz0.trans hw0.symm)
    exact contradiction_of_nonzero w z hw0 hw hz hwa hwb hwbound
      (by rw [add_comm]; exact hsum)
  · exact contradiction_of_nonzero z w hz0 hz hw hza hzb hzbound hsum

end Erdos132.DoubleEndpoint
