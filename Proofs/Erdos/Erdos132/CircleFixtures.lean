import Erdos.Erdos132.DoubleEndpoint

set_option autoImplicit false

namespace Erdos132.CircleFixtures

open Erdos132.TwoInteriorCircle

/-- A hull containing the four corners of a genuine rectangle contains its open
rectangle in ambient interior, in the original Euclidean plane. -/
theorem rectangle_mem_interior (H : Finset Plane) {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s)
    (hcorners : ∀ i ∈ ({-r, r} : Finset ℝ), ∀ j ∈ ({-s, s} : Finset ℝ),
      WithLp.toLp 2 ![i, j] ∈ H)
    {x : Plane} (hx0 : -r < x 0 ∧ x 0 < r) (hx1 : -s < x 1 ∧ x 1 < s) :
    x ∈ interior (convexHull ℝ (H : Set Plane)) := by
  let U : Set Plane := {y | -r < y 0 ∧ y 0 < r} ∩ {y | -s < y 1 ∧ y 1 < s}
  have hUopen : IsOpen U := by
    exact ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).isOpen_preimage
      _ isOpen_Ioo).inter ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).isOpen_preimage
      _ isOpen_Ioo)
  have hUsub : U ⊆ convexHull ℝ (H : Set Plane) := by
    intro y hy
    obtain ⟨hy0, hy1⟩ := hy
    let t := (y 0 + r) / (2 * r)
    let u := (y 1 + s) / (2 * s)
    have ht0 : 0 ≤ t := le_of_lt (div_pos (by linarith [hy0.1]) (by positivity))
    have ht1 : t ≤ 1 := (div_le_iff₀ (by positivity : 0 < 2 * r)).mpr (by linarith [hy0.2])
    have hu0 : 0 ≤ u := le_of_lt (div_pos (by linarith [hy1.1]) (by positivity))
    have hu1 : u ≤ 1 := (div_le_iff₀ (by positivity : 0 < 2 * s)).mpr (by linarith [hy1.2])
    have hc := convex_convexHull ℝ (H : Set Plane)
    have hvertex : ∀ i ∈ ({-r, r} : Finset ℝ), ∀ j ∈ ({-s, s} : Finset ℝ),
        WithLp.toLp 2 ![i, j] ∈ convexHull ℝ (H : Set Plane) := by
      intro i hi j hj
      exact subset_convexHull ℝ (H : Set Plane) (hcorners i hi j hj)
    have hlow := hc (hvertex (-r) (by simp) (-s) (by simp))
      (hvertex r (by simp) (-s) (by simp)) (sub_nonneg.mpr ht1) ht0 (by ring : (1-t)+t=1)
    have hhigh := hc (hvertex (-r) (by simp) s (by simp))
      (hvertex r (by simp) s (by simp)) (sub_nonneg.mpr ht1) ht0 (by ring : (1-t)+t=1)
    have hcombo := hc hlow hhigh (sub_nonneg.mpr hu1) hu0 (by ring : (1-u)+u=1)
    have he : (1-u) • ((1-t) • WithLp.toLp 2 ![-r, -s] + t • WithLp.toLp 2 ![r, -s]) +
        u • ((1-t) • WithLp.toLp 2 ![-r, s] + t • WithLp.toLp 2 ![r, s]) = y := by
      ext i
      fin_cases i <;> simp [t, u] <;> field_simp <;> ring
    rw [he] at hcombo
    exact hcombo
  apply interior_mono hUsub
  rw [hUopen.interior_eq]
  exact ⟨hx0, hx1⟩

example : ∃ (H : Finset Plane) (R L : ℝ) (a b z w : Plane),
    0 < R ∧ (∀ h ∈ H, ‖h‖ = R) ∧ a ∈ H ∧ b ∈ H ∧ a ≠ b ∧ 0 < L ∧
    z ∈ interior (convexHull ℝ (H : Set Plane)) ∧
    w ∈ interior (convexHull ℝ (H : Set Plane)) ∧
    dist z a = L ∧ dist z b = L ∧ dist w a = L ∧ dist w b = L ∧
    (∀ h ∈ H, dist z h ≤ L) ∧ (∀ h ∈ H, dist w h ≤ L) := by
  classical
  let a : Plane := WithLp.toLp 2 ![3, 4]
  let b : Plane := WithLp.toLp 2 ![-3, 4]
  let c : Plane := WithLp.toLp 2 ![3, -4]
  let e : Plane := WithLp.toLp 2 ![-3, -4]
  let H : Finset Plane := {a, b, c, e}
  have hcircle : ∀ h ∈ H, ‖h‖ = 5 := by
    intro h hh
    simp only [H, Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with rfl | rfl | rfl | rfl <;>
      norm_num [a, b, c, e, EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.sqrt_eq_iff_mul_self_eq]
  have hzero : (0 : Plane) ∈ interior (convexHull ℝ (H : Set Plane)) := by
    apply rectangle_mem_interior H (r := 3) (s := 4) (by norm_num) (by norm_num)
    · intro i hi j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> simp [H, a, b, c, e]
    · norm_num
    · norm_num
  have hab : a ≠ b := by
    intro he
    have he0 := congrArg (fun x : Plane => x 0) he
    norm_num [a, b] at he0
  refine ⟨H, 5, 5, a, b, 0, 0, by norm_num, hcircle,
    by simp [H], by simp [H], hab, by norm_num, hzero, hzero, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [dist_zero_left]
  · exact hcircle a (by simp [H])
  · exact hcircle b (by simp [H])
  · exact hcircle a (by simp [H])
  · exact hcircle b (by simp [H])
  · intro h hh; exact (hcircle h hh).le
  · intro h hh; exact (hcircle h hh).le

/-- A rational seven-vertex circle polygon and three explicit distinct ambient
interiors jointly satisfy the original hypotheses at the first even size, n = 10. -/
theorem rational_three_interior_fixture : ∃ (H : Finset Plane) (z w v : Plane),
    H.card = 7 ∧ (∀ h ∈ H, dist h (0 : Plane) = 5) ∧
    (∀ h ∈ H, h ∈ (convexHull ℝ (H : Set Plane)).extremePoints ℝ) ∧
    z ∈ interior (convexHull ℝ (H : Set Plane)) ∧
    w ∈ interior (convexHull ℝ (H : Set Plane)) ∧
    v ∈ interior (convexHull ℝ (H : Set Plane)) ∧ z ≠ w ∧ z ≠ v ∧ w ≠ v := by
  classical
  let A : Plane := WithLp.toLp 2 ![3, 4]
  let B : Plane := WithLp.toLp 2 ![-3, 4]
  let C : Plane := WithLp.toLp 2 ![3, -4]
  let D : Plane := WithLp.toLp 2 ![-3, -4]
  let E : Plane := WithLp.toLp 2 ![5, 0]
  let F : Plane := WithLp.toLp 2 ![-5, 0]
  let G : Plane := WithLp.toLp 2 ![0, 5]
  let H : Finset Plane := {A, B, C, D, E, F, G}
  let z : Plane := 0
  let w : Plane := WithLp.toLp 2 ![1/8, 0]
  let v : Plane := WithLp.toLp 2 ![0, 1/8]
  have hcard : H.card = 7 := by
    norm_num [H, A, B, C, D, E, F, G, Finset.card_insert_of_notMem,
      WithLp.ext_iff, funext_iff, Fin.forall_fin_two]
  have hcircle : ∀ h ∈ H, dist h (0 : Plane) = 5 := by
    intro h hh
    have hsq : ‖h‖ ^ 2 = 25 := by
      simp only [H, Finset.mem_insert, Finset.mem_singleton] at hh
      rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        norm_num [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, A, B, C, D, E, F, G]
    rw [dist_zero_right]
    nlinarith [norm_nonneg h]
  have hcorners : ∀ i ∈ ({-3, 3} : Finset ℝ), ∀ j ∈ ({-4, 4} : Finset ℝ),
      WithLp.toLp 2 ![i, j] ∈ H := by
    intro i hi j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> simp [H, A, B, C, D]
  have hz : z ∈ interior (convexHull ℝ (H : Set Plane)) :=
    rectangle_mem_interior H (by norm_num) (by norm_num) hcorners (by norm_num [z]) (by norm_num [z])
  have hw : w ∈ interior (convexHull ℝ (H : Set Plane)) :=
    rectangle_mem_interior H (by norm_num) (by norm_num) hcorners (by norm_num [w]) (by norm_num [w])
  have hv : v ∈ interior (convexHull ℝ (H : Set Plane)) :=
    rectangle_mem_interior H (by norm_num) (by norm_num) hcorners (by norm_num [v]) (by norm_num [v])
  have hext : ∀ h ∈ H, h ∈ (convexHull ℝ (H : Set Plane)).extremePoints ℝ := by
    intro h hh
    have hsub : convexHull ℝ (H : Set Plane) ⊆ Metric.closedBall (0 : Plane) 5 :=
      convexHull_min (by intro a ha; simpa [Metric.mem_closedBall, hcircle a ha])
        (convex_closedBall 0 5)
    apply inter_extremePoints_subset_extremePoints_of_subset hsub
    exact ⟨subset_convexHull ℝ _ hh,
      StrictConvexSpace.sphere_subset_extremePoints_closedBall 0 (by norm_num)
        (by simpa [Metric.mem_sphere] using hcircle h hh)⟩
  refine ⟨H, z, w, v, hcard, hcircle, hext, hz, hw, hv, ?_, ?_, ?_⟩
  all_goals
    intro he
    have hcoordinates := congrArg WithLp.ofLp he
    norm_num [z, w, v, funext_iff, Fin.forall_fin_two] at hcoordinates

end Erdos132.CircleFixtures
