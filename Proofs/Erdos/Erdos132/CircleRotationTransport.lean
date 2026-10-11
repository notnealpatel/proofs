import Erdos.Erdos132.CircleRotation
import Erdos.Erdos132.ThreeInteriorRadial
import Erdos.Erdos132.RadialTransport

set_option autoImplicit false

namespace Erdos132.CircleRotationTransport

open TwoInteriorCircle CircleRotation

/-- Common actual radial support with two points in every fiber on a positive-radius
circle of at least six points supplies a transporter in the full geometric stabilizer.
No equal-norm or hull-preservation certificate is assumed. -/
theorem exists_stabilizer_map_of_saturated_common_support
    (H : Finset Plane) (R : ℝ) (u v : Plane)
    (hH : 6 ≤ H.card) (hR : 0 < R) (hu : u ≠ 0) (hv : v ≠ 0)
    (hcircle : ∀ h ∈ H, ‖h‖ = R)
    (hsupport : H.image (fun h => dist u h) = H.image (fun h => dist v h))
    (hfibers : ∀ d ∈ H.image (fun h => dist u h),
      (H.filter fun h => dist u h = d).card = 2 ∧
      (H.filter fun h => dist v h = d).card = 2) :
    ∃ g : Stabilizer H, rotate g.val u = v := by
  classical
  have hsatu : ∀ h ∈ H, (H.filter fun b => dist b u = dist h u).card = 2 := by
    intro h hh
    simpa only [dist_comm] using
      (hfibers (dist u h) (Finset.mem_image.mpr ⟨h, hh, rfl⟩)).1
  have hsatv : ∀ h ∈ H, (H.filter fun b => dist b v = dist h v).card = 2 := by
    intro h hh
    have hd : dist v h ∈ H.image (fun h => dist u h) := by
      rw [hsupport]
      exact Finset.mem_image.mpr ⟨h, hh, rfl⟩
    simpa only [dist_comm] using (hfibers (dist v h) hd).2
  have hnorm : ‖u‖ = ‖v‖ :=
    ThreeInteriorRadial.norm_eq_of_saturated_common_support H R u v
      hH hR hu hv hcircle hsatu hsatv (by simpa only [dist_comm] using hsupport)
  obtain ⟨g, hgu⟩ := exists_rotation_map (norm_pos_iff.mpr hu) rfl hnorm.symm
  have hg0 : rotate g 0 = 0 := by
    apply norm_eq_zero.mp
    rw [norm_rotate, norm_zero]
  have himage : H.image (rotate g) = H :=
    RadialTransport.image_eq_of_common_support H R u v (rotate g)
      hR hcircle hu hv (rotate_isometry g) hg0 hgu hsupport hfibers
  exact ⟨⟨g, (mem_stabilizer_iff_image H g).mpr himage⟩, hgu⟩

set_option maxHeartbeats 2000000 in
/-- The eight points `(±3,±4)` and `(±4,±3)` on the radius-five circle jointly
realize the entire transport contract at the distinct nonzero centers `(1,0)` and
`(0,1)`, and admit a nonidentity transporter in the full stabilizer. The concrete
fiber calculations reuse the private fixture proof from `ThreeInteriorRadial`. -/
theorem joint_eight_point_fixture : ∃ (H : Finset Plane) (u v : Plane),
    H.card = 8 ∧ 0 < (5 : ℝ) ∧ (∀ h ∈ H, ‖h‖ = 5) ∧
    u ≠ 0 ∧ v ≠ 0 ∧ u ≠ v ∧
    H.image (fun h => dist u h) = H.image (fun h => dist v h) ∧
    (∀ d ∈ H.image (fun h => dist u h),
      (H.filter fun h => dist u h = d).card = 2 ∧
      (H.filter fun h => dist v h = d).card = 2) ∧
    ∃ g : Stabilizer H, rotate g.val u = v ∧ g.val ≠ 1 := by
  classical
  let A : Plane := WithLp.toLp 2 ![3,4]
  let B : Plane := WithLp.toLp 2 ![3,-4]
  let C : Plane := WithLp.toLp 2 ![-3,4]
  let D : Plane := WithLp.toLp 2 ![-3,-4]
  let E : Plane := WithLp.toLp 2 ![4,3]
  let F : Plane := WithLp.toLp 2 ![4,-3]
  let G : Plane := WithLp.toLp 2 ![-4,3]
  let J : Plane := WithLp.toLp 2 ![-4,-3]
  let H : Finset Plane := {A,B,C,D,E,F,G,J}
  let u : Plane := WithLp.toLp 2 ![1,0]
  let v : Plane := WithLp.toLp 2 ![0,1]
  have hcard : H.card = 8 := by
    norm_num [H,A,B,C,D,E,F,G,J,Finset.card_insert_of_notMem,WithLp.ext_iff,
      funext_iff,Fin.forall_fin_two]
  have hcircle : ∀ h ∈ H, ‖h‖ = 5 := by
    intro h hh
    have hs : ‖h‖ ^ 2 = 25 := by
      simp only [H,Finset.mem_insert,Finset.mem_singleton] at hh
      rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        norm_num [EuclideanSpace.norm_sq_eq,Fin.sum_univ_two,A,B,C,D,E,F,G,J]
    nlinarith [norm_nonneg h]
  have heq : ∀ (a b w : Plane), dist a w = dist b w ↔ dist a w ^ 2 = dist b w ^ 2 := by
    intro a b w
    constructor
    · intro he
      rw [he]
    · intro he
      nlinarith [show 0 ≤ dist a w from dist_nonneg, show 0 ≤ dist b w from dist_nonneg]
  have hAu : dist A u ^ 2 = 20 := by norm_num [A,u,dist_eq_norm,EuclideanSpace.norm_sq_eq,Fin.sum_univ_two]
  have hBu : dist B u ^ 2 = 20 := by norm_num [B,u,dist_eq_norm,EuclideanSpace.norm_sq_eq,Fin.sum_univ_two]
  have hCu : dist C u ^ 2 = 32 := by norm_num [C,u,dist_eq_norm,EuclideanSpace.norm_sq_eq,Fin.sum_univ_two]
  have hDu : dist D u ^ 2 = 32 := by norm_num [D,u,dist_eq_norm,EuclideanSpace.norm_sq_eq,Fin.sum_univ_two]
  have hEu : dist E u ^ 2 = 18 := by norm_num [E,u,dist_eq_norm,EuclideanSpace.norm_sq_eq,Fin.sum_univ_two]
  have hFu : dist F u ^ 2 = 18 := by norm_num [F,u,dist_eq_norm,EuclideanSpace.norm_sq_eq,Fin.sum_univ_two]
  have hGu : dist G u ^ 2 = 34 := by norm_num [G,u,dist_eq_norm,EuclideanSpace.norm_sq_eq,Fin.sum_univ_two]
  have hJu : dist J u ^ 2 = 34 := by norm_num [J,u,dist_eq_norm,EuclideanSpace.norm_sq_eq,Fin.sum_univ_two]
  have hAv : dist A v ^ 2 = 18 := by norm_num [A,v,dist_eq_norm,EuclideanSpace.norm_sq_eq,Fin.sum_univ_two]
  have hBv : dist B v ^ 2 = 34 := by norm_num [B,v,dist_eq_norm,EuclideanSpace.norm_sq_eq,Fin.sum_univ_two]
  have hCv : dist C v ^ 2 = 18 := by norm_num [C,v,dist_eq_norm,EuclideanSpace.norm_sq_eq,Fin.sum_univ_two]
  have hDv : dist D v ^ 2 = 34 := by norm_num [D,v,dist_eq_norm,EuclideanSpace.norm_sq_eq,Fin.sum_univ_two]
  have hEv : dist E v ^ 2 = 20 := by norm_num [E,v,dist_eq_norm,EuclideanSpace.norm_sq_eq,Fin.sum_univ_two]
  have hFv : dist F v ^ 2 = 32 := by norm_num [F,v,dist_eq_norm,EuclideanSpace.norm_sq_eq,Fin.sum_univ_two]
  have hGv : dist G v ^ 2 = 20 := by norm_num [G,v,dist_eq_norm,EuclideanSpace.norm_sq_eq,Fin.sum_univ_two]
  have hJv : dist J v ^ 2 = 32 := by norm_num [J,v,dist_eq_norm,EuclideanSpace.norm_sq_eq,Fin.sum_univ_two]
  have hsatu : ∀ h ∈ H, (H.filter fun b => dist b u = dist h u).card = 2 := by
    intro h hh
    simp only [H,Finset.mem_insert,Finset.mem_singleton] at hh
    rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_rw [heq] <;>
      norm_num [H,hAu,hBu,hCu,hDu,hEu,hFu,hGu,hJu,
        Finset.filter_insert,Finset.filter_singleton] <;>
      norm_num [A,B,C,D,E,F,G,J,WithLp.ext_iff,funext_iff,Fin.forall_fin_two]
  have hsatv : ∀ h ∈ H, (H.filter fun b => dist b v = dist h v).card = 2 := by
    intro h hh
    simp only [H,Finset.mem_insert,Finset.mem_singleton] at hh
    rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_rw [heq] <;>
      norm_num [H,hAv,hBv,hCv,hDv,hEv,hFv,hGv,hJv,
        Finset.filter_insert,Finset.filter_singleton] <;>
      norm_num [A,B,C,D,E,F,G,J,WithLp.ext_iff,funext_iff,Fin.forall_fin_two]
  have hsupport : (H.image fun h => dist h u) = (H.image fun h => dist h v) := by
    norm_num [H,A,B,C,D,E,F,G,J,u,v,dist_eq_norm,EuclideanSpace.norm_eq,
      Fin.sum_univ_two]
    ext d
    simp only [Finset.mem_insert, Finset.mem_singleton, or_assoc, or_left_comm, or_comm]
  have hu : u ≠ 0 := by
    norm_num [u,WithLp.ext_iff,funext_iff,Fin.forall_fin_two]
  have hv : v ≠ 0 := by
    norm_num [v,WithLp.ext_iff,funext_iff,Fin.forall_fin_two]
  have huv : u ≠ v := by
    intro he
    have hc := congrArg (fun w : Plane => w 0) he
    norm_num [u, v] at hc
  have hsupport' : H.image (fun h => dist u h) = H.image (fun h => dist v h) := by
    simpa only [dist_comm] using hsupport
  have hfibers : ∀ d ∈ H.image (fun h => dist u h),
      (H.filter fun h => dist u h = d).card = 2 ∧
      (H.filter fun h => dist v h = d).card = 2 := by
    intro d hd
    have hdu := hd
    rw [hsupport'] at hd
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hdu
    obtain ⟨b, hb, hbd⟩ := Finset.mem_image.mp hd
    constructor
    · simpa only [dist_comm] using hsatu a ha
    · rw [← hbd]
      simpa only [dist_comm] using hsatv b hb
  obtain ⟨g, hgu⟩ := exists_stabilizer_map_of_saturated_common_support H 5 u v
    (by omega) (by norm_num) hu hv hcircle hsupport' hfibers
  have hg1 : g.val ≠ 1 := by
    intro he
    apply huv
    simpa only [he, rotate_one] using hgu
  exact ⟨H, u, v, hcard, by norm_num, hcircle, hu, hv, huv,
    hsupport', hfibers, g, hgu, hg1⟩

end Erdos132.CircleRotationTransport
