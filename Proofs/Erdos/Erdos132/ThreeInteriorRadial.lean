import Erdos.Erdos132.TwoInteriorCircle

set_option autoImplicit false

open scoped BigOperators

namespace Erdos132.ThreeInteriorRadial

open Erdos132.TwoInteriorCircle

set_option maxHeartbeats 2000000 in
/-- Eight rational points on the radius-five circle jointly satisfy all radial premises,
including distinct axes. Taking the first center twice also witnesses the common-axis premises. -/
private theorem saturated_circle_fixture : ∃ (H : Finset Plane) (R : ℝ) (u v : Plane),
    6 ≤ H.card ∧ 0 < R ∧ u ≠ 0 ∧ v ≠ 0 ∧
    (∀ h ∈ H, ‖h‖ = R) ∧
    (∀ h ∈ H, (H.filter fun b => dist b u = dist h u).card = 2) ∧
    (∀ h ∈ H, (H.filter fun b => dist b v = dist h v).card = 2) ∧
    (H.image fun h => dist h u) = (H.image fun h => dist h v) ∧
    v ∉ ℝ ∙ u := by
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
  have haxes : v ∉ ℝ ∙ u := by
    intro hm
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hm
    have he := congrArg (fun w : Plane => w 1) ha
    norm_num [u,v] at he
  exact ⟨H,5,u,v,by omega,by norm_num,hu,hv,hcircle,hsatu,hsatv,hsupport,haxes⟩


/-- A saturated radial map on at least six vertices has at least two distinct squared distances. -/
theorem two_le_card_squared_radial_support (H : Finset Plane) (u : Plane)
    (hH : 6 ≤ H.card)
    (hsat : ∀ h ∈ H, (H.filter fun b => dist b u = dist h u).card = 2) :
    2 ≤ (H.image fun h => dist h u ^ 2).card := by
  classical
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < H.card by omega)
  have hex : ∃ b ∈ H, dist b u ≠ dist a u := by
    by_contra hno
    push Not at hno
    have hf : (H.filter fun b => dist b u = dist a u) = H := by
      ext b
      simp only [Finset.mem_filter]
      exact ⟨And.left, fun hb => ⟨hb, hno b hb⟩⟩
    have hc := hsat a ha
    rw [hf] at hc
    omega
  obtain ⟨b, hb, hba⟩ := hex
  have hsq : dist a u ^ 2 ≠ dist b u ^ 2 := by
    intro he
    have hd : dist b u = dist a u := by
      nlinarith [show 0 ≤ dist a u from dist_nonneg, show 0 ≤ dist b u from dist_nonneg]
    exact hba hd
  exact Nat.succ_le_of_lt (Finset.one_lt_card.mpr
    ⟨dist a u ^ 2, Finset.mem_image.mpr ⟨a, ha, rfl⟩,
      dist b u ^ 2, Finset.mem_image.mpr ⟨b, hb, rfl⟩, hsq⟩)

/-- Collinear centers with common saturated radial support have the same norm. -/
theorem norm_eq_of_common_axis (H : Finset Plane) (R : ℝ) (u v : Plane)
    (hH : 6 ≤ H.card)
    (hcircle : ∀ h ∈ H, ‖h‖ = R)
    (hsat : ∀ h ∈ H, (H.filter fun b => dist b u = dist h u).card = 2)
    (hsupport : (H.image fun h => dist h u) = (H.image fun h => dist h v))
    (hv : v ∈ ℝ ∙ u) : ‖u‖ = ‖v‖ := by
  classical
  obtain ⟨a, hav⟩ := Submodule.mem_span_singleton.mp hv
  have hsquare : (H.image fun h => dist h (a • u) ^ 2) =
      (H.image fun h => dist h u ^ 2) := by
    have he := congrArg (fun S : Finset ℝ => S.image (fun d => d ^ 2)) hsupport.symm
    simpa only [Finset.image_image, Function.comp_def, ← hav] using he
  by_cases ha : a = 1
  · simpa only [ha, one_smul] using congrArg norm hav
  · have ha' : a = -1 := opposite_centers_of_support H u R a hcircle ha
      (two_le_card_squared_radial_support H u hH hsat) hsquare
    rw [← hav, ha', neg_one_smul, norm_neg]

/-- Reflection saturation puts the sum of the hull vertices on the radial axis. -/
theorem sum_mem_axis_of_saturated (H : Finset Plane) (R : ℝ) (u : Plane)
    (hu : u ≠ 0) (hcircle : ∀ h ∈ H, ‖h‖ = R)
    (hsat : ∀ h ∈ H, (H.filter fun b => dist b u = dist h u).card = 2) :
    (∑ h ∈ H, h) ∈ ℝ ∙ u := by
  classical
  let r := Submodule.reflection (ℝ ∙ u)
  have hmem : ∀ h ∈ H, r h ∈ H := fun h hh =>
    (reflection_preserves_saturated_hull H u R hu hcircle hsat h hh).1
  have hperm : (∑ h ∈ H, r h) = ∑ h ∈ H, h := by
    apply Finset.sum_bij (fun h _ => r h)
    · exact hmem
    · intro a ha b hb he
      exact r.injective he
    · intro b hb
      exact ⟨r b, hmem b hb, Submodule.reflection_reflection (ℝ ∙ u) b⟩
    · intro a ha
      rfl
  apply (Submodule.reflection_eq_self_iff _).mp
  change r (∑ h ∈ H, h) = ∑ h ∈ H, h
  rw [map_sum]
  exact hperm

/-- Two different radial axes force the sum of all hull vertices to vanish. -/
theorem sum_eq_zero_of_distinct_axes (H : Finset Plane) (R : ℝ) (u v : Plane)
    (hu : u ≠ 0) (hv : v ≠ 0) (hcircle : ∀ h ∈ H, ‖h‖ = R)
    (hsatu : ∀ h ∈ H, (H.filter fun b => dist b u = dist h u).card = 2)
    (hsatv : ∀ h ∈ H, (H.filter fun b => dist b v = dist h v).card = 2)
    (haxes : v ∉ ℝ ∙ u) : (∑ h ∈ H, h) = 0 := by
  classical
  let C := ∑ h ∈ H, h
  have hCu : C ∈ ℝ ∙ u := sum_mem_axis_of_saturated H R u hu hcircle hsatu
  have hCv : C ∈ ℝ ∙ v := sum_mem_axis_of_saturated H R v hv hcircle hsatv
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hCv
  by_cases hb0 : b = 0
  · simpa only [hb0, zero_smul] using hb.symm
  · have he : v = b⁻¹ • C := by
      rw [← hb, smul_smul, inv_mul_cancel₀ hb0, one_smul]
    exact False.elim (haxes (he ▸ (ℝ ∙ u).smul_mem b⁻¹ hCu))

/-- Saturated fibers count every squared radial support value exactly twice. -/
theorem sum_sq_dist_eq_twice_support (H : Finset Plane) (u : Plane)
    (hsat : ∀ h ∈ H, (H.filter fun b => dist b u = dist h u).card = 2) :
    (∑ h ∈ H, dist h u ^ 2) = 2 * ∑ d ∈ H.image (fun h => dist h u), d ^ 2 := by
  classical
  let S := H.image (fun h => dist h u)
  have hmap : ∀ h ∈ H, dist h u ∈ S := fun h hh => Finset.mem_image.mpr ⟨h, hh, rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to' hmap (fun d : ℝ => d ^ 2)]
  calc
    (∑ d ∈ S, ∑ h ∈ H.filter (fun h => dist h u = d), d ^ 2) =
        ∑ d ∈ S, 2 * d ^ 2 := by
      apply Finset.sum_congr rfl
      intro d hd
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hd
      rw [Finset.sum_const, hsat a ha]
      simp
    _ = 2 * ∑ d ∈ S, d ^ 2 := (Finset.mul_sum S (fun d => d ^ 2) 2).symm

/-- A zero hull sum removes the cross term in the sum of squared radial distances. -/
theorem sum_sq_dist_of_sum_eq_zero (H : Finset Plane) (R : ℝ) (u : Plane)
    (hcircle : ∀ h ∈ H, ‖h‖ = R) (hzero : (∑ h ∈ H, h) = 0) :
    (∑ h ∈ H, dist h u ^ 2) = (H.card : ℝ) * (R ^ 2 + ‖u‖ ^ 2) := by
  calc
    (∑ h ∈ H, dist h u ^ 2) = ∑ h ∈ H, (R ^ 2 + ‖u‖ ^ 2 - 2 * inner ℝ h u) := by
      apply Finset.sum_congr rfl
      intro h hh
      rw [dist_eq_norm, norm_sub_sq_real, hcircle h hh]
      ring
    _ = (H.card : ℝ) * (R ^ 2 + ‖u‖ ^ 2) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, ← Finset.mul_sum, ← sum_inner,
        hzero, inner_zero_left, mul_zero, sub_zero, nsmul_eq_mul]

/-- Common saturated radial support on a circle forces equal radii for two nonzero centers.
The common-axis case uses finite affine support width; distinct axes force zero hull centroid. -/
theorem norm_eq_of_saturated_common_support (H : Finset Plane) (R : ℝ) (u v : Plane)
    (hH : 6 ≤ H.card) (_hR : 0 < R) (hu : u ≠ 0) (hv : v ≠ 0)
    (hcircle : ∀ h ∈ H, ‖h‖ = R)
    (hsatu : ∀ h ∈ H, (H.filter fun b => dist b u = dist h u).card = 2)
    (hsatv : ∀ h ∈ H, (H.filter fun b => dist b v = dist h v).card = 2)
    (hsupport : (H.image fun h => dist h u) = (H.image fun h => dist h v)) :
    ‖u‖ = ‖v‖ := by
  classical
  by_cases haxes : v ∈ ℝ ∙ u
  · exact norm_eq_of_common_axis H R u v hH hcircle hsatu hsupport haxes
  · have hzero := sum_eq_zero_of_distinct_axes H R u v hu hv hcircle hsatu hsatv haxes
    have hsum : (∑ h ∈ H, dist h u ^ 2) = ∑ h ∈ H, dist h v ^ 2 := by
      rw [sum_sq_dist_eq_twice_support H u hsatu,
        sum_sq_dist_eq_twice_support H v hsatv, hsupport]
    rw [sum_sq_dist_of_sum_eq_zero H R u hcircle hzero,
      sum_sq_dist_of_sum_eq_zero H R v hcircle hzero] at hsum
    have hc : (0 : ℝ) < H.card := by exact_mod_cast (show 0 < H.card by omega)
    have hsq : ‖u‖ ^ 2 = ‖v‖ ^ 2 := by nlinarith
    nlinarith [norm_nonneg u, norm_nonneg v]

end Erdos132.ThreeInteriorRadial
