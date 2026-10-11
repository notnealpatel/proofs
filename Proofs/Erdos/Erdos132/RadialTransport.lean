import Erdos.Erdos132.TwoInteriorCircle

set_option autoImplicit false

namespace Erdos132.RadialTransport

open TwoInteriorCircle

/-- An origin-fixing isometry taking `u` to a nonzero `v` preserves a finite
origin-centered circle set when the radial support at `u` is included in that at
`v` and every actual radial fiber at `v` has two points. -/
theorem image_eq_of_support_subset (H : Finset Plane) (R : ℝ) (u v : Plane)
    (f : Plane → Plane) (hcircle : ∀ h ∈ H, ‖h‖ = R) (hv : v ≠ 0)
    (hf : Isometry f) (hf0 : f 0 = 0) (hfu : f u = v)
    (hsupport : H.image (fun h => dist u h) ⊆ H.image (fun h => dist v h))
    (hfibers : ∀ d ∈ H.image (fun h => dist v h),
      (H.filter fun h => dist v h = d).card = 2) :
    H.image f = H := by
  classical
  have hnorm (h : Plane) : ‖f h‖ = ‖h‖ := by
    simpa only [hf0, dist_zero_right] using hf.dist_eq h 0
  have hdist (h : Plane) : dist v (f h) = dist u h := by
    simpa only [hfu] using hf.dist_eq u h
  have hmaps : ∀ h ∈ H, f h ∈ H := by
    intro h hh
    let d := dist u h
    have hd : d ∈ H.image (fun h => dist v h) :=
      hsupport (Finset.mem_image.mpr ⟨h, hh, rfl⟩)
    have hcard : (H.filter fun y => dist v y = d).card = 2 := hfibers d hd
    have hbound : ((insert (f h) H).filter fun y => dist y v = d).card ≤ 2 :=
      radial_card_le_two (insert (f h) H) 0 v R d
        (by
          intro y hy
          rcases Finset.mem_insert.mp hy with rfl | hy
          · simpa only [dist_zero_right, hnorm] using hcircle h hh
          · simpa only [dist_zero_right] using hcircle y hy) hv
    have hfilter : (insert (f h) H).filter (fun y => dist y v = d) =
        insert (f h) (H.filter fun y => dist v y = d) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_insert, dist_comm]
      constructor
      · rintro ⟨rfl | hy, hdy⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hy, hdy⟩
      · rintro (rfl | ⟨hy, hdy⟩)
        · exact ⟨Or.inl rfl, hdist h⟩
        · exact ⟨Or.inr hy, hdy⟩
    rw [hfilter] at hbound
    by_contra hnot
    have hnotfiber : f h ∉ H.filter (fun y => dist v y = d) := by
      intro hmem
      exact hnot (Finset.mem_filter.mp hmem).1
    rw [Finset.card_insert_of_notMem hnotfiber, hcard] at hbound
    omega
  have hsubset : H.image f ⊆ H := by
    intro y hy
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hy
    exact hmaps h hh
  apply Finset.eq_of_subset_of_card_le hsubset
  exact (Finset.card_image_of_injective H hf.injective).ge

/-- The common-support, two-fiber radial contract transports the original finite
circle set under any origin-fixing isometry taking `u` to `v`. No equality of
center norms or hull-preservation premise is needed. -/
theorem image_eq_of_common_support (H : Finset Plane) (R : ℝ) (u v : Plane)
    (f : Plane → Plane) (_hR : 0 < R) (hcircle : ∀ h ∈ H, ‖h‖ = R)
    (_hu : u ≠ 0) (hv : v ≠ 0) (hf : Isometry f) (hf0 : f 0 = 0)
    (hfu : f u = v)
    (hsupport : H.image (fun h => dist u h) = H.image (fun h => dist v h))
    (hfibers : ∀ d ∈ H.image (fun h => dist u h),
      (H.filter fun h => dist u h = d).card = 2 ∧
      (H.filter fun h => dist v h = d).card = 2) :
    H.image f = H := by
  apply image_eq_of_support_subset H R u v f hcircle hv hf hf0 hfu
  · exact hsupport.subset
  · intro d hd
    exact (hfibers d (hsupport.symm ▸ hd)).2

/-- Joint nonempty satisfiability of every transport hypothesis: the identity
map, center `(1/2, 0)`, radius one, and the two points `(0, 1)` and `(0, -1)`.
The two actual radial fibers each contain both original points. -/
theorem joint_identity_fixture : ∃ (H : Finset Plane) (R : ℝ) (u v : Plane) (f : Plane → Plane),
    H.card = 2 ∧ 0 < R ∧ (∀ h ∈ H, ‖h‖ = R) ∧
    u ≠ 0 ∧ v ≠ 0 ∧ Isometry f ∧ f 0 = 0 ∧ f u = v ∧
    H.image (fun h => dist u h) = H.image (fun h => dist v h) ∧
    (∀ d ∈ H.image (fun h => dist u h),
      (H.filter fun h => dist u h = d).card = 2 ∧
      (H.filter fun h => dist v h = d).card = 2) := by
  classical
  let A : Plane := WithLp.toLp 2 ![0,1]
  let B : Plane := WithLp.toLp 2 ![0,-1]
  let u : Plane := WithLp.toLp 2 ![1/2,0]
  let H : Finset Plane := {A,B}
  have hcard : H.card = 2 := by
    norm_num [H, A, B, Finset.card_insert_of_notMem, WithLp.ext_iff,
      funext_iff, Fin.forall_fin_two]
  have hcircle : ∀ h ∈ H, ‖h‖ = (1 : ℝ) := by
    intro h hh
    have hs : ‖h‖ ^ 2 = 1 := by
      simp only [H, Finset.mem_insert, Finset.mem_singleton] at hh
      rcases hh with rfl | rfl <;>
        norm_num [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, A, B]
    nlinarith [norm_nonneg h]
  have hu : u ≠ 0 := by
    simp [u, WithLp.ext_iff, funext_iff, Fin.forall_fin_two]
  have hdist : dist u A = dist u B := by
    have hA : (dist u A) ^ 2 = 5/4 := by
      norm_num [dist_eq_norm, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, u, A]
    have hB : (dist u B) ^ 2 = 5/4 := by
      norm_num [dist_eq_norm, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, u, B]
    nlinarith [dist_nonneg (x := u) (y := A), dist_nonneg (x := u) (y := B)]
  have hfiber : ∀ d ∈ H.image (fun h => dist u h),
      (H.filter fun h => dist u h = d).card = 2 := by
    intro d hd
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hd
    have heq : ∀ y ∈ H, dist u y = dist u h := by
      intro y hy
      simp only [H, Finset.mem_insert, Finset.mem_singleton] at hh hy
      rcases hh with rfl | rfl <;> rcases hy with rfl | rfl
      · rfl
      · exact hdist.symm
      · exact hdist
      · rfl
    rw [Finset.filter_eq_self.mpr heq]
    exact hcard
  exact ⟨H, 1, u, u, id, hcard, by norm_num, hcircle, hu, hu,
    isometry_id, rfl, rfl, rfl, fun d hd => ⟨hfiber d hd, hfiber d hd⟩⟩

end Erdos132.RadialTransport
