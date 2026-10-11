import Erdos.Erdos132.ThreeInteriorCounting
import Erdos.Erdos132.CircleFixtures

set_option autoImplicit false

open scoped BigOperators

namespace Erdos132.HullOutlierOutside

open Erdos132.TwoInteriorCircle

private theorem interior_not_mem_extreme_generators (A : Finset Plane) (p : Plane)
    (hext : ∀ a ∈ A, a ∈ (convexHull ℝ (A : Set Plane)).extremePoints ℝ)
    (hp : p ∈ interior (convexHull ℝ (A : Set Plane))) : p ∉ A := by
  intro hpA
  exact Set.disjoint_left.mp (disjoint_interior_extremePoints (convexHull ℝ (A : Set Plane)))
    hp (hext p hpA)

/-- Six circle vertices, one off-circle extreme vertex, and two distinct ambient
interior points give nine actual distinct points. Adding the interiors preserves
the positive diameter of the augmented seven-vertex hull, not that of the circle. -/
theorem original_geometry_card_and_diameter (C : Finset Plane) (O u z : Plane) (R : ℝ)
    (hC : C.card = 6) (hcircle : ∀ c ∈ C, dist c O = R)
    (hu : dist u O ≠ R)
    (hext : ∀ a ∈ insert u C,
      a ∈ (convexHull ℝ ((insert u C : Finset Plane) : Set Plane)).extremePoints ℝ)
    (hO : O ∈ interior (convexHull ℝ ((insert u C : Finset Plane) : Set Plane)))
    (hz : z ∈ interior (convexHull ℝ ((insert u C : Finset Plane) : Set Plane)))
    (hOz : O ≠ z) :
    (insert O (insert z (insert u C))).card = 9 ∧
      Metric.diam ((insert O (insert z (insert u C)) : Finset Plane) : Set Plane) =
        Metric.diam ((insert u C : Finset Plane) : Set Plane) ∧
      0 < Metric.diam ((insert O (insert z (insert u C)) : Finset Plane) : Set Plane) := by
  classical
  have huC : u ∉ C := fun hm => hu (hcircle u hm)
  have hAcard : (insert u C).card = 7 := by simp [huC, hC]
  have hOA := interior_not_mem_extreme_generators (insert u C) O hext hO
  have hzA := interior_not_mem_extreme_generators (insert u C) z hext hz
  have hcard : (insert O (insert z (insert u C))).card = 9 := by
    simp [hOA, hzA, hOz, huC, hC]
  have hdiam := diam_insert_interiors (insert u C) O z hO hz
  refine ⟨hcard, hdiam, ?_⟩
  rw [hdiam]
  exact diam_pos (insert u C) (by omega)

private theorem multiplicity_pos_of_occurs (X : Finset Plane) (d : ℝ)
    (hd : 0 < d) (hocc : ∃ a ∈ X, ∃ b ∈ X, dist a b = d) :
    0 < multiplicity X d := by
  classical
  obtain ⟨a, ha, b, hb, habd⟩ := hocc
  have hab : a ≠ b := by
    intro he
    rw [he, dist_self] at habd
    linarith
  apply Finset.card_pos.mpr
  exact ⟨s(a,b), Finset.mem_filter.mpr
    ⟨(mk_mem_pairs X a b).mpr ⟨ha,hb,hab⟩, habd⟩⟩

/-- From the original augmented-hull geometry, failure of the desired small
positive non-diameter class forces exactly three actual distance values. Every
circle-to-offcenter-interior fiber has two points, and its image is the entire
whole-configuration non-diameter support. This is the original-geometry counting
reduction; it does not yet exclude the outside branch. -/
theorem original_target_or_saturation (C : Finset Plane) (O u z : Plane) (R : ℝ)
    (hC : C.card = 6) (hcircle : ∀ c ∈ C, dist c O = R)
    (hu : dist u O ≠ R)
    (hext : ∀ a ∈ insert u C,
      a ∈ (convexHull ℝ ((insert u C : Finset Plane) : Set Plane)).extremePoints ℝ)
    (hO : O ∈ interior (convexHull ℝ ((insert u C : Finset Plane) : Set Plane)))
    (hz : z ∈ interior (convexHull ℝ ((insert u C : Finset Plane) : Set Plane)))
    (hOz : O ≠ z) :
    let X := insert O (insert z (insert u C))
    let S := nonDiameterDistances X
    X.card = 9 ∧
      ((∃ d : ℝ, 0 < d ∧ d < Metric.diam (X : Set Plane) ∧
        1 ≤ multiplicity X d ∧ multiplicity X d ≤ 9) ∨
      (S.card = 3 ∧ C.image (fun c => dist c z) = S ∧
        (∀ d ∈ S, (C.filter fun c => dist c z = d).card = 2) ∧
        (∀ c ∈ C, (C.filter fun b => dist b z = dist c z).card = 2) ∧
        (∀ d ∈ S, 10 ≤ multiplicity X d))) := by
  classical
  let A := insert u C
  let X := insert O (insert z A)
  let S := nonDiameterDistances X
  change X.card = 9 ∧ _
  obtain ⟨hcard, hdiam, _hdiampos⟩ := original_geometry_card_and_diameter
    C O u z R hC hcircle hu hext hO hz hOz
  change X.card = 9 at hcard
  change Metric.diam (X : Set Plane) = Metric.diam (A : Set Plane) at hdiam
  refine ⟨hcard, ?_⟩
  by_cases htarget : ∃ d : ℝ, 0 < d ∧ d < Metric.diam (X : Set Plane) ∧
      1 ≤ multiplicity X d ∧ multiplicity X d ≤ 9
  · exact Or.inl htarget
  · apply Or.inr
    have hlarge : ∀ d ∈ S, 10 ≤ multiplicity X d := by
      intro d hd
      obtain ⟨hpos, hlt, hocc⟩ :=
        (Erdos132.ThreeInteriorCounting.mem_nonDiameterDistances_iff_positive X d).mp hd
      have hmu := multiplicity_pos_of_occurs X d hpos hocc
      have hn : ¬multiplicity X d ≤ 9 := fun hm => htarget ⟨d,hpos,hlt,hmu,hm⟩
      omega
    have huC : u ∉ C := fun hm => hu (hcircle u hm)
    have hAcard : A.card = 7 := by simp [A, huC, hC]
    have hzA := interior_not_mem_extreme_generators A z hext hz
    have hmap : ∀ c ∈ C, dist c z ∈ S := by
      intro c hc
      apply (mem_nonDiameterDistances X (dist c z)).mpr
      refine ⟨⟨c, by simp [X,A,hc], z, by simp [X], ?_, rfl⟩, ?_⟩
      · intro he
        exact hzA (he ▸ Finset.mem_insert_of_mem hc)
      · rw [hdiam, dist_comm]
        exact dist_lt_diam_hull A (by omega) hz
          (subset_convexHull ℝ (A : Set Plane) (Finset.mem_insert_of_mem hc))
    have hcap : ∀ d ∈ S, (C.filter fun c => dist c z = d).card ≤ 2 := by
      intro d _hd
      exact radial_card_le_two C O z R d hcircle hOz.symm
    have hlower : C.card ≤ 2 * S.card :=
      Finset.card_le_mul_card_image_of_maps_to hmap 2 hcap
    have hb := nonDiameter_pair_budget X (by omega) (by
      intro d hd
      rw [hcard]
      exact hlarge d hd)
    have hbudget : S.card * 10 + 1 ≤ 36 := by
      norm_num [hcard, Nat.choose_two_right] at hb
      exact hb
    have hScard : S.card = 3 := by omega
    have hfiber : ∀ d ∈ S, (C.filter fun c => dist c z = d).card = 2 :=
      saturated_fibers C S (fun c => dist c z) hmap hcap (by omega)
    have hsupport : C.image (fun c => dist c z) = S := by
      apply Finset.Subset.antisymm
      · intro d hd
        obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hd
        exact hmap c hc
      · intro d hd
        obtain ⟨c,hc⟩ := Finset.card_pos.mp (show 0 < (C.filter fun c => dist c z = d).card by
          rw [hfiber d hd]
          decide)
        exact Finset.mem_image.mpr ⟨c,(Finset.mem_filter.mp hc).1,(Finset.mem_filter.mp hc).2⟩
    exact ⟨hScard,hsupport,hfiber,fun c hc => hfiber (dist c z) (hmap c hc),hlarge⟩

set_option maxHeartbeats 1000000 in
/-- The six rational unit-circle points, outlier `(6/5,0)`, and interior `(11/10,0)`
jointly realize every original outside-branch geometric hypothesis. Extremeness
is certified by tangent enclosing balls; both interiors belong to the actual
augmented hull. The impossible failed-target hypothesis is not assumed. -/
theorem original_outside_geometry_fixture : ∃ (C : Finset Plane) (u z : Plane),
    C.card = 6 ∧ (∀ c ∈ C, dist c (0 : Plane) = 1) ∧ dist u (0 : Plane) ≠ 1 ∧
    (∀ a ∈ insert u C,
      a ∈ (convexHull ℝ ((insert u C : Finset Plane) : Set Plane)).extremePoints ℝ) ∧
    (0 : Plane) ∈ interior (convexHull ℝ ((insert u C : Finset Plane) : Set Plane)) ∧
    z ∈ interior (convexHull ℝ ((insert u C : Finset Plane) : Set Plane)) ∧
    (0 : Plane) ≠ z ∧ 1 < dist z (0 : Plane) := by
  classical
  let p : Plane := WithLp.toLp 2 ![4/5,3/5]
  let q : Plane := WithLp.toLp 2 ![4/5,-3/5]
  let s : Plane := WithLp.toLp 2 ![-4/5,3/5]
  let t : Plane := WithLp.toLp 2 ![-4/5,-3/5]
  let v : Plane := WithLp.toLp 2 ![0,1]
  let w : Plane := WithLp.toLp 2 ![0,-1]
  let C : Finset Plane := {p,q,s,t,v,w}
  let u : Plane := WithLp.toLp 2 ![6/5,0]
  let z : Plane := WithLp.toLp 2 ![11/10,0]
  let A := insert u C
  have hC : C.card = 6 := by
    norm_num [C,p,q,s,t,v,w,Finset.card_insert_of_notMem,WithLp.ext_iff,
      funext_iff,Fin.forall_fin_two]
  have hcircle : ∀ c ∈ C, dist c (0 : Plane) = 1 := by
    intro c hc
    have hsq : ‖c‖ ^ 2 = 1 := by
      simp only [C,Finset.mem_insert,Finset.mem_singleton] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
        norm_num [p,q,s,t,v,w,EuclideanSpace.norm_sq_eq,Fin.sum_univ_two]
    rw [dist_zero_right]
    nlinarith [norm_nonneg c]
  have hu : dist u (0 : Plane) = 6/5 := by
    rw [dist_zero_right]
    have hsq : ‖u‖ ^ 2 = (6/5 : ℝ)^2 := by
      norm_num [u,EuclideanSpace.norm_sq_eq,Fin.sum_univ_two]
    nlinarith [norm_nonneg u]
  have hzdist : dist z (0 : Plane) = 11/10 := by
    rw [dist_zero_right]
    have hsq : ‖z‖ ^ 2 = (11/10 : ℝ)^2 := by
      norm_num [z,EuclideanSpace.norm_sq_eq,Fin.sum_univ_two]
    nlinarith [norm_nonneg z]
  have hballs : ∀ c ∈ C, ∀ a ∈ A, dist a ((-6 : ℝ) • c) ≤ 7 := by
    intro c hc a ha
    have hsq : dist a ((-6 : ℝ) • c) ^ 2 ≤ 49 := by
      simp only [C,Finset.mem_insert,Finset.mem_singleton] at hc
      simp only [A,C,Finset.mem_insert,Finset.mem_singleton] at ha
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
        rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        norm_num [p,q,s,t,v,w,u,dist_eq_norm,EuclideanSpace.norm_sq_eq,Fin.sum_univ_two]
    nlinarith [dist_nonneg (x := a) (y := (-6 : ℝ) • c)]
  have hext : ∀ a ∈ A, a ∈ (convexHull ℝ (A : Set Plane)).extremePoints ℝ := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | haC
    · have hsub : convexHull ℝ (A : Set Plane) ⊆ Metric.closedBall (0 : Plane) (6/5) := by
        apply convexHull_min _ (convex_closedBall _ _)
        intro a ha
        rcases Finset.mem_insert.mp ha with rfl | haC
        · simp [Metric.mem_closedBall,hu]
        · norm_num [Metric.mem_closedBall,hcircle a haC]
      apply inter_extremePoints_subset_extremePoints_of_subset hsub
      refine ⟨subset_convexHull ℝ (A : Set Plane) (by simp [A]), ?_⟩
      exact StrictConvexSpace.sphere_subset_extremePoints_closedBall 0 (by norm_num)
        (by simpa [Metric.mem_sphere] using hu)
    · have hsub : convexHull ℝ (A : Set Plane) ⊆ Metric.closedBall ((-6 : ℝ) • a) 7 := by
        apply convexHull_min _ (convex_closedBall _ _)
        intro b hb
        exact hballs a haC b hb
      apply inter_extremePoints_subset_extremePoints_of_subset hsub
      refine ⟨subset_convexHull ℝ (A : Set Plane) ha, ?_⟩
      apply StrictConvexSpace.sphere_subset_extremePoints_closedBall _ (by norm_num)
      rw [Metric.mem_sphere,dist_eq_norm]
      have he : a - (-6 : ℝ) • a = (7 : ℝ) • a := by module
      rw [he,norm_smul]
      have haone : ‖a‖ = 1 := by simpa only [dist_zero_right] using hcircle a haC
      simp [haone]
  have hcorners : ∀ i ∈ ({-(4/5),4/5} : Finset ℝ), ∀ j ∈ ({-(3/5),3/5} : Finset ℝ),
      WithLp.toLp 2 ![i,j] ∈ A := by
    intro i hi j hj
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> norm_num [A,C,p,q,s,t]
  have hzero : (0 : Plane) ∈ interior (convexHull ℝ (A : Set Plane)) :=
    Erdos132.CircleFixtures.rectangle_mem_interior A (by norm_num) (by norm_num) hcorners (by norm_num) (by norm_num)
  have hz : z ∈ interior (convexHull ℝ (A : Set Plane)) := by
    apply (convex_convexHull ℝ (A : Set Plane)).openSegment_interior_self_subset_interior
      hzero (y := u) (subset_convexHull ℝ (A : Set Plane) (by simp [A]))
    refine ⟨1/12,11/12,by norm_num,by norm_num,by norm_num,?_⟩
    ext i
    fin_cases i <;> norm_num [u,z]
  refine ⟨C,u,z,hC,hcircle,by rw [hu]; norm_num,hext,hzero,hz,?_,?_⟩
  · intro he
    have hc := congrArg (fun x : Plane => x 0) he
    norm_num [z] at hc
  · rw [hzdist]
    norm_num

private theorem reflected_chord_sq (z c : Plane) (hz : z ≠ 0) :
    dist c ((ℝ ∙ z).reflection c) ^ 2 * ‖z‖ ^ 2 =
      4 * (‖c‖ ^ 2 * ‖z‖ ^ 2 - (inner ℝ z c)^2) := by
  have hn : ‖z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
  rw [dist_eq_norm,Submodule.reflection_singleton_apply]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  have he : c - (2 • (inner ℝ z c / ‖z‖ ^ 2) • z - c) =
      (2 : ℝ) • c - (2 * (inner ℝ z c / ‖z‖ ^ 2)) • z := by module
  rw [he,norm_sub_sq_real]
  simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,inner_smul_left,inner_smul_right,
    real_inner_comm c z]
  norm_num only [map_ofNat]
  field_simp [hn]
  ring

private theorem exists_generator_inner_gt (A : Finset Plane) (p z : Plane) (hz : z ≠ 0)
    (hp : p ∈ interior (convexHull ℝ (A : Set Plane))) :
    ∃ a ∈ A, inner ℝ z p < inner ℝ z a := by
  by_contra hno
  push Not at hno
  have hsub : convexHull ℝ (A : Set Plane) ⊆ {x : Plane | inner ℝ z x ≤ inner ℝ z p} := by
    apply convexHull_min hno
    exact convex_halfSpace_le (f := fun x : Plane => inner ℝ z x)
      ⟨fun x y => inner_add_right z x y, fun a x => inner_smul_right z x a⟩ _
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hp)
  let t : ℝ := ε / (2 * (‖z‖ + 1))
  have hden : 0 < 2 * (‖z‖ + 1) := by positivity
  have ht : 0 < t := div_pos hε hden
  have htε : t * ‖z‖ < ε := by
    dsimp [t]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hden).mpr
    nlinarith [norm_nonneg z]
  have hqp : dist (p + t • z) p = t * ‖z‖ := by
    simp [dist_eq_norm,norm_smul,Real.norm_eq_abs,abs_of_pos ht]
  have hq : p + t • z ∈ convexHull ℝ (A : Set Plane) := hball (by
    simpa only [Metric.mem_ball,hqp] using htε)
  have hbound := hsub hq
  have hself : inner ℝ z z = ‖z‖ ^ 2 := real_inner_self_eq_norm_sq z
  simp only [Set.mem_ofPred_eq,inner_add_right,inner_smul_right,hself] at hbound
  have hnorm : 0 < ‖z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
  nlinarith

private theorem outside_projection_separation (C : Finset Plane) (u z : Plane) (R : ℝ) (hR : 0 < R)
    (hcircle : ∀ c ∈ C, ‖c‖ = R) (houtside : R ≤ ‖z‖)
    (hO : (0 : Plane) ∈ interior (convexHull ℝ ((insert u C : Finset Plane) : Set Plane)))
    (hz : z ∈ interior (convexHull ℝ ((insert u C : Finset Plane) : Set Plane))) :
    ‖z‖ ^ 2 < inner ℝ z u ∧ ‖z‖ < ‖u‖ ∧ ∃ c ∈ C, inner ℝ z c < 0 := by
  classical
  have hzpos : 0 < ‖z‖ := hR.trans_le houtside
  have hz0 : z ≠ 0 := norm_pos_iff.mp hzpos
  obtain ⟨a,ha,hagt⟩ := exists_generator_inner_gt (insert u C) z z hz0 hz
  have huinner : ‖z‖ ^ 2 < inner ℝ z u := by
    rw [real_inner_self_eq_norm_sq] at hagt
    rcases Finset.mem_insert.mp ha with rfl | haC
    · exact hagt
    · have hbound := real_inner_le_norm z a
      rw [hcircle a haC] at hbound
      have hm := mul_le_mul_of_nonneg_left houtside (norm_nonneg z)
      nlinarith
  have hunorm : ‖z‖ < ‖u‖ := by
    have hbound := real_inner_le_norm z u
    nlinarith
  obtain ⟨a,ha,hneg⟩ := exists_generator_inner_gt (insert u C) 0 (-z) (neg_ne_zero.mpr hz0) hO
  simp only [inner_zero_right,inner_neg_left,neg_pos] at hneg
  have haC : a ∈ C := by
    rcases Finset.mem_insert.mp ha with hau | haC
    · rw [hau] at hneg
      nlinarith [sq_nonneg ‖z‖]
    · exact haC
  exact ⟨huinner,hunorm,a,haC,hneg⟩

/-- Original zero-centered outside geometry yields either the desired actual
multiplicity class or the precise three-value reflected-circle chord obstruction.
Every support and separation fact is derived, rather than assumed as a certificate. -/
theorem original_outside_target_or_chord_obstruction (C : Finset Plane) (u z : Plane) (R : ℝ)
    (hC : C.card = 6) (hR : 0 < R) (hcircle : ∀ c ∈ C, ‖c‖ = R)
    (hu : ‖u‖ ≠ R)
    (hext : ∀ a ∈ insert u C,
      a ∈ (convexHull ℝ ((insert u C : Finset Plane) : Set Plane)).extremePoints ℝ)
    (hO : (0 : Plane) ∈ interior (convexHull ℝ ((insert u C : Finset Plane) : Set Plane)))
    (hz : z ∈ interior (convexHull ℝ ((insert u C : Finset Plane) : Set Plane)))
    (houtside : R ≤ ‖z‖) :
    let X := insert (0 : Plane) (insert z (insert u C))
    let δ := Metric.diam (X : Set Plane) ^ 2
    X.card = 9 ∧
      ((∃ d : ℝ, 0 < d ∧ d < Metric.diam (X : Set Plane) ∧
        1 ≤ multiplicity X d ∧ multiplicity X d ≤ 9) ∨
      ∃ T : Finset ℝ, T.card = 3 ∧
        (∀ t ∈ T, 0 < t ∧ t < δ ∧ ∃ c ∈ C, dist c z ^ 2 = t) ∧
        R ^ 2 ∈ T ∧ ‖z‖ ^ 2 ∈ T ∧ ‖u‖ ^ 2 ∈ T ∧
        ‖z‖ ^ 2 < inner ℝ z u ∧ ‖z‖ < ‖u‖ ∧
        (∃ c ∈ C, inner ℝ z c < 0) ∧
        (∀ c ∈ C, dist c z ^ 2 ∈ T) ∧
        (∀ c ∈ C, (ℝ ∙ z).reflection c ∈ C ∧ (ℝ ∙ z).reflection c ≠ c ∧
          dist c z ^ 2 = R ^ 2 + ‖z‖ ^ 2 - 2 * inner ℝ z c ∧
          dist c ((ℝ ∙ z).reflection c) ^ 2 * ‖z‖ ^ 2 =
            4 * (R ^ 2 * ‖z‖ ^ 2 - (inner ℝ z c) ^ 2)) ∧
        (∀ a ∈ C, ∀ b ∈ C, a ≠ b → dist a b ^ 2 ∈ T ∨ dist a b ^ 2 = δ)) := by
  classical
  let A := insert u C
  let X := insert (0 : Plane) (insert z A)
  let S := nonDiameterDistances X
  let δ := Metric.diam (X : Set Plane) ^ 2
  change X.card = 9 ∧ _
  have hzpos : 0 < ‖z‖ := hR.trans_le houtside
  have hz0 : z ≠ 0 := norm_pos_iff.mp hzpos
  have hcircle0 : ∀ c ∈ C, dist c (0 : Plane) = R := by
    simpa only [dist_zero_right] using hcircle
  have hu0 : dist u (0 : Plane) ≠ R := by simpa only [dist_zero_right] using hu
  obtain ⟨hcard,hcase⟩ := original_target_or_saturation C 0 u z R hC hcircle0 hu0 hext hO hz hz0.symm
  change X.card = 9 at hcard
  refine ⟨hcard,?_⟩
  rcases hcase with htarget | ⟨hS,hsupport,hfibers,hsat,_hlarge⟩
  · exact Or.inl htarget
  · apply Or.inr
    let T := S.image (fun d => d ^ 2)
    have hSpos : ∀ d ∈ S, 0 < d ∧ d < Metric.diam (X : Set Plane) := by
      intro d hd
      obtain ⟨hp,hl,_⟩ :=
        (Erdos132.ThreeInteriorCounting.mem_nonDiameterDistances_iff_positive X d).mp hd
      exact ⟨hp,hl⟩
    have hTcard : T.card = 3 := by
      have hi : Set.InjOn (fun d : ℝ => d ^ 2) (S : Set ℝ) := by
        intro a ha b hb he
        have hapos := (hSpos a ha).1
        have hbpos := (hSpos b hb).1
        nlinarith
      exact (Finset.card_image_iff.mpr hi).trans hS
    have hT : ∀ t ∈ T, 0 < t ∧ t < δ ∧ ∃ c ∈ C, dist c z ^ 2 = t := by
      intro t ht
      obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨hdpos,hdlt⟩ := hSpos d hd
      have hdimage : d ∈ C.image (fun c => dist c z) := hsupport.symm ▸ hd
      obtain ⟨c,hc,hcd⟩ := Finset.mem_image.mp hdimage
      refine ⟨sq_pos_of_pos hdpos,?_,c,hc,?_⟩
      · dsimp [δ]
        nlinarith [Metric.diam_nonneg (s := (X : Set Plane))]
      · rw [hcd]
    have hXhull : (X : Set Plane) ⊆ convexHull ℝ (A : Set Plane) := by
      intro a ha
      simp only [X,Finset.mem_coe,Finset.mem_insert] at ha
      rcases ha with rfl | rfl | ha
      · exact interior_subset hO
      · exact interior_subset hz
      · exact subset_convexHull ℝ (A : Set Plane) ha
    obtain ⟨_hc,hdiam,hdiampos⟩ := original_geometry_card_and_diameter C 0 u z R hC hcircle0 hu0 hext hO hz hz0.symm
    change Metric.diam (X : Set Plane) = Metric.diam (A : Set Plane) at hdiam
    have hcenter : ∀ a ∈ X, a ≠ 0 → ‖a‖ ∈ S := by
      intro a ha ha0
      apply (mem_nonDiameterDistances X ‖a‖).mpr
      refine ⟨⟨a,ha,0,by simp [X],ha0,dist_zero_right a⟩,?_⟩
      rw [← dist_zero_right,dist_comm,hdiam]
      have hAcard : 2 ≤ A.card := (Finset.card_le_card (Finset.subset_insert u C)).trans' (by omega)
      exact dist_lt_diam_hull A hAcard hO (hXhull ha)
    have hsep := Erdos132.HullOutlierOutside.outside_projection_separation C u z R hR hcircle houtside hO hz
    have huPos : 0 < ‖u‖ := hzpos.trans hsep.2.1
    have hRmem : R ^ 2 ∈ T := by
      obtain ⟨c,hc⟩ := Finset.card_pos.mp (show 0 < C.card by omega)
      have hc0 : c ≠ 0 := norm_pos_iff.mp ((hcircle c hc).symm ▸ hR)
      have hcS := hcenter c (by simp [X,A,hc]) hc0
      rw [hcircle c hc] at hcS
      exact Finset.mem_image.mpr ⟨R,hcS,rfl⟩
    have hzmem : ‖z‖ ^ 2 ∈ T := Finset.mem_image.mpr ⟨‖z‖,hcenter z (by simp [X]) hz0,rfl⟩
    have humem : ‖u‖ ^ 2 ∈ T := Finset.mem_image.mpr
      ⟨‖u‖,hcenter u (by simp [X,A]) (norm_pos_iff.mp huPos),rfl⟩
    have hradmem : ∀ c ∈ C, dist c z ^ 2 ∈ T := by
      intro c hc
      have hsupportS : C.image (fun c => dist c z) = S := hsupport
      have hd : dist c z ∈ S := by
        rw [← hsupportS]
        exact Finset.mem_image.mpr ⟨c,hc,rfl⟩
      exact Finset.mem_image.mpr ⟨dist c z,hd,rfl⟩
    refine ⟨T,hTcard,hT,hRmem,hzmem,humem,hsep.1,hsep.2.1,hsep.2.2,hradmem,?_,?_⟩
    · intro c hc
      obtain ⟨hr,hrne⟩ := reflection_preserves_saturated_hull C z R hz0 hcircle hsat c hc
      refine ⟨hr,hrne,?_,?_⟩
      · rw [dist_eq_norm,norm_sub_sq_real,hcircle c hc,real_inner_comm c z]
        ring
      · simpa only [hcircle c hc] using Erdos132.HullOutlierOutside.reflected_chord_sq z c hz0
    · intro a ha b hb hab
      have haX : a ∈ X := by simp [X,A,ha]
      have hbX : b ∈ X := by simp [X,A,hb]
      have hle := Metric.dist_le_diam_of_mem X.finite_toSet.isBounded haX hbX
      by_cases hlt : dist a b < Metric.diam (X : Set Plane)
      · apply Or.inl
        have hdS := (mem_nonDiameterDistances X (dist a b)).mpr ⟨⟨a,haX,b,hbX,hab,rfl⟩,hlt⟩
        exact Finset.mem_image.mpr ⟨dist a b,hdS,rfl⟩
      · apply Or.inr
        exact congrArg (fun d : ℝ => d ^ 2) (le_antisymm hle (le_of_not_gt hlt))

set_option maxHeartbeats 1000000

private theorem strict_algebra (s t q δ A B E : ℝ)
    (hs : 0 < s) (ht : s < t) (hq : s + t < q)
    (hδ : q < δ)
    (hA : A * t = 4*s*t-t^2)
    (hB : B * t = 4*s*t-s^2)
    (hE : E * t = 4*s*t-(s+t-q)^2)
    (hAs : A = s ∨ A = t ∨ A = q ∨ A = δ)
    (hBs : B = s ∨ B = t ∨ B = q ∨ B = δ)
    (hAle : A ≤ δ) (hBle : B ≤ δ) (hEle : E ≤ δ)
    (hcross : t = 2*s → q = 7*s/2 → ∃ a b : ℝ,
      a+b = 3*s ∧ a*b = s^2/2 ∧
      (a = s ∨ a = t ∨ a = q ∨ a = δ) ∧
      (b = s ∨ b = t ∨ b = q ∨ b = δ)) : False := by
  have htpos : 0 < t := hs.trans ht
  have hqpos : 0 < q := by linarith
  have hAB : A < B := by nlinarith [sq_nonneg (t-s)]
  have hB4 : B < 4*s := by nlinarith [sq_pos_of_pos hs]
  rcases hAs with hAs | hAt | hAq | hAδ
  · have ht3 : t = 3*s := by nlinarith
    rcases hBs with hBs | hBt | hBq | hBδ <;> nlinarith [sq_pos_of_pos hs]
  · have ht2 : t = 2*s := by nlinarith
    have hB7 : B = 7*s/2 := by nlinarith
    have hq3 : 3*s < q := by linarith
    by_cases hqB : q = B
    · obtain ⟨a,b,hab,hprod,ha,hb⟩ := hcross ht2 (hqB.trans hB7)
      have hat : s ≤ a := by rcases ha with rfl | rfl | rfl | rfl <;> linarith
      have hbt : s ≤ b := by rcases hb with rfl | rfl | rfl | rfl <;> linarith
      have hprodge : s^2 ≤ a*b := by nlinarith [mul_nonneg (sub_nonneg.mpr hat) (sub_nonneg.mpr hbt)]
      nlinarith [sq_pos_of_pos hs]
    · have hδB : δ = B := by
        rcases hBs with hBs | hBt | hBq | hBδ
        · linarith
        · linarith
        · exact False.elim (hqB hBq.symm)
        · exact hBδ.symm
      have hqBlt : q < B := hδB ▸ hδ
      have hEsq : (s+t-q)^2 < s^2 := by
        nlinarith [sq_nonneg (q-3*s),sq_nonneg (7*s/2-q)]
      nlinarith
  · have hqform : q = 4*s-t := by nlinarith
    have htbound : t < 3*s/2 := by linarith
    have hBq : q < B := by nlinarith [sq_nonneg (t-s)]
    have hδB : δ = B := by
      rcases hBs with hBs | hBt | hBqeq | hBδ
      · linarith
      · nlinarith [sq_nonneg (t-s)]
      · linarith
      · exact hBδ.symm
    have hEsq : (s+t-q)^2 < s^2 := by
      nlinarith [sq_nonneg (t-s),sq_nonneg (3*s/2-t)]
    nlinarith
  · linarith


private theorem gram (z a b : Plane) :
    ‖z‖^2 * (inner ℝ a b)^2 + ‖a‖^2 * (inner ℝ z b)^2 +
    ‖b‖^2 * (inner ℝ z a)^2 =
    ‖z‖^2 * ‖a‖^2 * ‖b‖^2 +
      2 * inner ℝ z a * inner ℝ z b * inner ℝ a b := by
  simp only [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two,
    Real.norm_eq_abs, sq_abs, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Fin.sum_univ_two, Pi.star_apply, star_trivial]
  ring

private theorem strict_obstruction_false (C : Finset Plane) (z : Plane) (R δ : ℝ)
    (T : Finset ℝ) (hR : 0 < R) (hout : R < ‖z‖)
    (hc : ∀ c ∈ C, ‖c‖ = R) (hcard : T.card = 3)
    (hT : ∀ t ∈ T, 0 < t ∧ t < δ ∧ ∃ c ∈ C, dist c z ^ 2 = t)
    (hs : R^2 ∈ T) (ht : ‖z‖^2 ∈ T) (q : ℝ) (hqmem : q ∈ T)
    (hqt : ‖z‖^2 < q) (hneg : ∃ c ∈ C, inner ℝ z c < 0)
    (href : ∀ c ∈ C, (ℝ ∙ z).reflection c ∈ C ∧ (ℝ ∙ z).reflection c ≠ c ∧
      dist c z ^ 2 = R ^ 2 + ‖z‖ ^ 2 - 2 * inner ℝ z c ∧
      dist c ((ℝ ∙ z).reflection c) ^ 2 * ‖z‖ ^ 2 =
        4 * (R ^ 2 * ‖z‖ ^ 2 - (inner ℝ z c) ^ 2))
    (hradmem : ∀ c ∈ C, dist c z ^ 2 ∈ T)
    (hch : ∀ a ∈ C, ∀ b ∈ C, a ≠ b → dist a b ^ 2 ∈ T ∨ dist a b ^ 2 = δ) : False := by
  classical
  let s := R^2
  let t := ‖z‖^2
  have hspos : 0 < s := sq_pos_of_pos hR
  have hst : s < t := by dsimp [s,t]; nlinarith [norm_nonneg z]
  have htpos : 0 < t := hspos.trans hst
  have hset : T = {s,t,q} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hs
      · exact ht
      · exact hqmem
    · have hneqst : s ≠ t := ne_of_lt hst
      have hneqsq : s ≠ q := ne_of_lt (hst.trans hqt)
      have hneqtq : t ≠ q := ne_of_lt hqt
      simp [hcard,hneqst,hneqsq,hneqtq]
  have mem_cases : ∀ x ∈ T, x = s ∨ x = t ∨ x = q := by
    intro x hx
    simpa only [hset,Finset.mem_insert,Finset.mem_singleton] using hx
  have hq : s+t < q := by
    obtain ⟨c,hcm,hcn⟩ := hneg
    have hr := (href c hcm).2.2.1
    have hdmem := hradmem c hcm
    rcases mem_cases _ hdmem with he | he | he <;> dsimp [s,t] at * <;> nlinarith
  obtain ⟨a,ha,has⟩ := (hT s hs).2.2
  obtain ⟨b,hb,hbt⟩ := (hT t ht).2.2
  obtain ⟨e,he,heq⟩ := (hT q hqmem).2.2
  let A := dist a ((ℝ ∙ z).reflection a)^2
  let B := dist b ((ℝ ∙ z).reflection b)^2
  let E := dist e ((ℝ ∙ z).reflection e)^2
  have hza : inner ℝ z a = t/2 := by have hr := (href a ha).2.2.1; dsimp [s,t] at *; linarith
  have hzb : inner ℝ z b = s/2 := by have hr := (href b hb).2.2.1; dsimp [s,t] at *; linarith
  have hze : inner ℝ z e = (s+t-q)/2 := by have hr := (href e he).2.2.1; dsimp [s,t] at *; linarith
  have hA : A*t = 4*s*t-t^2 := by have hr := (href a ha).2.2.2; rw [hza] at hr; dsimp [A,s,t] at *; nlinarith
  have hB : B*t = 4*s*t-s^2 := by have hr := (href b hb).2.2.2; rw [hzb] at hr; dsimp [B,s,t] at *; nlinarith
  have hE : E*t = 4*s*t-(s+t-q)^2 := by have hr := (href e he).2.2.2; rw [hze] at hr; dsimp [E,s,t] at *; nlinarith
  have chord_cases : ∀ a ∈ C, ∀ b ∈ C, a ≠ b →
      dist a b ^ 2 = s ∨ dist a b ^ 2 = t ∨ dist a b ^ 2 = q ∨ dist a b ^ 2 = δ := by
    intro a ha b hb hab
    rcases hch a ha b hb hab with hm | hd
    · rcases mem_cases _ hm with hh | hh | hh
      · exact Or.inl hh
      · exact Or.inr (Or.inl hh)
      · exact Or.inr (Or.inr (Or.inl hh))
    · exact Or.inr (Or.inr (Or.inr hd))
  have chord_le : ∀ a ∈ C, ∀ b ∈ C, a ≠ b → dist a b ^ 2 ≤ δ := by
    intro a ha b hb hab
    rcases hch a ha b hb hab with hm | hd
    · exact (hT _ hm).2.1.le
    · exact hd.le
  apply strict_algebra s t q δ A B E hspos hst hq (hT q hqmem).2.1 hA hB hE
    (chord_cases a ha _ (href a ha).1 (href a ha).2.1.symm)
    (chord_cases b hb _ (href b hb).1 (href b hb).2.1.symm)
    (chord_le a ha _ (href a ha).1 (href a ha).2.1.symm)
    (chord_le b hb _ (href b hb).1 (href b hb).2.1.symm)
    (chord_le e he _ (href e he).1 (href e he).2.1.symm)
  intro ht2 hq7
  let rb := (ℝ ∙ z).reflection b
  have hrb : rb ∈ C := (href b hb).1
  have hzrb : inner ℝ z rb = inner ℝ z b := by
    dsimp [rb]
    rw [Submodule.reflection_singleton_apply]
    simp only [RCLike.ofReal_real_eq_id,id_eq,inner_sub_right,two_smul,inner_add_right,inner_smul_right,
      real_inner_self_eq_norm_sq]
    have hn : ‖z‖^2 ≠ 0 := ne_of_gt htpos
    have hn0 : ‖z‖ ≠ 0 := by intro he; simp [he] at hn
    field_simp [hn0]
    ring
  have hab : a ≠ b := by intro hh; rw [hh] at hza; linarith
  have harb : a ≠ rb := by intro hh; rw [hh,hzrb,hzb] at hza; linarith
  have haN : ‖a‖^2 = s := by rw [hc a ha]
  have hbN : ‖b‖^2 = s := by rw [hc b hb]
  have hrbN : ‖rb‖^2 = s := by rw [hc rb hrb]
  have hinner : inner ℝ a rb = 2*(inner ℝ z b)/t*(inner ℝ z a)-inner ℝ a b := by
    dsimp [rb]
    rw [Submodule.reflection_singleton_apply]
    simp only [RCLike.ofReal_real_eq_id,id_eq,inner_sub_right,two_smul,inner_add_right,inner_smul_right,
      real_inner_comm a z]
    dsimp [t]
    ring
  have hd1 : dist a b ^ 2 = 2*s-2*inner ℝ a b := by
    rw [dist_eq_norm,norm_sub_sq_real,haN,hbN]; ring
  have hd2 : dist a rb ^ 2 = 2*s-2*inner ℝ a rb := by
    rw [dist_eq_norm,norm_sub_sq_real,haN,hrbN]; ring
  have hirb : inner ℝ a rb = s/2-inner ℝ a b := by
    rw [hinner,hza,hzb,ht2]
    field_simp
  have hg := gram z a b
  rw [haN,hbN,hza,hzb] at hg
  change t * (inner ℝ a b)^2 + s*(s/2)^2+s*(t/2)^2 = t*s*s+2*(t/2)*(s/2)*inner ℝ a b at hg
  rw [ht2] at hg
  refine ⟨dist a b ^ 2,dist a rb ^ 2,?_,?_,chord_cases a ha b hb hab,chord_cases a ha rb hrb harb⟩
  · rw [hd1,hd2,hirb]; ring
  · rw [hd1,hd2,hirb]
    have hpoly : 2*(inner ℝ a b)^2-s*inner ℝ a b = 3*s^2/4 := by
      nlinarith
    nlinarith

private theorem cross_pair (z a b : Plane) (s t : ℝ) (ht : 0 < t)
    (hz : ‖z‖^2 = t) (ha : ‖a‖^2 = s) (hb : ‖b‖^2 = s)
    (hrb : ‖(ℝ ∙ z).reflection b‖^2 = s) :
    (dist a b^2 + dist a ((ℝ ∙ z).reflection b)^2)*t =
      4*s*t-4*inner ℝ z a*inner ℝ z b ∧
    (dist a b^2 * dist a ((ℝ ∙ z).reflection b)^2)*t =
      4*s*(inner ℝ z a-inner ℝ z b)^2 := by
  let rb := (ℝ ∙ z).reflection b
  have hir : inner ℝ a rb = 2*inner ℝ z b/t*inner ℝ z a-inner ℝ a b := by
    dsimp [rb]
    rw [Submodule.reflection_singleton_apply]
    simp only [RCLike.ofReal_real_eq_id,id_eq,inner_sub_right,two_smul,inner_add_right,inner_smul_right,
      real_inner_comm a z,hz]
    ring
  have h1 : dist a b^2 = 2*s-2*inner ℝ a b := by
    rw [dist_eq_norm,norm_sub_sq_real,ha,hb]; ring
  have h2 : dist a rb^2 = 2*s-2*inner ℝ a rb := by
    rw [dist_eq_norm,norm_sub_sq_real,ha,hrb]; ring
  have hg := gram z a b
  rw [hz,ha,hb] at hg
  change (dist a b^2 + dist a rb^2)*t = _ ∧ (dist a b^2 * dist a rb^2)*t = _
  rw [h1,h2,hir]
  constructor
  · field_simp
    ring
  · field_simp
    nlinarith only [hg]

private theorem reflection_inner (z b : Plane) (hz : 0 < ‖z‖^2) :
    inner ℝ z ((ℝ ∙ z).reflection b) = inner ℝ z b := by
  rw [Submodule.reflection_singleton_apply]
  simp only [RCLike.ofReal_real_eq_id,id_eq,inner_sub_right,two_smul,inner_add_right,
    inner_smul_right,real_inner_self_eq_norm_sq]
  have hn0 : ‖z‖ ≠ 0 := by intro he; simp [he] at hz
  field_simp [hn0]
  ring

private theorem boundary_false (C : Finset Plane) (z : Plane) (R δ : ℝ)
    (T : Finset ℝ) (hR : 0 < R) (hzN : ‖z‖ = R)
    (hc : ∀ c ∈ C, ‖c‖ = R) (hcard : T.card = 3)
    (hT : ∀ t ∈ T, 0 < t ∧ t < δ ∧ ∃ c ∈ C, dist c z ^ 2 = t)
    (hs : R^2 ∈ T) (hneg : ∃ c ∈ C, inner ℝ z c < 0)
    (href : ∀ c ∈ C, (ℝ ∙ z).reflection c ∈ C ∧ (ℝ ∙ z).reflection c ≠ c ∧
      dist c z ^ 2 = R ^ 2 + ‖z‖ ^ 2 - 2 * inner ℝ z c ∧
      dist c ((ℝ ∙ z).reflection c) ^ 2 * ‖z‖ ^ 2 =
        4 * (R ^ 2 * ‖z‖ ^ 2 - (inner ℝ z c) ^ 2))
    (hradmem : ∀ c ∈ C, dist c z ^ 2 ∈ T)
    (hch : ∀ a ∈ C, ∀ b ∈ C, a ≠ b → dist a b ^ 2 ∈ T ∨ dist a b ^ 2 = δ) : False := by
  classical
  let s := R^2
  have hspos : 0 < s := sq_pos_of_pos hR
  have hzsq : ‖z‖^2 = s := by rw [hzN]
  have normsq : ∀ c ∈ C, ‖c‖^2 = s := by intro c hcC; rw [hc c hcC]
  have dot_bound : ∀ c ∈ C, (inner ℝ z c)^2 < s^2 := by
    intro c hcC
    have hh := (href c hcC).2.2.2
    rw [hzsq] at hh
    have hd : 0 < dist c ((ℝ ∙ z).reflection c)^2 :=
      sq_pos_of_pos (dist_pos.mpr (href c hcC).2.1.symm)
    have hp := mul_pos hd hspos
    dsimp [s] at *
    nlinarith only [hh,hp]
  have radial : ∀ c ∈ C, dist c z^2 = 2*s-2*inner ℝ z c := by
    intro c hcC
    have hh := (href c hcC).2.2.1
    rw [hzsq] at hh
    dsimp [s] at *
    linarith
  have support_lt_four : ∀ v ∈ T, v < 4*s := by
    intro v hv
    obtain ⟨c,hcC,hcv⟩ := (hT v hv).2.2
    have hw := dot_bound c hcC
    have hr := radial c hcC
    nlinarith only [hw,hr,hcv,hspos,sq_nonneg (inner ℝ z c-s)]
  have chord_le : ∀ a ∈ C, ∀ b ∈ C, a ≠ b → dist a b ^ 2 ≤ δ := by
    intro a ha b hb hab
    rcases hch a ha b hb hab with hm | hd
    · exact (hT _ hm).2.1.le
    · exact hd.le
  obtain ⟨a,ha,has⟩ := (hT s hs).2.2
  have hza : inner ℝ z a = s/2 := by have hr := radial a ha; linarith
  have hthree : dist a ((ℝ ∙ z).reflection a)^2 = 3*s := by
    have hr := (href a ha).2.2.2
    rw [hzsq,hza] at hr
    dsimp [s] at *
    nlinarith only [hr,hspos]
  have hthree_cases : 3*s ∈ T ∨ 3*s = δ := by
    simpa only [hthree] using hch a ha _ (href a ha).1 (href a ha).2.1.symm
  have pairs : ∀ c ∈ C,
      dist a c^2 + dist a ((ℝ ∙ z).reflection c)^2 = 4*s-2*inner ℝ z c ∧
      dist a c^2 * dist a ((ℝ ∙ z).reflection c)^2 =
        s^2-4*s*inner ℝ z c+4*(inner ℝ z c)^2 := by
    intro c hcC
    have hh := cross_pair z a c s s hspos hzsq (normsq a ha) (normsq c hcC)
      (normsq _ (href c hcC).1)
    rw [hza] at hh
    constructor
    · apply mul_right_cancel₀ (ne_of_gt hspos)
      nlinarith only [hh.1]
    · apply mul_right_cancel₀ (ne_of_gt hspos)
      nlinarith only [hh.2]
  have hδne : δ ≠ 3*s := by
    intro hδeq
    obtain ⟨c,hcC,hwneg⟩ := hneg
    have hr := radial c hcC
    have hvlt := (hT _ (hradmem c hcC)).2.1
    rw [hδeq] at hvlt
    have hac : a ≠ c := by intro he; rw [he] at hza; linarith
    have harc : a ≠ (ℝ ∙ z).reflection c := by
      intro he
      rw [he,reflection_inner z c (by rw [hzsq]; exact hspos)] at hza
      linarith
    have hH := chord_le a ha c hcC hac
    have hK := chord_le a ha _ (href c hcC).1 harc
    rw [hδeq] at hH hK
    obtain ⟨hsum,hprod⟩ := pairs c hcC
    have hprodnonneg := mul_nonneg (sub_nonneg.mpr hH) (sub_nonneg.mpr hK)
    have hpos := mul_pos (show 0 < s-2*inner ℝ z c by linarith)
      (show 0 < s+inner ℝ z c by linarith)
    have hscaled := congrArg (fun v : ℝ => 3*s*v) hsum
    nlinarith only [hscaled,hprod,hprodnonneg,hpos]
  have h3mem : 3*s ∈ T := hthree_cases.resolve_right (Ne.symm hδne)
  have h3lt : 3*s < δ := (hT _ h3mem).2.1
  obtain ⟨b,hb,hb3⟩ := (hT _ h3mem).2.2
  have hzb : inner ℝ z b = -s/2 := by have hr := radial b hb; linarith
  have hab : a ≠ b := by intro he; rw [he] at hza; linarith
  have harb : a ≠ (ℝ ∙ z).reflection b := by
    intro he
    rw [he,reflection_inner z b (by rw [hzsq]; exact hspos)] at hza
    linarith
  obtain ⟨hsum,hprod⟩ := pairs b hb
  rw [hzb] at hsum hprod
  have hfour : dist a b^2 = 4*s ∨ dist a ((ℝ ∙ z).reflection b)^2 = 4*s := by
    have hf : (dist a b^2-4*s)*(dist a b^2-s) = 0 := by nlinarith only [hsum,hprod]
    rcases mul_eq_zero.mp hf with hh | hh
    · exact Or.inl (by linarith)
    · exact Or.inr (by nlinarith only [hh,hsum])
  have hδ4 : δ = 4*s := by
    rcases hfour with hfour | hfour
    · rcases hch a ha b hb hab with hm | hd
      · have hl := support_lt_four _ hm; linarith
      · linarith
    · rcases hch a ha _ (href b hb).1 harb with hm | hd
      · have hl := support_lt_four _ hm; linarith
      · linarith
  have hanti : ∃ b ∈ C, b = -a := by
    rcases hfour with hh | hh
    · refine ⟨b,hb,?_⟩
      have hn : ‖a+b‖^2 = 0 := by
        have hd : dist a b^2 = 2*s-2*inner ℝ a b := by
          rw [dist_eq_norm,norm_sub_sq_real,normsq a ha,normsq b hb]; ring
        rw [norm_add_sq_real,normsq a ha,normsq b hb]
        nlinarith only [hd,hh]
      have hzab : a+b = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (a+b)])
      exact eq_neg_of_add_eq_zero_right hzab
    · let b' := (ℝ ∙ z).reflection b
      have hb' := (href b hb).1
      refine ⟨b',hb',?_⟩
      have hn : ‖a+b'‖^2 = 0 := by
        have hd : dist a b'^2 = 2*s-2*inner ℝ a b' := by
          rw [dist_eq_norm,norm_sub_sq_real,normsq a ha,normsq b' hb']; ring
        rw [norm_add_sq_real,normsq a ha,normsq b' hb']
        nlinarith only [hd,hh]
      have hzab : a+b' = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (a+b')])
      exact eq_neg_of_add_eq_zero_right hzab
  obtain ⟨an,han,haneg⟩ := hanti
  have hvexists : ∃ v ∈ T, v ≠ s ∧ v ≠ 3*s := by
    by_contra hn
    push Not at hn
    have hsub : T ⊆ {s,3*s} := by
      intro v hv
      simp only [Finset.mem_insert,Finset.mem_singleton]
      by_cases hh : v = s
      · exact Or.inl hh
      · exact Or.inr (hn v hv hh)
    have hle := Finset.card_le_card hsub
    have htwo : ({s,3*s} : Finset ℝ).card ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨v,hv,hvs,hv3⟩ := hvexists
  have hset : T = {s,3*s,v} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hs
      · exact h3mem
      · exact hv
    · have hn : s ≠ 3*s := by linarith
      simp [hcard,hn,hvs.symm,hv3.symm]
  obtain ⟨p,hp,hpv⟩ := (hT v hv).2.2
  have hzp : inner ℝ z p = s-v/2 := by have hr := radial p hp; linarith
  have hwp := dot_bound p hp
  let ra := (ℝ ∙ z).reflection a
  have hra : ra ∈ C := (href a ha).1
  have hzra : inner ℝ z ra = s/2 := by rw [reflection_inner z a (by rw [hzsq]; exact hspos),hza]
  have hraanti : -ra ∈ C := by
    have hrefl := (href an han).1
    rw [haneg] at hrefl
    simpa only [map_neg] using hrefl
  have antipodal_support : ∀ a ∈ C, -a ∈ C → inner ℝ z a = s/2 →
      dist a p^2 ∈ T ∧ 4*s-dist a p^2 ∈ T := by
    intro c hcC hnc hzc
    have hcp : c ≠ p := by intro hh; rw [hh,hzp] at hzc; apply hvs; linarith
    have hncp : -c ≠ p := by intro hh; have he := congrArg (inner ℝ z) hh; simp only [inner_neg_right,hzc] at he; rw [hzp] at he; apply hv3; linarith
    have hcpos : 0 < dist c p^2 := sq_pos_of_pos (dist_pos.mpr hcp)
    have hnpos : 0 < dist (-c) p^2 := sq_pos_of_pos (dist_pos.mpr hncp)
    have hcomp : dist c p^2+dist (-c) p^2 = 4*s := by
      rw [dist_eq_norm,dist_eq_norm,norm_sub_sq_real,norm_sub_sq_real,
        normsq c hcC,normsq p hp,norm_neg,normsq c hcC,inner_neg_left]
      ring
    have hcmem : dist c p^2 ∈ T := by
      rcases hch c hcC p hp hcp with hm | hd
      · exact hm
      · rw [hδ4] at hd; linarith
    have hnmem : dist (-c) p^2 ∈ T := by
      rcases hch (-c) hnc p hp hncp with hm | hd
      · exact hm
      · rw [hδ4] at hd; linarith
    exact ⟨hcmem,by convert hnmem using 1; linarith⟩
  have haS := antipodal_support a ha (by simpa only [haneg] using han) hza
  have hraS := antipodal_support ra hra hraanti hzra
  let x := inner ℝ a p
  let y := inner ℝ ra p
  have hx : dist a p^2 = 2*s-2*x := by
    rw [dist_eq_norm,norm_sub_sq_real,normsq a ha,normsq p hp]
    dsimp [x]; ring
  have hy : dist ra p^2 = 2*s-2*y := by
    rw [dist_eq_norm,norm_sub_sq_real,normsq ra hra,normsq p hp]
    dsimp [y]; ring
  have hxy : x+y = inner ℝ z p := by
    dsimp [x,y,ra]
    rw [Submodule.reflection_singleton_apply]
    simp only [RCLike.ofReal_real_eq_id,id_eq,inner_sub_left,two_smul,inner_add_left,
      real_inner_smul_left,hza,hzsq]
    field_simp [ne_of_gt hspos]
    ring
  have hg := gram z a p
  rw [hzsq,normsq a ha,normsq p hp,hza] at hg
  have hgram : x^2-x*(inner ℝ z p)+(inner ℝ z p)^2 = 3*s^2/4 := by
    dsimp [x]
    nlinarith only [hg,hspos]
  have mem_cases : ∀ h ∈ T, h = s ∨ h = 3*s ∨ h = v := by
    intro h hh
    simpa only [hset,Finset.mem_insert,Finset.mem_singleton] using hh
  have cases_x := mem_cases _ haS.1
  have cases_xc := mem_cases _ haS.2
  have cases_y := mem_cases _ hraS.1
  have cases_yc := mem_cases _ hraS.2
  rw [hx] at cases_x cases_xc
  rw [hy] at cases_y cases_yc
  by_cases hv2 : v = 2*s
  · rw [hv2] at hzp cases_x cases_y
    have hwzero : inner ℝ z p = 0 := by linarith
    rw [hwzero] at hgram
    rcases cases_x with hh | hh | hh
    · have hxv : x = s/2 := by linarith only [hh]
      rw [hxv] at hgram
      nlinarith only [hgram,sq_pos_of_pos hspos]
    · have hxv : x = -s/2 := by linarith only [hh]
      rw [hxv] at hgram
      nlinarith only [hgram,sq_pos_of_pos hspos]
    · have hxv : x = 0 := by linarith only [hh]
      rw [hxv] at hgram
      nlinarith only [hgram,sq_pos_of_pos hspos]
  · have hxn : 2*s-2*x ≠ v := by
      intro hh
      rcases cases_xc with he | he | he
      · apply hv3; linarith
      · apply hvs; linarith
      · apply hv2; linarith
    have hyn : 2*s-2*y ≠ v := by
      intro hh
      rcases cases_yc with he | he | he
      · apply hv3; linarith
      · apply hvs; linarith
      · apply hv2; linarith
    have hx13 : 2*s-2*x = s ∨ 2*s-2*x = 3*s := by
      rcases cases_x with hh | hh | hh
      · exact Or.inl hh
      · exact Or.inr hh
      · exact False.elim (hxn hh)
    have hy13 : 2*s-2*y = s ∨ 2*s-2*y = 3*s := by
      rcases cases_y with hh | hh | hh
      · exact Or.inl hh
      · exact Or.inr hh
      · exact False.elim (hyn hh)
    rcases hx13 with hx1 | hx3
    · have hxv : x = s/2 := by linarith only [hx1]
      rcases hy13 with hy1 | hy3
      · have hyv : y = s/2 := by linarith only [hy1]
        have hwv : inner ℝ z p = s := by linarith only [hxy,hxv,hyv]
        rw [hwv] at hwp
        exact lt_irrefl _ hwp
      · have hyv : y = -s/2 := by linarith only [hy3]
        have hwv : inner ℝ z p = 0 := by linarith only [hxy,hxv,hyv]
        rw [hxv,hwv] at hgram
        nlinarith only [hgram,sq_pos_of_pos hspos]
    · have hxv : x = -s/2 := by linarith only [hx3]
      rcases hy13 with hy1 | hy3
      · have hyv : y = s/2 := by linarith only [hy1]
        have hwv : inner ℝ z p = 0 := by linarith only [hxy,hxv,hyv]
        rw [hxv,hwv] at hgram
        nlinarith only [hgram,sq_pos_of_pos hspos]
      · have hyv : y = -s/2 := by linarith only [hy3]
        have hwv : inner ℝ z p = -s := by linarith only [hxy,hxv,hyv]
        rw [hwv,neg_sq] at hwp
        exact lt_irrefl _ hwp


/-- In the original zero-centered six-circle-vertex geometry, an interior point
on or outside the circumcircle forces an occurring positive non-diameter distance
with actual unordered, loop-free multiplicity between one and nine. The augmented
hull supplies all extremeness and ambient interior hypotheses; no saturation or
support certificate is a premise. -/
theorem original_zero_centered_outside (C : Finset Plane) (u z : Plane) (R : ℝ)
    (hC : C.card = 6) (hR : 0 < R) (hcircle : ∀ c ∈ C, dist c (0 : Plane) = R)
    (hu : dist u (0 : Plane) ≠ R)
    (hext : ∀ a ∈ insert u C,
      a ∈ (convexHull ℝ ((insert u C : Finset Plane) : Set Plane)).extremePoints ℝ)
    (hO : (0 : Plane) ∈ interior (convexHull ℝ ((insert u C : Finset Plane) : Set Plane)))
    (hz : z ∈ interior (convexHull ℝ ((insert u C : Finset Plane) : Set Plane)))
    (houtside : R ≤ dist z (0 : Plane)) :
    let X := insert (0 : Plane) (insert z (insert u C))
    X.card = 9 ∧ ∃ d : ℝ, 0 < d ∧ d < Metric.diam (X : Set Plane) ∧
      1 ≤ multiplicity X d ∧ multiplicity X d ≤ 9 := by
  have hc : ∀ c ∈ C, ‖c‖ = R := by simpa only [dist_zero_right] using hcircle
  have huN : ‖u‖ ≠ R := by simpa only [dist_zero_right] using hu
  have hout : R ≤ ‖z‖ := by simpa only [dist_zero_right] using houtside
  obtain ⟨hcard,hcase⟩ := original_outside_target_or_chord_obstruction
    C u z R hC hR hc huN hext hO hz hout
  refine ⟨hcard,?_⟩
  rcases hcase with htarget | ⟨T,hTcard,hT,hs,ht,hq,hzu,hun,hneg,hrad,href,hch⟩
  · exact htarget
  · by_cases hstrict : R < ‖z‖
    · have hqt : ‖z‖^2 < ‖u‖^2 := by nlinarith [norm_nonneg z,norm_nonneg u]
      exact False.elim (strict_obstruction_false C z R _ T hR hstrict hc hTcard hT
        hs ht (‖u‖^2) hq hqt hneg href hrad hch)
    · have hzN : ‖z‖ = R := le_antisymm (le_of_not_gt hstrict) hout
      exact False.elim (boundary_false C z R _ T hR hzN hc hTcard hT hs hneg href hrad hch)

/-- A simultaneous rational original-geometry fixture also satisfies the final
outside-branch multiplicity conclusion. This applies the consumer to real hull
geometry rather than to the impossible failed-target certificate. -/
theorem original_outside_fixture_with_conclusion : ∃ (C : Finset Plane) (u z : Plane),
    C.card = 6 ∧ (∀ c ∈ C, dist c (0 : Plane) = 1) ∧ dist u (0 : Plane) ≠ 1 ∧
    (∀ a ∈ insert u C,
      a ∈ (convexHull ℝ ((insert u C : Finset Plane) : Set Plane)).extremePoints ℝ) ∧
    (0 : Plane) ∈ interior (convexHull ℝ ((insert u C : Finset Plane) : Set Plane)) ∧
    z ∈ interior (convexHull ℝ ((insert u C : Finset Plane) : Set Plane)) ∧
    (0 : Plane) ≠ z ∧ 1 < dist z (0 : Plane) ∧
    (insert (0 : Plane) (insert z (insert u C))).card = 9 ∧
    ∃ d : ℝ, 0 < d ∧
      d < Metric.diam ((insert (0 : Plane) (insert z (insert u C)) : Finset Plane) : Set Plane) ∧
      1 ≤ multiplicity (insert (0 : Plane) (insert z (insert u C))) d ∧
      multiplicity (insert (0 : Plane) (insert z (insert u C))) d ≤ 9 := by
  obtain ⟨C,u,z,hC,hcircle,hu,hext,hO,hz,hOz,hout⟩ := original_outside_geometry_fixture
  have htarget := original_zero_centered_outside C u z 1 hC (by norm_num) hcircle hu hext hO hz hout.le
  exact ⟨C,u,z,hC,hcircle,hu,hext,hO,hz,hOz,hout,htarget⟩

end Erdos132.HullOutlierOutside
