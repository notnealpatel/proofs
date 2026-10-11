import Erdos.Erdos132.EvenThreeInteriorCircle
import Erdos.Erdos132.CircleFixtures

set_option autoImplicit false

namespace Erdos132.UniqueDiameterCircle

open Erdos132.TwoInteriorCircle

/-- Adjoining any finite collection of ambient hull interiors preserves diameter. -/
theorem diam_union_interiors (H I : Finset Plane)
    (hInt : ∀ i ∈ I, i ∈ interior (convexHull ℝ (H : Set Plane))) :
    Metric.diam ((H ∪ I : Finset Plane) : Set Plane) = Metric.diam (H : Set Plane) := by
  classical
  have hsub : ((H ∪ I : Finset Plane) : Set Plane) ⊆ convexHull ℝ (H : Set Plane) := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxH | hxI
    · exact subset_convexHull ℝ _ hxH
    · exact interior_subset (hInt x hxI)
  apply le_antisymm
  · exact Metric.diam_le_of_forall_dist_le Metric.diam_nonneg
      (fun _ hx _ hy => dist_le_diam_hull H (hsub hx) (hsub hy))
  · exact Metric.diam_mono (by intro x hx; exact Finset.mem_union_left _ hx)
      (H ∪ I).finite_toSet.isBounded

/-- Circle vertices and ambient hull interiors are disjoint, hence their sizes add. -/
theorem card_union_interiors (H I : Finset Plane) (O : Plane) {R : ℝ}
    (hR : 0 < R) (hcircle : ∀ h ∈ H, dist h O = R)
    (hInt : ∀ i ∈ I, i ∈ interior (convexHull ℝ (H : Set Plane))) :
    (H ∪ I).card = H.card + I.card := by
  classical
  apply Finset.card_union_of_disjoint
  apply Finset.disjoint_left.mpr
  intro x hxH hxI
  exact (ne_of_lt (dist_center_lt_radius H O hR hcircle (hInt x hxI))) (hcircle x hxH)

/-- Every endpoint of an actual diameter of an augmented hull is a hull vertex. -/
theorem diameter_endpoint_mem_hull (H I : Finset Plane) (hcard : 2 ≤ H.card)
    (hInt : ∀ i ∈ I, i ∈ interior (convexHull ℝ (H : Set Plane)))
    {a b : Plane} (ha : a ∈ H ∪ I) (hb : b ∈ H ∪ I)
    (hdiam : dist a b = Metric.diam ((H ∪ I : Finset Plane) : Set Plane)) : a ∈ H := by
  classical
  rcases Finset.mem_union.mp ha with haH | haI
  · exact haH
  · have hbK : b ∈ convexHull ℝ (H : Set Plane) := by
      rcases Finset.mem_union.mp hb with hbH | hbI
      · exact subset_convexHull ℝ _ hbH
      · exact interior_subset (hInt b hbI)
    have hlt := dist_lt_diam_hull H hcard (hInt a haI) hbK
    rw [hdiam, diam_union_interiors H I hInt] at hlt
    exact False.elim (lt_irrefl _ hlt)

/-- The existing centered longest-class bound holds about any center, by translation. -/
theorem longest_class_bound (H I : Finset Plane) (O : Plane) {R L : ℝ} {a b : Plane}
    (hR : 0 < R) (hcircle : ∀ h ∈ H, dist h O = R)
    (ha : a ∈ H) (hb : b ∈ H) (hab : a ≠ b)
    (hdiam : dist a b = Metric.diam (H : Set Plane))
    (hunique : ∀ x ∈ H, ∀ y ∈ H, dist x y = dist a b → s(x,y) = s(a,b))
    (hInt : ∀ i ∈ I, i ∈ interior (convexHull ℝ (H : Set Plane)))
    (hL : 0 < L) (hLD : L < Metric.diam (H : Set Plane))
    (hmax : ∀ x ∈ H ∪ I, ∀ y ∈ H ∪ I,
      dist x y < Metric.diam (H : Set Plane) → dist x y ≤ L) :
    multiplicity (H ∪ I) L ≤ H.card + I.card := by
  classical
  let f : Plane → Plane := fun x => x - O
  have hf : Isometry f := by
    intro x y
    simp [f, edist_dist, dist_eq_norm]
  have hd : Metric.diam ((H.image f : Finset Plane) : Set Plane) = Metric.diam (H : Set Plane) := by
    rw [Finset.coe_image]
    exact hf.diam_image (H : Set Plane)
  have hc : ∀ h ∈ H.image f, ‖h‖ = R := by
    intro h hh
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hh
    exact (dist_eq_norm x O).symm.trans (hcircle x hx)
  have hu : ∀ x ∈ H.image f, ∀ y ∈ H.image f,
      dist x y = dist (f a) (f b) → s(x,y) = s(f a,f b) := by
    intro x hx y hy hxy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    rw [hf.dist_eq, hf.dist_eq] at hxy
    exact congrArg (Sym2.map f) (hunique u hu v hv hxy)
  have hi : ∀ i ∈ I.image f,
      i ∈ interior (convexHull ℝ ((H.image f : Finset Plane) : Set Plane)) := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact sub_mem_interior_hull H O j (hInt j hj)
  have hm : ∀ x ∈ H.image f ∪ I.image f, ∀ y ∈ H.image f ∪ I.image f,
      dist x y < Metric.diam ((H.image f : Finset Plane) : Set Plane) → dist x y ≤ L := by
    rw [← Finset.image_union]
    intro x hx y hy hxy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    rw [hf.dist_eq, hd] at hxy
    rw [hf.dist_eq]
    exact hmax u hu v hv hxy
  have hbound := EvenThreeInteriorCircle.longest_class_bound (H.image f) (I.image f)
    hR hc (Finset.mem_image.mpr ⟨a,ha,rfl⟩) (Finset.mem_image.mpr ⟨b,hb,rfl⟩)
    (fun he => hab (hf.injective he)) (by rw [hf.dist_eq, hd]; exact hdiam) hu hi hL
    (by rw [hd]; exact hLD) hm
  rw [← Finset.image_union, multiplicity_image_isometry _ f hf,
    Finset.card_image_of_injective _ hf.injective,
    Finset.card_image_of_injective _ hf.injective] at hbound
  exact hbound

/-- A finite circular hull with any positive number of distinct ambient interiors
and a genuinely unique unordered diameter pair has an occurring largest positive
nondiameter length whose loop-free unordered multiplicity is at most its total size.
The center is arbitrary; the diameter endpoints and maximum length are derived. -/
theorem unique_diameter_circle (N k : ℕ) (H I : Finset Plane) (O : Plane) (R : ℝ)
    (hN : 3 ≤ N) (hk : 1 ≤ k) (hHcard : H.card = N) (hIcard : I.card = k)
    (hR : 0 < R) (hcircle : ∀ h ∈ H, dist h O = R)
    (_hfull : (interior (convexHull ℝ (H : Set Plane))).Nonempty)
    (hInt : ∀ i ∈ I, i ∈ interior (convexHull ℝ (H : Set Plane)))
    (hunique : ∃ a ∈ H ∪ I, ∃ b ∈ H ∪ I, a ≠ b ∧
      dist a b = Metric.diam ((H ∪ I : Finset Plane) : Set Plane) ∧
      ∀ x ∈ H ∪ I, ∀ y ∈ H ∪ I,
        dist x y = Metric.diam ((H ∪ I : Finset Plane) : Set Plane) → s(x,y) = s(a,b)) :
    (H ∪ I).card = N + k ∧ ∃ L : ℝ,
      0 < L ∧ L < Metric.diam ((H ∪ I : Finset Plane) : Set Plane) ∧
      (∃ x ∈ H ∪ I, ∃ y ∈ H ∪ I, x ≠ y ∧ dist x y = L) ∧
      (∀ x ∈ H ∪ I, ∀ y ∈ H ∪ I,
        0 < dist x y → dist x y < Metric.diam ((H ∪ I : Finset Plane) : Set Plane) →
          dist x y ≤ L) ∧
      1 ≤ multiplicity (H ∪ I) L ∧ multiplicity (H ∪ I) L ≤ N + k := by
  classical
  have hcard : 2 ≤ H.card := by omega
  have hD := diam_union_interiors H I hInt
  have htotal : (H ∪ I).card = N + k := by
    rw [card_union_interiors H I O hR hcircle hInt, hHcard, hIcard]
  obtain ⟨a, ha, b, hb, hab, habD, hu⟩ := hunique
  have haH := diameter_endpoint_mem_hull H I hcard hInt ha hb habD
  have hbH := diameter_endpoint_mem_hull H I hcard hInt hb ha ((dist_comm b a).trans habD)
  have huH : ∀ x ∈ H, ∀ y ∈ H, dist x y = dist a b → s(x,y) = s(a,b) := by
    intro x hx y hy hxy
    exact hu x (Finset.mem_union_left _ hx) y (Finset.mem_union_left _ hy) (hxy.trans habD)
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < I.card)
  have hiH : i ∉ H := fun he =>
    (ne_of_lt (dist_center_lt_radius H O hR hcircle (hInt i hi))) (hcircle i he)
  have hia : i ≠ a := fun he => hiH (he ▸ haH)
  let T := nonDiameterDistances (H ∪ I)
  have hT : T.Nonempty := by
    refine ⟨dist i a, (mem_nonDiameterDistances _ _).mpr ⟨?_, ?_⟩⟩
    · exact ⟨i, Finset.mem_union_right _ hi, a, Finset.mem_union_left _ haH, hia, rfl⟩
    · rw [hD]
      exact dist_lt_diam_hull H hcard (hInt i hi) (subset_convexHull ℝ _ haH)
  let L := T.max' hT
  have hLT : L ∈ T := T.max'_mem hT
  obtain ⟨hocc, hLD⟩ := (mem_nonDiameterDistances _ _).mp hLT
  obtain ⟨x, hx, y, hy, hxy, hxyL⟩ := hocc
  have hL : 0 < L := hxyL ▸ dist_pos.mpr hxy
  have hmax : ∀ u ∈ H ∪ I, ∀ v ∈ H ∪ I,
      dist u v < Metric.diam (H : Set Plane) → dist u v ≤ L := by
    intro u hu v hv huv
    by_cases he : u = v
    · simpa [he] using le_of_lt hL
    · exact T.le_max' _ ((mem_nonDiameterDistances _ _).mpr
        ⟨⟨u,hu,v,hv,he,rfl⟩, by rw [hD]; exact huv⟩)
  have hbound := longest_class_bound H I O hR hcircle haH hbH hab
    (habD.trans hD) huH hInt hL (by rw [hD] at hLD; exact hLD) hmax
  have hmult : 1 ≤ multiplicity (H ∪ I) L := by
    apply Finset.card_pos.mpr
    exact ⟨s(x,y), Finset.mem_filter.mpr
      ⟨(mk_mem_pairs _ _ _).mpr ⟨hx,hy,hxy⟩, hxyL⟩⟩
  refine ⟨htotal, L, hL, hLD, ⟨x,hx,y,hy,hxy,hxyL⟩, ?_, hmult, ?_⟩
  · intro u hu v hv _ huv
    exact hmax u hu v hv (by rw [← hD]; exact huv)
  · simpa only [hHcard, hIcard] using hbound

/-- An explicit scalene cyclic triangle has ambient interior and a unique diameter. -/
theorem scalene_triangle_fixture : ∃ (H : Finset Plane) (O : Plane) (R : ℝ) (a b : Plane),
    H.card = 3 ∧ 0 < R ∧ (∀ h ∈ H, dist h O = R) ∧
    (interior (convexHull ℝ (H : Set Plane))).Nonempty ∧
    a ∈ H ∧ b ∈ H ∧ a ≠ b ∧ dist a b = Metric.diam (H : Set Plane) ∧
    (∀ x ∈ H, ∀ y ∈ H, dist x y = dist a b → s(x,y) = s(a,b)) := by
  classical
  let A : Plane := WithLp.toLp 2 ![-1, -1/2]
  let B : Plane := WithLp.toLp 2 ![3, -1/2]
  let C : Plane := WithLp.toLp 2 ![0, 3/2]
  let O : Plane := WithLp.toLp 2 ![1, -1/4]
  let H : Finset Plane := {A, B, C}
  have hcard : H.card = 3 := by
    norm_num [H, A, B, C, Finset.card_insert_of_notMem,
      WithLp.ext_iff, funext_iff, Fin.forall_fin_two]
  have hcircle : ∀ h ∈ H, dist h O = Real.sqrt (65/16) := by
    intro h hh
    have hsq : dist h O ^ 2 = 65/16 := by
      simp only [H, Finset.mem_insert, Finset.mem_singleton] at hh
      rcases hh with rfl | rfl | rfl <;>
        norm_num [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, A, B, C, O, Real.dist_eq, sq_abs]
    nlinarith [dist_nonneg (x := h) (y := O), Real.sqrt_nonneg (65/16),
      Real.sq_sqrt (show (0 : ℝ) ≤ 65/16 by norm_num)]
  have hcorners : ∀ i ∈ ({-(1/4), 1/4} : Finset ℝ),
      ∀ j ∈ ({-(1/4), 1/4} : Finset ℝ),
      WithLp.toLp 2 ![i,j] ∈ convexHull ℝ (H : Set Plane) := by
    intro i hi j hj
    let t : ℝ := (j + 1/2) / 2
    let u : ℝ := (i + 1 - t) / (4 * (1-t))
    have ht : 0 ≤ t ∧ t ≤ 1 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl <;> norm_num [t]
    have hu : 0 ≤ u ∧ u ≤ 1 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> norm_num [t,u]
    have hc := convex_convexHull ℝ (H : Set Plane)
    have hA : A ∈ convexHull ℝ (H : Set Plane) := subset_convexHull ℝ _ (by simp [H])
    have hB : B ∈ convexHull ℝ (H : Set Plane) := subset_convexHull ℝ _ (by simp [H])
    have hC : C ∈ convexHull ℝ (H : Set Plane) := subset_convexHull ℝ _ (by simp [H])
    have hlow := hc hA hB (sub_nonneg.mpr hu.2) hu.1 (by ring : (1-u)+u=1)
    have hcombo := hc hlow hC (sub_nonneg.mpr ht.2) ht.1 (by ring : (1-t)+t=1)
    have he : (1-t) • ((1-u) • A + u • B) + t • C = WithLp.toLp 2 ![i,j] := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
        ext l <;> fin_cases l <;> norm_num [A,B,C,u,t]
    rw [he] at hcombo
    exact hcombo
  have hrectangle : ∀ x : Plane, (-1/4 < x 0 ∧ x 0 < 1/4) →
      (-1/4 < x 1 ∧ x 1 < 1/4) → x ∈ interior (convexHull ℝ (H : Set Plane)) := by
    intro x hx0 hx1
    let K : Finset Plane := ({-(1/4), 1/4} : Finset ℝ).biUnion
      (fun i => ({-(1/4), 1/4} : Finset ℝ).image (fun j => WithLp.toLp 2 ![i,j]))
    have hKsub : (K : Set Plane) ⊆ convexHull ℝ (H : Set Plane) := by
      intro p hp
      obtain ⟨i,hi,hp⟩ := Finset.mem_biUnion.mp hp
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hp
      exact hcorners i hi j hj
    have hxK := CircleFixtures.rectangle_mem_interior K (r := 1/4) (s := 1/4)
      (by norm_num) (by norm_num)
      (fun i hi j hj => Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_image.mpr ⟨j,hj,rfl⟩⟩)
      (x := x) (by simpa only [neg_div] using hx0) (by simpa only [neg_div] using hx1)
    exact interior_mono (convexHull_min hKsub (convex_convexHull ℝ _)) hxK
  have hfull : (interior (convexHull ℝ (H : Set Plane))).Nonempty :=
    ⟨0, hrectangle 0 (by norm_num) (by norm_num)⟩
  have hAB : dist A B = 4 := by
    norm_num [EuclideanSpace.dist_eq, Fin.sum_univ_two, A, B, Real.dist_eq,
      Real.sqrt_eq_iff_mul_self_eq]
  have hbound : ∀ x ∈ H, ∀ y ∈ H, dist x y ≤ 4 := by
    intro x hx y hy
    have hsq : dist x y ^ 2 ≤ 16 := by
      simp only [H, Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
        norm_num [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, A, B, C, Real.dist_eq, sq_abs]
    nlinarith [dist_nonneg (x := x) (y := y)]
  have hdiam : dist A B = Metric.diam (H : Set Plane) := by
    apply le_antisymm
    · exact Metric.dist_le_diam_of_mem H.finite_toSet.isBounded (by simp [H]) (by simp [H])
    · rw [hAB]
      exact Metric.diam_le_of_forall_dist_le (by norm_num) hbound
  have hunique : ∀ x ∈ H, ∀ y ∈ H, dist x y = dist A B → s(x,y) = s(A,B) := by
    intro x hx y hy hxy
    rw [hAB] at hxy
    have hsq := congrArg (fun d : ℝ => d^2) hxy
    simp only [H, Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    all_goals first | rfl | exact Sym2.eq_swap | exfalso; norm_num [EuclideanSpace.dist_sq_eq,
      Fin.sum_univ_two, A, B, C, Real.dist_eq, sq_abs] at hsq
  have hne : A ≠ B := by
    intro he
    have he0 := congrArg (fun x : Plane => x 0) he
    norm_num [A,B] at he0
  exact ⟨H,O,Real.sqrt (65/16),A,B,hcard,Real.sqrt_pos.mpr (by norm_num),hcircle,
    hfull,by simp [H],by simp [H],hne,hdiam,hunique⟩

/-- For every positive k, the original arbitrary-center hypotheses and the entire
largest-nondiameter conclusion are jointly inhabited on a scalene cyclic triangle.
Distinct interiors are selected from its infinite ambient open interior. -/
theorem original_hypotheses_every_positive_k (k : ℕ) (hk : 1 ≤ k) :
    ∃ (H I : Finset Plane) (O : Plane) (R : ℝ),
      H.card = 3 ∧ I.card = k ∧ 0 < R ∧ (∀ h ∈ H, dist h O = R) ∧
      (interior (convexHull ℝ (H : Set Plane))).Nonempty ∧
      (∀ i ∈ I, i ∈ interior (convexHull ℝ (H : Set Plane))) ∧
      (∃ a ∈ H ∪ I, ∃ b ∈ H ∪ I, a ≠ b ∧
        dist a b = Metric.diam ((H ∪ I : Finset Plane) : Set Plane) ∧
        ∀ x ∈ H ∪ I, ∀ y ∈ H ∪ I,
          dist x y = Metric.diam ((H ∪ I : Finset Plane) : Set Plane) → s(x,y) = s(a,b)) ∧
      (H ∪ I).card = 3 + k ∧ ∃ L : ℝ,
        0 < L ∧ L < Metric.diam ((H ∪ I : Finset Plane) : Set Plane) ∧
        (∃ x ∈ H ∪ I, ∃ y ∈ H ∪ I, x ≠ y ∧ dist x y = L) ∧
        (∀ x ∈ H ∪ I, ∀ y ∈ H ∪ I,
          0 < dist x y → dist x y < Metric.diam ((H ∪ I : Finset Plane) : Set Plane) →
            dist x y ≤ L) ∧
        1 ≤ multiplicity (H ∪ I) L ∧ multiplicity (H ∪ I) L ≤ 3 + k := by
  classical
  obtain ⟨H,O,R,a,b,hH,hR,hcircle,hfull,ha,hb,hab,hdiam,hu⟩ := scalene_triangle_fixture
  obtain ⟨p,hp⟩ := hfull
  have hinfinite : (interior (convexHull ℝ (H : Set Plane))).Infinite :=
    infinite_of_mem_nhds p (isOpen_interior.mem_nhds hp)
  obtain ⟨I,hIsub,hIcard⟩ := hinfinite.exists_subset_card_eq k
  have hInt : ∀ i ∈ I, i ∈ interior (convexHull ℝ (H : Set Plane)) := hIsub
  have hD := diam_union_interiors H I hInt
  have hunique : ∃ a ∈ H ∪ I, ∃ b ∈ H ∪ I, a ≠ b ∧
      dist a b = Metric.diam ((H ∪ I : Finset Plane) : Set Plane) ∧
      ∀ x ∈ H ∪ I, ∀ y ∈ H ∪ I,
        dist x y = Metric.diam ((H ∪ I : Finset Plane) : Set Plane) → s(x,y) = s(a,b) := by
    refine ⟨a,Finset.mem_union_left _ ha,b,Finset.mem_union_left _ hb,hab,
      hdiam.trans hD.symm, ?_⟩
    intro x hx y hy hxy
    have hxH := diameter_endpoint_mem_hull H I (by omega) hInt hx hy hxy
    have hyH := diameter_endpoint_mem_hull H I (by omega) hInt hy hx ((dist_comm y x).trans hxy)
    exact hu x hxH y hyH (hxy.trans (hD.trans hdiam.symm))
  have hclaim := unique_diameter_circle 3 k H I O R (by decide) hk hH hIcard hR hcircle
    ⟨p,hp⟩ hInt hunique
  exact ⟨H,I,O,R,hH,hIcard,hR,hcircle,⟨p,hp⟩,hInt,hunique,hclaim⟩

/-- A concrete joint instance at N = 3 and k = 4 witnesses nonvacuity beyond
three interiors, with the same original unique-diameter assumptions. -/
theorem original_hypotheses_four_interiors : ∃ (H I : Finset Plane) (O : Plane) (R : ℝ),
    H.card = 3 ∧ I.card = 4 ∧ 0 < R ∧ (∀ h ∈ H, dist h O = R) ∧
    (interior (convexHull ℝ (H : Set Plane))).Nonempty ∧
    (∀ i ∈ I, i ∈ interior (convexHull ℝ (H : Set Plane))) ∧
    (∃ a ∈ H ∪ I, ∃ b ∈ H ∪ I, a ≠ b ∧
      dist a b = Metric.diam ((H ∪ I : Finset Plane) : Set Plane) ∧
      ∀ x ∈ H ∪ I, ∀ y ∈ H ∪ I,
        dist x y = Metric.diam ((H ∪ I : Finset Plane) : Set Plane) → s(x,y) = s(a,b)) := by
  obtain ⟨H,I,O,R,hH,hI,hR,hcircle,hfull,hInt,hunique,_⟩ :=
    original_hypotheses_every_positive_k 4 (by decide)
  exact ⟨H,I,O,R,hH,hI,hR,hcircle,hfull,hInt,hunique⟩

end Erdos132.UniqueDiameterCircle
