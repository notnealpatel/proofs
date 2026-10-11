import Erdos.Erdos132.ThreeInteriorCounting
import Erdos.Erdos132.CircleRotationTransport
import Erdos.Erdos132.CircleRotationOrder
import Erdos.Erdos132.CircleShortChord

set_option autoImplicit false

namespace Erdos132.ThreeInteriorCenter

open TwoInteriorCircle CircleRotation

/-- Inserting a genuinely new point adds exactly its distance fiber to the inherited
unordered, loop-free distance multiplicity. Each new pair is counted once. -/
theorem multiplicity_insert (H : Finset Plane) (x : Plane) (d : ℝ) (hx : x ∉ H) :
    multiplicity (insert x H) d = multiplicity H d +
      (H.filter fun y => dist x y = d).card := by
  classical
  let P := (pairs H).filter fun e => pairDist e = d
  let F := H.filter fun y => dist x y = d
  let Q := F.image (fun y => s(x, y))
  have hsplit : ((pairs (insert x H)).filter fun e => pairDist e = d) = P ∪ Q := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      simp only [Finset.mem_filter, mk_mem_pairs, Finset.mem_insert, pairDist_mk,
        Finset.mem_union, P, Q, F, Finset.mem_image, Sym2.eq_iff]
      constructor
      · rintro ⟨⟨rfl | ha, rfl | hb, hab⟩, hd⟩
        · exact False.elim (hab rfl)
        · exact Or.inr ⟨b, ⟨hb, hd⟩, Or.inl ⟨rfl, rfl⟩⟩
        · exact Or.inr ⟨a, ⟨ha, by simpa only [dist_comm] using hd⟩,
            Or.inr ⟨rfl, rfl⟩⟩
        · exact Or.inl ⟨⟨ha, hb, hab⟩, hd⟩
      · rintro (⟨⟨ha, hb, hab⟩, hd⟩ | ⟨y, ⟨hy, hd⟩, he⟩)
        · exact ⟨⟨Or.inr ha, Or.inr hb, hab⟩, hd⟩
        · rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨⟨Or.inl rfl, Or.inr hy, fun he => hx (he ▸ hy)⟩, hd⟩
          · exact ⟨⟨Or.inr hy, Or.inl rfl, fun he => hx (he ▸ hy)⟩,
              by simpa only [dist_comm] using hd⟩
  have hdisjoint : Disjoint P Q := by
    apply Finset.disjoint_left.mpr
    intro e heP heQ
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp heQ
    exact hx ((mk_mem_pairs H x y).mp (Finset.mem_filter.mp heP).1).1
  have hQ : Q.card = F.card :=
    Finset.card_image_of_injective F (Sym2.mkEmbedding x).injective
  unfold TwoInteriorCircle.multiplicity
  rw [hsplit, Finset.card_union_of_disjoint hdisjoint, hQ]

example : TwoInteriorCircle.multiplicity (insert (WithLp.toLp 2 ![1, 0] : Plane)
    ({0} : Finset Plane)) 1 =
    multiplicity ({0} : Finset Plane) 1 + 1 := by
  classical
  rw [multiplicity_insert _ _ _ (by
    simp [WithLp.ext_iff, funext_iff, Fin.forall_fin_two])]
  norm_num [Finset.filter_singleton, dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_two]

/-- A radial fiber gains one point exactly when the newly inserted point has the
specified distance. This counts points, not orientations of unordered pairs. -/
theorem card_radial_filter_insert (H : Finset Plane) (x z : Plane) (d : ℝ)
    (hx : x ∉ H) :
    ((insert x H).filter fun y => dist z y = d).card =
      (H.filter fun y => dist z y = d).card + if dist z x = d then 1 else 0 := by
  classical
  by_cases hd : dist z x = d
  · rw [Finset.filter_insert, if_pos hd, Finset.card_insert_of_notMem]
    · simp [hd]
    · exact fun hm => hx (Finset.mem_filter.mp hm).1
  · simp [Finset.filter_insert, hd]

example : ((insert (WithLp.toLp 2 ![1, 0] : Plane) ({0} : Finset Plane)).filter
    fun y => dist (0 : Plane) y = 1).card = 1 := by
  classical
  norm_num [Finset.filter_insert, Finset.filter_singleton, dist_eq_norm,
    EuclideanSpace.norm_eq, Fin.sum_univ_two]

/-- With two nonzero centers of equal norm and saturated two-point radial fibers,
a non-center-radius class has the exact inherited hull contribution, four radial
pairs, and the three actual interior-pair indicators. No condition separates the
center radius from the distance between the nonzero centers. -/
theorem centered_multiplicity_decomposition (H : Finset Plane) (R d : ℝ) (u v : Plane)
    (hcircle : ∀ h ∈ H, ‖h‖ = R) (h0 : (0 : Plane) ∉ H)
    (hu : u ∉ H) (hv : v ∉ H) (hu0 : u ≠ 0) (hv0 : v ≠ 0) (huv : u ≠ v)
    (hnorm : ‖u‖ = ‖v‖) (hdR : d ≠ R)
    (hfu : (H.filter fun h => dist h u = d).card = 2)
    (hfv : (H.filter fun h => dist h v = d).card = 2) :
    multiplicity (insert (0 : Plane) (insert u (insert v H))) d =
      multiplicity H d + 4 + 2 * (if d = ‖u‖ then 1 else 0) +
        (if d = dist u v then 1 else 0) := by
  classical
  have h0insert : (0 : Plane) ∉ insert u (insert v H) := by
    simp [h0, Ne.symm hu0, Ne.symm hv0]
  have huinsert : u ∉ insert v H := by simp [hu, huv]
  have hf0 : (H.filter fun y => dist (0 : Plane) y = d) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro y hy hdy
    have hRd : R = d := by simpa only [dist_zero_left, hcircle y hy] using hdy
    exact hdR hRd.symm
  rw [multiplicity_insert _ _ _ h0insert,
    multiplicity_insert _ _ _ huinsert, multiplicity_insert _ _ _ hv,
    card_radial_filter_insert _ _ _ _ hv,
    card_radial_filter_insert _ _ _ _ huinsert,
    card_radial_filter_insert _ _ _ _ hv]
  have hfu' : (H.filter fun h => dist u h = d).card = 2 := by
    simpa only [dist_comm] using hfu
  have hfv' : (H.filter fun h => dist v h = d).card = 2 := by
    simpa only [dist_comm] using hfv
  simp only [hfu', hfv', dist_zero_left, ← hnorm]
  have hf0norm : (H.filter fun y => ‖y‖ = d) = ∅ := by
    simpa only [dist_zero_left] using hf0
  rw [hf0norm]
  simp only [Finset.card_empty]
  have hcommr : (if ‖u‖ = d then 1 else 0 : ℕ) =
      if d = ‖u‖ then 1 else 0 := if_congr eq_comm rfl rfl
  have hcommell : (if dist u v = d then 1 else 0 : ℕ) =
      if d = dist u v then 1 else 0 := if_congr eq_comm rfl rfl
  rw [hcommr, hcommell]
  omega

/-- Original odd-order centered geometry under the contrary multiplicity assumption
derives the actual radial support, equal strict interior radii, a nonidentity full
stabilizer transporter, and the exact centered class budget. In particular all
positive non-center-radius hull classes obey the divisibility and deficit premises
of the reviewed rotation-order argument. This is a precursor, not the final
small-multiplicity theorem. -/
theorem centered_contrary_model (n : ℕ) (H : Finset Plane) (R : ℝ) (u v : Plane)
    (hn : 9 ≤ n) (hodd : Odd n) (hH : H.card = n - 3) (hR : 0 < R)
    (hcircle : ∀ h ∈ H, ‖h‖ = R) (hu0 : u ≠ 0) (hv0 : v ≠ 0) (huv : u ≠ v)
    (h0 : (0 : Plane) ∈ interior (convexHull ℝ (H : Set Plane)))
    (hu : u ∈ interior (convexHull ℝ (H : Set Plane)))
    (hv : v ∈ interior (convexHull ℝ (H : Set Plane)))
    (hlarge : ∀ d : ℝ, 0 < d →
      d < Metric.diam ((insert (0 : Plane) (insert u (insert v H)) : Finset Plane) : Set Plane) →
      (∃ a ∈ insert (0 : Plane) (insert u (insert v H)),
        ∃ b ∈ insert (0 : Plane) (insert u (insert v H)), dist a b = d) →
      n + 1 ≤ multiplicity (insert (0 : Plane) (insert u (insert v H))) d) :
    let X := insert (0 : Plane) (insert u (insert v H))
    let S := nonDiameterDistances X
    X.card = n ∧ Metric.diam (X : Set Plane) = Metric.diam (H : Set Plane) ∧
      0 < Metric.diam (H : Set Plane) ∧ H.card = 2 * S.card ∧
      n = 2 * S.card + 3 ∧ 3 ≤ S.card ∧
      0 < ‖u‖ ∧ ‖u‖ < R ∧ ‖u‖ = ‖v‖ ∧
      R ∈ S ∧ ‖u‖ ∈ S ∧ dist u v ∈ S ∧
      H.image (fun h => dist h u) = S ∧ H.image (fun h => dist h v) = S ∧
      (∃ g : Stabilizer H, rotate g.val u = v ∧ g.val ≠ 1) ∧
      2 ≤ order H ∧ order H ∣ H.card ∧
      ∀ d ∈ S, d ≠ R →
        multiplicity X d = multiplicity H d + 4 +
          2 * (if d = ‖u‖ then 1 else 0) + (if d = dist u v then 1 else 0) ∧
        H.card ≤ multiplicity H d +
          2 * (if d = ‖u‖ then 1 else 0) + (if d = dist u v then 1 else 0) ∧
        order H ∣ multiplicity H d ∧ multiplicity H d ≤ H.card := by
  classical
  let X := insert (0 : Plane) (insert u (insert v H))
  let S := nonDiameterDistances X
  obtain ⟨hX, hdiam, hdiampos, hHS, hnS, hS, hrad⟩ :=
    ThreeInteriorCounting.counting_saturation n H R 0 u v hn hodd hH hR
      hcircle (Ne.symm hu0) (Ne.symm hv0) huv h0 hu hv hlarge
  obtain ⟨hsu, hfu, hsatu⟩ := hrad u (by simp) hu0
  obtain ⟨hsv, hfv, hsatv⟩ := hrad v (by simp) hv0
  have hHsix : 6 ≤ H.card := by omega
  have hnonempty : H.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, ha⟩ := (show H.Nonempty from hnonempty)
  have hnorm : ‖u‖ = ‖v‖ :=
    ThreeInteriorRadial.norm_eq_of_saturated_common_support H R u v hHsix hR hu0 hv0
      hcircle hsatu hsatv (hsu.trans hsv.symm)
  have hnormpos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  have hcircle0 : ∀ h ∈ H, dist h (0 : Plane) = R := by
    simpa only [dist_zero_right] using hcircle
  have hnormlt : ‖u‖ < R := by
    simpa only [dist_zero_right] using dist_center_lt_radius H 0 hR hcircle0 hu
  have h0H := ThreeInteriorCounting.interior_not_mem_circle H R 0 hR hcircle h0
  have huH := ThreeInteriorCounting.interior_not_mem_circle H R u hR hcircle hu
  have hvH := ThreeInteriorCounting.interior_not_mem_circle H R v hR hcircle hv
  have hmemR : R ∈ S := by
    apply (ThreeInteriorCounting.mem_nonDiameterDistances_iff_positive X R).mpr
    refine ⟨hR, ?_, 0, by simp [X], a, by simp [X, ha], ?_⟩
    · rw [hdiam]
      have hlt := dist_lt_diam_hull H (by omega) h0 (subset_convexHull ℝ _ ha)
      simpa only [dist_zero_left, hcircle a ha] using hlt
    · simpa only [dist_zero_left] using hcircle a ha
  have hmemr : ‖u‖ ∈ S := by
    apply (ThreeInteriorCounting.mem_nonDiameterDistances_iff_positive X ‖u‖).mpr
    refine ⟨hnormpos, ?_, u, by simp [X], 0, by simp [X], dist_zero_right u⟩
    rw [hdiam]
    simpa only [dist_zero_right] using
      dist_lt_diam_hull H (by omega) hu (interior_subset h0)
  have hmemell : dist u v ∈ S := by
    apply (ThreeInteriorCounting.mem_nonDiameterDistances_iff_positive X (dist u v)).mpr
    refine ⟨dist_pos.mpr huv, ?_, u, by simp [X], v, by simp [X], rfl⟩
    rw [hdiam]
    exact dist_lt_diam_hull H (by omega) hu (interior_subset hv)
  have hsupport : H.image (fun h => dist u h) = H.image (fun h => dist v h) := by
    simpa only [dist_comm] using hsu.trans hsv.symm
  have hfibers : ∀ d ∈ H.image (fun h => dist u h),
      (H.filter fun h => dist u h = d).card = 2 ∧
      (H.filter fun h => dist v h = d).card = 2 := by
    intro d hd
    have hdS : d ∈ S := by
      have hsu' : H.image (fun h => dist u h) = S := by
        simpa only [dist_comm] using hsu
      exact hsu' ▸ hd
    simpa only [dist_comm] using And.intro (hfu d hdS) (hfv d hdS)
  obtain ⟨g, hgu⟩ := CircleRotationTransport.exists_stabilizer_map_of_saturated_common_support
    H R u v hHsix hR hu0 hv0 hcircle hsupport hfibers
  have hg1 : g.val ≠ 1 := by
    intro heq
    exact huv (by simpa only [heq, rotate_one] using hgu)
  letI := finite_stabilizer H hnonempty hR hcircle
  have horder : 2 ≤ order H := by
    apply Nat.succ_le_of_lt
    exact Finite.one_lt_card_iff_nontrivial.mpr
      ⟨⟨g, 1, fun he => hg1 (congrArg Subtype.val he)⟩⟩
  have hdiv : order H ∣ H.card := order_dvd_card H hnonempty hR hcircle
  have hdiambound : Metric.diam (H : Set Plane) ≤ 2 * R := by
    apply Metric.diam_le_of_forall_dist_le (by positivity)
    intro x hx y hy
    calc
      dist x y ≤ ‖x‖ + ‖y‖ := dist_le_norm_add_norm x y
      _ = 2 * R := by rw [hcircle x hx, hcircle y hy]; ring
  refine ⟨hX, hdiam, hdiampos, hHS, hnS, hS, hnormpos, hnormlt, hnorm,
    hmemR, hmemr, hmemell, hsu, hsv, ⟨g, hgu, hg1⟩, horder, hdiv, ?_⟩
  intro d hd hdR
  have hdecomp := centered_multiplicity_decomposition H R d u v hcircle
    h0H huH hvH hu0 hv0 huv hnorm hdR (hfu d hd) (hfv d hd)
  obtain ⟨hdpos, hdlt, hdocc⟩ :=
    (ThreeInteriorCounting.mem_nonDiameterDistances_iff_positive X d).mp hd
  have hbound := hlarge d hdpos hdlt hdocc
  have hdeficit : H.card ≤ multiplicity H d +
      2 * (if d = ‖u‖ then 1 else 0) + (if d = dist u v then 1 else 0) := by
    change n + 1 ≤ multiplicity X d at hbound
    rw [hdecomp] at hbound
    omega
  have hd2R : d < 2 * R := by
    rw [hdiam] at hdlt
    exact hdlt.trans_le hdiambound
  refine ⟨hdecomp, hdeficit,
    order_dvd_multiplicity H hnonempty hR hcircle hdpos hd2R, ?_⟩
  exact chord_capacity H 0 R d hR hcircle0

/-- A six-point antipodal rational unit-circle hull jointly realizes the original
odd-order centered premises: the center and two distinct noncenter points lie in
its ambient interior, and every hull vertex is extreme. The impossible contrary
multiplicity assumption is not included in this satisfiability witness. -/
theorem original_centered_geometry_fixture :
    ∃ (n : ℕ) (H : Finset Plane) (R : ℝ) (u v : Plane),
      9 ≤ n ∧ Odd n ∧ H.card = n - 3 ∧ 0 < R ∧
      (∀ h ∈ H, ‖h‖ = R) ∧
      (∀ h ∈ H, h ∈ (convexHull ℝ (H : Set Plane)).extremePoints ℝ) ∧
      (∀ h ∈ H, -h ∈ H) ∧ u ≠ 0 ∧ v ≠ 0 ∧ u ≠ v ∧
      (0 : Plane) ∈ interior (convexHull ℝ (H : Set Plane)) ∧
      u ∈ interior (convexHull ℝ (H : Set Plane)) ∧
      v ∈ interior (convexHull ℝ (H : Set Plane)) := by
  classical
  let A : Plane := WithLp.toLp 2 ![1,0]
  let B : Plane := WithLp.toLp 2 ![0,1]
  let C : Plane := WithLp.toLp 2 ![-1,0]
  let D : Plane := WithLp.toLp 2 ![0,-1]
  let E : Plane := WithLp.toLp 2 ![3/5,4/5]
  let F : Plane := WithLp.toLp 2 ![-3/5,-4/5]
  let H : Finset Plane := {A,B,C,D,E,F}
  have hcard : H.card = 6 := by
    norm_num [H,A,B,C,D,E,F,Finset.card_insert_of_notMem,WithLp.ext_iff,
      funext_iff,Fin.forall_fin_two]
  have hcircle : ∀ h ∈ H, ‖h‖ = 1 := by
    intro h hh
    have hs : ‖h‖ ^ 2 = 1 := by
      simp only [H,Finset.mem_insert,Finset.mem_singleton] at hh
      rcases hh with rfl | rfl | rfl | rfl | rfl | rfl <;>
        norm_num [EuclideanSpace.norm_sq_eq,Fin.sum_univ_two,A,B,C,D,E,F]
    nlinarith [norm_nonneg h]
  have hanti : ∀ h ∈ H, -h ∈ H := by
    intro h hh
    simp only [H,Finset.mem_insert,Finset.mem_singleton] at hh
    rcases hh with rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [H,A,B,C,D,E,F,WithLp.ext_iff,funext_iff,Fin.forall_fin_two]
  have hA : A ∈ affineSpan ℝ (H : Set Plane) := subset_affineSpan ℝ _ (by simp [H])
  have hB : B ∈ affineSpan ℝ (H : Set Plane) := subset_affineSpan ℝ _ (by simp [H])
  have hC : C ∈ affineSpan ℝ (H : Set Plane) := subset_affineSpan ℝ _ (by simp [H])
  have htop : affineSpan ℝ (H : Set Plane) = ⊤ := by
    apply top_unique
    intro p _hp
    have hv := (affineSpan ℝ (H : Set Plane)).direction.add_mem
      ((affineSpan ℝ (H : Set Plane)).direction.smul_mem (p 1)
        (AffineSubspace.vsub_mem_direction hB hA))
      ((affineSpan ℝ (H : Set Plane)).direction.smul_mem ((1-p 0-p 1)/2)
        (AffineSubspace.vsub_mem_direction hC hA))
    have hm := AffineSubspace.vadd_mem_of_mem_direction hv hA
    have he : (p 1 • (B -ᵥ A) + ((1-p 0-p 1)/2) • (C -ᵥ A)) +ᵥ A = p := by
      ext i
      fin_cases i <;> simp [A,B,C] <;> ring
    rwa [he] at hm
  obtain ⟨z, hz⟩ := interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr htop
  have hnegset : -(H : Set Plane) = (H : Set Plane) := by
    ext x
    simp only [Set.mem_neg, Finset.mem_coe]
    exact ⟨fun hx => by simpa only [neg_neg] using hanti (-x) hx, hanti x⟩
  have hneghull : -(convexHull ℝ (H : Set Plane)) = convexHull ℝ (H : Set Plane) := by
    rw [← convexHull_neg, hnegset]
  have hnz : -z ∈ interior (convexHull ℝ (H : Set Plane)) := by
    have himage := (Homeomorph.neg Plane).image_interior (convexHull ℝ (H : Set Plane))
    have hmem : -z ∈ (Homeomorph.neg Plane) '' interior (convexHull ℝ (H : Set Plane)) :=
      ⟨z, hz, rfl⟩
    rw [himage] at hmem
    change -z ∈ interior ((fun x : Plane => -x) '' convexHull ℝ (H : Set Plane)) at hmem
    rwa [Set.image_neg_eq_neg, hneghull] at hmem
  have h0 : (0 : Plane) ∈ interior (convexHull ℝ (H : Set Plane)) := by
    have hm := (convex_convexHull ℝ (H : Set Plane)).interior.midpoint_mem hz hnz
    simpa only [midpoint_self_neg] using hm
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior 0 h0
  let u := (ε / 2) • A
  let v := -u
  have hnA : ‖A‖ = 1 := hcircle A (by simp [H])
  have hnu : ‖u‖ = ε / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < ε / 2), hnA, mul_one]
  have hnv : ‖v‖ = ε / 2 := by rw [norm_neg, hnu]
  have hu0 : u ≠ 0 := norm_pos_iff.mp (by rw [hnu]; linarith)
  have hv0 : v ≠ 0 := norm_pos_iff.mp (by rw [hnv]; linarith)
  have huv : u ≠ v := by
    intro he
    have hz2 : u + u = 0 := by
      calc
        u + u = u + v := congrArg (fun w : Plane => u + w) he
        _ = 0 := by simp [v]
    have hucoord : ∀ i : Fin 2, u i = 0 := by
      intro i
      have hc := congrArg (fun x : Plane => x i) hz2
      simp only [PiLp.add_apply, PiLp.zero_apply] at hc
      linarith
    exact hu0 (by ext i; exact hucoord i)
  have hu : u ∈ interior (convexHull ℝ (H : Set Plane)) :=
    hball (by rw [Metric.mem_ball, dist_zero_right, hnu]; linarith)
  have hv : v ∈ interior (convexHull ℝ (H : Set Plane)) :=
    hball (by rw [Metric.mem_ball, dist_zero_right, hnv]; linarith)
  have hext : ∀ h ∈ H, h ∈ (convexHull ℝ (H : Set Plane)).extremePoints ℝ := by
    intro h hh
    have hsub : convexHull ℝ (H : Set Plane) ⊆ Metric.closedBall (0 : Plane) 1 :=
      convexHull_min (by intro a ha; simpa [Metric.mem_closedBall,hcircle a ha])
        (convex_closedBall 0 1)
    apply inter_extremePoints_subset_extremePoints_of_subset hsub
    exact ⟨subset_convexHull ℝ _ hh,
      StrictConvexSpace.sphere_subset_extremePoints_closedBall 0 (by norm_num)
        (by simpa [Metric.mem_sphere] using hcircle h hh)⟩
  refine ⟨9, H, 1, u, v, by decide, ⟨4, by decide⟩, ?_, by norm_num,
    hcircle, hext, hanti, hu0, hv0, huv, h0, hu, hv⟩
  simpa using hcard

/-- A divisible class cannot have a positive deficit smaller than the divisor.
The upper bound guards the natural subtraction used only inside the proof. -/
theorem eq_of_divisible_small_remainder (M N h t : ℕ) (hMN : M ∣ N) (hMh : M ∣ h)
    (hle : h ≤ N) (hcover : N ≤ h + t) (ht : t < M) : h = N := by
  have hsmall : N - h < M := by omega
  have hzero : N - h = 0 := Nat.eq_zero_of_dvd_of_lt (Nat.dvd_sub hMN hMh) hsmall
  omega

example : (8 : ℕ) = 8 :=
  eq_of_divisible_small_remainder 4 8 8 3 (by decide) (by decide)
    (by decide) (by decide) (by decide)

private theorem saturation_of_centered_model (H : Finset Plane) (S : Finset ℝ)
    (R : ℝ) (u v : Plane) (hR : 0 < R) (hcircle : ∀ h ∈ H, ‖h‖ = R)
    (hH : 6 ≤ H.card) (hS : 3 ≤ S.card) (hu : u ≠ 0)
    (hg : ∃ g : Stabilizer H, rotate g.val u = v ∧ g.val ≠ 1)
    (horder : 2 ≤ order H) (hdiv : order H ∣ H.card)
    (hpositive : ∀ d ∈ S, 0 < d ∧ d < 2 * R)
    (hbudget : ∀ d ∈ S, d ≠ R →
      H.card ≤ multiplicity H d + 2 * (if d = ‖u‖ then 1 else 0) +
        (if d = dist u v then 1 else 0) ∧
      order H ∣ multiplicity H d ∧ multiplicity H d ≤ H.card) :
    3 ≤ order H ∧ ∀ d ∈ S, d ≠ R → multiplicity H d = H.card := by
  classical
  have hnot2 : order H ≠ 2 := by
    intro htwo
    have hex : ∃ d ∈ S, d ≠ R ∧ d ≠ ‖u‖ := by
      by_contra hno
      push Not at hno
      have hsub : S ⊆ {R, ‖u‖} := by
        intro d hd
        by_cases hdR : d = R
        · simp [hdR]
        · simp [hno d hd hdR]
      have hcard := Finset.card_le_card hsub
      have htwo : ({R, ‖u‖} : Finset ℝ).card ≤ 2 :=
        (Finset.card_insert_le R {‖u‖}).trans (by simp)
      omega
    obtain ⟨d, hd, hdR, hdr⟩ := hex
    obtain ⟨hcover, hdh, hupper⟩ := hbudget d hd hdR
    have ht : (2 * (if d = ‖u‖ then 1 else 0) +
        (if d = dist u v then 1 else 0) : ℕ) < order H := by
      rw [htwo, if_neg hdr]
      split_ifs <;> omega
    have hsat : multiplicity H d = H.card :=
      eq_of_divisible_small_remainder (order H) H.card (multiplicity H d)
        _ hdiv hdh hupper (by omega) ht
    have hpos : 0 < ((pairs H).filter fun e => pairDist e = d).card := by
      change 0 < multiplicity H d
      rw [hsat]
      omega
    obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
    induction e using Sym2.ind with
    | _ a b =>
      obtain ⟨ha, hb, _hab⟩ := (mk_mem_pairs H a b).mp (Finset.mem_filter.mp he).1
      have habd : dist a b = d := (Finset.mem_filter.mp he).2
      obtain ⟨k, _hmap, hk1, hkneg⟩ := exists_stabilizer_map_of_saturated_chord H hR
        hcircle (hpositive d hd).1 (hpositive d hd).2 hsat ha hb habd
      exact hkneg (eq_neg_one_of_order_eq_two H htwo k hk1)
  have hthree : 3 ≤ order H := by omega
  refine ⟨hthree, ?_⟩
  intro d hd hdR
  obtain ⟨hcover, hdh, hupper⟩ := hbudget d hd hdR
  have ht : (2 * (if d = ‖u‖ then 1 else 0) +
      (if d = dist u v then 1 else 0) : ℕ) < order H := by
    by_cases horder3 : order H = 3
    · obtain ⟨g, hgu, hg1⟩ := hg
      have hsquare : dist u v ^ 2 = 3 * ‖u‖ ^ 2 := by
        rw [← hgu]
        exact dist_rotate_sq_of_order_eq_three H horder3 g hg1 u
      have hellr : dist u v ≠ ‖u‖ := by
        intro heq
        rw [heq] at hsquare
        have hnormpos := norm_pos_iff.mpr hu
        nlinarith
      rw [horder3]
      by_cases hdr : d = ‖u‖
      · have hdell : d ≠ dist u v := by
          intro heq
          exact hellr (heq.symm.trans hdr)
        rw [if_pos hdr, if_neg hdell]
        decide
      · rw [if_neg hdr]
        split_ifs <;> omega
    · have hfour : 4 ≤ order H := by omega
      split_ifs <;> omega
  exact eq_of_divisible_small_remainder (order H) H.card (multiplicity H d)
    _ hdiv hdh hupper (by omega) ht

/-- Under the original odd-order centered geometry and contrary multiplicities,
the full rotation order is at least three and every actual non-diameter class
other than the center radius is saturated on the hull. The order-two obstruction
uses an actual new chord transporter; the order-three case uses the proved orbit
metric. The possible coincidence of the center radius and interior chord is retained. -/
theorem centered_contrary_saturation (n : ℕ) (H : Finset Plane) (R : ℝ) (u v : Plane)
    (hn : 9 ≤ n) (hodd : Odd n) (hH : H.card = n - 3) (hR : 0 < R)
    (hcircle : ∀ h ∈ H, ‖h‖ = R) (hu0 : u ≠ 0) (hv0 : v ≠ 0) (huv : u ≠ v)
    (h0 : (0 : Plane) ∈ interior (convexHull ℝ (H : Set Plane)))
    (hu : u ∈ interior (convexHull ℝ (H : Set Plane)))
    (hv : v ∈ interior (convexHull ℝ (H : Set Plane)))
    (hlarge : ∀ d : ℝ, 0 < d →
      d < Metric.diam ((insert (0 : Plane) (insert u (insert v H)) : Finset Plane) : Set Plane) →
      (∃ a ∈ insert (0 : Plane) (insert u (insert v H)),
        ∃ b ∈ insert (0 : Plane) (insert u (insert v H)), dist a b = d) →
      n + 1 ≤ multiplicity (insert (0 : Plane) (insert u (insert v H))) d) :
    3 ≤ order H ∧ ∀ d ∈ nonDiameterDistances (insert (0 : Plane) (insert u (insert v H))),
      d ≠ R → multiplicity H d = H.card := by
  classical
  obtain ⟨_hX, hdiam, _hdiampos, _hHS, _hnS, hS, _hrpos, _hrlt, _hnorm,
    _hmemR, _hmemr, _hmemell, _hsu, _hsv, hg, horder, hdiv, hclasses⟩ :=
    centered_contrary_model n H R u v hn hodd hH hR hcircle hu0 hv0 huv h0 hu hv hlarge
  have hdiambound : Metric.diam (H : Set Plane) ≤ 2 * R := by
    apply Metric.diam_le_of_forall_dist_le (by positivity)
    intro x hx y hy
    calc
      dist x y ≤ ‖x‖ + ‖y‖ := dist_le_norm_add_norm x y
      _ = 2 * R := by rw [hcircle x hx, hcircle y hy]; ring
  apply saturation_of_centered_model H _ R u v hR hcircle (by omega) hS hu0
    hg horder hdiv
  · intro d hd
    obtain ⟨hdpos, hdlt, _hdocc⟩ :=
      (ThreeInteriorCounting.mem_nonDiameterDistances_iff_positive _ d).mp hd
    rw [hdiam] at hdlt
    exact ⟨hdpos, hdlt.trans_le hdiambound⟩
  · intro d hd hdR
    exact (hclasses d hd hdR).2

private theorem hull_rotation_image_card (H : Finset Plane) (R : ℝ)
    (hH : H.Nonempty) (hR : 0 < R) (hcircle : ∀ h ∈ H, ‖h‖ = R)
    (a : Plane) (ha : a ∈ H) :
    ∃ A : Finset Plane, A ⊆ H ∧ A.card = order H ∧ a ∈ A ∧
      ∀ x : Plane, x ∈ A ↔ ∃ g : Stabilizer H, rotate g.val a = x := by
  classical
  letI := finite_stabilizer H hH hR hcircle
  letI := Fintype.ofFinite (Stabilizer H)
  let A := Finset.univ.image (fun g : Stabilizer H => rotate g.val a)
  have hinj : Function.Injective (fun g : Stabilizer H => rotate g.val a) := by
    intro g k he
    exact Subtype.ext (rotate_coeff_injective a (ne_zero_of_norm_eq hR (hcircle a ha)) he)
  refine ⟨A, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨g, _hg, rfl⟩ := Finset.mem_image.mp hx
    exact (g.property a).2 ha
  · simp only [A, Finset.card_image_of_injective _ hinj, Finset.card_univ,
      order, Nat.card_eq_fintype_card]
  · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rotate_one a⟩
  · intro x
    simp [A]

/-- If every actual hull class below the diameter except `R` is saturated,
then odd full rotation order at least three forces exactly six hull vertices and
order three. This is the outside-orbit reduction, not yet the hexagon exclusion. -/
theorem order_three_card_six_of_odd_saturation (H : Finset Plane) (R : ℝ)
    (hH : 6 ≤ H.card) (hHeven : Even H.card) (hR : 0 < R)
    (hcircle : ∀ h ∈ H, ‖h‖ = R) (horder : 3 ≤ order H) (hodd : Odd (order H))
    (hsat : ∀ a ∈ H, ∀ b ∈ H, dist a b ≠ R →
      0 < dist a b → dist a b < Metric.diam (H : Set Plane) →
      multiplicity H (dist a b) = H.card) : order H = 3 ∧ H.card = 6 := by
  classical
  have hnonempty : H.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, ha⟩ := (show H.Nonempty from hnonempty)
  obtain ⟨A, hAH, hAcard, haA, hAorbit⟩ :=
    hull_rotation_image_card H R hnonempty hR hcircle a ha
  let B := H \ A
  have hbound : Metric.diam (H : Set Plane) ≤ 2 * R := by
    apply Metric.diam_le_of_forall_dist_le (by positivity)
    intro x hx y hy
    calc
      dist x y ≤ ‖x‖ + ‖y‖ := dist_le_norm_add_norm x y
      _ = 2 * R := by rw [hcircle x hx, hcircle y hy]; ring
  have hsub : B ⊆ (H.filter fun x => dist x a = R) ∪
      (H.filter fun x => dist x a = Metric.diam (H : Set Plane)) := by
    intro b hb
    obtain ⟨hbH, hbA⟩ := Finset.mem_sdiff.mp hb
    by_cases hdR : dist a b = R
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hbH,
        (dist_comm b a).trans hdR⟩)
    · have hab : a ≠ b := by
        intro he
        exact hbA (he ▸ haA)
      have hle : dist a b ≤ Metric.diam (H : Set Plane) :=
        Metric.dist_le_diam_of_mem H.finite_toSet.isBounded ha hbH
      have heq : dist a b = Metric.diam (H : Set Plane) := by
        by_contra hne
        have hlt : dist a b < Metric.diam (H : Set Plane) := lt_of_le_of_ne hle hne
        obtain ⟨g, hgab, _hg1, _hgneg⟩ := exists_stabilizer_map_of_saturated_chord H hR
          hcircle (dist_pos.mpr hab) (hlt.trans_le hbound)
          (hsat a ha b hbH hdR (dist_pos.mpr hab) hlt) ha hbH rfl
        exact hbA ((hAorbit b).mpr ⟨g, hgab⟩)
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hbH,
        (dist_comm b a).trans heq⟩)
  have hcR : (H.filter fun x => dist x a = R).card ≤ 2 := by
    apply radial_card_le_two H 0 a R R
    · simpa only [dist_zero_right] using hcircle
    · exact ne_zero_of_norm_eq hR (hcircle a ha)
  have hcD : (H.filter fun x => dist x a = Metric.diam (H : Set Plane)).card ≤ 2 := by
    apply radial_card_le_two H 0 a R _
    · simpa only [dist_zero_right] using hcircle
    · exact ne_zero_of_norm_eq hR (hcircle a ha)
  have hBfour : B.card ≤ 4 :=
    (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by omega))
  have hBcard : B.card = H.card - order H := by
    rw [Finset.card_sdiff_of_subset hAH, hAcard]
  obtain ⟨k, hk⟩ := order_dvd_card H hnonempty hR hcircle
  have hkeven : Even k := by
    rcases Nat.even_mul.mp (hk ▸ hHeven) with hMeven | hkEven
    · obtain ⟨j, hj⟩ := hMeven
      obtain ⟨i, hi⟩ := hodd
      omega
    · exact hkEven
  obtain ⟨j, hj⟩ := hkeven
  have hjpos : 0 < j := by
    by_contra hno
    have hjzero : j = 0 := by omega
    rw [hjzero] at hj
    rw [hj] at hk
    simp only [zero_add, mul_zero] at hk
    omega
  have hdouble : 2 * order H ≤ H.card := by
    rw [hk, hj]
    nlinarith
  have hMfour : order H ≤ 4 := by omega
  have hMthree : order H = 3 := by
    obtain ⟨j, hj⟩ := hodd
    omega
  have hNsix : H.card = 6 := by
    rw [hMthree] at hk hBcard
    obtain ⟨j, hj⟩ := hHeven
    omega
  exact ⟨hMthree, hNsix⟩

private theorem square_mem_stabilizer_of_re_half (H : Finset Plane)
    (horder : order H = 3) (k : Stabilizer H) (hk : k.val ≠ 1)
    (g : Rotation) (hg : (g : ℂ).re = (1 / 2 : ℝ)) : g ^ 2 ∈ Stabilizer H := by
  have hn := Circle.normSq_coe g
  simp only [Complex.normSq_apply] at hn
  have hgre : ((g ^ 2 : Rotation) : ℂ).re = -(1 / 2 : ℝ) := by
    change ((g : ℂ) ^ 2).re = -(1 / 2 : ℝ)
    simp only [pow_two, Complex.mul_re]
    nlinarith
  have hn2 := Circle.normSq_coe (g ^ 2)
  simp only [Complex.normSq_apply] at hn2
  let z : ℂ := ((g ^ 2 : Rotation) : ℂ)
  change z.re = -(1 / 2 : ℝ) at hgre
  change z.re * z.re + z.im * z.im = 1 at hn2
  have hq : (((g ^ 2 : Rotation) : ℂ)) ^ 2 + (((g ^ 2 : Rotation) : ℂ)) + 1 = 0 := by
    change z ^ 2 + z + 1 = 0
    apply Complex.ext
    · simp only [pow_two, Complex.add_re, Complex.mul_re, Complex.one_re, Complex.zero_re]
      nlinarith
    · simp only [pow_two, Complex.add_im, Complex.mul_im, Complex.one_im, Complex.zero_im]
      rw [hgre]
      ring
  have hkq := quadratic_eq_zero_of_order_eq_three H horder k hk
  have hkc : (k.val : ℂ) ^ 3 = 1 := by
    simpa only [Circle.coe_pow, Circle.coe_one] using
      congrArg (fun z : Rotation => (z : ℂ)) (cube_eq_one_of_order_eq_three H horder k)
  have hfactor : ((((g ^ 2 : Rotation) : ℂ)) - (k.val : ℂ)) *
      ((((g ^ 2 : Rotation) : ℂ)) - (k.val : ℂ) ^ 2) = 0 := by
    calc
      _ = (((g ^ 2 : Rotation) : ℂ)) ^ 2 - (((g ^ 2 : Rotation) : ℂ)) *
          ((k.val : ℂ) ^ 2 + (k.val : ℂ)) + (k.val : ℂ) ^ 3 := by ring
      _ = 0 := by
        rw [show (k.val : ℂ) ^ 2 + (k.val : ℂ) = -1 by linear_combination hkq, hkc]
        linear_combination hq
  rcases mul_eq_zero.mp hfactor with he | he
  · have heq : g ^ 2 = k.val := Circle.ext (sub_eq_zero.mp he)
    rw [heq]
    exact k.property
  · have heq : g ^ 2 = k.val ^ 2 := Circle.ext (by
      simpa only [Circle.coe_pow] using sub_eq_zero.mp he)
    rw [heq]
    exact (Stabilizer H).pow_mem k.property 2

private theorem six_vertex_order_three_impossible (H : Finset Plane) (R : ℝ)
    (hcard : H.card = 6) (hR : 0 < R) (hcircle : ∀ h ∈ H, ‖h‖ = R)
    (horder : order H = 3) (k : Stabilizer H) (hk : k.val ≠ 1)
    (hsat : ∀ a ∈ H, ∀ b ∈ H, dist a b ≠ R →
      0 < dist a b → dist a b < Metric.diam (H : Set Plane) →
      multiplicity H (dist a b) = H.card) : False := by
  classical
  have hnonempty : H.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, ha⟩ := (show H.Nonempty from hnonempty)
  obtain ⟨A, hAH, hAcard, haA, hAorbit⟩ :=
    hull_rotation_image_card H R hnonempty hR hcircle a ha
  let B := H \ A
  have hBcard : B.card = 3 := by
    rw [Finset.card_sdiff_of_subset hAH, hAcard, horder, hcard]
  have hAmap : ∀ l : Stabilizer H, ∀ x ∈ A, rotate l.val x ∈ A := by
    intro l x hx
    obtain ⟨m, hm⟩ := (hAorbit x).mp hx
    apply (hAorbit _).mpr
    refine ⟨l * m, ?_⟩
    change rotate (l.val * m.val) a = rotate l.val x
    rw [rotate_mul, hm]
  have hbound : Metric.diam (H : Set Plane) ≤ 2 * R := by
    apply Metric.diam_le_of_forall_dist_le (by positivity)
    intro x hx y hy
    calc
      dist x y ≤ ‖x‖ + ‖y‖ := dist_le_norm_add_norm x y
      _ = 2 * R := by rw [hcircle x hx, hcircle y hy]; ring
  have hex : ∃ b ∈ B, dist a b = R := by
    by_contra hno
    push Not at hno
    have hsub : B ⊆ H.filter fun x => dist x a = Metric.diam (H : Set Plane) := by
      intro b hb
      obtain ⟨hbH, hbA⟩ := Finset.mem_sdiff.mp hb
      have hab : a ≠ b := by
        intro he
        exact hbA (he ▸ haA)
      have hle : dist a b ≤ Metric.diam (H : Set Plane) :=
        Metric.dist_le_diam_of_mem H.finite_toSet.isBounded ha hbH
      have heq : dist a b = Metric.diam (H : Set Plane) := by
        by_contra hne
        have hlt := lt_of_le_of_ne hle hne
        obtain ⟨g, hgab, _hg1, _hgneg⟩ := exists_stabilizer_map_of_saturated_chord H hR
          hcircle (dist_pos.mpr hab) (hlt.trans_le hbound)
          (hsat a ha b hbH (hno b hb) (dist_pos.mpr hab) hlt) ha hbH rfl
        exact hbA ((hAorbit b).mpr ⟨g, hgab⟩)
      exact Finset.mem_filter.mpr ⟨hbH, (dist_comm b a).trans heq⟩
    have hcD : (H.filter fun x => dist x a = Metric.diam (H : Set Plane)).card ≤ 2 := by
      apply radial_card_le_two H 0 a R _
      · simpa only [dist_zero_right] using hcircle
      · exact ne_zero_of_norm_eq hR (hcircle a ha)
    have hle := Finset.card_le_card hsub
    omega
  obtain ⟨b, hbB, habR⟩ := hex
  obtain ⟨hbH, hbA⟩ := Finset.mem_sdiff.mp hbB
  obtain ⟨C, hCH, hCcard, hbC, hCorbit⟩ :=
    hull_rotation_image_card H R hnonempty hR hcircle b hbH
  have hCB : C ⊆ B := by
    intro x hx
    refine Finset.mem_sdiff.mpr ⟨hCH hx, ?_⟩
    intro hxA
    obtain ⟨l, hl⟩ := (hCorbit x).mp hx
    have hbA' := hAmap l⁻¹ x hxA
    rw [← hl, ← rotate_mul] at hbA'
    change rotate (l.val⁻¹ * l.val) b ∈ A at hbA'
    rw [inv_mul_cancel, rotate_one] at hbA'
    exact hbA hbA'
  have hCB_eq : C = B := Finset.eq_of_subset_of_card_le hCB (by omega)
  obtain ⟨g, hga⟩ := exists_rotation_map hR (hcircle a ha) (hcircle b hbH)
  have hgnorm : ‖(g : ℂ) - 1‖ ^ 2 = 1 := by
    have hdisp : R = ‖(g : ℂ) - 1‖ * R := by
      calc
        R = dist b a := habR.symm.trans (dist_comm a b)
        _ = ‖(g : ℂ) - 1‖ * R := by rw [← hga, dist_rotate_self, hcircle a ha]
    have hglen : ‖(g : ℂ) - 1‖ = 1 := by nlinarith
    rw [hglen]
    norm_num
  have hre : (g : ℂ).re = (1 / 2 : ℝ) := by
    have hn := Circle.normSq_coe g
    rw [Complex.sq_norm] at hgnorm
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im] at hn hgnorm
    nlinarith
  have hg2 := square_mem_stabilizer_of_re_half H horder k hk g hre
  have hgb : rotate g b = rotate (g ^ 2) a := by
    rw [← hga, ← rotate_mul, pow_two]
  have hmap : ∀ x ∈ H, rotate g x ∈ H := by
    intro x hx
    by_cases hxA : x ∈ A
    · obtain ⟨l, hl⟩ := (hAorbit x).mp hxA
      have hgx : rotate g x = rotate l.val b := by
        rw [← hl, ← rotate_mul, mul_comm g l.val, rotate_mul, hga]
      rw [hgx]
      exact hCH ((hCorbit _).mpr ⟨l, rfl⟩)
    · have hxB : x ∈ B := Finset.mem_sdiff.mpr ⟨hx, hxA⟩
      obtain ⟨l, hl⟩ := (hCorbit x).mp (hCB_eq.symm ▸ hxB)
      have hgx : rotate g x = rotate l.val (rotate (g ^ 2) a) := by
        rw [← hl, ← rotate_mul, mul_comm g l.val, rotate_mul, hgb]
      rw [hgx]
      exact hAH (hAmap l _ (hAmap ⟨g ^ 2, hg2⟩ a haA))
  have hgH : g ∈ Stabilizer H := by
    apply (mem_stabilizer_iff_image H g).mpr
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact hmap y hy
    · rw [Finset.card_image_of_injective _ (rotate_isometry g).injective]
  have hg1 : g ≠ 1 := by
    intro he
    have heR := hre
    rw [he] at heR
    norm_num at heR
  have hre' := re_eq_neg_half_of_order_eq_three H horder ⟨g, hgH⟩ hg1
  change (g : ℂ).re = -(1 / 2 : ℝ) at hre'
  linarith

/-- Saturated actual hull classes other than the radius force even full rotation
order. The odd obstruction reduces to two actual cubic orbits; a radius-length
transporter swaps them and hence lies in the full group, a contradiction. -/
theorem even_order_of_saturation (H : Finset Plane) (R : ℝ)
    (hH : 6 ≤ H.card) (hHeven : Even H.card) (hR : 0 < R)
    (hcircle : ∀ h ∈ H, ‖h‖ = R) (horder : 3 ≤ order H)
    (k : Stabilizer H) (hk : k.val ≠ 1)
    (hsat : ∀ a ∈ H, ∀ b ∈ H, dist a b ≠ R →
      0 < dist a b → dist a b < Metric.diam (H : Set Plane) →
      multiplicity H (dist a b) = H.card) : Even (order H) := by
  rcases Nat.even_or_odd (order H) with heven | hodd
  · exact heven
  · obtain ⟨hthree, hsix⟩ := order_three_card_six_of_odd_saturation
      H R hH hHeven hR hcircle horder hodd hsat
    exact False.elim (six_vertex_order_three_impossible H R hsix hR hcircle hthree k hk hsat)

/-- The original odd-order centered geometry and contrary multiplicities force
an even FULL hull rotation order. No order, symmetry, or support certificate is
assumed: the order-two, cubic, and outside-orbit obstructions are discharged above. -/
theorem centered_contrary_even_order (n : ℕ) (H : Finset Plane) (R : ℝ) (u v : Plane)
    (hn : 9 ≤ n) (hodd : Odd n) (hH : H.card = n - 3) (hR : 0 < R)
    (hcircle : ∀ h ∈ H, ‖h‖ = R) (hu0 : u ≠ 0) (hv0 : v ≠ 0) (huv : u ≠ v)
    (h0 : (0 : Plane) ∈ interior (convexHull ℝ (H : Set Plane)))
    (hu : u ∈ interior (convexHull ℝ (H : Set Plane)))
    (hv : v ∈ interior (convexHull ℝ (H : Set Plane)))
    (hlarge : ∀ d : ℝ, 0 < d →
      d < Metric.diam ((insert (0 : Plane) (insert u (insert v H)) : Finset Plane) : Set Plane) →
      (∃ a ∈ insert (0 : Plane) (insert u (insert v H)),
        ∃ b ∈ insert (0 : Plane) (insert u (insert v H)), dist a b = d) →
      n + 1 ≤ multiplicity (insert (0 : Plane) (insert u (insert v H))) d) : Even (order H) := by
  classical
  obtain ⟨_hX, hdiam, _hdiampos, hHS, _hnS, _hS, _hrpos, _hrlt, _hnorm,
    _hmemR, _hmemr, _hmemell, _hsu, _hsv, hg, _horder, _hdiv, _hclasses⟩ :=
    centered_contrary_model n H R u v hn hodd hH hR hcircle hu0 hv0 huv h0 hu hv hlarge
  obtain ⟨horder, hsaturated⟩ :=
    centered_contrary_saturation n H R u v hn hodd hH hR hcircle hu0 hv0 huv h0 hu hv hlarge
  obtain ⟨k, _hku, hk⟩ := hg
  have hHeven : Even H.card := ⟨(nonDiameterDistances
      (insert (0 : Plane) (insert u (insert v H)))).card, by omega⟩
  apply even_order_of_saturation H R (by omega) hHeven hR hcircle horder k hk
  intro a ha b hb hdR hdpos hdlt
  apply hsaturated (dist a b) _ hdR
  apply (ThreeInteriorCounting.mem_nonDiameterDistances_iff_positive _ _).mpr
  refine ⟨hdpos, ?_, a, by simp [ha], b, by simp [hb], rfl⟩
  rw [hdiam]
  exact hdlt

private theorem antipodal_diam (H : Finset Plane) (R : ℝ)
    (hH : H.Nonempty) (hR : 0 < R) (hcircle : ∀ x ∈ H, ‖x‖ = R)
    (hsym : ∀ x ∈ H, -x ∈ H) : Metric.diam (H : Set Plane) = 2 * R := by
  obtain ⟨a, ha⟩ := hH
  have hanti : dist a (-a) = 2 * R := by
    rw [dist_eq_norm, sub_neg_eq_add, ← two_smul ℝ a, norm_smul,
      Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2), hcircle a ha]
  apply le_antisymm
  · apply Metric.diam_le_of_forall_dist_le (by positivity)
    intro x hx y hy
    calc
      dist x y ≤ ‖x‖ + ‖y‖ := dist_le_norm_add_norm x y
      _ = 2 * R := by rw [hcircle x hx, hcircle y hy]; ring
  · rw [← hanti]
    exact Metric.dist_le_diam_of_mem H.finite_toSet.isBounded ha (hsym a ha)

private theorem saturated_neighbors_exhaust (H : Finset Plane) (T : Finset ℝ)
    (R : ℝ) (hR : 0 < R) (hcircle : ∀ x ∈ H, ‖x‖ = R)
    (hsym : ∀ x ∈ H, -x ∈ H) (hcard : H.card = 2 * T.card + 2)
    (hT : ∀ d ∈ T, 0 < d ∧ d < 2 * R)
    (hsat : ∀ d ∈ T, multiplicity H d = H.card) (a : Plane) (ha : a ∈ H) :
    ∀ b ∈ H, b ≠ a → b ≠ -a → dist b a ∈ T := by
  classical
  let F := H.filter fun b => dist b a ∈ T
  let B := H \ {a, -a}
  have hanti : dist (-a) a = 2 * R := by
    rw [dist_comm, dist_eq_norm, sub_neg_eq_add, ← two_smul ℝ a, norm_smul,
      Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2), hcircle a ha]
  have hane : a ≠ -a := by
    intro he
    rw [← he, dist_self] at hanti
    linarith
  have hFcard : F.card = 2 * T.card := by
    have hmap : ∀ b ∈ F, dist b a ∈ T := by
      intro b hb
      exact (Finset.mem_filter.mp hb).2
    rw [Finset.card_eq_sum_card_fiberwise hmap]
    have hfiber : ∀ d ∈ T, (F.filter fun b => dist b a = d).card = 2 := by
      intro d hd
      have he : F.filter (fun b => dist b a = d) = H.filter (fun b => dist b a = d) := by
        ext b
        simp only [F, Finset.mem_filter]
        constructor
        · rintro ⟨⟨hb, _hbd⟩, heq⟩
          exact ⟨hb, heq⟩
        · rintro ⟨hb, heq⟩
          exact ⟨⟨hb, heq ▸ hd⟩, heq⟩
      rw [he]
      exact chord_neighbors_card_eq_two H hR hcircle (hT d hd).1 (hsat d hd) a ha
    calc
      _ = ∑ _d ∈ T, 2 := Finset.sum_congr rfl hfiber
      _ = 2 * T.card := by simp [Nat.mul_comm]
  have hFB : F ⊆ B := by
    intro b hb
    obtain ⟨hbH, hbd⟩ := Finset.mem_filter.mp hb
    refine Finset.mem_sdiff.mpr ⟨hbH, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (rfl | rfl)
    · have hp := (hT 0 (by simpa using hbd)).1
      exact (lt_irrefl 0) hp
    · have hp := (hT (2 * R) (hanti ▸ hbd)).2
      exact (lt_irrefl _) hp
  have hBcard : B.card = H.card - 2 := by
    rw [Finset.card_sdiff_of_subset, Finset.card_pair hane]
    intro b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl
    · exact ha
    · exact hsym a ha
  have hFB_eq : F = B := Finset.eq_of_subset_of_card_le hFB (by omega)
  intro b hb hba hbneg
  have hbB : b ∈ B := by
    exact Finset.mem_sdiff.mpr ⟨hb, by simpa using And.intro hba hbneg⟩
  have hbF : b ∈ F := hFB_eq.symm ▸ hbB
  change b ∈ H.filter (fun x => dist x a ∈ T) at hbF
  exact (Finset.mem_filter.mp hbF).2

private theorem support_exhaustion (H : Finset Plane) (S : Finset ℝ) (R : ℝ)
    (hH : H.Nonempty) (hR : 0 < R) (hcircle : ∀ x ∈ H, ‖x‖ = R)
    (hsym : ∀ x ∈ H, -x ∈ H) (hcard : H.card = 2 * S.card) (hRS : R ∈ S)
    (hS : ∀ d ∈ S, 0 < d ∧ d < 2 * R)
    (hHS : ∀ d ∈ nonDiameterDistances H, d ∈ S)
    (hsat : ∀ d ∈ S, d ≠ R → multiplicity H d = H.card) :
    multiplicity H R = 0 ∧ nonDiameterDistances H = S.erase R := by
  classical
  let T := S.erase R
  have hTcard : H.card = 2 * T.card + 2 := by
    have hc := Finset.card_erase_add_one hRS
    change (S.erase R).card + 1 = S.card at hc
    dsimp only [T]
    omega
  have hTd : ∀ d ∈ T, 0 < d ∧ d < 2 * R := by
    intro d hd
    exact hS d (Finset.mem_erase.mp hd).2
  have hTsat : ∀ d ∈ T, multiplicity H d = H.card := by
    intro d hd
    obtain ⟨hdR, hdS⟩ := Finset.mem_erase.mp hd
    exact hsat d hdS hdR
  have hneighbor := saturated_neighbors_exhaust H T R hR hcircle hsym hTcard hTd hTsat
  have hnoR : ∀ a ∈ H, ∀ b ∈ H, dist a b ≠ R := by
    intro a ha b hb he
    have hba : b ≠ a := by
      intro h
      rw [h, dist_self] at he
      linarith
    have hbneg : b ≠ -a := by
      intro h
      have hanti : dist a (-a) = 2 * R := by
        rw [dist_eq_norm, sub_neg_eq_add, ← two_smul ℝ a, norm_smul,
          Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2), hcircle a ha]
      rw [h, hanti] at he
      linarith
    have hdT := hneighbor a ha b hb hba hbneg
    rw [dist_comm b a, he] at hdT
    exact (Finset.mem_erase.mp hdT).1 rfl
  have hmR : multiplicity H R = 0 := by
    unfold TwoInteriorCircle.multiplicity
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro e heH hed
    induction e using Sym2.ind with
    | _ a b =>
      obtain ⟨ha, hb, _hab⟩ := (mk_mem_pairs H a b).mp heH
      exact hnoR a ha b hb hed
  refine ⟨hmR, ?_⟩
  have hdiam := antipodal_diam H R hH hR hcircle hsym
  apply Finset.Subset.antisymm
  · intro d hd
    obtain ⟨hdpos, _hdlt, a, ha, b, hb, habd⟩ :=
      (ThreeInteriorCounting.mem_nonDiameterDistances_iff_positive H d).mp hd
    exact Finset.mem_erase.mpr ⟨fun he => hnoR a ha b hb (habd.trans he), hHS d hd⟩
  · intro d hd
    obtain ⟨a, ha⟩ := hH
    have hf := chord_neighbors_card_eq_two H hR hcircle (hTd d hd).1 (hTsat d hd) a ha
    obtain ⟨b, hb⟩ := Finset.card_pos.mp (by omega : 0 < (H.filter fun b => dist b a = d).card)
    obtain ⟨hbH, hbd⟩ := Finset.mem_filter.mp hb
    apply (ThreeInteriorCounting.mem_nonDiameterDistances_iff_positive H d).mpr
    refine ⟨(hTd d hd).1, ?_, b, hbH, a, ha, hbd⟩
    rw [hdiam]
    exact (hTd d hd).2

/-- Under the original centered contrary model, the hull is antipodal, its
actual diameter is twice its radius, no hull pair has radius length, and its
actual positive nondiameter support is exactly the full support with radius erased.
This follows from exhaustion of actual two-neighbor fibers, not an assumed pair
budget certificate. -/
theorem centered_contrary_support (n : ℕ) (H : Finset Plane) (R : ℝ) (u v : Plane)
    (hn : 9 ≤ n) (hodd : Odd n) (hH : H.card = n - 3) (hR : 0 < R)
    (hcircle : ∀ h ∈ H, ‖h‖ = R) (hu0 : u ≠ 0) (hv0 : v ≠ 0) (huv : u ≠ v)
    (h0 : (0 : Plane) ∈ interior (convexHull ℝ (H : Set Plane)))
    (hu : u ∈ interior (convexHull ℝ (H : Set Plane)))
    (hv : v ∈ interior (convexHull ℝ (H : Set Plane)))
    (hlarge : ∀ d : ℝ, 0 < d →
      d < Metric.diam ((insert (0 : Plane) (insert u (insert v H)) : Finset Plane) : Set Plane) →
      (∃ a ∈ insert (0 : Plane) (insert u (insert v H)),
        ∃ b ∈ insert (0 : Plane) (insert u (insert v H)), dist a b = d) →
      n + 1 ≤ multiplicity (insert (0 : Plane) (insert u (insert v H))) d) :
    (∀ x ∈ H, -x ∈ H) ∧ Metric.diam (H : Set Plane) = 2 * R ∧
      multiplicity H R = 0 ∧ nonDiameterDistances H =
        (nonDiameterDistances (insert (0 : Plane) (insert u (insert v H)))).erase R := by
  classical
  let X := insert (0 : Plane) (insert u (insert v H))
  let S := nonDiameterDistances X
  have hnonempty : H.Nonempty := Finset.card_pos.mp (by omega)
  have heven := centered_contrary_even_order n H R u v hn hodd hH hR hcircle hu0 hv0 huv h0 hu hv hlarge
  have hsym : ∀ x ∈ H, -x ∈ H := by
    intro x hx
    exact (mem_iff_neg_mem_of_even_order H hnonempty hR hcircle heven x).mp hx
  have hdiamR := antipodal_diam H R hnonempty hR hcircle hsym
  obtain ⟨_hX, hdiam, _hdiampos, hHS, _hnS, _hS, _hrpos, _hrlt, _hnorm,
    hmemR, _hmemr, _hmemell, _hsu, _hsv, _hg, _horder, _hdiv, _hclasses⟩ :=
    centered_contrary_model n H R u v hn hodd hH hR hcircle hu0 hv0 huv h0 hu hv hlarge
  obtain ⟨_horder, hsaturated⟩ :=
    centered_contrary_saturation n H R u v hn hodd hH hR hcircle hu0 hv0 huv h0 hu hv hlarge
  have hSbounds : ∀ d ∈ S, 0 < d ∧ d < 2 * R := by
    intro d hd
    obtain ⟨hdpos, hdlt, _hdocc⟩ := (ThreeInteriorCounting.mem_nonDiameterDistances_iff_positive X d).mp hd
    rw [hdiam, hdiamR] at hdlt
    exact ⟨hdpos, hdlt⟩
  have hsubset : ∀ d ∈ nonDiameterDistances H, d ∈ S := by
    intro d hd
    obtain ⟨hdpos, hdlt, a, ha, b, hb, habd⟩ :=
      (ThreeInteriorCounting.mem_nonDiameterDistances_iff_positive H d).mp hd
    apply (ThreeInteriorCounting.mem_nonDiameterDistances_iff_positive X d).mpr
    refine ⟨hdpos, ?_, a, by simp [X, ha], b, by simp [X, hb], habd⟩
    rw [hdiam]
    exact hdlt
  obtain ⟨hmR, hsupport⟩ := support_exhaustion H S R hnonempty hR hcircle hsym hHS hmemR hSbounds hsubset hsaturated
  exact ⟨hsym, hdiamR, hmR, hsupport⟩

/-- Antipodal hull chords below the diameter have another positive
nondiameter hull chord with complementary square, their sum being four radius squares. -/
theorem hull_squared_complement (H : Finset Plane) (R : ℝ)
    (hH : H.Nonempty) (hR : 0 < R) (hcircle : ∀ x ∈ H, ‖x‖ = R)
    (hsym : ∀ x ∈ H, -x ∈ H) :
    ∀ d ∈ nonDiameterDistances H, ∃ e ∈ nonDiameterDistances H,
      d ^ 2 + e ^ 2 = 4 * R ^ 2 := by
  intro d hd
  obtain ⟨hdpos, hdlt, a, ha, b, hb, habd⟩ :=
    (ThreeInteriorCounting.mem_nonDiameterDistances_iff_positive H d).mp hd
  have hdiam := antipodal_diam H R hH hR hcircle hsym
  rw [hdiam] at hdlt
  have hsq : d ^ 2 + dist a (-b) ^ 2 = 4 * R ^ 2 := by
    have hp := parallelogram_law_with_norm ℝ a b
    rw [hcircle a ha, hcircle b hb] at hp
    rw [← habd, dist_eq_norm, dist_eq_norm, sub_neg_eq_add]
    nlinarith only [hp]
  have hepos : 0 < dist a (-b) := by
    have hn := dist_nonneg (x := a) (y := -b)
    nlinarith
  have helt : dist a (-b) < 2 * R := by
    have hn := dist_nonneg (x := a) (y := -b)
    nlinarith
  refine ⟨dist a (-b), ?_, hsq⟩
  apply (ThreeInteriorCounting.mem_nonDiameterDistances_iff_positive H _).mpr
  exact ⟨hepos, hdiam.symm ▸ helt, a, ha, -b, hsym b hb, rfl⟩

/-- Distances from an arbitrary point to an antipodal circular hull occur in
pairs whose squared sum is twice the sum of radius square and point norm square. -/
theorem radial_squared_complement (H : Finset Plane) (R : ℝ) (u : Plane)
    (hcircle : ∀ x ∈ H, ‖x‖ = R) (hsym : ∀ x ∈ H, -x ∈ H) :
    ∀ d ∈ H.image (fun h => dist h u),
      ∃ e ∈ H.image (fun h => dist h u), d ^ 2 + e ^ 2 = 2 * (R ^ 2 + ‖u‖ ^ 2) := by
  classical
  intro d hd
  obtain ⟨a, ha, had⟩ := Finset.mem_image.mp hd
  refine ⟨dist (-a) u, Finset.mem_image.mpr ⟨-a, hsym a ha, rfl⟩, ?_⟩
  have hp := parallelogram_law_with_norm ℝ a u
  rw [hcircle a ha] at hp
  rw [← had, dist_eq_norm, dist_eq_norm]
  have he : -a - u = -(a + u) := by abel
  rw [he, norm_neg]
  nlinarith only [hp]

private theorem min_sq_add_max_sq_of_complement (S : Finset ℝ) (hS : S.Nonempty)
    (C : ℝ) (hpos : ∀ d ∈ S, 0 < d)
    (hcomp : ∀ d ∈ S, ∃ e ∈ S, d ^ 2 + e ^ 2 = C) :
    (S.min' hS) ^ 2 + (S.max' hS) ^ 2 = C := by
  have hminpos := hpos _ (Finset.min'_mem S hS)
  have hmaxpos := hpos _ (Finset.max'_mem S hS)
  obtain ⟨e, he, hmine⟩ := hcomp _ (Finset.min'_mem S hS)
  obtain ⟨f, hf, hmaxf⟩ := hcomp _ (Finset.max'_mem S hS)
  have hemax := Finset.le_max' S e he
  have hminf := Finset.min'_le S f hf
  have hesq := (sq_le_sq₀ (le_of_lt (hpos e he)) (le_of_lt hmaxpos)).mpr hemax
  have hfsq := (sq_le_sq₀ (le_of_lt hminpos) (le_of_lt (hpos f hf))).mpr hminf
  linarith

private theorem complementary_constants_eq (S : Finset ℝ) (R A B : ℝ)
    (hpos : ∀ d ∈ S, 0 < d)
    (hcompS : ∀ d ∈ S, ∃ e ∈ S, d ^ 2 + e ^ 2 = A)
    (hcompT : ∀ d ∈ S.erase R, ∃ e ∈ S.erase R, d ^ 2 + e ^ 2 = B)
    (d e : ℝ) (hd : d ∈ S.erase R) (he : e ∈ S.erase R)
    (hdR : d < R) (hRe : R < e) : A = B := by
  classical
  let T := S.erase R
  have hT : T.Nonempty := ⟨d, hd⟩
  have hS : S.Nonempty := ⟨d, (Finset.mem_erase.mp hd).2⟩
  have hminlt : S.min' hS < R :=
    (Finset.min'_le S d (Finset.mem_erase.mp hd).2).trans_lt hdR
  have hmaxlt : R < S.max' hS :=
    hRe.trans_le (Finset.le_max' S e (Finset.mem_erase.mp he).2)
  have hminT : S.min' hS ∈ T :=
    Finset.mem_erase.mpr ⟨ne_of_lt hminlt, Finset.min'_mem S hS⟩
  have hmaxT : S.max' hS ∈ T :=
    Finset.mem_erase.mpr ⟨ne_of_gt hmaxlt, Finset.max'_mem S hS⟩
  have hminEq : S.min' hS = T.min' hT := by
    apply le_antisymm
    · exact Finset.min'_le S _ (Finset.mem_erase.mp (Finset.min'_mem T hT)).2
    · exact Finset.min'_le T _ hminT
  have hmaxEq : S.max' hS = T.max' hT := by
    apply le_antisymm
    · exact Finset.le_max' T _ hmaxT
    · exact Finset.le_max' S _ (Finset.mem_erase.mp (Finset.max'_mem T hT)).2
  have hA := min_sq_add_max_sq_of_complement S hS A hpos hcompS
  have hB := min_sq_add_max_sq_of_complement T hT B
    (fun x hx => hpos x (Finset.mem_erase.mp hx).2) hcompT
  rw [hminEq, hmaxEq] at hA
  exact hA.symm.trans hB

private theorem centered_contrary_of_short_pair (n : ℕ) (H : Finset Plane) (R : ℝ) (u v : Plane)
    (hn : 9 ≤ n) (hodd : Odd n) (hH : H.card = n - 3) (hR : 0 < R)
    (hcircle : ∀ h ∈ H, ‖h‖ = R) (hu0 : u ≠ 0) (hv0 : v ≠ 0) (huv : u ≠ v)
    (h0 : (0 : Plane) ∈ interior (convexHull ℝ (H : Set Plane)))
    (hu : u ∈ interior (convexHull ℝ (H : Set Plane)))
    (hv : v ∈ interior (convexHull ℝ (H : Set Plane)))
    (hlarge : ∀ d : ℝ, 0 < d →
      d < Metric.diam ((insert (0 : Plane) (insert u (insert v H)) : Finset Plane) : Set Plane) →
      (∃ a ∈ insert (0 : Plane) (insert u (insert v H)),
        ∃ b ∈ insert (0 : Plane) (insert u (insert v H)), dist a b = d) →
      n + 1 ≤ multiplicity (insert (0 : Plane) (insert u (insert v H))) d)
    (hshort : ∃ a ∈ H, ∃ b ∈ H, a ≠ b ∧ dist a b ≤ R) : False := by
  classical
  let X := insert (0 : Plane) (insert u (insert v H))
  let S := nonDiameterDistances X
  let T := nonDiameterDistances H
  have hnonempty : H.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨_hX, _hdiam, _hdiampos, _hHS, _hnS, _hS, _hrpos, hrlt, _hnorm,
    _hmemR, _hmemr, _hmemell, hsu, _hsv, _hg, _horder, _hdiv, _hclasses⟩ :=
    centered_contrary_model n H R u v hn hodd hH hR hcircle hu0 hv0 huv h0 hu hv hlarge
  obtain ⟨hsym, hdiamR, _hmR, hsupport⟩ :=
    centered_contrary_support n H R u v hn hodd hH hR hcircle hu0 hv0 huv h0 hu hv hlarge
  change H.image (fun h => dist h u) = S at hsu
  change T = S.erase R at hsupport
  have hcompT : ∀ d ∈ T, ∃ e ∈ T, d ^ 2 + e ^ 2 = 4 * R ^ 2 :=
    hull_squared_complement H R hnonempty hR hcircle hsym
  have hcompS : ∀ d ∈ S, ∃ e ∈ S, d ^ 2 + e ^ 2 = 2 * (R ^ 2 + ‖u‖ ^ 2) := by
    rw [← hsu]
    exact radial_squared_complement H R u hcircle hsym
  obtain ⟨a, ha, b, hb, hab, habR⟩ := hshort
  have hdT : dist a b ∈ T := by
    apply (ThreeInteriorCounting.mem_nonDiameterDistances_iff_positive H _).mpr
    refine ⟨dist_pos.mpr hab, ?_, a, ha, b, hb, rfl⟩
    rw [hdiamR]
    linarith
  have hdErase : dist a b ∈ S.erase R := hsupport ▸ hdT
  have hdlt : dist a b < R := lt_of_le_of_ne habR (Finset.mem_erase.mp hdErase).1
  obtain ⟨e, heT, hde⟩ := hcompT _ hdT
  have hepos := (ThreeInteriorCounting.mem_nonDiameterDistances_iff_positive H e).mp heT
  have hRe : R < e := by
    have hdpos := dist_pos.mpr hab
    nlinarith
  have hconstant := complementary_constants_eq S R (2 * (R ^ 2 + ‖u‖ ^ 2)) (4 * R ^ 2)
    (fun d hd => ((ThreeInteriorCounting.mem_nonDiameterDistances_iff_positive X d).mp hd).1)
    hcompS (hsupport ▸ hcompT) (dist a b) e hdErase (hsupport ▸ heT) hdlt hRe
  have hrnonneg := norm_nonneg u
  nlinarith

/-- For odd order at least nine, the original centered three-interior geometry
cannot have multiplicity at least `n+1` on every occurring positive nondiameter class. -/
theorem centered_contrary (n : ℕ) (H : Finset Plane) (R : ℝ) (u v : Plane)
    (hn : 9 ≤ n) (hodd : Odd n) (hH : H.card = n - 3) (hR : 0 < R)
    (hcircle : ∀ h ∈ H, ‖h‖ = R) (hu0 : u ≠ 0) (hv0 : v ≠ 0) (huv : u ≠ v)
    (h0 : (0 : Plane) ∈ interior (convexHull ℝ (H : Set Plane)))
    (hu : u ∈ interior (convexHull ℝ (H : Set Plane)))
    (hv : v ∈ interior (convexHull ℝ (H : Set Plane)))
    (hlarge : ∀ d : ℝ, 0 < d →
      d < Metric.diam ((insert (0 : Plane) (insert u (insert v H)) : Finset Plane) : Set Plane) →
      (∃ a ∈ insert (0 : Plane) (insert u (insert v H)),
        ∃ b ∈ insert (0 : Plane) (insert u (insert v H)), dist a b = d) →
      n + 1 ≤ multiplicity (insert (0 : Plane) (insert u (insert v H))) d)
 : False := by
  have hcard : 6 ≤ H.card := by omega
  obtain ⟨a, ha, b, hb, hab, _hpos, hshort⟩ :=
    Erdos132.CircleShortChord.exists_short_chord H R hR hcircle hcard
  exact centered_contrary_of_short_pair n H R u v hn hodd hH hR hcircle hu0 hv0 huv
    h0 hu hv hlarge ⟨a, ha, b, hb, hab, hshort⟩

/-- The original odd centered configuration has an occurring positive nondiameter
length with inherited unordered, loop-free multiplicity between one and `n`. -/
theorem zero_center_witness (n : ℕ) (H : Finset Plane) (R : ℝ) (u v : Plane)
    (hn : 9 ≤ n) (hodd : Odd n) (hH : H.card = n - 3) (hR : 0 < R)
    (hcircle : ∀ h ∈ H, ‖h‖ = R) (hu0 : u ≠ 0) (hv0 : v ≠ 0) (huv : u ≠ v)
    (h0 : (0 : Plane) ∈ interior (convexHull ℝ (H : Set Plane)))
    (hu : u ∈ interior (convexHull ℝ (H : Set Plane)))
    (hv : v ∈ interior (convexHull ℝ (H : Set Plane)))
 :
    ∃ d : ℝ, 0 < d ∧
      d < Metric.diam ((insert (0 : Plane) (insert u (insert v H)) : Finset Plane) : Set Plane) ∧
      1 ≤ multiplicity (insert (0 : Plane) (insert u (insert v H))) d ∧
      multiplicity (insert (0 : Plane) (insert u (insert v H))) d ≤ n := by
  classical
  by_contra hno
  apply centered_contrary n H R u v hn hodd hH hR hcircle hu0 hv0 huv h0 hu hv
  intro d hdpos hdlt hdocc
  obtain ⟨a, ha, b, hb, habd⟩ := hdocc
  have hab : a ≠ b := by
    intro heq
    subst b
    simp only [dist_self] at habd
    linarith
  have hm : 1 ≤ multiplicity (insert (0 : Plane) (insert u (insert v H))) d := by
    apply Nat.succ_le_of_lt
    apply Finset.card_pos.mpr
    exact ⟨s(a,b), Finset.mem_filter.mpr ⟨(mk_mem_pairs _ a b).mpr ⟨ha, hb, hab⟩, habd⟩⟩
  have hnot : ¬ multiplicity (insert (0 : Plane) (insert u (insert v H))) d ≤ n := by
    intro hbound
    exact hno ⟨d, hdpos, hdlt, hm, hbound⟩
  omega

/-- An odd configuration of at least nine points on a positive-radius circle,
with three distinct ambient interiors including the center, has exactly `n` points
and an occurring positive nondiameter length of multiplicity between one and `n`.
The center is arbitrary and multiplicity counts inherited unordered loop-free pairs. -/
theorem one_center_circle (n : ℕ) (H : Finset Plane) (O u v : Plane) (R : ℝ)
    (hn : 9 ≤ n) (hodd : Odd n) (hH : H.card = n - 3) (hR : 0 < R)
    (hcircle : ∀ h ∈ H, dist h O = R) (huO : u ≠ O) (hvO : v ≠ O) (huv : u ≠ v)
    (hO : O ∈ interior (convexHull ℝ (H : Set Plane)))
    (hu : u ∈ interior (convexHull ℝ (H : Set Plane)))
    (hv : v ∈ interior (convexHull ℝ (H : Set Plane))) :
    (insert O (insert u (insert v H))).card = n ∧
      ∃ d : ℝ, 0 < d ∧
        d < Metric.diam ((insert O (insert u (insert v H)) : Finset Plane) : Set Plane) ∧
        1 ≤ multiplicity (insert O (insert u (insert v H))) d ∧
        multiplicity (insert O (insert u (insert v H))) d ≤ n := by
  classical
  let f : Plane → Plane := fun h => h - O
  have hf : Isometry f := fun a b => by simp [f, edist_dist]
  have hcard : (H.image f).card = H.card := Finset.card_image_of_injective H hf.injective
  have hcircle' : ∀ h ∈ H.image f, ‖h‖ = R := by
    intro h hh
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hh
    exact hcircle a ha
  have h0' : (0 : Plane) ∈ interior (convexHull ℝ ((H.image f) : Set Plane)) := by
    simpa only [sub_self] using sub_mem_interior_hull H O O hO
  have hu' := sub_mem_interior_hull H O u hu
  have hv' := sub_mem_interior_hull H O v hv
  have hu0' : f u ≠ 0 := fun he => huO (sub_eq_zero.mp he)
  have hv0' : f v ≠ 0 := fun he => hvO (sub_eq_zero.mp he)
  have huv' : f u ≠ f v := fun he => huv (hf.injective he)
  have hH' : (H.image f).card = n - 3 := hcard.trans hH
  obtain ⟨d, hpos, hlt, hm, hbound⟩ := zero_center_witness n (H.image f) R (f u) (f v)
    hn hodd hH' hR hcircle' hu0' hv0' huv' h0' hu' hv'
  have himage : insert (0 : Plane) (insert (f u) (insert (f v) (H.image f))) =
      (insert O (insert u (insert v H))).image f := by
    simp only [Finset.image_insert, f, sub_self]
  rw [himage] at hlt hm hbound
  rw [multiplicity_image_isometry _ f hf] at hm hbound
  rw [Finset.coe_image, hf.diam_image] at hlt
  have hcount := ThreeInteriorCounting.card_insert_three_interiors (H.image f) R 0 (f u) (f v)
    hR hcircle' h0' hu' hv' hu0'.symm hv0'.symm huv'
  rw [himage, Finset.card_image_of_injective _ hf.injective, hcard, hH] at hcount
  refine ⟨?_, d, hpos, hlt, hm, hbound⟩
  omega

end Erdos132.ThreeInteriorCenter
