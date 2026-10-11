import Erdos.Erdos132.DoubleEndpoint
import Erdos.Erdos132.CircleRotation

set_option autoImplicit false

namespace Erdos132.EvenThreeInteriorCircle

open Erdos132.TwoInteriorCircle Erdos132.CircleRotation
open scoped BigOperators

/-- A uniform distance bound on the vertices extends to their convex hull and
is strict at every ambient interior point, even with an external comparison point. -/
theorem dist_lt_vertex_bound (H : Finset Plane) {p y : Plane} {L : ℝ}
    (hL : 0 < L) (hbound : ∀ h ∈ H, dist h y ≤ L)
    (hp : p ∈ interior (convexHull ℝ (H : Set Plane))) : dist p y < L := by
  have hK : ∀ x ∈ convexHull ℝ (H : Set Plane), dist x y ≤ L := by
    intro x hx
    obtain ⟨h, hh, hle⟩ := convexHull_exists_dist_ge hx y
    exact hle.trans (hbound h hh)
  by_cases hpy : p = y
  · simpa [hpy] using hL
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hp)
  let t : ℝ := ε / (2 * (‖p - y‖ + 1))
  have hnorm : 0 ≤ ‖p - y‖ := norm_nonneg _
  have hden : 0 < 2 * (‖p - y‖ + 1) := by positivity
  have ht : 0 < t := div_pos hε hden
  have htε : t * ‖p - y‖ < ε := by
    dsimp [t]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hden).2
    nlinarith
  let q := p + t • (p - y)
  have hqp : dist q p = t * ‖p - y‖ := by
    rw [dist_eq_norm]
    dsimp [q]
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  have hq : q ∈ convexHull ℝ (H : Set Plane) :=
    hball (by simpa only [Metric.mem_ball, hqp] using htε)
  have hqy : dist q y = (1 + t) * dist p y := by
    rw [dist_eq_norm, dist_eq_norm]
    have hv : q - y = (1 + t) • (p - y) := by dsimp [q]; module
    rw [hv, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < 1 + t)]
  have hpos : 0 < dist p y := dist_pos.mpr hpy
  have hle := hK q hq
  rw [hqy] at hle
  nlinarith

/-- Three distinct ambient interiors augment the circle hull by exactly three points. -/
theorem card_insert_three (H : Finset Plane) {R : ℝ} {z w v : Plane}
    (hR : 0 < R) (hcircle : ∀ h ∈ H, ‖h‖ = R)
    (hz : z ∈ interior (convexHull ℝ (H : Set Plane)))
    (hw : w ∈ interior (convexHull ℝ (H : Set Plane)))
    (hv : v ∈ interior (convexHull ℝ (H : Set Plane)))
    (hzw : z ≠ w) (hzv : z ≠ v) (hwv : w ≠ v) :
    (insert z (insert w (insert v H))).card = H.card + 3 := by
  classical
  have hcircle' : ∀ h ∈ H, dist h (0 : Plane) = R := by simpa only [dist_zero_right] using hcircle
  have hzR := dist_center_lt_radius H 0 hR hcircle' hz
  have hwR := dist_center_lt_radius H 0 hR hcircle' hw
  have hvR := dist_center_lt_radius H 0 hR hcircle' hv
  have hzH : z ∉ H := fun h => (ne_of_lt hzR) (hcircle' z h)
  have hwH : w ∉ H := fun h => (ne_of_lt hwR) (hcircle' w h)
  have hvH : v ∉ H := fun h => (ne_of_lt hvR) (hcircle' v h)
  simp [Finset.card_insert_of_notMem, hzH, hwH, hvH, hzw, hzv, hwv, Nat.add_assoc]

/-- Adding three ambient hull interiors does not change the actual metric diameter. -/
theorem diam_insert_three (H : Finset Plane) {z w v : Plane}
    (hz : z ∈ interior (convexHull ℝ (H : Set Plane)))
    (hw : w ∈ interior (convexHull ℝ (H : Set Plane)))
    (hv : v ∈ interior (convexHull ℝ (H : Set Plane))) :
    Metric.diam ((insert z (insert w (insert v H)) : Finset Plane) : Set Plane) =
      Metric.diam (H : Set Plane) := by
  classical
  have hsub : ((insert z (insert w (insert v H)) : Finset Plane) : Set Plane) ⊆
      convexHull ℝ (H : Set Plane) := by
    intro p hp
    simp only [Finset.mem_coe, Finset.mem_insert] at hp
    rcases hp with rfl | rfl | rfl | hp
    · exact interior_subset hz
    · exact interior_subset hw
    · exact interior_subset hv
    · exact subset_convexHull ℝ _ hp
  apply le_antisymm
  · exact Metric.diam_le_of_forall_dist_le Metric.diam_nonneg
      (fun _ hx _ hy => dist_le_diam_hull H (hsub hx) (hsub hy))
  · exact Metric.diam_mono (by intro p hp; simp [hp])
      (insert z (insert w (insert v H))).finite_toSet.isBounded

/-- A genuine rotation preserving a distinct unordered pair is identity or half-turn. -/
theorem rotation_pair_fixed (g : Rotation) {a b : Plane}
    (ha0 : a ≠ 0) (hpair : s(rotate g a, rotate g b) = s(a, b)) : g = 1 ∨ g = -1 := by
  rcases Sym2.eq_iff.mp hpair with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact Or.inl (point_fixed_imp_one g a ha0 ha)
  · have hgg : g * g = 1 := point_fixed_imp_one (g*g) a ha0 (by rw [rotate_mul, ha, hb])
    have hcoeff : (g : ℂ) * (g : ℂ) = 1 := by
      exact congrArg (fun k : Rotation => (k : ℂ)) hgg
    rcases mul_self_eq_one_iff.mp hcoeff with hg | hg
    · exact Or.inl (Circle.ext hg)
    · exact Or.inr (Circle.ext hg)

/-- A positive strictly subdiametral chord class in a circle hull with a unique
diameter pair cannot saturate the circle's degree-two capacity. -/
theorem chord_lt_card_of_unique_diameter (H : Finset Plane) {R d : ℝ} {a b : Plane}
    (hR : 0 < R) (hcircle : ∀ h ∈ H, ‖h‖ = R)
    (ha : a ∈ H) (hb : b ∈ H) (hab : a ≠ b)
    (hdiam : dist a b = Metric.diam (H : Set Plane))
    (hunique : ∀ x ∈ H, ∀ y ∈ H, dist x y = dist a b → s(x,y) = s(a,b))
    (hd : 0 < d) (hdD : d < Metric.diam (H : Set Plane)) :
    multiplicity H d < H.card := by
  have hcircle' : ∀ h ∈ H, dist h (0 : Plane) = R := by simpa only [dist_zero_right] using hcircle
  have hcap := chord_capacity H 0 R d hR hcircle'
  have hD : Metric.diam (H : Set Plane) ≤ 2 * R := by
    apply Metric.diam_le_of_forall_dist_le (by positivity)
    intro x hx y hy
    calc
      dist x y ≤ dist x 0 + dist 0 y := dist_triangle _ _ _
      _ = 2 * R := by rw [hcircle' x hx, dist_comm 0 y, hcircle' y hy]; ring
  by_contra hnot
  have hsat : multiplicity H d = H.card := le_antisymm hcap (le_of_not_gt hnot)
  have hmpos : 0 < multiplicity H d := by
    rw [hsat]
    exact Finset.card_pos.mpr ⟨a, ha⟩
  obtain ⟨e, he⟩ := Finset.card_pos.mp hmpos
  have he' := Finset.mem_filter.mp he
  induction e using Sym2.ind with
  | _ x y =>
    obtain ⟨hx, hy, hxy⟩ := (mk_mem_pairs H x y).mp he'.1
    obtain ⟨g, hgxy, hg1, hgneg⟩ := exists_stabilizer_map_of_saturated_chord H hR hcircle
      hd (hdD.trans_le hD) hsat hx hy he'.2
    have hga : rotate g.val a ∈ H := (g.property a).mpr ha
    have hgb : rotate g.val b ∈ H := (g.property b).mpr hb
    have hpair := hunique _ hga _ hgb ((rotate_isometry g.val).dist_eq a b)
    rcases rotation_pair_fixed g.val (ne_zero_of_norm_eq hR (hcircle a ha)) hpair with hg | hg
    · exact hg1 hg
    · exact hgneg hg

/-- The largest nondiameter class has at most hull-size plus interior-size edges
when its circle hull has a unique diameter pair. This uses ambient interior and
the proved double-endpoint geometry, not an endpoint-intersection certificate. -/
theorem longest_class_bound (H I : Finset Plane) {R L : ℝ} {a b : Plane}
    (hR : 0 < R) (hcircle : ∀ h ∈ H, ‖h‖ = R)
    (ha : a ∈ H) (hb : b ∈ H) (hab : a ≠ b)
    (hdiam : dist a b = Metric.diam (H : Set Plane))
    (hunique : ∀ x ∈ H, ∀ y ∈ H, dist x y = dist a b → s(x,y) = s(a,b))
    (hInt : ∀ i ∈ I, i ∈ interior (convexHull ℝ (H : Set Plane)))
    (hL : 0 < L) (hLD : L < Metric.diam (H : Set Plane))
    (hmax : ∀ x ∈ H ∪ I, ∀ y ∈ H ∪ I,
      dist x y < Metric.diam (H : Set Plane) → dist x y ≤ L) :
    multiplicity (H ∪ I) L ≤ H.card + I.card := by
  classical
  have hcard : 2 ≤ H.card := by
    have hpair : ({a,b} : Finset Plane) ⊆ H := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ha
      · exact (Finset.mem_singleton.mp hx) ▸ hb
    have hc := Finset.card_le_card hpair
    rw [Finset.card_pair hab] at hc
    exact hc
  have hcross : ∀ i ∈ I, ∀ h ∈ H, dist i h ≤ L := by
    intro i hi h hh
    exact hmax i (Finset.mem_union_right _ hi) h (Finset.mem_union_left _ hh)
      (dist_lt_diam_hull H hcard (hInt i hi) (subset_convexHull ℝ _ hh))
  have hII : ∀ i ∈ I, ∀ j ∈ I, dist i j < L := by
    intro i hi j hj
    apply dist_lt_vertex_bound H hL _ (hInt i hi)
    intro h hh
    rw [dist_comm]
    exact hcross j hj h hh
  have honly : ∀ i ∈ I, ∀ h ∈ H, dist i h = L → h = a ∨ h = b := by
    intro i hi h hh hih
    by_contra hn
    have hna : h ≠ a := fun he => hn (Or.inl he)
    have hnb : h ≠ b := fun he => hn (Or.inr he)
    have hHbound : ∀ x ∈ H, dist x h ≤ L := by
      intro x hx
      apply hmax x (Finset.mem_union_left _ hx) h (Finset.mem_union_left _ hh)
      have hle := Metric.dist_le_diam_of_mem H.finite_toSet.isBounded hx hh
      apply lt_of_le_of_ne hle
      intro he
      have hu := hunique x hx h hh (he.trans hdiam.symm)
      rcases Sym2.eq_iff.mp hu with ⟨hx', hh'⟩ | ⟨hx', hh'⟩
      · exact hnb hh'
      · exact hna hh'
    have hstrict := dist_lt_vertex_bound H hL hHbound (hInt i hi)
    rw [hih] at hstrict
    exact lt_irrefl L hstrict
  let F := fun i : Plane => H.filter (fun h => dist i h = L)
  have hFsub : ∀ i ∈ I, F i ⊆ {a,b} := by
    intro i hi h hh
    have hhm := Finset.mem_filter.mp hh
    simpa only [Finset.mem_insert, Finset.mem_singleton] using honly i hi h hhm.1 hhm.2
  have hFcap : ∀ i ∈ I, (F i).card ≤ 2 := by
    intro i hi
    exact (Finset.card_le_card (hFsub i hi)).trans Finset.card_le_two
  have hFtwo : ∀ i ∈ I, (F i).card = 2 → dist i a = L ∧ dist i b = L := by
    intro i hi hc
    have he : F i = {a,b} := Finset.eq_of_subset_of_card_le (hFsub i hi)
      (by rw [hc, Finset.card_pair hab])
    have hfa : a ∈ F i := by rw [he]; simp
    have hfb : b ∈ F i := by rw [he]; simp
    exact ⟨(Finset.mem_filter.mp hfa).2, (Finset.mem_filter.mp hfb).2⟩
  have hdouble : (I.filter fun i => (F i).card = 2).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    obtain ⟨hiI, hi2⟩ := Finset.mem_filter.mp hi
    obtain ⟨hjI, hj2⟩ := Finset.mem_filter.mp hj
    obtain ⟨hia, hib⟩ := hFtwo i hiI hi2
    obtain ⟨hja, hjb⟩ := hFtwo j hjI hj2
    exact DoubleEndpoint.double_endpoint_unique H hR hcircle ha hb hab hL
      (hInt i hiI) (hInt j hjI) hia hib hja hjb (hcross i hiI) (hcross j hjI)
  have hsum : ∑ i ∈ I, (F i).card ≤ I.card + 1 := by
    calc
      _ ≤ ∑ i ∈ I, (1 + if (F i).card = 2 then 1 else 0) := by
        apply Finset.sum_le_sum
        intro i hi
        have hcap := hFcap i hi
        split_ifs <;> omega
      _ = I.card + (I.filter fun i => (F i).card = 2).card := by
        simp [Finset.sum_add_distrib, Finset.sum_boole]
      _ ≤ I.card + 1 := Nat.add_le_add_left hdouble _
  let P := (pairs H).filter fun e => pairDist e = L
  let Q := (pairs (H ∪ I)).filter fun e => pairDist e = L
  let S := I.biUnion (fun i => (F i).image fun h => s(i,h))
  have hQsub : Q ⊆ P ∪ S := by
    intro e he
    have hem := Finset.mem_filter.mp he
    induction e using Sym2.ind with
    | _ x y =>
      obtain ⟨hx, hy, hxy⟩ := (mk_mem_pairs (H ∪ I) x y).mp hem.1
      have hdist : dist x y = L := hem.2
      rcases Finset.mem_union.mp hx with hxH | hxI <;>
        rcases Finset.mem_union.mp hy with hyH | hyI
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
          ⟨(mk_mem_pairs H x y).mpr ⟨hxH, hyH, hxy⟩, hem.2⟩)
      · apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr
        exact ⟨y, hyI, Finset.mem_image.mpr
          ⟨x, Finset.mem_filter.mpr ⟨hxH, (dist_comm y x).trans hdist⟩, Sym2.eq_swap⟩⟩
      · apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr
        exact ⟨x, hxI, Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨hyH, hdist⟩, rfl⟩⟩
      · have hstrict := hII x hxI y hyI
        rw [hdist] at hstrict
        exact False.elim (lt_irrefl L hstrict)
  have hS : S.card ≤ I.card + 1 := by
    calc
      _ ≤ ∑ i ∈ I, ((F i).image fun h => s(i,h)).card := Finset.card_biUnion_le
      _ ≤ ∑ i ∈ I, (F i).card := Finset.sum_le_sum (fun _ _ => Finset.card_image_le)
      _ ≤ I.card + 1 := hsum
  have hP : P.card < H.card := chord_lt_card_of_unique_diameter H hR hcircle
    ha hb hab hdiam hunique hL hLD
  have hQ : Q.card ≤ P.card + S.card :=
    (Finset.card_le_card hQsub).trans (Finset.card_union_le _ _)
  change Q.card ≤ H.card + I.card
  omega

/-- In an even configuration, contrary large multiplicities imply the exact pair
budget; its unique diameter and longest class contradict the geometric bound. -/
theorem zero_center_contrary (H : Finset Plane) (z w v : Plane) (R : ℝ)
    (hH : 7 ≤ H.card) (hR : 0 < R) (hcircle : ∀ h ∈ H, ‖h‖ = R)
    (hz : z ∈ interior (convexHull ℝ (H : Set Plane)))
    (hw : w ∈ interior (convexHull ℝ (H : Set Plane)))
    (hv : v ∈ interior (convexHull ℝ (H : Set Plane)))
    (hzw : z ≠ w) (hzv : z ≠ v) (hwv : w ≠ v) (hz0 : z ≠ 0)
    (hEven : Even (insert z (insert w (insert v H))).card)
    (hlarge : ∀ d ∈ nonDiameterDistances (insert z (insert w (insert v H))),
      (insert z (insert w (insert v H))).card + 1 ≤
        multiplicity (insert z (insert w (insert v H))) d) : False := by
  classical
  let X := insert z (insert w (insert v H))
  let T := nonDiameterDistances X
  have hcircle' : ∀ h ∈ H, dist h (0 : Plane) = R := by
    simpa only [dist_zero_right] using hcircle
  have hXcard := card_insert_three H hR hcircle hz hw hv hzw hzv hwv
  have hXdiam := diam_insert_three H hz hw hv
  have hzH : z ∉ H := fun he => (ne_of_lt (dist_center_lt_radius H 0 hR hcircle' hz))
    (hcircle' z he)
  have hlower : H.card ≤ 2 * T.card := by
    apply Finset.card_le_mul_card_image_of_maps_to (f := fun h => dist h z)
    · intro h hh
      apply (mem_nonDiameterDistances X _).mpr
      refine ⟨⟨h, by simp [X, hh], z, by simp [X],
        Ne.symm (fun he => hzH (he ▸ hh)), rfl⟩, ?_⟩
      rw [hXdiam, dist_comm]
      exact dist_lt_diam_hull H (by omega) hz (subset_convexHull ℝ _ hh)
    · intro d _hd
      exact radial_card_le_two H 0 z R d hcircle' hz0
  have hlowerEven : X.card - 2 ≤ 2 * T.card := by
    rcases hEven with ⟨k, hk⟩
    dsimp only [X] at *
    omega
  obtain ⟨heven, hq, hmu, hD⟩ := equality_structure X (by dsimp [X]; omega)
    hlowerEven hlarge
  obtain ⟨a, ha, b, hb, habD⟩ := exists_diameter_pair H (Finset.card_pos.mp (by omega))
  have hab : a ≠ b := by
    intro he
    have hpos := diam_pos H (by omega)
    rw [← habD, he, dist_self] at hpos
    exact lt_irrefl 0 hpos
  have hmemD : ∀ x ∈ H, ∀ y ∈ H, dist x y = Metric.diam (H : Set Plane) →
      s(x,y) ∈ (pairs X).filter fun e => ¬pairDist e < Metric.diam (X : Set Plane) := by
    intro x hx y hy hxy
    have hne : x ≠ y := by
      intro he
      have hpos := diam_pos H (by omega)
      rw [← hxy, he, dist_self] at hpos
      exact lt_irrefl 0 hpos
    apply Finset.mem_filter.mpr
    refine ⟨(mk_mem_pairs X x y).mpr ⟨by simp [X,hx], by simp [X,hy], hne⟩, ?_⟩
    change ¬dist x y < Metric.diam ((insert z (insert w (insert v H)) : Finset Plane) : Set Plane)
    rw [hxy, hXdiam]
    exact lt_irrefl _
  have hunique : ∀ x ∈ H, ∀ y ∈ H, dist x y = dist a b → s(x,y) = s(a,b) := by
    intro x hx y hy hxy
    exact Finset.card_le_one.mp (le_of_eq hD) _ (hmemD x hx y hy (hxy.trans habD))
      _ (hmemD a ha b hb habD)
  have hT : T.Nonempty := Finset.card_pos.mp (by omega)
  let L := T.max' hT
  have hLT : L ∈ T := T.max'_mem hT
  obtain ⟨⟨x, hx, y, hy, hxy, hxyL⟩, hLD⟩ := (mem_nonDiameterDistances X L).mp hLT
  have hL : 0 < L := hxyL ▸ dist_pos.mpr hxy
  let I : Finset Plane := {z,w,v}
  have hunion : H ∪ I = X := by ext p; simp [I, X, or_comm, or_left_comm]
  have hInt : ∀ i ∈ I, i ∈ interior (convexHull ℝ (H : Set Plane)) := by
    intro i hi
    simp only [I, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact hz
    · exact hw
    · exact hv
  have hIcard : I.card = 3 := by simp [I, hzw, hzv, hwv]
  have hmax : ∀ x ∈ H ∪ I, ∀ y ∈ H ∪ I,
      dist x y < Metric.diam (H : Set Plane) → dist x y ≤ L := by
    intro x hx y hy hlt
    by_cases hxy : x = y
    · simpa [hxy] using le_of_lt hL
    · have hmem : dist x y ∈ T := (mem_nonDiameterDistances X _).mpr
        ⟨⟨x, hunion ▸ hx, y, hunion ▸ hy, hxy, rfl⟩, by rw [hXdiam]; exact hlt⟩
      exact T.le_max' _ hmem
  have hbound := longest_class_bound H I hR hcircle ha hb hab habD hunique hInt hL
    (by rw [hXdiam] at hLD; exact hLD) hmax
  rw [hunion, hIcard] at hbound
  have hmult := hmu L hLT
  dsimp [X] at hmult hbound
  omega

/-- Every even centered-circle configuration with at least seven hull points
and three distinct ambient interior points has a positive nondiameter distance
whose genuine unordered-pair multiplicity is between one and the total size. -/
theorem zero_center_witness (H : Finset Plane) (z w v : Plane) (R : ℝ)
    (hH : 7 ≤ H.card) (hR : 0 < R) (hcircle : ∀ h ∈ H, ‖h‖ = R)
    (hz : z ∈ interior (convexHull ℝ (H : Set Plane)))
    (hw : w ∈ interior (convexHull ℝ (H : Set Plane)))
    (hv : v ∈ interior (convexHull ℝ (H : Set Plane)))
    (hzw : z ≠ w) (hzv : z ≠ v) (hwv : w ≠ v)
    (hEven : Even (insert z (insert w (insert v H))).card) :
    ∃ d : ℝ, 0 < d ∧ d < Metric.diam ((insert z (insert w (insert v H)):Finset Plane):Set Plane) ∧
      1 ≤ multiplicity (insert z (insert w (insert v H))) d ∧
      multiplicity (insert z (insert w (insert v H))) d ≤ (insert z (insert w (insert v H))).card := by
  classical
  by_contra hno
  have hlarge : ∀ d ∈ nonDiameterDistances (insert z (insert w (insert v H))),
      (insert z (insert w (insert v H))).card + 1 ≤ multiplicity (insert z (insert w (insert v H))) d := by
    intro d hd
    obtain ⟨⟨a,ha,b,hb,hab,hdist⟩,hlt⟩ := (mem_nonDiameterDistances _ _).mp hd
    have hpos : 0 < d := hdist ▸ dist_pos.mpr hab
    have hm : 1 ≤ multiplicity (insert z (insert w (insert v H))) d := by
      apply Nat.succ_le_of_lt
      apply Finset.card_pos.mpr
      exact ⟨s(a,b), Finset.mem_filter.mpr ⟨(mk_mem_pairs _ a b).mpr ⟨ha,hb,hab⟩,hdist⟩⟩
    by_contra hsmall
    exact hno ⟨d,hpos,hlt,hm,by omega⟩
  by_cases hz0 : z = 0
  · have hw0 : w ≠ 0 := by intro he; exact hzw (hz0.trans he.symm)
    apply zero_center_contrary H w z v R hH hR hcircle hw hz hv hzw.symm hwv hzv hw0
    · simpa only [Finset.insert_comm] using hEven
    · simpa only [Finset.insert_comm] using hlarge
  · exact zero_center_contrary H z w v R hH hR hcircle hz hw hv hzw hzv hwv hz0 hEven hlarge

/-- Translation reduces an arbitrary circle center to zero without changing
diameter, cardinality, ambient interior, or unordered distance multiplicity. -/
theorem circle_witness (H : Finset Plane) (O z w v : Plane) (R : ℝ)
    (hH : 7 ≤ H.card) (hR : 0 < R) (hcircle : ∀ h ∈ H, dist h O = R)
    (hz : z ∈ interior (convexHull ℝ (H : Set Plane)))
    (hw : w ∈ interior (convexHull ℝ (H : Set Plane)))
    (hv : v ∈ interior (convexHull ℝ (H : Set Plane)))
    (hzw : z ≠ w) (hzv : z ≠ v) (hwv : w ≠ v)
    (hEven : Even (insert z (insert w (insert v H))).card) :
    ∃ d : ℝ, 0 < d ∧ d < Metric.diam ((insert z (insert w (insert v H)):Finset Plane):Set Plane) ∧
      1 ≤ multiplicity (insert z (insert w (insert v H))) d ∧
      multiplicity (insert z (insert w (insert v H))) d ≤ (insert z (insert w (insert v H))).card := by
  classical
  let f : Plane → Plane := fun h => h-O
  have hf : Isometry f := fun a b => by simp [f,edist_dist]
  have hcard : (H.image f).card = H.card := Finset.card_image_of_injective H hf.injective
  have hcircle' : ∀ h ∈ H.image f, ‖h‖ = R := by
    intro h hh
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hh
    exact hcircle a ha
  have himage : insert (f z) (insert (f w) (insert (f v) (H.image f))) =
      (insert z (insert w (insert v H))).image f := by simp only [Finset.image_insert]
  have hEven' : Even (insert (f z) (insert (f w) (insert (f v) (H.image f)))).card := by
    rw [himage, Finset.card_image_of_injective _ hf.injective]
    exact hEven
  obtain ⟨d,hpos,hlt,hm,hbound⟩ := zero_center_witness (H.image f) (f z) (f w) (f v) R
    (by rw [hcard]; exact hH) hR hcircle'
    (sub_mem_interior_hull H O z hz) (sub_mem_interior_hull H O w hw)
    (sub_mem_interior_hull H O v hv)
    (fun he => hzw (hf.injective he)) (fun he => hzv (hf.injective he))
    (fun he => hwv (hf.injective he)) hEven'
  rw [himage] at hlt hm hbound
  rw [multiplicity_image_isometry _ f hf] at hm hbound
  rw [Finset.card_image_of_injective _ hf.injective] at hbound
  rw [Finset.coe_image,hf.diam_image] at hlt
  exact ⟨d,hpos,hlt,hm,hbound⟩

/-- Erdős #132 for every even n at least ten: n−3 distinct concyclic extreme
vertices and three distinct ambient hull interiors give n points and a positive
nondiameter distance occurring between one and n times among unordered pairs.
The circle center is arbitrary; no diameter-uniqueness or antipodality assumption
is imposed. -/
theorem even_three_interior_circle (n : ℕ) (H : Finset Plane) (O z w v : Plane) (R : ℝ)
    (hn : 10 ≤ n) (hEven : Even n) (hH : H.card = n - 3)
    (hcircle : ∀ h ∈ H, dist h O = R)
    (_hextreme : ∀ h ∈ H, h ∈ (convexHull ℝ (H : Set Plane)).extremePoints ℝ)
    (hz : z ∈ interior (convexHull ℝ (H : Set Plane)))
    (hw : w ∈ interior (convexHull ℝ (H : Set Plane)))
    (hv : v ∈ interior (convexHull ℝ (H : Set Plane)))
    (hzw : z ≠ w) (hzv : z ≠ v) (hwv : w ≠ v) :
    (insert z (insert w (insert v H))).card = n ∧
    ∃ d : ℝ, 0 < d ∧ d < Metric.diam ((insert z (insert w (insert v H)):Finset Plane):Set Plane) ∧
      1 ≤ multiplicity (insert z (insert w (insert v H))) d ∧
      multiplicity (insert z (insert w (insert v H))) d ≤ n := by
  classical
  have hH7 : 7 ≤ H.card := by omega
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp (show 1 < H.card by omega)
  have hR : 0 < R := by
    have hnon : 0 ≤ R := (hcircle a ha) ▸ dist_nonneg
    have hne : R ≠ 0 := by
      intro he
      have haO : a = O := dist_eq_zero.mp ((hcircle a ha).trans he)
      have hbO : b = O := dist_eq_zero.mp ((hcircle b hb).trans he)
      exact hab (haO.trans hbO.symm)
    exact lt_of_le_of_ne hnon (Ne.symm hne)
  have hzR := dist_center_lt_radius H O hR hcircle hz
  have hwR := dist_center_lt_radius H O hR hcircle hw
  have hvR := dist_center_lt_radius H O hR hcircle hv
  have hzH : z ∉ H := fun he => (ne_of_lt hzR) (hcircle z he)
  have hwH : w ∉ H := fun he => (ne_of_lt hwR) (hcircle w he)
  have hvH : v ∉ H := fun he => (ne_of_lt hvR) (hcircle v he)
  have hXcard : (insert z (insert w (insert v H))).card = n := by
    simp only [Finset.card_insert_of_notMem
      (show z ∉ insert w (insert v H) by simp [hzw, hzv, hzH]),
      Finset.card_insert_of_notMem (show w ∉ insert v H by simp [hwv, hwH]),
      Finset.card_insert_of_notMem hvH]
    omega
  obtain ⟨d,hpos,hlt,hm,hbound⟩ := circle_witness H O z w v R hH7 hR hcircle hz hw hv
    hzw hzv hwv (by rw [hXcard]; exact hEven)
  rw [hXcard] at hbound
  exact ⟨hXcard,d,hpos,hlt,hm,hbound⟩

end Erdos132.EvenThreeInteriorCircle
