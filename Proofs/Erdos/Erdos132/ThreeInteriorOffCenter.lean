import Erdos.Erdos132.ThreeInteriorCounting
import Erdos.Erdos132.CircleRotationTransport
import Erdos.Erdos132.CircleRotationOrder

set_option autoImplicit false

open scoped BigOperators

namespace Erdos132.ThreeInteriorOffCenter

open TwoInteriorCircle CircleRotation

/-- Adding a genuinely new point splits actual unordered distance pairs into the
old pairs and the radial pairs incident to the new point. -/
theorem multiplicity_insert (Y : Finset Plane) (z : Plane) (d : ℝ) (hz : z ∉ Y) :
    multiplicity (insert z Y) d = multiplicity Y d +
      (Y.filter fun h => dist h z = d).card := by
  classical
  have hinj : Function.Injective (fun h : Plane => s(z, h)) := by
    intro a b hab
    rcases Sym2.eq_iff.mp hab with ⟨_, hab⟩ | ⟨hzb, haz⟩
    · exact hab
    · exact haz.trans hzb
  have hpart : (pairs (insert z Y)).filter (fun e => pairDist e = d) =
      (pairs Y).filter (fun e => pairDist e = d) ∪
        (Y.filter fun h => dist h z = d).image (fun h => s(z, h)) := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      simp only [Finset.mem_filter, mk_mem_pairs, Finset.mem_insert, pairDist_mk,
        Finset.mem_union, Finset.mem_image, Sym2.eq_iff]
      constructor
      · rintro ⟨⟨ha, hb, hab⟩, hd⟩
        rcases ha with rfl | ha <;> rcases hb with rfl | hb
        · exact False.elim (hab rfl)
        · exact Or.inr ⟨b, ⟨hb, (dist_comm b _).trans hd⟩, Or.inl ⟨rfl, rfl⟩⟩
        · exact Or.inr ⟨a, ⟨ha, hd⟩, Or.inr ⟨rfl, rfl⟩⟩
        · exact Or.inl ⟨⟨ha, hb, hab⟩, hd⟩
      · rintro (⟨⟨ha, hb, hab⟩, hd⟩ | ⟨h, ⟨hh, hd⟩, he⟩)
        · exact ⟨⟨Or.inr ha, Or.inr hb, hab⟩, hd⟩
        · rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨⟨Or.inl rfl, Or.inr hh, fun heq => hz (heq.symm ▸ hh)⟩,
              (dist_comm z h).trans hd⟩
          · exact ⟨⟨Or.inr hh, Or.inl rfl, fun heq => hz (heq ▸ hh)⟩, hd⟩
  have hdis : Disjoint ((pairs Y).filter fun e => pairDist e = d)
      ((Y.filter fun h => dist h z = d).image fun h => s(z, h)) := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨h, _hh, rfl⟩ := Finset.mem_image.mp hf
    exact hz ((mk_mem_pairs Y z h).mp (Finset.mem_filter.mp he).1).1
  unfold TwoInteriorCircle.multiplicity
  rw [hpart, Finset.card_union_of_disjoint hdis, Finset.card_image_of_injective _ hinj]

/-- Three new points split actual distance multiplicity into hull, three radial,
and the actual interior-interior multiplicities; no pair-count certificate is used. -/
theorem multiplicity_insert_three (H : Finset Plane) (u v w : Plane) (d : ℝ)
    (hu : u ∉ H) (hv : v ∉ H) (hw : w ∉ H)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    multiplicity (insert u (insert v (insert w H))) d =
      multiplicity H d + (H.filter fun h => dist h u = d).card +
      (H.filter fun h => dist h v = d).card +
      (H.filter fun h => dist h w = d).card + multiplicity ({u,v,w} : Finset Plane) d := by
  classical
  have hu' : u ∉ insert v (insert w H) := by simp [hu, huv, huw]
  have hv' : v ∉ insert w H := by simp [hv, hvw]
  have huI : u ∉ ({v,w} : Finset Plane) := by simp [huv,huw]
  have hvI : v ∉ ({w} : Finset Plane) := by simp [hvw]
  rw [multiplicity_insert _ u d hu', multiplicity_insert _ v d hv',
    multiplicity_insert _ w d hw]
  rw [multiplicity_insert _ u d huI, multiplicity_insert _ v d hvI]
  have hsingle : multiplicity ({w} : Finset Plane) d = 0 := by
    simp [TwoInteriorCircle.multiplicity, pairs]
  rw [hsingle]
  simp only [Finset.filter_insert, Finset.filter_singleton]
  split_ifs <;> simp_all [Finset.card_insert_of_notMem] <;> omega

/-- Summing true multiplicities over any support containing all actual pair lengths
counts each unordered pair exactly once. -/
theorem sum_multiplicity_of_pair_support (Y : Finset Plane) (T : Finset ℝ)
    (hmap : ∀ e ∈ pairs Y, pairDist e ∈ T) :
    ∑ d ∈ T, multiplicity Y d = Y.card.choose 2 := by
  classical
  rw [← card_pairs]
  exact (Finset.card_eq_sum_card_fiberwise hmap).symm

/-- An actual distinct pair contributes at least one to its true distance multiplicity. -/
theorem one_le_multiplicity_of_pair (Y : Finset Plane) (a b : Plane)
    (ha : a ∈ Y) (hb : b ∈ Y) (hab : a ≠ b) :
    1 ≤ multiplicity Y (dist a b) := by
  classical
  apply Finset.card_pos.mpr
  exact ⟨s(a,b), Finset.mem_filter.mpr ⟨(mk_mem_pairs Y a b).mpr ⟨ha,hb,hab⟩, rfl⟩⟩

/-- Hull pairs split exactly into the actual subdiametral support and the attained
diameter, even when some support classes have zero hull multiplicity. -/
theorem hull_pair_partition (H X : Finset Plane) (hsub : H ⊆ X)
    (hdiam : Metric.diam (X : Set Plane) = Metric.diam (H : Set Plane)) :
    (∑ d ∈ nonDiameterDistances X, multiplicity H d) +
      multiplicity H (Metric.diam (H : Set Plane)) = H.card.choose 2 := by
  classical
  let Δ := Metric.diam (H : Set Plane)
  have hnot : Δ ∉ nonDiameterDistances X := by
    intro hd
    have hlt := (mem_nonDiameterDistances X Δ).mp hd |>.2
    rw [hdiam] at hlt
    exact (lt_irrefl Δ) hlt
  have hmap : ∀ e ∈ pairs H, pairDist e ∈ insert Δ (nonDiameterDistances X) := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      obtain ⟨ha,hb,hab⟩ := (mk_mem_pairs H a b).mp he
      have hle : dist a b ≤ Δ := dist_le_diam_hull H
        (subset_convexHull ℝ (H : Set Plane) ha) (subset_convexHull ℝ (H : Set Plane) hb)
      rcases eq_or_lt_of_le hle with hd | hd
      · exact Finset.mem_insert.mpr (Or.inl hd)
      · apply Finset.mem_insert.mpr
        apply Or.inr
        exact (mem_nonDiameterDistances X _).mpr
          ⟨⟨a,hsub ha,b,hsub hb,hab,rfl⟩, hdiam.symm ▸ hd⟩
  have hc := sum_multiplicity_of_pair_support H (insert Δ (nonDiameterDistances X)) hmap
  rw [Finset.sum_insert hnot] at hc
  simpa only [Nat.add_comm] using hc

/-- Ordinary diameter on a positive-radius circle is at most twice the radius. -/
theorem diam_le_twice_radius (H : Finset Plane) (R : ℝ) (hR : 0 < R)
    (hc : ∀ h ∈ H, ‖h‖ = R) : Metric.diam (H : Set Plane) ≤ 2 * R := by
  apply Metric.diam_le_of_forall_dist_le (by linarith)
  intro a ha b hb
  calc
    dist a b ≤ dist a 0 + dist 0 b := dist_triangle a 0 b
    _ = 2 * R := by rw [dist_zero_right, dist_zero_left, hc a ha, hc b hb]; ring

/-- Antipodal hull closure forces actual diameter twice the circumradius. -/
theorem diam_eq_twice_radius_of_antipodal (H : Finset Plane) (R : ℝ)
    (hH : H.Nonempty) (hR : 0 < R) (hc : ∀ h ∈ H, ‖h‖ = R)
    (hanti : ∀ a ∈ H, -a ∈ H) : Metric.diam (H : Set Plane) = 2 * R := by
  apply le_antisymm (diam_le_twice_radius H R hR hc)
  obtain ⟨a, ha⟩ := hH
  have hd : dist a (-a) = 2 * R := by
    rw [dist_eq_norm, sub_neg_eq_add, ← two_smul ℝ a, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 2), hc a ha]
  rw [← hd]
  exact dist_le_diam_hull H (subset_convexHull ℝ (H : Set Plane) ha)
    (subset_convexHull ℝ (H : Set Plane) (hanti a ha))

/-- Two circle points at distance twice the radius are genuinely antipodal. -/
theorem eq_neg_of_dist_eq_twice_radius (a b : Plane) (R : ℝ)
    (ha : ‖a‖ = R) (hb : ‖b‖ = R) (hd : dist a b = 2 * R) : b = -a := by
  have hp := parallelogram_law_with_norm ℝ a b
  rw [ha, hb, ← dist_eq_norm, hd] at hp
  have hzero : ‖a + b‖ = 0 := by nlinarith [norm_nonneg (a + b)]
  have hab : a + b = 0 := norm_eq_zero.mp hzero
  exact eq_neg_of_add_eq_zero_right hab

/-- Antipodal diameter pairs are counted once, not twice: the actual diameter
multiplicity satisfies twice that multiplicity equals the hull cardinality. -/
theorem twice_diameter_multiplicity_of_antipodal (H : Finset Plane) (R : ℝ)
    (hH : H.Nonempty) (hR : 0 < R) (hc : ∀ h ∈ H, ‖h‖ = R)
    (hanti : ∀ a ∈ H, -a ∈ H) :
    2 * multiplicity H (Metric.diam (H : Set Plane)) = H.card := by
  classical
  let Q := (pairs H).filter fun e => pairDist e = Metric.diam (H : Set Plane)
  have hdiam := diam_eq_twice_radius_of_antipodal H R hH hR hc hanti
  have hne : ∀ a ∈ H, a ≠ -a := by
    intro a ha heq
    have hs : a + a = 0 := calc
      a + a = -a + a := congrArg (fun x => x + a) heq
      _ = 0 := neg_add_cancel a
    have hz : ‖(2 : ℝ) • a‖ = 0 := by rw [two_smul, hs, norm_zero]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2), hc a ha] at hz
    linarith
  have hdist : ∀ a ∈ H, dist a (-a) = Metric.diam (H : Set Plane) := by
    intro a ha
    rw [hdiam, dist_eq_norm, sub_neg_eq_add, ← two_smul ℝ a, norm_smul,
      Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2), hc a ha]
  have hmap : ∀ a ∈ H, s(a,-a) ∈ Q := by
    intro a ha
    exact Finset.mem_filter.mpr ⟨(mk_mem_pairs H a (-a)).mpr
      ⟨ha,hanti a ha,hne a ha⟩, hdist a ha⟩
  have hf : ∀ e ∈ Q, (H.filter fun a => s(a,-a) = e).card = 2 := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      have he' := Finset.mem_filter.mp he
      obtain ⟨ha,hb,hab⟩ := (mk_mem_pairs H a b).mp he'.1
      have hbneg : b = -a := eq_neg_of_dist_eq_twice_radius a b R (hc a ha) (hc b hb)
        (he'.2.trans hdiam)
      have hfset : (H.filter fun x => s(x,-x) = s(a,b)) = {a,b} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]
        constructor
        · rintro ⟨_hx, (⟨hxa,_⟩ | ⟨hxb,_⟩)⟩
          · exact Or.inl hxa
          · exact Or.inr hxb
        · rintro (rfl | rfl)
          · exact ⟨ha, Or.inl ⟨rfl,hbneg.symm⟩⟩
          · exact ⟨hb, Or.inr ⟨rfl, by rw [hbneg, neg_neg]⟩⟩
      rw [hfset, Finset.card_pair hab]
  have hsum := Finset.card_eq_sum_card_fiberwise hmap
  rw [Finset.sum_congr rfl hf] at hsum
  change 2 * Q.card = H.card
  simpa only [Finset.sum_const, nsmul_eq_mul, Nat.mul_comm, Nat.cast_id] using hsum.symm

/-- An open planar set containing a nonzero point contains three distinct nonzero
points; the construction stays inside one genuine positive-radius open ball. -/
private theorem three_nonzero_in_open (U : Set Plane) (hopen : IsOpen U)
    (p : Plane) (hp : p ∈ U) (hp0 : p ≠ 0) :
    ∃ u v w : Plane, u ∈ U ∧ v ∈ U ∧ w ∈ U ∧
      u ≠ 0 ∧ v ≠ 0 ∧ w ≠ 0 ∧ u ≠ v ∧ u ≠ w ∧ v ≠ w := by
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hopen p hp
  have hn : 0 < ‖p‖ := norm_pos_iff.mpr hp0
  let t := ε / (4 * ‖p‖)
  have ht : 0 < t := div_pos hε (by positivity)
  have htn : t * ‖p‖ = ε / 4 := by dsimp only [t]; field_simp
  let v := (1 + t) • p
  let w := (1 + 2 * t) • p
  have hnv : ‖v‖ = (1 + t) * ‖p‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < 1 + t)]
  have hnw : ‖w‖ = (1 + 2 * t) * ‖p‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < 1 + 2 * t)]
  have hdv : dist v p = ε / 4 := by
    calc
      dist v p = ‖t • p‖ := by
        rw [dist_eq_norm]
        change ‖(1+t) • p - p‖ = ‖t • p‖
        rw [add_smul, one_smul, add_sub_cancel_left]
      _ = t * ‖p‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      _ = ε / 4 := htn
  have hdw : dist w p = ε / 2 := by
    calc
      dist w p = ‖(2*t) • p‖ := by
        rw [dist_eq_norm]
        change ‖(1+2*t) • p - p‖ = ‖(2*t) • p‖
        rw [add_smul, one_smul, add_sub_cancel_left]
      _ = (2*t) * ‖p‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      _ = ε / 2 := by nlinarith [htn]
  have hv : v ∈ U := hball (by rw [Metric.mem_ball, hdv]; linarith)
  have hw : w ∈ U := hball (by rw [Metric.mem_ball, hdw]; linarith)
  have hv0 : v ≠ 0 := norm_pos_iff.mp (by rw [hnv]; positivity)
  have hw0 : w ≠ 0 := norm_pos_iff.mp (by rw [hnw]; positivity)
  have hpv : p ≠ v := by intro heq; rw [heq, dist_self] at hdv; linarith
  have hpw : p ≠ w := by intro heq; rw [heq, dist_self] at hdw; linarith
  have hvw : v ≠ w := by intro heq; rw [heq] at hdv; linarith
  exact ⟨p,v,w,hp,hv,hw,hp0,hv0,hw0,hpv,hpw,hvw⟩

/-- The original odd order-nine circle geometry jointly admits three pairwise
distinct, nonzero, ambient-interior points. No contrary premise is asserted. -/
theorem original_offcenter_geometry_fixture :
    ∃ (n : ℕ) (H : Finset Plane) (R : ℝ) (u v w : Plane),
      9 ≤ n ∧ Odd n ∧ H.card = n - 3 ∧ 0 < R ∧
      (∀ h ∈ H, ‖h‖ = R) ∧ u ≠ 0 ∧ v ≠ 0 ∧ w ≠ 0 ∧
      u ≠ v ∧ u ≠ w ∧ v ≠ w ∧
      u ∈ interior (convexHull ℝ (H : Set Plane)) ∧
      v ∈ interior (convexHull ℝ (H : Set Plane)) ∧
      w ∈ interior (convexHull ℝ (H : Set Plane)) := by
  obtain ⟨H,z,y,hcard,hcircle,_hext,hz,hy,hzy⟩ := rational_circle_fixture
  have hex : ∃ p : Plane, p ∈ interior (convexHull ℝ (H : Set Plane)) ∧ p ≠ 0 := by
    by_cases hz0 : z = 0
    · refine ⟨y,hy,?_⟩
      intro hy0
      exact hzy (hz0.trans hy0.symm)
    · exact ⟨z,hz,hz0⟩
  obtain ⟨p,hp,hp0⟩ := hex
  obtain ⟨u,v,w,hu,hv,hw,hu0,hv0,hw0,huv,huw,hvw⟩ :=
    three_nonzero_in_open _ isOpen_interior p hp hp0
  refine ⟨9,H,1,u,v,w,by decide,⟨4,by norm_num⟩,?_,by norm_num,?_,
    hu0,hv0,hw0,huv,huw,hvw,hu,hv,hw⟩
  · simpa using hcard
  · simpa only [dist_zero_right] using hcircle

/-- Three distinct actual images of one point force the full finite stabilizer
to have at least three elements. -/
theorem three_le_order_of_distinct_images (H : Finset Plane) (R : ℝ)
    (hH : H.Nonempty) (hR : 0 < R) (hc : ∀ a ∈ H, ‖a‖ = R)
    (u v w : Plane) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (g k : Stabilizer H) (hgv : rotate g.val u = v) (hkw : rotate k.val u = w) :
    3 ≤ order H := by
  classical
  letI := finite_stabilizer H hH hR hc
  letI := Fintype.ofFinite (Stabilizer H)
  have hg1 : g ≠ 1 := by
    intro heq
    have huv' : u = v := by simpa only [heq, OneMemClass.coe_one, rotate_one] using hgv
    exact huv huv'
  have hk1 : k ≠ 1 := by
    intro heq
    have huw' : u = w := by simpa only [heq, OneMemClass.coe_one, rotate_one] using hkw
    exact huw huw'
  have hgk : g ≠ k := by
    intro heq
    exact hvw (hgv.symm.trans (heq ▸ hkw))
  have hcard : ({1,g,k} : Finset (Stabilizer H)).card = 3 := by
    simp [hgk, Ne.symm hg1, Ne.symm hk1]
  change 3 ≤ Nat.card (Stabilizer H)
  rw [Nat.card_eq_fintype_card]
  rw [← hcard]
  exact Finset.card_le_univ _

/-- Arithmetic closure for the genuine geometric deficit package. -/
private theorem deficit_contradiction (S : Finset ℝ) (M q D : ℕ) (δ t : ℝ → ℕ)
    (hq : 3 ≤ q) (hM : 3 ≤ M) (hMq : M ∣ 2 * q) (hD : 1 ≤ D)
    (hsum : ∑ s ∈ S, δ s = q + D) (htsum : ∑ s ∈ S, t s = 3)
    (ht : ∀ s ∈ S, t s ≤ 3) (hδ : ∀ s ∈ S, δ s ≤ 2 + t s)
    (hdvd : ∀ s ∈ S, M ∣ δ s)
    (hfour : M = 4 → D = q)
    (hthree : M = 3 → ∃ ell ∈ S, ∀ s ∈ S, s ≠ ell → t s = 0) : False := by
  classical
  by_cases hbig : 6 ≤ M
  · have hz : ∀ s ∈ S, δ s = 0 := by
      intro s hs
      exact Nat.eq_zero_of_dvd_of_lt (hdvd s hs) (by have := hδ s hs; have := ht s hs; omega)
    have hzsum : ∑ s ∈ S, δ s = 0 := Finset.sum_eq_zero hz
    omega
  have hcases : M = 3 ∨ M = 4 ∨ M = 5 := by omega
  rcases hcases with h3 | h4 | h5
  · obtain ⟨ell,hell,hout⟩ := hthree h3
    have hz : ∀ s ∈ S, s ≠ ell → δ s = 0 := by
      intro s hs hne
      apply Nat.eq_zero_of_dvd_of_lt (hdvd s hs)
      have hb := hδ s hs
      rw [hout s hs hne] at hb
      omega
    have heq : ∑ s ∈ S, δ s = δ ell := by
      apply Finset.sum_eq_single ell
      · exact hz
      · intro hnot
        exact False.elim (hnot hell)
    have hbound : δ ell ≤ 3 := by
      obtain ⟨k,hk⟩ := hdvd ell hell
      have hb := hδ ell hell
      have htell := ht ell hell
      rw [h3] at hk
      omega
    omega
  · have hp : ∀ s ∈ S, δ s ≤ 2 * t s := by
      intro s hs
      obtain ⟨k,hk⟩ := hdvd s hs
      have hb := hδ s hs
      have hts := ht s hs
      rw [h4] at hk
      omega
    have hb := Finset.sum_le_sum hp
    rw [← Finset.mul_sum, htsum] at hb
    have hd : M ∣ ∑ s ∈ S, δ s := Finset.dvd_sum hdvd
    have hDq := hfour h4
    rw [hsum, h4] at hd
    obtain ⟨k,hk⟩ := hd
    omega
  · have hp : ∀ s ∈ S, 3 * δ s ≤ 5 * t s := by
      intro s hs
      obtain ⟨k,hk⟩ := hdvd s hs
      have hb := hδ s hs
      have hts := ht s hs
      rw [h5] at hk
      omega
    have hb := Finset.sum_le_sum hp
    rw [← Finset.mul_sum, ← Finset.mul_sum, hsum, htsum] at hb
    have hq5 : 5 ∣ q := by
      have hd : 5 ∣ 2 * q := h5 ▸ hMq
      exact ((Nat.Prime.dvd_mul (by decide : Nat.Prime 5)).mp hd).resolve_left (by decide)
    obtain ⟨k,hk⟩ := hq5
    omega

/-- The original off-center geometry cannot have every occurring positive
subdiametral distance of multiplicity at least `n+1`. All support, group, and
deficit facts are derived here from that geometry. -/
private theorem not_all_large (n : ℕ) (H : Finset Plane) (R : ℝ) (u v w : Plane)
    (hn : 9 ≤ n) (hodd : Odd n) (hH : H.card = n - 3) (hR : 0 < R)
    (hc : ∀ h ∈ H, ‖h‖ = R) (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hw0 : w ≠ 0)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hu : u ∈ interior (convexHull ℝ (H : Set Plane)))
    (hv : v ∈ interior (convexHull ℝ (H : Set Plane)))
    (hw : w ∈ interior (convexHull ℝ (H : Set Plane)))
    (hlarge : ∀ d : ℝ, 0 < d →
      d < Metric.diam ((insert u (insert v (insert w H)) : Finset Plane) : Set Plane) →
      (∃ a ∈ insert u (insert v (insert w H)),
        ∃ b ∈ insert u (insert v (insert w H)), dist a b = d) →
      n + 1 ≤ multiplicity (insert u (insert v (insert w H))) d) : False := by
  classical
  let X := insert u (insert v (insert w H))
  let S := nonDiameterDistances X
  let I : Finset Plane := {u,v,w}
  let N := H.card
  let q := S.card
  let M := order H
  let D := multiplicity H (Metric.diam (H : Set Plane))
  let δ := fun s => N - multiplicity H s
  let t := fun s => multiplicity I s
  obtain ⟨_hXcard,hdiam,hpos,hN,hnq,hq,hrad⟩ :=
    ThreeInteriorCounting.counting_saturation n H R u v w hn hodd hH hR hc huv huw hvw hu hv hw hlarge
  change N = 2 * q at hN
  change n = 2 * q + 3 at hnq
  change 3 ≤ q at hq
  change Metric.diam (X : Set Plane) = Metric.diam (H : Set Plane) at hdiam
  have hH6 : 6 ≤ H.card := by omega
  have hHne : H.Nonempty := Finset.card_pos.mp (by omega)
  have hH2 : 2 ≤ H.card := by omega
  have hru := hrad u (by simp) hu0
  have htrans : ∀ z ∈ I, z ≠ 0 → ∃ g : Stabilizer H, rotate g.val u = z := by
    intro z hz hz0
    have hrz := hrad z hz hz0
    apply CircleRotationTransport.exists_stabilizer_map_of_saturated_common_support H R u z hH6 hR hu0 hz0 hc
    · simpa only [dist_comm] using hru.1.trans hrz.1.symm
    · intro d hd
      have hdS : d ∈ S := by
        have hh : H.image (fun h => dist h u) = S := hru.1
        rw [← hh]
        simpa only [dist_comm] using hd
      constructor
      · simpa only [dist_comm] using hru.2.1 d hdS
      · simpa only [dist_comm] using hrz.2.1 d hdS
  obtain ⟨g,hgv⟩ := htrans v (by simp [I]) hv0
  obtain ⟨k,hkw⟩ := htrans w (by simp [I]) hw0
  have hM : 3 ≤ M := three_le_order_of_distinct_images H R hHne hR hc u v w huv huw hvw g k hgv hkw
  have hMN : M ∣ N := order_dvd_card H hHne hR hc
  have hMq : M ∣ 2 * q := hN ▸ hMN
  have hsub : H ⊆ X := by intro a ha; simp [X,ha]
  have hIX : I ⊆ X := by
    intro a ha
    simp only [I,Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl <;> simp [X]
  have hIint : ∀ a ∈ I, a ∈ interior (convexHull ℝ (H : Set Plane)) := by
    intro a ha
    simp only [I,Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact hu
    · exact hv
    · exact hw
  have hIcard : I.card = 3 := by simp [I,huv,huw,hvw]
  have himap : ∀ e ∈ pairs I, pairDist e ∈ S := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      obtain ⟨ha,hb,hab⟩ := (mk_mem_pairs I a b).mp he
      apply (mem_nonDiameterDistances X _).mpr
      refine ⟨⟨a,hIX ha,b,hIX hb,hab,rfl⟩,?_⟩
      rw [hdiam]
      exact dist_lt_diam_hull H hH2 (hIint a ha) (interior_subset (hIint b hb))
  have htsum : ∑ s ∈ S, t s = 3 := by
    have hs := sum_multiplicity_of_pair_support I S himap
    rw [hIcard] at hs
    exact hs
  have ht : ∀ s ∈ S, t s ≤ 3 := by
    intro s _hs
    have hb := Finset.card_filter_le (pairs I) (fun e => pairDist e = s)
    rw [card_pairs, hIcard] at hb
    exact hb
  obtain ⟨a,ha,b,hb,habd⟩ := exists_diameter_pair H hHne
  have hab : a ≠ b := by intro heq; rw [heq,dist_self] at habd; linarith
  have hD : 1 ≤ D := by
    have hh := one_le_multiplicity_of_pair H a b ha hb hab
    rwa [habd] at hh
  have hcn : ∀ h ∈ H, dist h (0 : Plane) = R := by simpa only [dist_zero_right] using hc
  have hcap : ∀ s ∈ S, multiplicity H s ≤ N := by
    intro s _hs
    exact chord_capacity H 0 R s hR hcn
  have hsumadd : (∑ s ∈ S, δ s) + (∑ s ∈ S, multiplicity H s) = q * N := by
    rw [← Finset.sum_add_distrib]
    calc
      (∑ s ∈ S, (δ s + multiplicity H s)) = ∑ _s ∈ S, N := by
        apply Finset.sum_congr rfl
        intro s hs
        exact Nat.sub_add_cancel (hcap s hs)
      _ = q * N := by simp [q]
  have hhull := hull_pair_partition H X hsub hdiam
  change (∑ s ∈ S, multiplicity H s) + D = N.choose 2 at hhull
  have hchoose : N.choose 2 + q = q * N := by
    have he := choose_even_equality N (q-1) (by omega)
    have hqp : q-1+1 = q := by omega
    nlinarith
  have hsum : ∑ s ∈ S, δ s = q + D := by nlinarith [hhull]
  have hμ : ∀ s ∈ S, multiplicity X s = multiplicity H s + 6 + t s := by
    intro s hs
    have hr := multiplicity_insert_three H u v w s
      (ThreeInteriorCounting.interior_not_mem_circle H R u hR hc hu)
      (ThreeInteriorCounting.interior_not_mem_circle H R v hR hc hv)
      (ThreeInteriorCounting.interior_not_mem_circle H R w hR hc hw) huv huw hvw
    rw [hru.2.1 s hs, (hrad v (by simp) hv0).2.1 s hs,
      (hrad w (by simp) hw0).2.1 s hs] at hr
    exact hr
  have hδ : ∀ s ∈ S, δ s ≤ 2 + t s := by
    intro s hs
    obtain ⟨hspos,hslt,hsocc⟩ :=
      (ThreeInteriorCounting.mem_nonDiameterDistances_iff_positive X s).mp hs
    have hbig := hlarge s hspos hslt hsocc
    rw [hμ s hs] at hbig
    have hcaps := hcap s hs
    dsimp only [δ]
    omega
  have hdvd : ∀ s ∈ S, M ∣ δ s := by
    intro s hs
    obtain ⟨hspos,hslt,_hsocc⟩ :=
      (ThreeInteriorCounting.mem_nonDiameterDistances_iff_positive X s).mp hs
    rw [hdiam] at hslt
    have hsR : s < 2 * R := hslt.trans_le (diam_le_twice_radius H R hR hc)
    exact Nat.dvd_sub hMN (order_dvd_multiplicity H hHne hR hc hspos hsR)
  have hfour : M = 4 → D = q := by
    intro h4
    have heven : Even (order H) := by rw [show order H = 4 from h4]; decide
    have hanti : ∀ a ∈ H, -a ∈ H := by
      intro a ha
      exact (mem_iff_neg_mem_of_even_order H hHne hR hc heven a).mp ha
    have hcount := twice_diameter_multiplicity_of_antipodal H R hHne hR hc hanti
    change 2 * D = N at hcount
    omega
  have hthree : M = 3 → ∃ ell ∈ S, ∀ s ∈ S, s ≠ ell → t s = 0 := by
    intro h3
    have hvOrb : v ∈ MulAction.orbit (Stabilizer H) u := MulAction.mem_orbit_iff.mpr ⟨g,hgv⟩
    have hwOrb : w ∈ MulAction.orbit (Stabilizer H) u := MulAction.mem_orbit_iff.mpr ⟨k,hkw⟩
    have heq := equilateral_of_mem_orbit_order_eq_three H h3 u u v w
      (MulAction.mem_orbit_self u) hvOrb hwOrb huv huw hvw
    let ell := dist u v
    have hell : ell ∈ S := himap s(u,v) ((mk_mem_pairs I u v).mpr ⟨by simp [I],by simp [I],huv⟩)
    have hpair : ∀ e ∈ pairs I, pairDist e = ell := by
      intro e he
      induction e using Sym2.ind with
      | _ a b =>
        obtain ⟨ha,hb,hab⟩ := (mk_mem_pairs I a b).mp he
        simp only [I,Finset.mem_insert,Finset.mem_singleton] at ha hb
        rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
        all_goals simp only [pairDist_mk]
        all_goals first
          | exact False.elim (hab rfl)
          | exact rfl
          | exact heq.1.symm
          | exact heq.2.symm
          | exact dist_comm _ _
          | exact (dist_comm _ _).trans heq.1.symm
          | exact (dist_comm _ _).trans heq.2.symm
    refine ⟨ell,hell,?_⟩
    intro s hs hsne
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    have hf := Finset.mem_filter.mp he
    exact hsne (hf.2.symm.trans (hpair e hf.1))
  exact deficit_contradiction S M q D δ t hq hM hMq hD hsum htsum ht hδ hdvd hfour hthree

/-- For odd `n ≥ 9`, `n-3` points on a positive-radius zero-centered circle
and three distinct nonzero ambient-interior points form an `n`-point set with an
actual positive subdiametral distance of multiplicity between one and `n`.
No support, equal-radius, orbit, group-order, or deficit certificate is assumed. -/
theorem zero_center_witness (n : ℕ) (H : Finset Plane) (R : ℝ) (u v w : Plane)
    (hn : 9 ≤ n) (hodd : Odd n) (hH : H.card = n - 3) (hR : 0 < R)
    (hc : ∀ h ∈ H, ‖h‖ = R) (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hw0 : w ≠ 0)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hu : u ∈ interior (convexHull ℝ (H : Set Plane)))
    (hv : v ∈ interior (convexHull ℝ (H : Set Plane)))
    (hw : w ∈ interior (convexHull ℝ (H : Set Plane))) :
    let X := insert u (insert v (insert w H))
    X.card = n ∧ ∃ d : ℝ, 0 < d ∧ d < Metric.diam (X : Set Plane) ∧
      (∃ a ∈ X, ∃ b ∈ X, dist a b = d) ∧
      1 ≤ multiplicity X d ∧ multiplicity X d ≤ n := by
  classical
  let X := insert u (insert v (insert w H))
  have hcard : X.card = n := by
    have hh := ThreeInteriorCounting.card_insert_three_interiors H R u v w hR hc hu hv hw huv huw hvw
    change X.card = H.card + 3 at hh
    omega
  refine ⟨hcard,?_⟩
  by_contra hno
  apply not_all_large n H R u v w hn hodd hH hR hc hu0 hv0 hw0 huv huw hvw hu hv hw
  intro d hdpos hdlt hocc
  obtain ⟨a,ha,b,hb,habd⟩ := hocc
  have hab : a ≠ b := by
    intro heq
    rw [heq,dist_self] at habd
    linarith
  have hμ : 1 ≤ multiplicity X d := by
    have hh := one_le_multiplicity_of_pair X a b ha hb hab
    rwa [habd] at hh
  by_contra hsmall
  exact hno ⟨d,hdpos,hdlt,⟨a,ha,b,hb,habd⟩,hμ,by omega⟩

/-- Translating an arbitrary circle center to zero preserves the original
odd all-three-off-center geometry and yields an actual positive subdiametral
length with multiplicity between one and `n`, as well as exact set cardinality.
All three interiors remain distinct from the given center. -/
theorem circle_witness (n : ℕ) (H : Finset Plane) (O : Plane) (R : ℝ) (u v w : Plane)
    (hn : 9 ≤ n) (hodd : Odd n) (hH : H.card = n - 3) (hR : 0 < R)
    (hc : ∀ h ∈ H, dist h O = R) (huO : u ≠ O) (hvO : v ≠ O) (hwO : w ≠ O)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hu : u ∈ interior (convexHull ℝ (H : Set Plane)))
    (hv : v ∈ interior (convexHull ℝ (H : Set Plane)))
    (hw : w ∈ interior (convexHull ℝ (H : Set Plane))) :
    let X := insert u (insert v (insert w H))
    X.card = n ∧ ∃ d : ℝ, 0 < d ∧ d < Metric.diam (X : Set Plane) ∧
      (∃ a ∈ X, ∃ b ∈ X, dist a b = d) ∧
      1 ≤ multiplicity X d ∧ multiplicity X d ≤ n := by
  classical
  let f : Plane → Plane := fun h => h - O
  have hf : Isometry f := fun a b => by simp [f,edist_dist]
  have hcard : (H.image f).card = H.card := Finset.card_image_of_injective H hf.injective
  have hc' : ∀ h ∈ H.image f, ‖h‖ = R := by
    intro h hh
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hh
    exact hc a ha
  have himage : insert (f u) (insert (f v) (insert (f w) (H.image f))) =
      (insert u (insert v (insert w H))).image f := by simp only [Finset.image_insert]
  obtain ⟨hXcard,d,hpos,hlt,hocc,hμ,hbound⟩ := zero_center_witness n (H.image f) R (f u) (f v) (f w)
    hn hodd (by rw [hcard]; exact hH) hR hc'
    (sub_ne_zero.mpr huO) (sub_ne_zero.mpr hvO) (sub_ne_zero.mpr hwO)
    (fun he => huv (hf.injective he)) (fun he => huw (hf.injective he))
    (fun he => hvw (hf.injective he))
    (sub_mem_interior_hull H O u hu) (sub_mem_interior_hull H O v hv)
    (sub_mem_interior_hull H O w hw)
  rw [himage] at hXcard hlt hocc hμ hbound
  rw [Finset.card_image_of_injective _ hf.injective] at hXcard
  rw [multiplicity_image_isometry _ f hf] at hμ hbound
  rw [Finset.coe_image,hf.diam_image] at hlt
  obtain ⟨a,ha,b,hb,hab⟩ := hocc
  obtain ⟨a',ha',rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨b',hb',rfl⟩ := Finset.mem_image.mp hb
  have hab' : dist a' b' = d := (hf.dist_eq a' b').symm.trans hab
  exact ⟨hXcard,d,hpos,hlt,⟨a',ha',b',hb',hab'⟩,hμ,hbound⟩

end Erdos132.ThreeInteriorOffCenter
