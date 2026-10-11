import Erdos.Erdos132.FourInteriorLowerSupport
import Erdos.Erdos132.UniqueDiameterCircle

set_option autoImplicit false

namespace Erdos132.FourInteriorCircle

open Erdos132.TwoInteriorCircle

/-- An even configuration of at least ten points consisting of a positive-radius
zero-centered circular hull and four distinct nonzero ambient hull interiors has
an occurring positive nondiameter length with unordered loop-free multiplicity
between one and its actual total cardinality. No support or diameter certificate
is assumed. -/
theorem four_interior_circle (n : ℕ) (H I : Finset Plane) (R : ℝ)
    (hn : 10 ≤ n) (heven : Even n) (hH : H.card = n - 4)
    (hR : 0 < R) (hcircle : ∀ h ∈ H, ‖h‖ = R) (hI : I.card = 4)
    (hInt : ∀ z ∈ I, z ∈ interior (convexHull ℝ (H : Set Plane)))
    (hoff : ∀ z ∈ I, z ≠ 0) :
    (H ∪ I).card = n ∧ ∃ d : ℝ,
      0 < d ∧ d < Metric.diam ((H ∪ I : Finset Plane) : Set Plane) ∧
      (∃ a ∈ H ∪ I, ∃ b ∈ H ∪ I, a ≠ b ∧ dist a b = d) ∧
      1 ≤ multiplicity (H ∪ I) d ∧ multiplicity (H ∪ I) d ≤ n := by
  classical
  let X := H ∪ I
  let S := nonDiameterDistances X
  have hsize : H.card + 4 = n := by omega
  have hHtwo : 2 ≤ H.card := by omega
  have hcard : X.card = n := by
    change (H ∪ I).card = n
    rw [FourInteriorLowerSupport.card_union_four_interiors H I R hR hcircle hI hInt]
    exact hsize
  have hD : Metric.diam (X : Set Plane) = Metric.diam (H : Set Plane) :=
    FourInteriorLowerSupport.diam_union_interiors H I hInt
  have hc : ∀ h ∈ H, dist h (0 : Plane) = R := by
    simpa only [dist_zero_right] using hcircle
  refine ⟨hcard, ?_⟩
  by_contra hnone
  have hlarge : ∀ d ∈ S, X.card + 1 ≤ multiplicity X d := by
    intro d hd
    obtain ⟨hocc, hlt⟩ := (mem_nonDiameterDistances X d).mp hd
    obtain ⟨a, ha, b, hb, hab, habd⟩ := hocc
    have hpos : 0 < d := habd ▸ dist_pos.mpr hab
    have hmult : 1 ≤ multiplicity X d := by
      apply Finset.card_pos.mpr
      exact ⟨s(a,b), Finset.mem_filter.mpr
        ⟨(mk_mem_pairs X a b).mpr ⟨ha,hb,hab⟩, habd⟩⟩
    have hnot : ¬ multiplicity X d ≤ n := by
      intro hbound
      exact hnone ⟨d,hpos,hlt,⟨a,ha,b,hb,hab,habd⟩,hmult,hbound⟩
    omega
  obtain ⟨z, hz⟩ := Finset.card_pos.mp (by omega : 0 < I.card)
  have hzH : z ∉ H :=
    ThreeInteriorCounting.interior_not_mem_circle H R z hR hcircle (hInt z hz)
  have hmap : ∀ h ∈ H, dist h z ∈ S := by
    intro h hh
    apply (mem_nonDiameterDistances X _).mpr
    refine ⟨⟨h, Finset.mem_union_left _ hh, z, Finset.mem_union_right _ hz, ?_, rfl⟩, ?_⟩
    · intro heq
      exact hzH (heq ▸ hh)
    · rw [hD, dist_comm]
      exact dist_lt_diam_hull H hHtwo (hInt z hz) (subset_convexHull ℝ _ hh)
  have hcap : ∀ d ∈ S, (H.filter fun h => dist h z = d).card ≤ 2 := by
    intro d _hd
    exact radial_card_le_two H 0 z R d hc (hoff z hz)
  have hlower : H.card ≤ 2 * S.card :=
    Finset.card_le_mul_card_image_of_maps_to hmap 2 hcap
  by_cases hlow : 2 * S.card = H.card
  · obtain ⟨_hcard, d, hdpos, hdlt, hocc, hmult, hbound⟩ :=
      FourInteriorLowerSupport.exists_distance_of_even_lower_support
        n H I R hn heven hH hR hcircle hI hInt hoff hlow
    exact hnone ⟨d,hdpos,hdlt,hocc,hmult,hbound⟩
  · have hupperRadial : X.card - 2 ≤ 2 * S.card := by
      obtain ⟨k, hk⟩ := heven
      omega
    obtain ⟨_hsizeq, _hq, _hsaturated, hdiamCard⟩ :=
      equality_structure X (by omega) hupperRadial hlarge
    obtain ⟨a, ha, b, hb, habD⟩ := exists_diameter_pair X
      (Finset.card_pos.mp (by omega : 0 < X.card))
    have hDpos : 0 < Metric.diam (X : Set Plane) := diam_pos X (by omega)
    have hab : a ≠ b := by
      intro heq
      rw [← habD, heq, dist_self] at hDpos
      exact lt_irrefl 0 hDpos
    let D := (pairs X).filter fun e => ¬pairDist e < Metric.diam (X : Set Plane)
    have hDcard : D.card = 1 := hdiamCard
    have habMem : s(a,b) ∈ D := by
      exact Finset.mem_filter.mpr ⟨(mk_mem_pairs X a b).mpr ⟨ha,hb,hab⟩,
        by simp only [pairDist_mk, habD, lt_self_iff_false, not_false_eq_true]⟩
    have hsingle : D = {s(a,b)} := by
      obtain ⟨e, he⟩ := Finset.card_eq_one.mp hDcard
      have hae : s(a,b) = e := by simpa only [he, Finset.mem_singleton] using habMem
      rw [hae]
      exact he
    have hunique : ∃ a ∈ H ∪ I, ∃ b ∈ H ∪ I, a ≠ b ∧
        dist a b = Metric.diam ((H ∪ I : Finset Plane) : Set Plane) ∧
        ∀ x ∈ H ∪ I, ∀ y ∈ H ∪ I,
          dist x y = Metric.diam ((H ∪ I : Finset Plane) : Set Plane) → s(x,y) = s(a,b) := by
      refine ⟨a,ha,b,hb,hab,habD,?_⟩
      intro x hx y hy hxyD
      change dist x y = Metric.diam (X : Set Plane) at hxyD
      have hxy : x ≠ y := by
        intro heq
        rw [← hxyD, heq, dist_self] at hDpos
        exact lt_irrefl 0 hDpos
      have hxyMem : s(x,y) ∈ D := by
        exact Finset.mem_filter.mpr ⟨(mk_mem_pairs X x y).mpr ⟨hx,hy,hxy⟩,
          by simp only [pairDist_mk, hxyD, lt_self_iff_false, not_false_eq_true]⟩
      simpa only [hsingle, Finset.mem_singleton] using hxyMem
    obtain ⟨_hcard, d, hdpos, hdlt, hocc, _hmax, hmult, hbound⟩ :=
      UniqueDiameterCircle.unique_diameter_circle H.card 4 H I 0 R
        (by omega) (by decide) rfl hI hR hc ⟨z,hInt z hz⟩ hInt hunique
    rw [hsize] at hbound
    exact hnone ⟨d,hdpos,hdlt,hocc,hmult,hbound⟩

/-- The inherited rational six-vertex fixture with four nonzero ambient interiors
jointly satisfies all original even four-interior hypotheses and the complete
new theorem's conclusion, with no support or unique-diameter premise. -/
theorem original_geometry_and_conclusion : ∃ (n : ℕ) (H I : Finset Plane) (R : ℝ),
    10 ≤ n ∧ Even n ∧ H.card = n - 4 ∧ I.card = 4 ∧ 0 < R ∧
    (∀ h ∈ H, ‖h‖ = R) ∧
    (∀ z ∈ I, z ∈ interior (convexHull ℝ (H : Set Plane))) ∧
    (∀ z ∈ I, z ≠ 0) ∧ (H ∪ I).card = n ∧ ∃ d : ℝ,
      0 < d ∧ d < Metric.diam ((H ∪ I : Finset Plane) : Set Plane) ∧
      (∃ a ∈ H ∪ I, ∃ b ∈ H ∪ I, a ≠ b ∧ dist a b = d) ∧
      1 ≤ multiplicity (H ∪ I) d ∧ multiplicity (H ∪ I) d ≤ n := by
  obtain ⟨n,H,I,R,hn,heven,hH,hI,hR,hcircle,hInt,hoff,_hcard⟩ :=
    FourInteriorLowerSupport.original_geometry_family_nonempty
  have hclaim := four_interior_circle n H I R hn heven hH hR hcircle hI hInt hoff
  exact ⟨n,H,I,R,hn,heven,hH,hI,hR,hcircle,hInt,hoff,hclaim⟩

end Erdos132.FourInteriorCircle
