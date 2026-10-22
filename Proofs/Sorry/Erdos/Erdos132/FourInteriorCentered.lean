import Sorry.Erdos.Erdos132.FourInteriorLowerSupport
import Erdos.Erdos132.ThreeInteriorCenter
import Erdos.Erdos132.CircleFixtures
import Erdos.Erdos132.UniqueDiameterCircle
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false

open scoped BigOperators Pointwise

namespace Erdos132.FourInteriorCentered

open TwoInteriorCircle CircleRotation

noncomputable section

local instance : DecidableEq Rotation := Classical.decEq _

/-- Every noncentral interior has the full support of the actual
union, with exactly two hull vertices in every radial fiber. Erasing the center
only selects the radial base points; it does not change the distance support. -/
theorem radial_saturation (H I : Finset Plane) (R : ℝ)
    (hH : 6 ≤ H.card) (hR : 0 < R) (hcircle : ∀ h ∈ H, ‖h‖ = R)
    (hinterior : ∀ z ∈ I, z ∈ interior (convexHull ℝ (H : Set Plane)))
    (hq : 2 * (nonDiameterDistances (H ∪ I)).card = H.card) :
    ∀ z ∈ I.erase 0,
      H.image (fun h => dist z h) = nonDiameterDistances (H ∪ I) ∧
      (∀ d ∈ nonDiameterDistances (H ∪ I),
        (H.filter fun h => dist z h = d).card = 2) := by
  classical
  let X := H ∪ I
  let S := nonDiameterDistances X
  have hdiam := FourInteriorLowerSupport.diam_union_interiors H I hinterior
  intro z hz
  have hzI := (Finset.mem_erase.mp hz).2
  have hz0 := (Finset.mem_erase.mp hz).1
  have hzH := ThreeInteriorCounting.interior_not_mem_circle H R z hR hcircle
    (hinterior z hzI)
  have hmap : ∀ h ∈ H, dist z h ∈ S := by
    intro h hh
    apply (mem_nonDiameterDistances X (dist z h)).mpr
    refine ⟨⟨z, Finset.mem_union_right H hzI, h, Finset.mem_union_left I hh,
      fun heq => hzH (heq.symm ▸ hh), rfl⟩, ?_⟩
    rw [hdiam]
    exact dist_lt_diam_hull H (by omega) (hinterior z hzI)
      (subset_convexHull ℝ (H : Set Plane) hh)
  have hcap : ∀ d ∈ S, (H.filter fun h => dist z h = d).card ≤ 2 := by
    intro d _hd
    simpa only [dist_comm] using radial_card_le_two H 0 z R d
      (by simpa only [dist_zero_right] using hcircle) hz0
  have hfibers : ∀ d ∈ S, (H.filter fun h => dist z h = d).card = 2 :=
    saturated_fibers H S (fun h => dist z h) hmap hcap hq.symm
  refine ⟨Finset.Subset.antisymm ?_ ?_, hfibers⟩
  · intro d hd
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hd
    exact hmap h hh
  · intro d hd
    have hpos : 0 < (H.filter fun h => dist z h = d).card := by
      rw [hfibers d hd]
      decide
    obtain ⟨h, hh⟩ := Finset.card_pos.mp hpos
    exact Finset.mem_image.mpr ⟨h, (Finset.mem_filter.mp hh).1,
      (Finset.mem_filter.mp hh).2⟩

/-- The centered lower-support geometry supplies a preserving rotation between
any two members of the erased, noncentral interior set. -/
theorem exists_stabilizer_map (H I : Finset Plane) (R : ℝ)
    (hH : 6 ≤ H.card) (hR : 0 < R) (hcircle : ∀ h ∈ H, ‖h‖ = R)
    (hinterior : ∀ z ∈ I, z ∈ interior (convexHull ℝ (H : Set Plane)))
    (hq : 2 * (nonDiameterDistances (H ∪ I)).card = H.card)
    (u v : Plane) (hu : u ∈ I.erase 0) (hv : v ∈ I.erase 0) :
    ∃ g : Stabilizer H, rotate g.val u = v := by
  have hsatu := radial_saturation H I R hH hR hcircle hinterior hq u hu
  have hsatv := radial_saturation H I R hH hR hcircle hinterior hq v hv
  apply CircleRotationTransport.exists_stabilizer_map_of_saturated_common_support
    H R u v hH hR (Finset.mem_erase.mp hu).1 (Finset.mem_erase.mp hv).1 hcircle
    (hsatu.1.trans hsatv.1.symm)
  intro d hd
  have hdS := hsatu.1 ▸ hd
  exact ⟨hsatu.2 d hdS, hsatv.2 d hdS⟩

/-- Four interiors including the center give three distinct nonzero transported
points, so the full rotation stabilizer has order at least three and divides the
hull cardinality. No off-center hypothesis is imposed on the original set. -/
theorem three_le_order_and_order_dvd_card (H I : Finset Plane) (R : ℝ)
    (hH : 6 ≤ H.card) (hR : 0 < R) (hcircle : ∀ h ∈ H, ‖h‖ = R)
    (hI : I.card = 4) (hzero : (0 : Plane) ∈ I)
    (hinterior : ∀ z ∈ I, z ∈ interior (convexHull ℝ (H : Set Plane)))
    (hq : 2 * (nonDiameterDistances (H ∪ I)).card = H.card) :
    3 ≤ order H ∧ order H ∣ H.card := by
  classical
  have hHne : H.Nonempty := Finset.card_pos.mp (by omega)
  letI := finite_stabilizer H hHne hR hcircle
  have hJ : (I.erase 0).card = 3 := by rw [Finset.card_erase_of_mem hzero, hI]
  obtain ⟨u, hu⟩ := Finset.card_pos.mp (show 0 < (I.erase 0).card by omega)
  have hex : ∀ v : {z // z ∈ I.erase 0}, ∃ g : Stabilizer H, rotate g.val u = v.val := by
    intro v
    exact exists_stabilizer_map H I R hH hR hcircle hinterior hq u v.val hu v.property
  let f : {z // z ∈ I.erase 0} → Stabilizer H := fun v => (hex v).choose
  have hf : Function.Injective f := by
    intro v w heq
    apply Subtype.ext
    calc
      v.val = rotate (f v).val u := (hex v).choose_spec.symm
      _ = rotate (f w).val u := congrArg (fun g : Stabilizer H => rotate g.val u) heq
      _ = w.val := (hex w).choose_spec
  have hbound := Nat.card_le_card_of_injective f hf
  have hthree : 3 ≤ order H := by
    simpa only [order, Nat.card_eq_fintype_card, Fintype.card_coe, hJ] using hbound
  exact ⟨hthree, order_dvd_card H hHne hR hcircle⟩

private theorem full_orbit_of_four_le_order (H I : Finset Plane) (R : ℝ)
    (hH : 6 ≤ H.card) (hR : 0 < R) (hcircle : ∀ h ∈ H, ‖h‖ = R)
    (hfour : 4 ≤ order H)
    (hq : 2 * (nonDiameterDistances (H ∪ I)).card = H.card) :
    order H = H.card ∧ ∀ p ∈ H, ∀ h : Plane,
      h ∈ H ↔ ∃ g : Stabilizer H, rotate g.val p = h := by
  classical
  have hHne : H.Nonempty := Finset.card_pos.mp (by omega)
  letI := finite_stabilizer H hHne hR hcircle
  have hdiv := order_dvd_card H hHne hR hcircle
  have hcoeff : ∀ p ∈ H, ∃ A : Finset Rotation, A.card = H.card ∧
      (∀ g : Rotation, g ∈ A ↔ rotate g p ∈ H) ∧
      (∀ g : Rotation, g ∈ Stabilizer H ↔ g ∈ A) := by
    intro p hp
    obtain ⟨A, hOne, hcardA, hA⟩ := FourInteriorLowerSupport.exists_hull_coefficients H R p hR hcircle hp
    have hstableA : ∀ g : Stabilizer H, ∀ a ∈ A, g.val * a ∈ A := by
      intro g a ha
      apply (hA _).mpr
      rw [rotate_mul]
      exact (g.property (rotate a p)).mpr ((hA a).mp ha)
    have hstableT : ∀ g : Stabilizer H, ∀ t ∈ A / A, g.val * t ∈ A / A := by
      intro g t ht
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_div.mp ht
      exact Finset.mem_div.mpr ⟨g.val * a, hstableA g a ha, b, hb, mul_div_assoc _ _ _⟩
    have hupper : (A / A).card ≤ A.card + 3 := by
      have hbound := FourInteriorLowerSupport.quotient_support_card_le H I R p A hR hcircle hp hOne hA
      rw [hq, ← hcardA] at hbound
      exact hbound
    have hquot : A / A = A := FourInteriorLowerSupport.quotient_support_eq_of_small_gap A (Stabilizer H)
      hOne hfour (hcardA ▸ hdiv) hstableT hupper
    obtain ⟨K, hK⟩ := FourInteriorLowerSupport.exists_subgroup_of_quotient_support_eq A hOne hquot
    refine ⟨A, hcardA, hA, ?_⟩
    intro g
    constructor
    · intro hg
      exact (hA g).mpr ((hg p).mpr hp)
    · intro hg
      apply (mem_stabilizer_iff_image H g).mpr
      have hsub : H.image (rotate g) ⊆ H := by
        intro x hx
        obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨a, ha⟩ := exists_rotation_map hR (hcircle p hp) (hcircle h hh)
        have haA : a ∈ A := (hA a).mpr (ha ▸ hh)
        have hgaA : g * a ∈ A := (hK _).mp (K.mul_mem ((hK _).mpr hg) ((hK _).mpr haA))
        have hgaH := (hA _).mp hgaA
        rw [rotate_mul, ha] at hgaH
        exact hgaH
      apply Finset.eq_of_subset_of_card_le hsub
      rw [Finset.card_image_of_injective H (rotate_isometry g).injective]
  obtain ⟨p, hp⟩ := hHne
  obtain ⟨A, hcardA, _hrep, hA⟩ := hcoeff p hp
  have horder : order H = H.card := by
    let e : Stabilizer H ≃ {g // g ∈ A} := Equiv.subtypeEquivRight hA
    rw [order, Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, hcardA]
  refine ⟨horder, ?_⟩
  intro p hp h
  constructor
  · intro hh
    obtain ⟨B, _hcardB, hrepB, hB⟩ := hcoeff p hp
    obtain ⟨g, hg⟩ := exists_rotation_map hR (hcircle p hp) (hcircle h hh)
    have hgB : g ∈ B := (hrepB g).mpr (hg ▸ hh)
    exact ⟨⟨g, (hB g).mpr hgB⟩, hg⟩
  · rintro ⟨g, rfl⟩
    exact (g.property p).mpr hp

/-- The original centered lower-support premises imply the actual cardinality,
three genuine nonzero interiors, a common strict radius, center-radius support
membership, saturated actual-support fibers, and the full stabilizer transport
and order constraints. This is a geometry reduction, not branch exclusion. -/
theorem centered_lower_support_geometry (n : ℕ) (H I : Finset Plane) (R : ℝ)
    (hn : 10 ≤ n) (hH : H.card = n - 4) (hR : 0 < R)
    (hcircle : ∀ h ∈ H, ‖h‖ = R) (hI : I.card = 4) (hzero : (0 : Plane) ∈ I)
    (hinterior : ∀ z ∈ I, z ∈ interior (convexHull ℝ (H : Set Plane)))
    (hq : 2 * (nonDiameterDistances (H ∪ I)).card = H.card) :
    (H ∪ I).card = n ∧ (I.erase 0).card = 3 ∧
      ∃ ρ : ℝ, 0 < ρ ∧ ρ < R ∧ (∀ z ∈ I.erase 0, ‖z‖ = ρ) ∧
        R ∈ nonDiameterDistances (H ∪ I) ∧ ρ ∈ nonDiameterDistances (H ∪ I) ∧
        (∀ z ∈ I.erase 0,
          H.image (fun h => dist z h) = nonDiameterDistances (H ∪ I) ∧
          ∀ d ∈ nonDiameterDistances (H ∪ I),
            (H.filter fun h => dist z h = d).card = 2) ∧
        (∀ u ∈ I.erase 0, ∀ v ∈ I.erase 0,
          ∃ g : Stabilizer H, rotate g.val u = v) ∧
        3 ≤ order H ∧ order H ∣ H.card := by
  classical
  have hHsix : 6 ≤ H.card := by omega
  have hcard := FourInteriorLowerSupport.card_union_four_interiors H I R
    hR hcircle hI hinterior
  have hJ : (I.erase 0).card = 3 := by rw [Finset.card_erase_of_mem hzero, hI]
  obtain ⟨u, hu⟩ := Finset.card_pos.mp (show 0 < (I.erase 0).card by omega)
  have hu0 := (Finset.mem_erase.mp hu).1
  have huI := (Finset.mem_erase.mp hu).2
  have hnorm : ∀ z ∈ I.erase 0, ‖z‖ = ‖u‖ := by
    intro z hz
    obtain ⟨g, hg⟩ := exists_stabilizer_map H I R hHsix hR hcircle hinterior hq u z hu hz
    rw [← hg, norm_rotate]
  have hρpos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  have hρlt : ‖u‖ < R := by
    simpa only [dist_zero_right] using dist_center_lt_radius H 0 hR
      (by simpa only [dist_zero_right] using hcircle) (hinterior u huI)
  have hdiam := FourInteriorLowerSupport.diam_union_interiors H I hinterior
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < H.card by omega)
  have hmemR : R ∈ nonDiameterDistances (H ∪ I) := by
    apply (ThreeInteriorCounting.mem_nonDiameterDistances_iff_positive (H ∪ I) R).mpr
    refine ⟨hR, ?_, 0, Finset.mem_union_right H hzero,
      a, Finset.mem_union_left I ha, ?_⟩
    · rw [hdiam]
      have hlt := dist_lt_diam_hull H (by omega) (hinterior 0 hzero)
        (subset_convexHull ℝ _ ha)
      simpa only [dist_zero_left, hcircle a ha] using hlt
    · simpa only [dist_zero_left] using hcircle a ha
  have hmemρ : ‖u‖ ∈ nonDiameterDistances (H ∪ I) := by
    apply (ThreeInteriorCounting.mem_nonDiameterDistances_iff_positive (H ∪ I) ‖u‖).mpr
    refine ⟨hρpos, ?_, u, Finset.mem_union_right H huI,
      0, Finset.mem_union_right H hzero, dist_zero_right u⟩
    rw [hdiam]
    simpa only [dist_zero_right] using dist_lt_diam_hull H (by omega)
      (hinterior u huI) (interior_subset (hinterior 0 hzero))
  obtain ⟨horder, hdiv⟩ := three_le_order_and_order_dvd_card H I R hHsix hR
    hcircle hI hzero hinterior hq
  refine ⟨by omega, hJ, ‖u‖, hρpos, hρlt, hnorm, hmemR, hmemρ,
    radial_saturation H I R hHsix hR hcircle hinterior hq, ?_, horder, hdiv⟩
  intro v hv w hw
  exact exists_stabilizer_map H I R hHsix hR hcircle hinterior hq v w hv hw

private theorem nonexception_multiplicity (H : Finset Plane) (R d : ℝ) (u v w : Plane)
    (hcircle : ∀ h ∈ H, ‖h‖ = R) (h0H : (0 : Plane) ∉ H)
    (huH : u ∉ H) (hvH : v ∉ H) (hwH : w ∉ H)
    (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hw0 : w ≠ 0)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hnv : ‖v‖ = ‖u‖) (hnw : ‖w‖ = ‖u‖)
    (heuw : dist u w = dist u v) (hevw : dist v w = dist u v)
    (hdR : d ≠ R) (hdu : d ≠ ‖u‖) (hduv : d ≠ dist u v)
    (hfu : (H.filter fun h => dist u h = d).card = 2)
    (hfv : (H.filter fun h => dist v h = d).card = 2)
    (hfw : (H.filter fun h => dist w h = d).card = 2) :
    multiplicity (insert (0 : Plane) (insert u (insert v (insert w H)))) d =
      multiplicity H d + 6 := by
  classical
  have hvinsert : v ∉ insert w H := by simp [hvH, hvw]
  have huinsert : u ∉ insert v (insert w H) := by simp [huH, huv, huw]
  have h0insert : (0 : Plane) ∉ insert u (insert v (insert w H)) := by
    simp [h0H, Ne.symm hu0, Ne.symm hv0, Ne.symm hw0]
  have hf0 : (H.filter fun y => dist (0 : Plane) y = d) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro y hy hdy
    have hRd : R = d := by simpa only [dist_zero_left, hcircle y hy] using hdy
    exact hdR hRd.symm
  rw [ThreeInteriorCenter.multiplicity_insert _ _ _ h0insert,
    ThreeInteriorCenter.multiplicity_insert _ _ _ huinsert,
    ThreeInteriorCenter.multiplicity_insert _ _ _ hvinsert,
    ThreeInteriorCenter.multiplicity_insert _ _ _ hwH,
    ThreeInteriorCenter.card_radial_filter_insert _ _ _ _ hwH,
    ThreeInteriorCenter.card_radial_filter_insert _ _ _ _ hvinsert,
    ThreeInteriorCenter.card_radial_filter_insert _ _ _ _ hwH,
    ThreeInteriorCenter.card_radial_filter_insert _ _ _ _ huinsert,
    ThreeInteriorCenter.card_radial_filter_insert _ _ _ _ hvinsert,
    ThreeInteriorCenter.card_radial_filter_insert _ _ _ _ hwH]
  have hf0norm : (H.filter fun y => ‖y‖ = d) = ∅ := by
    simpa only [dist_zero_left] using hf0
  simp [hfu, hfv, hfw, hf0norm, hnv, hnw, heuw, hevw, Ne.symm hdu, Ne.symm hduv]

private theorem radial_square_sum (H : Finset Plane) (R : ℝ) (u : Plane)
    (hc : ∀ h ∈ H, ‖h‖ = R) (g : Stabilizer H) (hg : g.val ≠ 1) :
    ∑ h ∈ H, dist u h ^ 2 = H.card * (R ^ 2 + ‖u‖ ^ 2) := by
  classical
  let Z : ℂ := ∑ h ∈ H, encode h
  have hperm := (mem_stabilizer_iff_image H g.val).mp g.property
  have hsum : ∑ h ∈ H, encode (rotate g.val h) = Z := by
    rw [← Finset.sum_image (rotate_isometry g.val).injective.injOn, hperm]
  have hfix : (g.val : ℂ) * Z = Z := by
    simpa only [Z, Finset.mul_sum, encode_rotate] using hsum
  have hZ : Z = 0 := by
    have hgC : (g.val : ℂ) - 1 ≠ 0 := by
      intro he
      exact hg (Circle.ext (sub_eq_zero.mp he))
    have hmul : ((g.val : ℂ) - 1) * Z = 0 := by
      rw [sub_mul, hfix, one_mul, sub_self]
    exact (mul_eq_zero.mp hmul).resolve_left hgC
  have hs0 : ∑ h ∈ H, h 0 = 0 := by
    have he := congrArg Complex.re hZ
    simpa only [Z, Complex.re_sum, encode, Complex.zero_re] using he
  have hs1 : ∑ h ∈ H, h 1 = 0 := by
    have he := congrArg Complex.im hZ
    simpa only [Z, Complex.im_sum, encode, Complex.zero_im] using he
  have hpoint : ∀ h ∈ H, dist u h ^ 2 =
      R ^ 2 + ‖u‖ ^ 2 - 2 * (u 0 * h 0 + u 1 * h 1) := by
    intro h hh
    have hn := EuclideanSpace.real_norm_sq_eq h
    have hu := EuclideanSpace.real_norm_sq_eq u
    have hd := EuclideanSpace.real_norm_sq_eq (u - h)
    rw [hc h hh] at hn
    simp only [Fin.sum_univ_two, PiLp.sub_apply] at hn hu hd
    rw [dist_eq_norm]
    nlinarith only [hn, hu, hd]
  calc
    _ = ∑ h ∈ H, (R ^ 2 + ‖u‖ ^ 2 - 2 * (u 0 * h 0 + u 1 * h 1)) :=
      Finset.sum_congr rfl hpoint
    _ = H.card * (R ^ 2 + ‖u‖ ^ 2) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        hs0, hs1, mul_zero, add_zero, sub_zero, Finset.sum_const, nsmul_eq_mul]
      ring

private theorem order_three_support_structure (n : ℕ) (H I : Finset Plane) (R : ℝ)
    (hn : 10 ≤ n) (hH : H.card = n - 4) (hR : 0 < R)
    (hcircle : ∀ h ∈ H, ‖h‖ = R) (hI : I.card = 4) (hzero : (0 : Plane) ∈ I)
    (hinterior : ∀ z ∈ I, z ∈ interior (convexHull ℝ (H : Set Plane)))
    (hq : 2 * (nonDiameterDistances (H ∪ I)).card = H.card)
    (horder : order H = 3)
    (hlarge : ∀ d ∈ nonDiameterDistances (H ∪ I), n + 1 ≤ multiplicity (H ∪ I) d) :
    ∃ u v : Plane, u ∈ I.erase 0 ∧ v ∈ I.erase 0 ∧ u ≠ v ∧
      dist u v ^ 2 = 3 * ‖u‖ ^ 2 ∧
      nonDiameterDistances (H ∪ I) ⊆ {R, ‖u‖, dist u v, Real.sqrt 3 * R} := by
  classical
  have hHsix : 6 ≤ H.card := by omega
  have hHne : H.Nonempty := Finset.card_pos.mp (by omega)
  have hJcard : (I.erase 0).card = 3 := by rw [Finset.card_erase_of_mem hzero, hI]
  obtain ⟨u, v, w, huv, huw, hvw, hJ⟩ := Finset.card_eq_three.mp hJcard
  have hu : u ∈ I.erase 0 := by rw [hJ]; simp
  have hv : v ∈ I.erase 0 := by rw [hJ]; simp
  have hw : w ∈ I.erase 0 := by rw [hJ]; simp
  have hu0 := (Finset.mem_erase.mp hu).1
  have hv0 := (Finset.mem_erase.mp hv).1
  have hw0 := (Finset.mem_erase.mp hw).1
  have huI := (Finset.mem_erase.mp hu).2
  have hvI := (Finset.mem_erase.mp hv).2
  have hwI := (Finset.mem_erase.mp hw).2
  have hIeq : I = {0, u, v, w} := by
    rw [← Finset.insert_erase hzero, hJ]
  have hX : H ∪ I = insert (0 : Plane) (insert u (insert v (insert w H))) := by
    rw [hIeq]
    ext x
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  obtain ⟨gv, hgv⟩ := exists_stabilizer_map H I R hHsix hR hcircle hinterior hq u v hu hv
  obtain ⟨gw, hgw⟩ := exists_stabilizer_map H I R hHsix hR hcircle hinterior hq u w hu hw
  have hnv : ‖v‖ = ‖u‖ := by rw [← hgv, norm_rotate]
  have hnw : ‖w‖ = ‖u‖ := by rw [← hgw, norm_rotate]
  have huorb : u ∈ MulAction.orbit (Stabilizer H) u := ⟨1, by simp⟩
  have hvorb : v ∈ MulAction.orbit (Stabilizer H) u := ⟨gv, hgv⟩
  have hworb : w ∈ MulAction.orbit (Stabilizer H) u := ⟨gw, hgw⟩
  obtain ⟨heuw, hevw⟩ := equilateral_of_mem_orbit_order_eq_three H horder u u v w
    huorb hvorb hworb huv huw hvw
  have h0H := ThreeInteriorCounting.interior_not_mem_circle H R 0 hR hcircle (hinterior 0 hzero)
  have huH := ThreeInteriorCounting.interior_not_mem_circle H R u hR hcircle (hinterior u huI)
  have hvH := ThreeInteriorCounting.interior_not_mem_circle H R v hR hcircle (hinterior v hvI)
  have hwH := ThreeInteriorCounting.interior_not_mem_circle H R w hR hcircle (hinterior w hwI)
  have hsatu := radial_saturation H I R hHsix hR hcircle hinterior hq u hu
  have hsatv := radial_saturation H I R hHsix hR hcircle hinterior hq v hv
  have hsatw := radial_saturation H I R hHsix hR hcircle hinterior hq w hw
  have hdiam := FourInteriorLowerSupport.diam_union_interiors H I hinterior
  have hdiambound : Metric.diam (H : Set Plane) ≤ 2 * R := by
    apply Metric.diam_le_of_forall_dist_le (by positivity)
    intro x hx y hy
    calc
      dist x y ≤ ‖x‖ + ‖y‖ := dist_le_norm_add_norm x y
      _ = 2 * R := by rw [hcircle x hx, hcircle y hy]; ring
  have hsub : nonDiameterDistances (H ∪ I) ⊆ {R, ‖u‖, dist u v, Real.sqrt 3 * R} := by
    intro d hd
    by_cases hdR : d = R
    · simp [hdR]
    by_cases hdu : d = ‖u‖
    · simp [hdu]
    by_cases hduv : d = dist u v
    · simp [hduv]
    have hdecomp : multiplicity (H ∪ I) d = multiplicity H d + 6 := by
      rw [hX]
      exact nonexception_multiplicity H R d u v w hcircle h0H huH hvH hwH
        hu0 hv0 hw0 huv huw hvw hnv hnw heuw.symm hevw.symm hdR hdu hduv
        (hsatu.2 d hd) (hsatv.2 d hd) (hsatw.2 d hd)
    have hbound := hlarge d hd
    rw [hdecomp] at hbound
    have hcap := chord_capacity H 0 R d hR
      (by simpa only [dist_zero_right] using hcircle)
    obtain ⟨hdpos, hdlt, _⟩ :=
      (ThreeInteriorCounting.mem_nonDiameterDistances_iff_positive (H ∪ I) d).mp hd
    have hd2R : d < 2 * R := by rw [hdiam] at hdlt; exact hdlt.trans_le hdiambound
    have hdiv := order_dvd_multiplicity H hHne hR hcircle hdpos hd2R
    rw [horder] at hdiv
    have hdivN := order_dvd_card H hHne hR hcircle
    rw [horder] at hdivN
    have hsat : multiplicity H d = H.card := by omega
    have hpos : 0 < multiplicity H d := by omega
    obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
    induction e using Sym2.ind with
    | _ a b =>
      have hep := Finset.mem_filter.mp he
      obtain ⟨ha, hb, _hab⟩ := (mk_mem_pairs H a b).mp hep.1
      have habd : dist a b = d := by simpa only [pairDist_mk] using hep.2
      obtain ⟨g, hg, hg1, _hgneg⟩ := exists_stabilizer_map_of_saturated_chord
        H hR hcircle hdpos hd2R hsat ha hb habd
      have hsq := dist_rotate_sq_of_order_eq_three H horder g hg1 a
      rw [hg, habd, hcircle a ha] at hsq
      have heq : d = Real.sqrt 3 * R := by
        apply (sq_eq_sq₀ (le_of_lt hdpos) (by positivity)).mp
        rw [mul_pow, Real.sq_sqrt (by norm_num)]
        exact hsq
      simp [heq]
  have huvSq := dist_sq_of_mem_orbit_order_eq_three H horder u u v huorb hvorb huv
  exact ⟨u, v, hu, hv, huv, huvSq, hsub⟩

private theorem order_three_support_card_le (n : ℕ) (H I : Finset Plane) (R : ℝ)
    (hn : 10 ≤ n) (hH : H.card = n - 4) (hR : 0 < R)
    (hcircle : ∀ h ∈ H, ‖h‖ = R) (hI : I.card = 4) (hzero : (0 : Plane) ∈ I)
    (hinterior : ∀ z ∈ I, z ∈ interior (convexHull ℝ (H : Set Plane)))
    (hq : 2 * (nonDiameterDistances (H ∪ I)).card = H.card)
    (horder : order H = 3)
    (hlarge : ∀ d ∈ nonDiameterDistances (H ∪ I), n + 1 ≤ multiplicity (H ∪ I) d) :
    (nonDiameterDistances (H ∪ I)).card ≤ 4 := by
  classical
  obtain ⟨u, v, _hu, _hv, _huv, _huvSq, hsub⟩ :=
    order_three_support_structure n H I R hn hH hR hcircle hI hzero hinterior hq horder hlarge
  have hbound := Finset.card_le_card hsub
  have hfour : ({R, ‖u‖, dist u v, Real.sqrt 3 * R} : Finset ℝ).card ≤ 4 := by
    calc
      _ ≤ ({‖u‖, dist u v, Real.sqrt 3 * R} : Finset ℝ).card + 1 := Finset.card_insert_le _ _
      _ ≤ ({dist u v, Real.sqrt 3 * R} : Finset ℝ).card + 1 + 1 :=
        Nat.add_le_add_right (Finset.card_insert_le _ _) 1
      _ ≤ ({Real.sqrt 3 * R} : Finset ℝ).card + 1 + 1 + 1 :=
        Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_insert_le _ _) 1) 1
      _ = 4 := by simp
  exact hbound.trans hfour

private theorem order_three_contrary_ten (H I : Finset Plane) (R : ℝ)
    (hH : H.card = 6) (hR : 0 < R) (hcircle : ∀ h ∈ H, ‖h‖ = R)
    (hI : I.card = 4) (hzero : (0 : Plane) ∈ I)
    (hinterior : ∀ z ∈ I, z ∈ interior (convexHull ℝ (H : Set Plane)))
    (hq : 2 * (nonDiameterDistances (H ∪ I)).card = H.card)
    (horder : order H = 3)
    (hlarge : ∀ d ∈ nonDiameterDistances (H ∪ I), 11 ≤ multiplicity (H ∪ I) d) :
    False := by
  classical
  let S := nonDiameterDistances (H ∪ I)
  have hScard : S.card = 3 := by dsimp only [S]; omega
  obtain ⟨u, v, hu, hv, huv, hellSq, hsub⟩ := order_three_support_structure
    10 H I R (by omega) (by omega) hR hcircle hI hzero hinterior hq horder hlarge
  obtain ⟨_hcard, _hJ, ρ, hρpos, hρlt, hnorm, hmemR, hmemρ, _hsat,
      _htrans, _horder, _hdiv⟩ := centered_lower_support_geometry
    10 H I R (by omega) (by omega) hR hcircle hI hzero hinterior hq
  have hupos : 0 < ‖u‖ := by rw [hnorm u hu]; exact hρpos
  have hult : ‖u‖ < R := by rw [hnorm u hu]; exact hρlt
  have hmemu : ‖u‖ ∈ S := by rw [hnorm u hu]; exact hmemρ
  have hmemell : dist u v ∈ S := by
    apply (ThreeInteriorCounting.mem_nonDiameterDistances_iff_positive (H ∪ I) _).mpr
    refine ⟨dist_pos.mpr huv, ?_, u, Finset.mem_union_right H (Finset.mem_erase.mp hu).2,
      v, Finset.mem_union_right H (Finset.mem_erase.mp hv).2, rfl⟩
    rw [FourInteriorLowerSupport.diam_union_interiors H I hinterior]
    exact dist_lt_diam_hull H (by omega) (hinterior u (Finset.mem_erase.mp hu).2)
      (interior_subset (hinterior v (Finset.mem_erase.mp hv).2))
  obtain ⟨g, hg⟩ := exists_stabilizer_map H I R (by omega) hR hcircle hinterior hq u v hu hv
  have hg1 : g.val ≠ 1 := by
    intro he
    rw [he, rotate_one] at hg
    exact huv hg
  have hsat := radial_saturation H I R (by omega) hR hcircle hinterior hq u hu
  have hmap : ∀ h ∈ H, dist u h ∈ S := by
    intro h hh
    change dist u h ∈ nonDiameterDistances (H ∪ I)
    rw [← hsat.1]
    exact Finset.mem_image.mpr ⟨h, hh, rfl⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to hmap (fun h => dist u h ^ 2)
  have hsum : ∑ h ∈ H, dist u h ^ 2 = 2 * ∑ d ∈ S, d ^ 2 := by
    rw [← hfiber, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    calc
      _ = ∑ _h ∈ H.filter (fun h => dist u h = d), d ^ 2 := by
        apply Finset.sum_congr rfl
        intro h hh
        rw [(Finset.mem_filter.mp hh).2]
      _ = 2 * d ^ 2 := by simp [hsat.2 d hd, nsmul_eq_mul]
  have hmoment : ∑ d ∈ S, d ^ 2 = 3 * (R ^ 2 + ‖u‖ ^ 2) := by
    have hm := radial_square_sum H R u hcircle g hg1
    rw [hH, hsum] at hm
    norm_num only [Nat.cast_ofNat] at hm
    linarith
  have hρR : ‖u‖ ≠ R := ne_of_lt hult
  have hRρ : R ≠ ‖u‖ := hρR.symm
  have hellρ : dist u v ≠ ‖u‖ := by
    intro he
    rw [he] at hellSq
    nlinarith [sq_pos_of_pos hupos]
  by_cases hellR : dist u v = R
  · have hTsub : S ⊆ {R, ‖u‖, Real.sqrt 3 * R} := by
      simpa [S, hellR, Finset.insert_comm] using hsub
    have hTcard : ({R, ‖u‖, Real.sqrt 3 * R} : Finset ℝ).card ≤ 3 := by
      calc
        _ ≤ ({‖u‖, Real.sqrt 3 * R} : Finset ℝ).card + 1 := Finset.card_insert_le _ _
        _ ≤ ({Real.sqrt 3 * R} : Finset ℝ).card + 1 + 1 :=
          Nat.add_le_add_right (Finset.card_insert_le _ _) 1
        _ = 3 := by simp
    have hSeq : S = {R, ‖u‖, Real.sqrt 3 * R} :=
      Finset.eq_of_subset_of_card_le hTsub (by omega)
    have hsqrtSq : (Real.sqrt 3 * R) ^ 2 = 3 * R ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num)]
    have hRL : R ≠ Real.sqrt 3 * R := by
      intro he
      rw [← he] at hsqrtSq
      nlinarith [sq_pos_of_pos hR]
    have hρL : ‖u‖ ≠ Real.sqrt 3 * R := by
      intro he
      rw [← he] at hsqrtSq
      nlinarith [sq_pos_of_pos hR]
    have hnotR : R ∉ ({‖u‖, Real.sqrt 3 * R} : Finset ℝ) := by simp [hRρ, hRL]
    have hnotρ : ‖u‖ ∉ ({Real.sqrt 3 * R} : Finset ℝ) := by simp [hρL]
    rw [hSeq, Finset.sum_insert hnotR, Finset.sum_insert hnotρ,
      Finset.sum_singleton, hsqrtSq] at hmoment
    rw [hellR] at hellSq
    nlinarith [sq_pos_of_pos hR]
  · have hTsub : ({R, ‖u‖, dist u v} : Finset ℝ) ⊆ S := by
      intro d hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with rfl | rfl | rfl
      · exact hmemR
      · exact hmemu
      · exact hmemell
    have hTcard : ({R, ‖u‖, dist u v} : Finset ℝ).card = 3 := by
      simp [hRρ, Ne.symm hellR, Ne.symm hellρ]
    have hSeq : S = {R, ‖u‖, dist u v} :=
      (Finset.eq_of_subset_of_card_le hTsub (by omega)).symm
    have hnotR : R ∉ ({‖u‖, dist u v} : Finset ℝ) := by
      simp [hRρ, Ne.symm hellR]
    have hnotρ : ‖u‖ ∉ ({dist u v} : Finset ℝ) := by simp [Ne.symm hellρ]
    rw [hSeq, Finset.sum_insert hnotR, Finset.sum_insert hnotρ,
      Finset.sum_singleton] at hmoment
    have husq : ‖u‖ ^ 2 < R ^ 2 := (sq_lt_sq₀ hupos.le hR.le).mpr hult
    nlinarith [sq_pos_of_pos hR]

/-- From exactly the original even centered lower-support premises, the actual
union has cardinality `n`, and either the requested small-multiplicity distance
exists, or its negation yields FAILURE and one of two remaining geometric cases:
the order-three case at `n = 10`, or one full hull orbit. The two exclusions are
not asserted here; this is the connected partial consumer for their completion. -/
theorem original_lower_support_reduction (n : ℕ) (heven : Even n) (hn : 10 ≤ n)
    (H I : Finset Plane) (hH : H.card = n - 4) (R : ℝ) (hR : 0 < R)
    (hcircle : ∀ h ∈ H, ‖h‖ = R) (hI : I.card = 4) (hzero : (0 : Plane) ∈ I)
    (hinterior : ∀ z ∈ I, z ∈ interior (convexHull ℝ (H : Set Plane)))
    (hq : 2 * (nonDiameterDistances (H ∪ I)).card = H.card) :
    (H ∪ I).card = n ∧
      ((∃ d : ℝ, 0 < d ∧ d < Metric.diam ((H ∪ I : Finset Plane) : Set Plane) ∧
          1 ≤ multiplicity (H ∪ I) d ∧ multiplicity (H ∪ I) d ≤ n) ∨
        ((∀ d ∈ nonDiameterDistances (H ∪ I), n + 1 ≤ multiplicity (H ∪ I) d) ∧
          ((n = 10 ∧ order H = 3) ∨
            (order H = H.card ∧ ∀ p ∈ H, ∀ h : Plane,
              h ∈ H ↔ ∃ g : Stabilizer H, rotate g.val p = h)))) := by
  classical
  obtain ⟨hcard, _hJ, ρ, _hρpos, _hρlt, _hnorm, _hmemR, _hmemρ,
    _hsat, _htransport, hthree, hdiv⟩ :=
    centered_lower_support_geometry n H I R hn hH hR hcircle hI hzero hinterior hq
  refine ⟨hcard, ?_⟩
  by_cases hsmall : ∃ d : ℝ, 0 < d ∧
      d < Metric.diam ((H ∪ I : Finset Plane) : Set Plane) ∧
      1 ≤ multiplicity (H ∪ I) d ∧ multiplicity (H ∪ I) d ≤ n
  · exact Or.inl hsmall
  have hlarge : ∀ d ∈ nonDiameterDistances (H ∪ I), n + 1 ≤ multiplicity (H ∪ I) d := by
    intro d hd
    obtain ⟨hdpos, hdlt, a, ha, b, hb, habd⟩ :=
      (ThreeInteriorCounting.mem_nonDiameterDistances_iff_positive (H ∪ I) d).mp hd
    have hab : a ≠ b := by
      intro heq
      rw [heq, dist_self] at habd
      linarith
    have hmult : 1 ≤ multiplicity (H ∪ I) d := by
      apply Finset.card_pos.mpr
      refine ⟨s(a,b), Finset.mem_filter.mpr ⟨(mk_mem_pairs _ _ _).mpr ⟨ha, hb, hab⟩, ?_⟩⟩
      simpa only [pairDist_mk] using habd
    by_contra hnot
    have hle : multiplicity (H ∪ I) d ≤ n := by omega
    exact hsmall ⟨d, hdpos, hdlt, hmult, hle⟩
  refine Or.inr ⟨hlarge, ?_⟩
  by_cases horder : order H = 3
  · have hqfour := order_three_support_card_le n H I R hn hH hR hcircle hI hzero
      hinterior hq horder hlarge
    have hthreeDvd : 3 ∣ H.card := horder ▸ hdiv
    obtain ⟨k, hk⟩ := heven
    have hnTen : n = 10 := by omega
    exact Or.inl ⟨hnTen, horder⟩
  · have hfour : 4 ≤ order H := by omega
    exact Or.inr (full_orbit_of_four_le_order H I R (by omega) hR hcircle hfour hq)

/-- Exactly the original even centered lower-support premises give actual union
cardinality `n` and either the requested small-multiplicity distance or FAILURE
on a single full hull orbit. The order-three residual has been excluded by the
actual radial squared-distance sum; no regularity certificate is a premise. -/
theorem original_lower_support_regular_reduction (n : ℕ) (heven : Even n) (hn : 10 ≤ n)
    (H I : Finset Plane) (hH : H.card = n - 4) (R : ℝ) (hR : 0 < R)
    (hcircle : ∀ h ∈ H, ‖h‖ = R) (hI : I.card = 4) (hzero : (0 : Plane) ∈ I)
    (hinterior : ∀ z ∈ I, z ∈ interior (convexHull ℝ (H : Set Plane)))
    (hq : 2 * (nonDiameterDistances (H ∪ I)).card = H.card) :
    (H ∪ I).card = n ∧
      ((∃ d : ℝ, 0 < d ∧ d < Metric.diam ((H ∪ I : Finset Plane) : Set Plane) ∧
          1 ≤ multiplicity (H ∪ I) d ∧ multiplicity (H ∪ I) d ≤ n) ∨
        ((∀ d ∈ nonDiameterDistances (H ∪ I), n + 1 ≤ multiplicity (H ∪ I) d) ∧
          order H = H.card ∧ ∀ p ∈ H, ∀ h : Plane,
            h ∈ H ↔ ∃ g : Stabilizer H, rotate g.val p = h)) := by
  obtain ⟨hcard, hcases⟩ := original_lower_support_reduction n heven hn H I hH R hR
    hcircle hI hzero hinterior hq
  refine ⟨hcard, ?_⟩
  rcases hcases with hsmall | ⟨hlarge, hthree | hfull⟩
  · exact Or.inl hsmall
  · obtain ⟨hnTen, horder⟩ := hthree
    have hHsix : H.card = 6 := by omega
    have hlargeTen : ∀ d ∈ nonDiameterDistances (H ∪ I),
        11 ≤ multiplicity (H ∪ I) d := by simpa only [hnTen] using hlarge
    exact False.elim (order_three_contrary_ten H I R hHsix hR hcircle hI hzero
      hinterior hq horder hlargeTen)
  · exact Or.inr ⟨hlarge, hfull⟩

private theorem actual_regular_enumeration (H : Finset Plane) (R : ℝ) (N : ℕ)
    (hN : N ≠ 0) (hH : H.Nonempty) (hR : 0 < R)
    (hcircle : ∀ x ∈ H, ‖x‖ = R) (horder : order H = N)
    (htrans : ∀ a ∈ H, ∀ b ∈ H, ∃ g : Stabilizer H, rotate g.val a = b)
    (a : Plane) (ha : a ∈ H) :
    H = (Finset.range N).image
      (fun i : ℕ => rotate (Circle.exp (2 * Real.pi * i / N)) a) := by
  classical
  letI := finite_stabilizer H hH hR hcircle
  letI := Fintype.ofFinite (Stabilizer H)
  letI : NeZero N := ⟨hN⟩
  let q : Circle := Circle.exp (2 * Real.pi / N)
  have hprim : IsPrimitiveRoot (q : ℂ) N := by
    have he : (q : ℂ) = Complex.exp (2 * Real.pi * Complex.I / N) := by
      dsimp only [q]
      rw [Circle.coe_exp]
      congr 1
      push_cast
      ring
    rw [he]
    exact Complex.isPrimitiveRoot_exp N hN
  let C : Finset ℂ := Finset.univ.image (fun g : Stabilizer H => (g.val : ℂ))
  let B : Finset ℂ := (Finset.range N).image (fun i => (q : ℂ)^i)
  have hCcard : C.card = N := by
    rw [Finset.card_image_of_injective]
    · simpa only [Finset.card_univ,order,Nat.card_eq_fintype_card] using horder
    · intro g l hgl
      exact Subtype.ext (Circle.ext hgl)
  have hCB : C ⊆ B := by
    intro c hc
    obtain ⟨g,_,rfl⟩ := Finset.mem_image.mp hc
    have hgpow : (g.val : ℂ)^N = 1 := by
      have hp := pow_card_eq_one' (x := g)
      change g ^ order H = 1 at hp
      rw [horder] at hp
      simpa only [Subgroup.coe_pow,Subgroup.coe_one,Circle.coe_pow,Circle.coe_one] using
        congrArg (fun g : Stabilizer H => (g.val : ℂ)) hp
    obtain ⟨i,hi,hqi⟩ := hprim.eq_pow_of_pow_eq_one hgpow
    exact Finset.mem_image.mpr ⟨i,Finset.mem_range.mpr hi,hqi⟩
  have hBC : B = C := by
    apply Eq.symm
    apply Finset.eq_of_subset_of_card_le hCB
    rw [hCcard]
    exact (Finset.card_image_le).trans_eq (Finset.card_range N)
  have hqp (i : ℕ) : q ^ i = Circle.exp (2 * Real.pi * i / N) := by
    apply Circle.ext
    simp only [Circle.coe_pow,Circle.coe_exp,q]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  ext b
  constructor
  · intro hb
    obtain ⟨g,hgab⟩ := htrans a ha b hb
    have hc : (g.val : ℂ) ∈ C := Finset.mem_image.mpr ⟨g,Finset.mem_univ g,rfl⟩
    obtain ⟨i,hi,hqi⟩ := Finset.mem_image.mp (hCB hc)
    have hqg : q^i = g.val := Circle.ext (by simpa only [Circle.coe_pow] using hqi)
    refine Finset.mem_image.mpr ⟨i,hi,?_⟩
    rw [← hqp,hqg]
    exact hgab
  · intro hb
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hb
    have hc : (q : ℂ)^i ∈ C := by
      rw [← hBC]
      exact Finset.mem_image.mpr ⟨i,hi,rfl⟩
    obtain ⟨g,_,hgi⟩ := Finset.mem_image.mp hc
    have hqg : q^i = g.val := Circle.ext (by simpa only [Circle.coe_pow] using hgi.symm)
    rw [← hqp,hqg]
    exact (g.property a).mpr ha


private theorem regular_chord_sq (a : Plane) (R θ : ℝ) (ha : ‖a‖ = R) :
    dist a (rotate (Circle.exp (2 * θ)) a) ^ 2 = (2 * R * Real.sin θ) ^ 2 := by
  have hn := EuclideanSpace.real_norm_sq_eq a
  have hd := EuclideanSpace.real_norm_sq_eq (a - rotate (Circle.exp (2 * θ)) a)
  simp only [Fin.sum_univ_two, PiLp.sub_apply] at hn hd
  rw [ha] at hn
  have hc : ((Circle.exp (2 * θ) : Circle) : ℂ).re = Real.cos (2 * θ) := by
    rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_re]
  have hs : ((Circle.exp (2 * θ) : Circle) : ℂ).im = Real.sin (2 * θ) := by
    rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_im]
  rw [dist_eq_norm, hd]
  change (a 0 - ((Circle.exp (2*θ) : ℂ).re * a 0 - (Circle.exp (2*θ) : ℂ).im * a 1))^2 +
    (a 1 - ((Circle.exp (2*θ) : ℂ).im * a 0 + (Circle.exp (2*θ) : ℂ).re * a 1))^2 = _
  rw [hc, hs]
  calc
    _ = (a 0 ^ 2 + a 1 ^ 2) * (1 + (Real.sin (2*θ)^2 + Real.cos (2*θ)^2) - 2*Real.cos (2*θ)) := by ring
    _ = R ^ 2 * (2 - 2 * Real.cos (2*θ)) := by rw [← hn, Real.sin_sq_add_cos_sq]; ring
    _ = (2 * R * Real.sin θ)^2 := by rw [Real.cos_two_mul]; nlinarith [Real.sin_sq_add_cos_sq θ]

private theorem regular_double_fiber (H : Finset Plane) (R : ℝ) (hR : 0 < R)
    (hcirc : ∀ a ∈ H, ‖a‖ = R) (a : Plane) (ha : a ∈ H)
    (g : Stabilizer H) (θ : ℝ) (hθ0 : 0 < θ) (hθπ : θ < Real.pi)
    (hg : g.val = Circle.exp θ) :
    (H.filter fun b => dist a b = dist a (rotate g.val a)).card = 2 := by
  classical
  have ha0 : a ≠ 0 := by
    intro he
    have hr := hcirc a ha
    rw [he, norm_zero] at hr
    linarith
  let b := rotate g.val a
  let c := rotate g.val⁻¹ a
  have hb : b ∈ H := (g.property a).mpr ha
  have hc : c ∈ H := (g⁻¹).property a |>.mpr ha
  have hdc : dist a c = dist a b := by
    have hi := (rotate_isometry g.val).dist_eq a c
    have hgc : rotate g.val c = a := by simp [c, ← rotate_mul]
    rw [hgc] at hi
    exact hi.symm.trans (dist_comm b a)
  have hbc : b ≠ c := by
    intro he
    have hec := rotate_coeff_injective a ha0 he
    have him := congrArg (fun z : Circle => (z : ℂ).im) hec
    rw [hg, Circle.coe_inv_eq_conj, Complex.conj_im, Circle.coe_exp,
      Complex.exp_ofReal_mul_I_im] at him
    have hs := Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ
    linarith
  have hsub : ({b,c} : Finset Plane) ⊆ H.filter (fun b => dist a b = dist a (rotate g.val a)) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨hb,rfl⟩
    · exact Finset.mem_filter.mpr ⟨hc,hdc⟩
  have hlower := Finset.card_le_card hsub
  have htwo : ({b,c} : Finset Plane).card = 2 := by simp [hbc]
  have hupper := radial_card_le_two H 0 a R (dist a (rotate g.val a))
    (by simpa only [dist_zero_right] using hcirc) ha0
  have hupper' : (H.filter fun b => dist a b = dist a (rotate g.val a)).card ≤ 2 := by
    simpa only [dist_comm] using hupper
  omega

private theorem chord_angle_bounds (k j : ℕ) (hk : 3 ≤ k)
    (hj : j ∈ Finset.Icc 1 (k - 1)) :
    0 < Real.pi * j / (2 * k) ∧ Real.pi * j / (2 * k) < Real.pi / 2 := by
  have hjn := Finset.mem_Icc.mp hj
  have hjk : j < k := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hjR : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hjkR : (j : ℝ) < k := by exact_mod_cast hjk
  constructor
  · positivity
  · apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * k)).mpr
    nlinarith [mul_lt_mul_of_pos_left hjkR Real.pi_pos]

private theorem regular_chord_data (H I : Finset Plane) (R : ℝ) (k : ℕ)
    (hk : 3 ≤ k) (hcard : H.card = 2 * k) (hR : 0 < R)
    (hcircle : ∀ h ∈ H, ‖h‖ = R) (horder : order H = H.card)
    (htrans : ∀ a ∈ H, ∀ b ∈ H, ∃ g : Stabilizer H, rotate g.val a = b) :
    ∃ a ∈ H, let C : Finset ℝ := ((Finset.Icc 1 (k - 1)).image
        (fun j : ℕ => 2 * R * Real.sin (Real.pi * j / (2 * k))))
      C.card = k - 1 ∧ C ⊆ nonDiameterDistances (H ∪ I) ∧
      (∀ d ∈ C, (H.filter fun h => dist a h = d).card = 2) ∧
      2 * R ≤ Metric.diam ((H ∪ I : Finset Plane) : Set Plane) ∧
      (∑ d ∈ C, d ^ 2) ≤ ((2 * k : ℕ) : ℝ) * R ^ 2 - 2 * R ^ 2 := by
  classical
  have hHne : H.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, ha⟩ := hHne
  have ha0 : a ≠ 0 := by
    intro he
    have hr := hcircle a ha
    rw [he, norm_zero] at hr
    linarith
  have henum := actual_regular_enumeration H R (2*k) (by omega) (show H.Nonempty from ⟨a,ha⟩) hR hcircle
    (horder.trans hcard) htrans a ha
  let f := fun j : ℕ => 2 * R * Real.sin (Real.pi * j / (2 * k))
  let J := Finset.Icc 1 (k - 1)
  let C := J.image f
  have hrot (j : ℕ) (hj : j < 2*k) : rotate (Circle.exp (2 * (Real.pi * j / (2*k)))) a ∈ H := by
    rw [henum]
    apply Finset.mem_image.mpr
    refine ⟨j, Finset.mem_range.mpr hj, ?_⟩
    congr 2
    push_cast
    ring
  have hd (j : ℕ) (hjn : 0 ≤ Real.pi * j / (2*k))
      (hjπ : Real.pi * j / (2*k) ≤ Real.pi) :
      dist a (rotate (Circle.exp (2 * (Real.pi * j / (2*k)))) a) = f j := by
    have hs : 0 ≤ f j := by
      dsimp [f]
      exact mul_nonneg (by positivity) (Real.sin_nonneg_of_nonneg_of_le_pi hjn hjπ)
    apply (sq_eq_sq₀ dist_nonneg hs).mp
    exact regular_chord_sq a R _ (hcircle a ha)
  have hanti : rotate (Circle.exp (2 * (Real.pi * k / (2*k)))) a ∈ H := hrot k (by omega)
  have hhalf : Real.pi * (k : ℝ) / (2 * k) = Real.pi / 2 := by
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    field_simp
  have hantiDist : dist a (rotate (Circle.exp (2 * (Real.pi * k / (2*k)))) a) = 2*R := by
    rw [hd k (by rw [hhalf]; positivity) (by rw [hhalf]; linarith [Real.pi_pos])]
    dsimp [f]
    rw [hhalf, Real.sin_pi_div_two, mul_one]
  have hdiam : 2*R ≤ Metric.diam ((H ∪ I : Finset Plane) : Set Plane) := by
    rw [← hantiDist]
    exact Metric.dist_le_diam_of_mem (H ∪ I).finite_toSet.isBounded (Finset.mem_union_left I ha)
      (Finset.mem_union_left I hanti)
  have hinj : Set.InjOn f J := by
    intro i hi j hj hij
    have hiB := chord_angle_bounds k i hk hi
    have hjB := chord_angle_bounds k j hk hj
    have he : Real.sin (Real.pi * i / (2*k)) = Real.sin (Real.pi * j / (2*k)) := by
      dsimp [f] at hij
      nlinarith
    have hae := Real.strictMonoOn_sin.injOn
      (show Real.pi * i / (2*k) ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by constructor <;> linarith [Real.pi_pos])
      (show Real.pi * j / (2*k) ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by constructor <;> linarith [Real.pi_pos]) he
    have hijR : (i : ℝ) = j := by
      have hk0 : (2 * (k : ℝ)) ≠ 0 := by positivity
      have he' := (div_left_inj' hk0).mp hae
      nlinarith [Real.pi_pos]
    exact_mod_cast hijR
  have hCcard : C.card = k - 1 := by
    rw [Finset.card_image_of_injOn hinj]
    simp [J, Nat.card_Icc]
  have hCbound : ∀ d ∈ C, 0 < d ∧ d < 2*R := by
    intro d hdC
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hdC
    have hB := chord_angle_bounds k j hk hj
    have hspos := Real.sin_pos_of_pos_of_lt_pi hB.1 (by linarith [Real.pi_pos])
    have hslt := Real.strictMonoOn_sin
      (show Real.pi * j / (2*k) ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by constructor <;> linarith [Real.pi_pos])
      (show Real.pi/2 ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by constructor <;> linarith [Real.pi_pos]) hB.2
    rw [Real.sin_pi_div_two] at hslt
    dsimp [f]
    constructor
    · positivity
    · nlinarith
  have hCsub : C ⊆ nonDiameterDistances (H ∪ I) := by
    intro d hdC
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hdC
    have hB := chord_angle_bounds k j hk hj
    have hjn := Finset.mem_Icc.mp hj
    have hb := hrot j (by omega)
    have hdist := hd j hB.1.le (by linarith [Real.pi_pos])
    have hpos := (hCbound (f j) (Finset.mem_image.mpr ⟨j,hj,rfl⟩)).1
    apply (ThreeInteriorCounting.mem_nonDiameterDistances_iff_positive _ _).mpr
    exact ⟨hpos, (hCbound _ (Finset.mem_image.mpr ⟨j,hj,rfl⟩)).2.trans_le hdiam,
      a, Finset.mem_union_left I ha, _, Finset.mem_union_left I hb, hdist⟩
  have hfiber : ∀ d ∈ C, (H.filter fun h => dist a h = d).card = 2 := by
    intro d hdC
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hdC
    have hB := chord_angle_bounds k j hk hj
    have hjn := Finset.mem_Icc.mp hj
    obtain ⟨g,hg⟩ := htrans a ha _ (hrot j (by omega))
    have hgval : g.val = Circle.exp (2 * (Real.pi * j / (2*k))) := rotate_coeff_injective a ha0 hg
    have hfib := regular_double_fiber H R hR hcircle a ha g _
      (by linarith) (by linarith) hgval
    rw [hg, hd j hB.1.le (by linarith [Real.pi_pos])] at hfib
    exact hfib
  refine ⟨a, ha, hCcard, hCsub, hfiber, hdiam, ?_⟩
  let T := H.image (fun h => dist a h)
  have hDsub : insert (2*R) C ⊆ T := by
    intro d hdD
    rcases Finset.mem_insert.mp hdD with rfl | hdC
    · exact Finset.mem_image.mpr ⟨_, hanti, hantiDist⟩
    · have hpos : 0 < (H.filter fun h => dist a h = d).card := by rw [hfiber d hdC]; decide
      obtain ⟨b,hb⟩ := Finset.card_pos.mp hpos
      exact Finset.mem_image.mpr ⟨b, (Finset.mem_filter.mp hb).1, (Finset.mem_filter.mp hb).2⟩
  have hsum : (∑ d ∈ T, d^2 * ((H.filter fun h => dist a h = d).card : ℝ)) =
      ∑ h ∈ H, dist a h^2 := by
    have hmap : ∀ h ∈ H, dist a h ∈ T := by
      intro h hh
      exact Finset.mem_image.mpr ⟨h,hh,rfl⟩
    rw [← Finset.sum_fiberwise_of_maps_to hmap (fun h => dist a h^2)]
    apply Finset.sum_congr rfl
    intro d hdT
    rw [show (∑ h ∈ H.filter (fun h => dist a h = d), dist a h^2) =
      ∑ _h ∈ H.filter (fun h => dist a h = d), d^2 by
        apply Finset.sum_congr rfl
        intro h hh
        rw [(Finset.mem_filter.mp hh).2]]
    simp [nsmul_eq_mul, mul_comm]
  have hantiCount : 1 ≤ (H.filter fun h => dist a h = 2*R).card :=
    Finset.card_pos.mpr ⟨_, Finset.mem_filter.mpr ⟨hanti,hantiDist⟩⟩
  have hnot : 2*R ∉ C := by
    intro he
    exact (hCbound _ he).2.false
  have hsmallSum : (∑ d ∈ insert (2*R) C, d^2 * ((H.filter fun h => dist a h = d).card : ℝ)) ≤
      ∑ d ∈ T, d^2 * ((H.filter fun h => dist a h = d).card : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hDsub
      (fun d _hd _hnot => mul_nonneg (sq_nonneg d) (Nat.cast_nonneg _))
  have hCsum : (∑ d ∈ C, d^2 * ((H.filter fun h => dist a h = d).card : ℝ)) =
      2 * ∑ d ∈ C, d^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hdC
    simp [hfiber d hdC, mul_comm]
  rw [Finset.sum_insert hnot, hCsum, hsum] at hsmallSum
  have hjOne : 1 ∈ J := by dsimp [J]; simp only [Finset.mem_Icc]; omega
  have hB := chord_angle_bounds k 1 hk hjOne
  obtain ⟨g,hg⟩ := htrans a ha _ (hrot 1 (by omega))
  have hg1 : g.val ≠ 1 := by
    intro he
    rw [he, rotate_one] at hg
    have hdist := hd 1 hB.1.le (by linarith [Real.pi_pos])
    rw [← hg, dist_self] at hdist
    have hpos := (hCbound _ (Finset.mem_image.mpr ⟨1,hjOne,rfl⟩)).1
    linarith
  have hmoment := radial_square_sum H R a hcircle g hg1
  rw [hcircle a ha, hcard] at hmoment
  have hantiCountR : (1 : ℝ) ≤ (H.filter fun h => dist a h = 2*R).card := by exact_mod_cast hantiCount
  have hantiBound := mul_le_mul_of_nonneg_left hantiCountR (sq_nonneg (2*R))
  nlinarith
private theorem radius_chord_exclusion (k j : ℕ) (r : ℝ) (hk : 3 ≤ k)
    (hj : j ∈ Finset.Icc 1 (k-1)) (hr : r < 1)
    (he : r = 2 * Real.sin (Real.pi * j / (2*k)))
    (hl : 2 * Real.cos (Real.pi / (2*k)) - 1 ≤ r) : False := by
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hjN := Finset.mem_Icc.mp hj
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hjN.1
  have hjk : j < k := by omega
  have hjkR : (j : ℝ) < k := by exact_mod_cast hjk
  let x := Real.pi / (2*k)
  let θ := Real.pi * j / (2*k)
  have hx : 0 < x := by dsimp [x]; positivity
  have hxBound : x ≤ Real.pi/6 := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2*k) (by norm_num : (0:ℝ)<6)).mpr
    nlinarith [Real.pi_pos]
  have hθ : 0 < θ ∧ θ < Real.pi/2 := by
    dsimp [θ]
    constructor
    · positivity
    · apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2*k)).mpr
      nlinarith [mul_lt_mul_of_pos_left hjkR Real.pi_pos]
  have hθSmall : θ < Real.pi / 6 := by
    by_contra hn
    have hs := Real.strictMonoOn_sin.monotoneOn
      (show Real.pi/6 ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by constructor <;> linarith [Real.pi_pos])
      (show θ ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by constructor <;> linarith [Real.pi_pos]) (le_of_not_gt hn)
    rw [Real.sin_pi_div_six] at hs
    nlinarith
  have h3j : 3*j < k := by
    have hR : (3*(j : ℝ)) < k := by
      have hh := (div_lt_iff₀ (by positivity : (0:ℝ) < 2*k)).mp hθSmall
      nlinarith [Real.pi_pos]
    exact_mod_cast hR
  have hgap : (3*(j : ℝ)) + 1 ≤ k := by exact_mod_cast (show 3*j+1 ≤ k by omega)
  have hθgap : θ ≤ Real.pi/6 - x/3 := by
    dsimp [θ,x]
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 2*k)).mpr
    have hm := mul_le_mul_of_nonneg_left hgap Real.pi_pos.le
    field_simp
    nlinarith
  let t := x/3
  have ht : 0 < t := by dsimp [t]; positivity
  have htSmall : t < 11/60 := by
    dsimp [t]
    linarith [Real.pi_lt_d2]
  have htsq : t^2 < 1/25 := by nlinarith
  have hsin : 99/100*t ≤ Real.sin t := by
    have hs := Real.sin_ge_sub_cube ht.le
    have hmul := mul_lt_mul_of_pos_right htsq ht
    nlinarith
  have hroot : (5/3 : ℝ) ≤ Real.sqrt 3 := by
    have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
    have hp := Real.sqrt_nonneg (3:ℝ)
    nlinarith
  have htBound : t ≤ Real.pi/18 := by dsimp [t]; linarith
  have hscomp := Real.strictMonoOn_sin.monotoneOn
    (show θ ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by constructor <;> linarith [Real.pi_pos])
    (show Real.pi/6-t ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by constructor <;> linarith [Real.pi_pos, htBound]) hθgap
  rw [Real.sin_sub, Real.sin_pi_div_six, Real.cos_pi_div_six] at hscomp
  have hprod : (5/3:ℝ)*(99/100*t) ≤ Real.sqrt 3 * Real.sin t :=
    mul_le_mul hroot hsin (by positivity) (Real.sqrt_nonneg _)
  have hcos := Real.cos_le_one t
  have hupper : r ≤ 1 - 11/20*x := by dsimp [t] at hprod; nlinarith
  have hxSmall : x < 11/20 := by linarith [Real.pi_lt_d2]
  have hquad := Real.one_sub_sq_div_two_le_cos (x := x)
  have hmul := mul_lt_mul_of_pos_right hxSmall hx
  nlinarith

private theorem radius_moment_exclusion (k : ℕ) (r : ℝ) (hk : 3 ≤ k)
    (hr : 0 ≤ r) (hl : 2 * Real.cos (Real.pi / (2*k)) - 1 ≤ r)
    (hm : ((k : ℝ)-1)*r^2 ≤ k-2) : False := by
  by_cases hk3 : k = 3
  · subst k
    norm_num at hl hm
    have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
    have hp := Real.sqrt_nonneg (3:ℝ)
    have hroot : 1 < Real.sqrt 3 := by nlinarith
    have hrootUpper : Real.sqrt 3 < 7/4 := by nlinarith
    have hsq : (Real.sqrt 3 - 1)^2 ≤ r^2 := by
      apply (sq_le_sq₀ (by linarith) hr).mpr
      nlinarith
    nlinarith
  have hk4 : 4 ≤ k := by omega
  have hkR : (4:ℝ) ≤ k := by exact_mod_cast hk4
  have hk0 : (0:ℝ) < k := by linarith
  let x := Real.pi / (2*k)
  have hx : 0 < x := by dsimp [x]; positivity
  have hpi : Real.pi^2 < 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hpoly : 10*((k:ℝ)-1) < 2*(k:ℝ)^2 := by
    have hp := mul_nonneg (show 0 ≤ (k:ℝ)-4 by linarith)
      (show 0 ≤ (k:ℝ)-1 by linarith)
    nlinarith
  have hxEq : x^2*(4*(k:ℝ)^2) = Real.pi^2 := by
    dsimp [x]
    field_simp
    ring
  have hquad : ((k:ℝ)-1)*x^2 < 1/2 := by
    have hp := mul_pos (show 0 < (k:ℝ)-1 by linarith) (show 0 < 10-Real.pi^2 by linarith)
    nlinarith
  have hxSmall : x^2 < 1 := by nlinarith [sq_nonneg x]
  have hcos := Real.one_sub_sq_div_two_le_cos (x := x)
  have hrlower : 1-x^2 ≤ r := by nlinarith
  have hsq : (1-x^2)^2 ≤ r^2 := (sq_le_sq₀ (by linarith) hr).mpr hrlower
  have hsqLower : 1-2*x^2 ≤ r^2 := by nlinarith [sq_nonneg (x^2)]
  have hmul := mul_le_mul_of_nonneg_left hsqLower (show 0 ≤ (k:ℝ)-1 by linarith)
  nlinarith

private theorem regular_contrary (n : ℕ) (H I : Finset Plane) (R : ℝ)
    (hn : 10 ≤ n) (hH : H.card = n - 4) (hR : 0 < R)
    (hcircle : ∀ h ∈ H, ‖h‖ = R) (hI : I.card = 4) (hzero : (0 : Plane) ∈ I)
    (hinterior : ∀ z ∈ I, z ∈ interior (convexHull ℝ (H : Set Plane)))
    (hq : 2 * (nonDiameterDistances (H ∪ I)).card = H.card)
    (horder : order H = H.card)
    (hfull : ∀ p ∈ H, ∀ h : Plane, h ∈ H ↔ ∃ g : Stabilizer H, rotate g.val p = h) : False := by
  classical
  let S := nonDiameterDistances (H ∪ I)
  let k := S.card
  have hcard2 : H.card = 2*k := hq.symm
  have hk : 3 ≤ k := by omega
  have htrans : ∀ a ∈ H, ∀ b ∈ H, ∃ g : Stabilizer H, rotate g.val a = b := by
    intro a ha b hb
    exact (hfull a ha b).mp hb
  obtain ⟨a,ha,hCcard,hCsub,hCf,hdiam,hCsum⟩ :=
    regular_chord_data H I R k hk hcard2 hR hcircle horder htrans
  let C := (Finset.Icc 1 (k-1)).image (fun j : ℕ => 2*R*Real.sin (Real.pi*j/(2*k)))
  change C.card = k-1 at hCcard
  change C ⊆ S at hCsub
  change (∑ d ∈ C, d^2) ≤ ((2*k:ℕ):ℝ)*R^2-2*R^2 at hCsum
  obtain ⟨_hcard,hJ,ρ,hρpos,hρlt,hnorm,_hmemR,hmemρ,hsat,hitrans,_hthree,_hdiv⟩ :=
    centered_lower_support_geometry n H I R hn hH hR hcircle hI hzero hinterior hq
  obtain ⟨u,hu⟩ := Finset.card_pos.mp (show 0 < (I.erase 0).card by omega)
  have hJv : 0 < ((I.erase 0).erase u).card := by
    rw [Finset.card_erase_of_mem hu, hJ]
    decide
  obtain ⟨v,hv'⟩ := Finset.card_pos.mp hJv
  have hv := (Finset.mem_erase.mp hv').2
  have huv : u ≠ v := (Finset.mem_erase.mp hv').1.symm
  obtain ⟨g,hg⟩ := hitrans u hu v hv
  have hg1 : g.val ≠ 1 := by
    intro he
    rw [he, rotate_one] at hg
    exact huv hg
  have hsat := hsat u hu
  change H.image (fun h => dist u h) = S ∧
    (∀ d ∈ S, (H.filter fun h => dist u h = d).card = 2) at hsat
  have hmap : ∀ h ∈ H, dist u h ∈ S := by
    intro h hh
    rw [← hsat.1]
    exact Finset.mem_image.mpr ⟨h,hh,rfl⟩
  have hsum : ∑ h ∈ H, dist u h^2 = 2*∑ d ∈ S, d^2 := by
    rw [← Finset.sum_fiberwise_of_maps_to hmap (fun h => dist u h^2), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    calc
      _ = ∑ _h ∈ H.filter (fun h => dist u h = d), d^2 := by
        apply Finset.sum_congr rfl
        intro h hh
        rw [(Finset.mem_filter.mp hh).2]
      _ = 2*d^2 := by simp [hsat.2 d hd, nsmul_eq_mul]
  have hmoment : ∑ d ∈ S, d^2 = (k:ℝ)*(R^2+ρ^2) := by
    have hm := radial_square_sum H R u hcircle g hg1
    rw [hcard2, hnorm u hu, hsum] at hm
    push_cast at hm
    linarith
  have hkR : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hangle : Real.pi*((k-1:ℕ):ℝ)/(2*k) = Real.pi/2-Real.pi/(2*k) := by
    rw [Nat.cast_sub (by omega : 1 ≤ k)]
    push_cast
    field_simp
  have hLmem : 2*R*Real.cos (Real.pi/(2*k)) ∈ C := by
    apply Finset.mem_image.mpr
    refine ⟨k-1, Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩, ?_⟩
    rw [hangle, Real.sin_pi_div_two_sub]
  have hLrad : 2*R*Real.cos (Real.pi/(2*k)) ∈ H.image (fun h => dist u h) := by
    rw [hsat.1]
    exact hCsub hLmem
  obtain ⟨b,hb,hbL⟩ := Finset.mem_image.mp hLrad
  have hbound : 2*R*Real.cos (Real.pi/(2*k)) ≤ ρ+R := by
    have ht := dist_triangle u 0 b
    rw [dist_zero_right, dist_zero_left, hnorm u hu, hcircle b hb, hbL] at ht
    exact ht
  let r := ρ/R
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hrlt : r < 1 := (div_lt_one hR).mpr hρlt
  have hρr : ρ = r*R := by dsimp [r]; field_simp
  have hl : 2*Real.cos (Real.pi/(2*k))-1 ≤ r := by
    apply (le_div_iff₀ hR).mpr
    nlinarith
  by_cases hρC : ρ ∈ C
  · obtain ⟨j,hj,hjρ⟩ := Finset.mem_image.mp hρC
    have he : r = 2*Real.sin (Real.pi*j/(2*k)) := by
      dsimp [r]
      rw [← hjρ]
      field_simp
    exact radius_chord_exclusion k j r hk hj hrlt he hl
  have hSeq : insert ρ C = S := by
    apply Finset.eq_of_subset_of_card_le
    · exact Finset.insert_subset hmemρ hCsub
    · rw [Finset.card_insert_of_notMem hρC, hCcard]
      dsimp [k]
      omega
  rw [← hSeq, Finset.sum_insert hρC] at hmoment
  have hscaled : ((k:ℝ)-1)*ρ^2 ≤ ((k:ℝ)-2)*R^2 := by
    push_cast at hCsum
    nlinarith
  have hm : ((k:ℝ)-1)*r^2 ≤ k-2 := by
    rw [hρr] at hscaled
    have hR2 : 0 < R^2 := sq_pos_of_pos hR
    apply (mul_le_mul_iff_left₀ hR2).mp
    nlinarith
  exact radius_moment_exclusion k r hk hr hl hm

/-- The original even centered lower-support geometry has an actual positive
nondiameter distance of unordered loop-free multiplicity between one and `n`;
no regularity or saturation certificate is assumed. -/
theorem exists_distance_of_even_centered_lower_support (n : ℕ) (heven : Even n) (hn : 10 ≤ n)
    (H I : Finset Plane) (hH : H.card = n-4) (R : ℝ) (hR : 0 < R)
    (hcircle : ∀ h ∈ H, ‖h‖ = R) (hI : I.card = 4) (hzero : (0:Plane) ∈ I)
    (hinterior : ∀ z ∈ I, z ∈ interior (convexHull ℝ (H : Set Plane)))
    (hq : 2*(nonDiameterDistances (H ∪ I)).card = H.card) :
    (H ∪ I).card = n ∧ ∃ d : ℝ, 0 < d ∧
      d < Metric.diam ((H ∪ I : Finset Plane) : Set Plane) ∧
      (∃ a ∈ H ∪ I, ∃ b ∈ H ∪ I, a ≠ b ∧ dist a b = d) ∧
      1 ≤ multiplicity (H ∪ I) d ∧ multiplicity (H ∪ I) d ≤ n := by
  obtain ⟨hcard,hcases⟩ := original_lower_support_regular_reduction n heven hn H I hH R hR
    hcircle hI hzero hinterior hq
  have hsmall : ∃ d : ℝ, 0 < d ∧
      d < Metric.diam ((H ∪ I : Finset Plane) : Set Plane) ∧
      1 ≤ multiplicity (H ∪ I) d ∧ multiplicity (H ∪ I) d ≤ n := by
    rcases hcases with hsmall | ⟨_hlarge,horder,hfull⟩
    · exact hsmall
    · exact False.elim (regular_contrary n H I R hn hH hR hcircle hI hzero hinterior hq horder hfull)
  obtain ⟨d,hdpos,hdlt,hμ,hbound⟩ := hsmall
  refine ⟨hcard,d,hdpos,hdlt,?_,hμ,hbound⟩
  obtain ⟨e,he⟩ := Finset.card_pos.mp hμ
  induction e using Sym2.ind with
  | _ a b =>
    have hep := Finset.mem_filter.mp he
    obtain ⟨ha,hb,hab⟩ := (mk_mem_pairs (H ∪ I) a b).mp hep.1
    exact ⟨a,ha,b,hb,hab,by simpa only [pairDist_mk] using hep.2⟩

/-- An even circular hull with four ambient interiors including its center has
an occurring positive strict nondiameter distance with unordered loop-free
multiplicity between one and the total number of points. Support cardinality,
regularity, saturation, and FAILURE are not hypotheses. -/
theorem four_interior_centered_circle (n : ℕ) (H I : Finset Plane) (R : ℝ)
    (hn : 10 ≤ n) (heven : Even n) (hH : H.card = n - 4)
    (hR : 0 < R) (hcircle : ∀ h ∈ H, ‖h‖ = R) (hI : I.card = 4)
    (hInt : ∀ z ∈ I, z ∈ interior (convexHull ℝ (H : Set Plane)))
    (hzero : (0 : Plane) ∈ I) :
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
  have hJ : (I.erase 0).card = 3 := by rw [Finset.card_erase_of_mem hzero, hI]
  obtain ⟨z, hzJ⟩ := Finset.card_pos.mp (by omega : 0 < (I.erase 0).card)
  have hz := (Finset.mem_erase.mp hzJ).2
  have hz0 := (Finset.mem_erase.mp hzJ).1
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
    exact radial_card_le_two H 0 z R d hc hz0
  have hlower : H.card ≤ 2 * S.card :=
    Finset.card_le_mul_card_image_of_maps_to hmap 2 hcap
  by_cases hlow : 2 * S.card = H.card
  · obtain ⟨_hcard, d, hdpos, hdlt, hocc, hmult, hbound⟩ :=
      exists_distance_of_even_centered_lower_support
        n heven hn H I hH R hR hcircle hI hzero hInt hlow
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

/-- Six explicit rational points on the radius-five circle and the center plus
three tiny distinct strict ambient interiors jointly inhabit the original
centered geometry at `n = 10`. This fixture deliberately does not assume the
lower-support equality or FAILURE; it is not a fixture of the excluded branch. -/
theorem original_centered_geometry_fixture : ∃ H I : Finset Plane,
    Even (10 : ℕ) ∧ 10 ≤ (10 : ℕ) ∧ H.card = 10 - 4 ∧ (0 : ℝ) < 5 ∧
      (∀ h ∈ H, ‖h‖ = 5) ∧ I.card = 4 ∧ (0 : Plane) ∈ I ∧
      (∀ z ∈ I, z ∈ interior (convexHull ℝ (H : Set Plane))) ∧
      (I.erase 0).card = 3 ∧ (H ∪ I).card = 10 := by
  classical
  let A : Plane := WithLp.toLp 2 ![3, 4]
  let B : Plane := WithLp.toLp 2 ![-3, 4]
  let C : Plane := WithLp.toLp 2 ![3, -4]
  let D : Plane := WithLp.toLp 2 ![-3, -4]
  let E : Plane := WithLp.toLp 2 ![5, 0]
  let F : Plane := WithLp.toLp 2 ![-5, 0]
  let H : Finset Plane := {A, B, C, D, E, F}
  let u : Plane := WithLp.toLp 2 ![1/8, 0]
  let v : Plane := WithLp.toLp 2 ![0, 1/8]
  let w : Plane := WithLp.toLp 2 ![-1/8, 0]
  let I : Finset Plane := {0, u, v, w}
  have hH : H.card = 6 := by
    norm_num [H, A, B, C, D, E, F, Finset.card_insert_of_notMem,
      WithLp.ext_iff, funext_iff, Fin.forall_fin_two]
  have hcircle : ∀ h ∈ H, ‖h‖ = 5 := by
    intro h hh
    have hsq : ‖h‖ ^ 2 = 25 := by
      simp only [H, Finset.mem_insert, Finset.mem_singleton] at hh
      rcases hh with rfl | rfl | rfl | rfl | rfl | rfl <;>
        norm_num [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, A, B, C, D, E, F]
    nlinarith [norm_nonneg h]
  have hI : I.card = 4 := by
    norm_num [I, u, v, w, Finset.card_insert_of_notMem,
      WithLp.ext_iff, funext_iff, Fin.forall_fin_two]
  have hzero : (0 : Plane) ∈ I := by simp [I]
  have hcorners : ∀ i ∈ ({-3, 3} : Finset ℝ), ∀ j ∈ ({-4, 4} : Finset ℝ),
      WithLp.toLp 2 ![i, j] ∈ H := by
    intro i hi j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> simp [H, A, B, C, D]
  have hinterior : ∀ z ∈ I, z ∈ interior (convexHull ℝ (H : Set Plane)) := by
    intro z hz
    apply CircleFixtures.rectangle_mem_interior H (r := 3) (s := 4)
      (by norm_num) (by norm_num) hcorners
    all_goals
      simp only [I, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl <;> norm_num [u, v, w]
  have hJ : (I.erase 0).card = 3 := by rw [Finset.card_erase_of_mem hzero, hI]
  have hcard := FourInteriorLowerSupport.card_union_four_interiors H I 5
    (by norm_num) hcircle hI hinterior
  exact ⟨H, I, by decide, by omega, by omega, by norm_num, hcircle, hI,
    hzero, hinterior, hJ, by omega⟩

end

/-- The same rational radius-five centered fixture satisfies the unconditional
centered-four conclusion, with no lower-support or FAILURE assertion. -/
theorem original_centered_geometry_and_conclusion : ∃ H I : Finset Plane,
    Even (10 : ℕ) ∧ 10 ≤ (10 : ℕ) ∧ H.card = 10 - 4 ∧ (0 : ℝ) < 5 ∧
      (∀ h ∈ H, ‖h‖ = 5) ∧ I.card = 4 ∧ (0 : Plane) ∈ I ∧
      (∀ z ∈ I, z ∈ interior (convexHull ℝ (H : Set Plane))) ∧
      (I.erase 0).card = 3 ∧ (H ∪ I).card = 10 ∧ ∃ d : ℝ,
        0 < d ∧ d < Metric.diam ((H ∪ I : Finset Plane) : Set Plane) ∧
        (∃ a ∈ H ∪ I, ∃ b ∈ H ∪ I, a ≠ b ∧ dist a b = d) ∧
        1 ≤ multiplicity (H ∪ I) d ∧ multiplicity (H ∪ I) d ≤ 10 := by
  obtain ⟨H,I,heven,hn,hH,hR,hcircle,hI,hzero,hInt,hJ,_hcard⟩ :=
    original_centered_geometry_fixture
  have hclaim := four_interior_centered_circle 10 H I 5 hn heven hH hR hcircle hI hInt hzero
  exact ⟨H,I,heven,hn,hH,hR,hcircle,hI,hzero,hInt,hJ,hclaim⟩

end Erdos132.FourInteriorCentered
