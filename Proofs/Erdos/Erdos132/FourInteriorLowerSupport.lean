import Erdos.Erdos132.ThreeInteriorCounting
import Erdos.Erdos132.CircleRotationTransport
import Erdos.Erdos132.CircleRotationOrder
import Mathlib.Algebra.Group.Pointwise.Finset.Basic

set_option autoImplicit false

open scoped BigOperators Pointwise

namespace Erdos132.FourInteriorLowerSupport

open TwoInteriorCircle CircleRotation

noncomputable section

local instance : DecidableEq Rotation := Classical.decEq _

/-- Four distinct ambient-interior points, represented without tags by a four-element
finset, add exactly four points to the positive-radius cyclic hull. -/
theorem card_union_four_interiors (H I : Finset Plane) (R : ℝ)
    (hR : 0 < R) (hcircle : ∀ h ∈ H, ‖h‖ = R) (hI : I.card = 4)
    (hinterior : ∀ z ∈ I, z ∈ interior (convexHull ℝ (H : Set Plane))) :
    (H ∪ I).card = H.card + 4 := by
  classical
  have hdisjoint : Disjoint H I := by
    apply Finset.disjoint_left.mpr
    intro z hzH hzI
    exact ThreeInteriorCounting.interior_not_mem_circle H R z hR hcircle
      (hinterior z hzI) hzH
  rw [Finset.card_union_of_disjoint hdisjoint, hI]

/-- Adding any finite set of ambient-interior points preserves the actual diameter. -/
theorem diam_union_interiors (H I : Finset Plane)
    (hinterior : ∀ z ∈ I, z ∈ interior (convexHull ℝ (H : Set Plane))) :
    Metric.diam ((H ∪ I : Finset Plane) : Set Plane) = Metric.diam (H : Set Plane) := by
  classical
  have hsub : ((H ∪ I : Finset Plane) : Set Plane) ⊆ convexHull ℝ (H : Set Plane) := by
    intro z hz
    rcases Finset.mem_union.mp hz with hzH | hzI
    · exact subset_convexHull ℝ (H : Set Plane) hzH
    · exact interior_subset (hinterior z hzI)
  apply le_antisymm
  · exact Metric.diam_le_of_forall_dist_le Metric.diam_nonneg
      (fun _ hx _ hy => dist_le_diam_hull H (hsub hx) (hsub hy))
  · exact Metric.diam_mono (by intro z hz; exact Finset.mem_union_left I hz)
      (H ∪ I).finite_toSet.isBounded

/-- In the lower-support branch every off-center interior has the entire actual
positive nondiameter support, and every radial fiber has exactly two hull vertices.
This deduction uses only the original geometry and the visible support-cardinality
equality, not a multiplicity, equal-norm, or symmetry certificate. -/
theorem radial_saturation (H I : Finset Plane) (R : ℝ)
    (hH : 6 ≤ H.card) (hR : 0 < R) (hcircle : ∀ h ∈ H, ‖h‖ = R)
    (hinterior : ∀ z ∈ I, z ∈ interior (convexHull ℝ (H : Set Plane)))
    (hoff : ∀ z ∈ I, z ≠ 0)
    (hq : 2 * (nonDiameterDistances (H ∪ I)).card = H.card) :
    ∀ z ∈ I,
      H.image (fun h => dist z h) = nonDiameterDistances (H ∪ I) ∧
      (∀ d ∈ nonDiameterDistances (H ∪ I),
        (H.filter fun h => dist z h = d).card = 2) := by
  classical
  let X := H ∪ I
  let S := nonDiameterDistances X
  have hdiam := diam_union_interiors H I hinterior
  intro z hz
  have hzH := ThreeInteriorCounting.interior_not_mem_circle H R z hR hcircle
    (hinterior z hz)
  have hmap : ∀ h ∈ H, dist z h ∈ S := by
    intro h hh
    apply (mem_nonDiameterDistances X (dist z h)).mpr
    refine ⟨⟨z, Finset.mem_union_right H hz, h, Finset.mem_union_left I hh,
      fun heq => hzH (heq.symm ▸ hh), rfl⟩, ?_⟩
    rw [hdiam]
    exact dist_lt_diam_hull H (by omega) (hinterior z hz)
      (subset_convexHull ℝ (H : Set Plane) hh)
  have hcap : ∀ d ∈ S, (H.filter fun h => dist z h = d).card ≤ 2 := by
    intro d _hd
    simpa only [dist_comm] using radial_card_le_two H 0 z R d
      (by simpa only [dist_zero_right] using hcircle) (hoff z hz)
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

/-- Original lower-support geometry supplies a preserving rotation between any two
of its nonzero interiors. In particular their norms agree; no norm or transport
certificate is a premise. -/
theorem exists_stabilizer_map (H I : Finset Plane) (R : ℝ)
    (hH : 6 ≤ H.card) (hR : 0 < R) (hcircle : ∀ h ∈ H, ‖h‖ = R)
    (hinterior : ∀ z ∈ I, z ∈ interior (convexHull ℝ (H : Set Plane)))
    (hoff : ∀ z ∈ I, z ≠ 0)
    (hq : 2 * (nonDiameterDistances (H ∪ I)).card = H.card)
    (u v : Plane) (hu : u ∈ I) (hv : v ∈ I) :
    ∃ g : Stabilizer H, rotate g.val u = v := by
  have hsatu := radial_saturation H I R hH hR hcircle hinterior hoff hq u hu
  have hsatv := radial_saturation H I R hH hR hcircle hinterior hoff hq v hv
  apply CircleRotationTransport.exists_stabilizer_map_of_saturated_common_support
    H R u v hH hR (hoff u hu) (hoff v hv) hcircle
    (hsatu.1.trans hsatv.1.symm)
  intro d hd
  have hdS := hsatu.1 ▸ hd
  exact ⟨hsatu.2 d hdS, hsatv.2 d hdS⟩

/-- Four distinct off-center ambient interiors and the actual lower-support equality
force at least four distinct elements in the full rotation stabilizer, whose order
divides the actual hull cardinality. This is the original-geometry symmetry checkpoint
for the remaining-branches four-interior consumer, not the final branch exclusion. -/
theorem four_le_order_and_order_dvd_card (H I : Finset Plane) (R : ℝ)
    (hH : 6 ≤ H.card) (hR : 0 < R) (hcircle : ∀ h ∈ H, ‖h‖ = R)
    (hI : I.card = 4)
    (hinterior : ∀ z ∈ I, z ∈ interior (convexHull ℝ (H : Set Plane)))
    (hoff : ∀ z ∈ I, z ≠ 0)
    (hq : 2 * (nonDiameterDistances (H ∪ I)).card = H.card) :
    4 ≤ order H ∧ order H ∣ H.card := by
  classical
  have hHne : H.Nonempty := Finset.card_pos.mp (by omega)
  letI := finite_stabilizer H hHne hR hcircle
  obtain ⟨u, hu⟩ := Finset.card_pos.mp (show 0 < I.card by omega)
  have hex : ∀ v : {z // z ∈ I}, ∃ g : Stabilizer H, rotate g.val u = v.val := by
    intro v
    exact exists_stabilizer_map H I R hH hR hcircle hinterior hoff hq
      u v.val hu v.property
  let f : {z // z ∈ I} → Stabilizer H := fun v => (hex v).choose
  have hf : Function.Injective f := by
    intro v w heq
    apply Subtype.ext
    calc
      v.val = rotate (f v).val u := (hex v).choose_spec.symm
      _ = rotate (f w).val u := congrArg (fun g : Stabilizer H => rotate g.val u) heq
      _ = w.val := (hex w).choose_spec
  have hbound := Nat.card_le_card_of_injective f hf
  have hfour : 4 ≤ order H := by
    simpa only [order, Nat.card_eq_fintype_card, Fintype.card_coe, hI] using hbound
  exact ⟨hfour, order_dvd_card H hHne hR hcircle⟩

private theorem card_dvd_of_free (G Y : Type*) [Group G] [MulAction G Y]
    [Finite G] [Finite Y] (hfree : ∀ g : G, ∀ y : Y, g • y = y → g = 1) :
    Nat.card G ∣ Nat.card Y := by
  have hs : ∀ y : Y, MulAction.stabilizer G y = ⊥ := by
    intro y
    apply le_antisymm
    · intro g hg
      exact Subgroup.mem_bot.mpr (hfree g y hg)
    · exact bot_le
  rw [Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd (G := G) (X := Y) hs),
    Nat.card_prod]
  exact dvd_mul_left _ _

private theorem card_dvd_of_mul_invariant {G : Type*} [Group G]
    (K : Subgroup G) [Finite K] (T : Finset G)
    (hstable : ∀ g : K, ∀ t ∈ T, g.val * t ∈ T) : Nat.card K ∣ T.card := by
  classical
  letI : MulAction K {t // t ∈ T} :=
    { smul := fun g t => ⟨g.val * t.val, hstable g t.val t.property⟩
      one_smul := fun t => Subtype.ext (one_mul t.val)
      mul_smul := fun g k t => Subtype.ext (mul_assoc g.val k.val t.val) }
  have hd := card_dvd_of_free K {t // t ∈ T} (by
    intro g t heq
    apply Subtype.ext
    have hval : g.val * t.val = t.val := congrArg Subtype.val heq
    exact mul_right_cancel (hval.trans (one_mul t.val).symm))
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hd

private theorem eq_of_divisible_gap (m N t : ℕ) (hm : 4 ≤ m)
    (hmN : m ∣ N) (hmt : m ∣ t) (hlower : N ≤ t) (hupper : t ≤ N + 3) : t = N := by
  have hmdiff : m ∣ t - N := Nat.dvd_sub hmt hmN
  have hdiff : t - N < m := by omega
  have hzero : t - N = 0 := Nat.eq_zero_of_dvd_of_lt hmdiff hdiff
  omega

/-- For any finite circle-coefficient set containing the identity, left invariance
of its actual quotient support under a subgroup of order at least four, together
with the sharp pre-antipodal bound `|A| ≤ |A/A| ≤ |A|+3`, forces `A/A=A`.
The cardinality jump is excluded by divisibility, not by assuming antipodes. -/
theorem quotient_support_eq_of_small_gap (A : Finset Rotation) (K : Subgroup Rotation)
    [Finite K] (hOne : 1 ∈ A) (hfour : 4 ≤ Nat.card K)
    (hcard : Nat.card K ∣ A.card)
    (hstable : ∀ g : K, ∀ t ∈ A / A, g.val * t ∈ A / A)
    (hupper : (A / A).card ≤ A.card + 3) : A / A = A := by
  classical
  have hsub : A ⊆ A / A := by
    intro a ha
    exact Finset.mem_div.mpr ⟨a, ha, 1, hOne, div_one a⟩
  have hdiv := card_dvd_of_mul_invariant K (A / A) hstable
  have heq : (A / A).card = A.card := eq_of_divisible_gap
    (Nat.card K) A.card (A / A).card hfour hcard hdiv
    (Finset.card_le_card hsub) hupper
  exact (Finset.eq_of_subset_of_card_le hsub heq.le).symm

/-- A nonempty finite circle-coefficient set containing the identity and equal to
its actual quotient support is the carrier of a subgroup. -/
theorem exists_subgroup_of_quotient_support_eq (A : Finset Rotation)
    (hOne : 1 ∈ A) (hquot : A / A = A) :
    ∃ K : Subgroup Rotation, ∀ g : Rotation, g ∈ K ↔ g ∈ A := by
  classical
  let K : Subgroup Rotation :=
    { carrier := {g | g ∈ A}
      one_mem' := hOne
      inv_mem' := by
        intro a ha
        rw [← hquot]
        exact Finset.mem_div.mpr ⟨1, hOne, a, ha, one_div a⟩
      mul_mem' := by
        intro a b ha hb
        have hbinv : b⁻¹ ∈ A := by
          rw [← hquot]
          exact Finset.mem_div.mpr ⟨1, hOne, b, hb, one_div b⟩
        rw [← hquot]
        exact Finset.mem_div.mpr ⟨a, ha, b⁻¹, hbinv, by simp⟩ }
  exact ⟨K, fun _ => Iff.rfl⟩

private theorem quotient_chord (a b : Rotation) (p : Plane) :
    dist (rotate (a / b) p) p = dist (rotate a p) (rotate b p) := by
  calc
    dist (rotate (a / b) p) p =
        dist (rotate b (rotate (a / b) p)) (rotate b p) :=
      ((rotate_isometry b).dist_eq _ _).symm
    _ = dist (rotate a p) (rotate b p) := by
      rw [← rotate_mul]
      have hba : b * (a / b) = a := by simp [div_eq_mul_inv, mul_left_comm]
      rw [hba]

/-- Relative to any hull vertex, the actual hull is represented bijectively by
unit-circle coefficients, with the base vertex represented by the identity. -/
theorem exists_hull_coefficients (H : Finset Plane) (R : ℝ) (p : Plane)
    (hR : 0 < R) (hcircle : ∀ h ∈ H, ‖h‖ = R) (hp : p ∈ H) :
    ∃ A : Finset Rotation, 1 ∈ A ∧ A.card = H.card ∧
      ∀ g : Rotation, g ∈ A ↔ rotate g p ∈ H := by
  classical
  have hp0 : p ≠ 0 := ne_zero_of_norm_eq hR (hcircle p hp)
  let A := H.preimage (fun g : Rotation => rotate g p)
    (rotate_coeff_injective p hp0).injOn
  have hmem : ∀ g : Rotation, g ∈ A ↔ rotate g p ∈ H := fun _ => Finset.mem_preimage
  have himage : A.image (fun g => rotate g p) = H := by
    ext h
    constructor
    · intro hh
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hh
      exact (hmem g).mp hg
    · intro hh
      obtain ⟨g, hg⟩ := exists_rotation_map hR (hcircle p hp) (hcircle h hh)
      exact Finset.mem_image.mpr ⟨g, (hmem g).mpr (hg ▸ hh), hg⟩
  have hcard : A.card = H.card := by
    rw [← himage, Finset.card_image_of_injective A (rotate_coeff_injective p hp0)]
  exact ⟨A, (hmem 1).mpr (by simpa using hp), hcard, hmem⟩

/-- The actual quotient support of hull coefficients has at most two coefficients
per positive chord length, at most two for the global diameter, and one for zero.
Thus the valid pre-antipodal bound is `|A/A| ≤ 2|S|+3`, not `2|S|+2`. -/
theorem quotient_support_card_le (H I : Finset Plane) (R : ℝ) (p : Plane)
    (A : Finset Rotation) (hR : 0 < R) (hcircle : ∀ h ∈ H, ‖h‖ = R)
    (hp : p ∈ H) (hOne : 1 ∈ A)
    (hA : ∀ g : Rotation, g ∈ A ↔ rotate g p ∈ H) :
    (A / A).card ≤ 2 * (nonDiameterDistances (H ∪ I)).card + 3 := by
  classical
  let T := A / A
  let E := (T.erase 1).image (fun g => rotate g p)
  let S := nonDiameterDistances (H ∪ I)
  let D := Metric.diam ((H ∪ I : Finset Plane) : Set Plane)
  have hp0 : p ≠ 0 := ne_zero_of_norm_eq hR (hcircle p hp)
  have hOneT : 1 ∈ T := Finset.mem_div.mpr ⟨1, hOne, 1, hOne, by simp⟩
  have hcardE : E.card = (T.erase 1).card :=
    Finset.card_image_of_injective _ (rotate_coeff_injective p hp0)
  have hcircleE : ∀ x ∈ E, dist x (0 : Plane) = R := by
    intro x hx
    obtain ⟨g, _hg, rfl⟩ := Finset.mem_image.mp hx
    rw [dist_zero_right, norm_rotate, hcircle p hp]
  have hmap : ∀ x ∈ E, dist x p ∈ insert D S := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hx
    have hgT := (Finset.mem_erase.mp hg).2
    have hg1 := (Finset.mem_erase.mp hg).1
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_div.mp hgT
    have haH := (hA a).mp ha
    have hbH := (hA b).mp hb
    have hd : dist (rotate g p) p = dist (rotate a p) (rotate b p) := by
      rw [← hab]
      exact quotient_chord a b p
    have hpos : 0 < dist (rotate g p) p := by
      apply dist_pos.mpr
      intro hfix
      exact hg1 (point_fixed_imp_one g p hp0 hfix)
    have hle : dist (rotate g p) p ≤ D := by
      rw [hd]
      exact Metric.dist_le_diam_of_mem (H ∪ I).finite_toSet.isBounded
        (Finset.mem_union_left I haH) (Finset.mem_union_left I hbH)
    by_cases heq : dist (rotate g p) p = D
    · exact Finset.mem_insert.mpr (Or.inl heq)
    · apply Finset.mem_insert_of_mem
      apply (ThreeInteriorCounting.mem_nonDiameterDistances_iff_positive (H ∪ I) _).mpr
      exact ⟨hpos, lt_of_le_of_ne hle heq,
        rotate a p, Finset.mem_union_left I haH,
        rotate b p, Finset.mem_union_left I hbH, hd.symm⟩
  have hcap : ∀ d ∈ insert D S, (E.filter fun x => dist x p = d).card ≤ 2 := by
    intro d _hd
    exact radial_card_le_two E 0 p R d hcircleE hp0
  have hbound := Finset.card_le_mul_card_image_of_maps_to hmap 2 hcap
  have hcardInsert : (insert D S).card ≤ S.card + 1 := Finset.card_insert_le _ _
  have hmul := Nat.mul_le_mul_left 2 hcardInsert
  have herase : (T.erase 1).card + 1 = T.card := Finset.card_erase_add_one hOneT
  dsimp only [T, S] at hcardE hbound hmul herase
  omega

/-- The lower-support original geometry forces the hull itself to be one orbit
of its full finite unit-circle stabilizer. Its order is exactly the hull cardinality.
This implements the complete small angular-difference kernel without quotient angles:
relative coefficients satisfy `A/A=A` and therefore form a finite subgroup. -/
theorem hull_is_full_stabilizer_orbit (H I : Finset Plane) (R : ℝ)
    (hH : 6 ≤ H.card) (hR : 0 < R) (hcircle : ∀ h ∈ H, ‖h‖ = R)
    (hI : I.card = 4)
    (hinterior : ∀ z ∈ I, z ∈ interior (convexHull ℝ (H : Set Plane)))
    (hoff : ∀ z ∈ I, z ≠ 0)
    (hq : 2 * (nonDiameterDistances (H ∪ I)).card = H.card) :
    order H = H.card ∧ ∀ p ∈ H, ∀ h : Plane,
      h ∈ H ↔ ∃ g : Stabilizer H, rotate g.val p = h := by
  classical
  have hHne : H.Nonempty := Finset.card_pos.mp (by omega)
  letI := finite_stabilizer H hHne hR hcircle
  obtain ⟨hfour, hdiv⟩ := four_le_order_and_order_dvd_card
    H I R hH hR hcircle hI hinterior hoff hq
  have hcoeff : ∀ p ∈ H, ∃ A : Finset Rotation, A.card = H.card ∧
      (∀ g : Rotation, g ∈ A ↔ rotate g p ∈ H) ∧
      (∀ g : Rotation, g ∈ Stabilizer H ↔ g ∈ A) := by
    intro p hp
    obtain ⟨A, hOne, hcardA, hA⟩ := exists_hull_coefficients H R p hR hcircle hp
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
      have hbound := quotient_support_card_le H I R p A hR hcircle hp hOne hA
      rw [hq, ← hcardA] at hbound
      exact hbound
    have hquot : A / A = A := quotient_support_eq_of_small_gap A (Stabilizer H)
      hOne hfour (hcardA ▸ hdiv) hstableT hupper
    obtain ⟨K, hK⟩ := exists_subgroup_of_quotient_support_eq A hOne hquot
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

private theorem antipodal_distance (p : Plane) (R : ℝ) (hp : ‖p‖ = R) :
    dist (-p) p = 2 * R := by
  rw [dist_comm, dist_eq_norm, sub_neg_eq_add, ← two_smul ℝ p, norm_smul,
    Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2), hp]

/-- In one full finite rotation orbit of even order on a positive circle,
there are exactly `(H.card-2)/2` occurring nondiameter chord classes.
The subtraction-free equality records the zero and diameter singleton fibers. -/
theorem hull_card_eq_twice_support_add_two (H : Finset Plane) (R : ℝ)
    (hH : H.Nonempty) (hR : 0 < R) (hcircle : ∀ h ∈ H, ‖h‖ = R)
    (heven : Even (order H))
    (horbit : ∀ p ∈ H, ∀ h : Plane, h ∈ H ↔ ∃ g : Stabilizer H, rotate g.val p = h) :
    H.card = 2 * (nonDiameterDistances H).card + 2 := by
  classical
  have hnonempty := hH
  obtain ⟨p, hp⟩ := hH
  have hp0 : p ≠ 0 := by
    intro heq
    have hr := hcircle p hp
    rw [heq, norm_zero] at hr
    linarith
  have hsym : ∀ x ∈ H, -x ∈ H := fun x hx =>
    (mem_iff_neg_mem_of_even_order H hnonempty hR hcircle heven x).mp hx
  have hdiam := antipodal_diam H R hnonempty hR hcircle hsym
  let T := nonDiameterDistances H
  let D := H.image (fun h => dist h p)
  have hD : D = insert 0 (insert (2 * R) T) := by
    ext d
    constructor
    · intro hd
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hd
      by_cases heq : h = p
      · simp [heq]
      by_cases hmax : dist h p = 2 * R
      · simp [hmax]
      apply Finset.mem_insert_of_mem
      apply Finset.mem_insert_of_mem
      apply (ThreeInteriorCounting.mem_nonDiameterDistances_iff_positive H _).mpr
      refine ⟨dist_pos.mpr heq, ?_, h, hh, p, hp, rfl⟩
      rw [hdiam]
      exact lt_of_le_of_ne (hdiam ▸ Metric.dist_le_diam_of_mem H.finite_toSet.isBounded hh hp) hmax
    · intro hd
      rcases Finset.mem_insert.mp hd with rfl | hd
      · exact Finset.mem_image.mpr ⟨p, hp, dist_self p⟩
      rcases Finset.mem_insert.mp hd with rfl | hd
      · exact Finset.mem_image.mpr ⟨-p, hsym p hp, antipodal_distance p R (hcircle p hp)⟩
      obtain ⟨_hdpos, _hdlt, a, ha, b, hb, hab⟩ :=
        (ThreeInteriorCounting.mem_nonDiameterDistances_iff_positive H d).mp hd
      obtain ⟨g, hg⟩ := (horbit p hp a).mp ha
      refine Finset.mem_image.mpr ⟨rotate g.val⁻¹ b, (g⁻¹).property b |>.mpr hb, ?_⟩
      have hiso := (rotate_isometry g.val).dist_eq (rotate g.val⁻¹ b) p
      rw [← rotate_mul, mul_inv_cancel, rotate_one, hg] at hiso
      exact hiso.symm.trans (dist_comm b a |>.trans hab)
  have hTpos : ∀ d ∈ T, 0 < d ∧ d < 2 * R := by
    intro d hd
    obtain ⟨hdpos, hdlt, _⟩ := (ThreeInteriorCounting.mem_nonDiameterDistances_iff_positive H d).mp hd
    exact ⟨hdpos, hdiam ▸ hdlt⟩
  have hf0 : (H.filter fun h => dist h p = 0) = {p} := by
    ext h
    simp only [Finset.mem_filter, Finset.mem_singleton, dist_eq_zero]
    exact ⟨fun hh => hh.2, fun heq => ⟨heq ▸ hp, heq⟩⟩
  have hfmax : (H.filter fun h => dist h p = 2 * R) = {-p} := by
    ext h
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hh, hdist⟩
      have hsub : ‖h - p‖ ^ 2 = (2 * R) ^ 2 := by rw [← dist_eq_norm, hdist]
      have hadd := norm_add_sq_real h p
      have hminus := norm_sub_sq_real h p
      rw [hcircle h hh, hcircle p hp] at hadd hminus
      have hnorm : ‖h + p‖ = 0 := by nlinarith [norm_nonneg (h + p)]
      exact eq_neg_of_add_eq_zero_left (norm_eq_zero.mp hnorm)
    · rintro rfl
      exact ⟨hsym p hp, antipodal_distance p R (hcircle p hp)⟩
  have hfT : ∀ d ∈ T, (H.filter fun h => dist h p = d).card = 2 := by
    intro d hd
    have hdm : d ∈ D := by rw [hD]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hd)
    obtain ⟨h, hh, hdist⟩ := Finset.mem_image.mp hdm
    obtain ⟨g, hg⟩ := (horbit p hp h).mp hh
    have hg1 : g.val ≠ 1 := by
      intro heq
      rw [heq, rotate_one] at hg
      rw [← hg, dist_self] at hdist
      have hpos := (hTpos d hd).1
      linarith
    have hginv : g.val ≠ g.val⁻¹ := by
      intro heq
      have hsq : g.val ^ 2 = 1 := by
        rw [pow_two]
        calc
          g.val * g.val = g.val⁻¹ * g.val := congrArg (fun x => x * g.val) heq
          _ = 1 := inv_mul_cancel g.val
      have hneg := eq_neg_one_of_sq_eq_one g.val hsq hg1
      rw [hneg, rotate_neg_one] at hg
      have hanti := antipodal_distance p R (hcircle p hp)
      rw [hg, hdist] at hanti
      have hlt := (hTpos d hd).2
      linarith
    have hdistinct : rotate g.val p ≠ rotate g.val⁻¹ p :=
      fun heq => hginv (rotate_coeff_injective p hp0 heq)
    have hinvdist : dist (rotate g.val⁻¹ p) p = d := by
      have hiso := (rotate_isometry g.val).dist_eq (rotate g.val⁻¹ p) p
      rw [← rotate_mul, mul_inv_cancel, rotate_one, hg, dist_comm p h, hdist] at hiso
      exact hiso.symm
    have hpair : {rotate g.val p, rotate g.val⁻¹ p} ⊆ H.filter (fun h => dist h p = d) := by
      intro x hx
      rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hx :
          x = rotate g.val p ∨ x = rotate g.val⁻¹ p) with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨hg ▸ hh, hg ▸ hdist⟩
      · exact Finset.mem_filter.mpr ⟨(g⁻¹).property p |>.mpr hp, hinvdist⟩
    apply le_antisymm
    · exact radial_card_le_two H 0 p R d (by simpa only [dist_zero_right] using hcircle) hp0
    · have hle := Finset.card_le_card hpair
      rw [Finset.card_pair hdistinct] at hle
      exact hle
  have hzero : (0 : ℝ) ∉ T := fun hz => (lt_irrefl 0) ((hTpos 0 hz).1)
  have hmax : 2 * R ∉ T := fun hz => (lt_irrefl (2 * R)) ((hTpos _ hz).2)
  have hzeroMax : (0 : ℝ) ≠ 2 * R := by positivity
  calc
    H.card = ∑ d ∈ D, (H.filter fun h => dist h p = d).card := by
      have hs := Finset.sum_card_fiberwise_eq_card_filter H D (fun h => dist h p)
      rw [Finset.filter_eq_self.mpr (by intro h hh; exact Finset.mem_image.mpr ⟨h, hh, rfl⟩)] at hs
      exact hs.symm
    _ = 2 * T.card + 2 := by
      rw [hD, Finset.sum_insert (by simp [hzero, hzeroMax]), Finset.sum_insert hmax, hf0, hfmax]
      rw [Finset.sum_congr rfl hfT]
      simp only [Finset.card_singleton, Finset.sum_const, smul_eq_mul]
      omega

/-- In the original lower-support geometry, any occurring nondiameter class
absent from the hull has at most twelve loop-free unordered occurrences:
eight radial edges and at most four edges on the equal-radius interior circle. -/
theorem multiplicity_le_twelve_of_not_mem_hull_support (H I : Finset Plane) (R d : ℝ)
    (hH : 6 ≤ H.card) (hR : 0 < R) (hcircle : ∀ h ∈ H, ‖h‖ = R)
    (hI : I.card = 4)
    (hinterior : ∀ z ∈ I, z ∈ interior (convexHull ℝ (H : Set Plane)))
    (hoff : ∀ z ∈ I, z ≠ 0)
    (hq : 2 * (nonDiameterDistances (H ∪ I)).card = H.card)
    (hd : d ∈ nonDiameterDistances (H ∪ I)) (hdH : d ∉ nonDiameterDistances H) :
    multiplicity (H ∪ I) d ≤ 12 := by
  classical
  let X := H ∪ I
  let Q := (pairs X).filter (fun e => pairDist e = d)
  let P := (pairs I).filter (fun e => pairDist e = d)
  let F := fun z : Plane => (H.filter (fun h => dist z h = d)).image (fun h => s(z,h))
  have hdim := diam_union_interiors H I hinterior
  have hsub : Q ⊆ P ∪ I.biUnion F := by
    intro e he
    have he' := Finset.mem_filter.mp he
    induction e using Sym2.ind with
    | _ a b =>
      obtain ⟨ha, hb, hab⟩ := (mk_mem_pairs X a b).mp he'.1
      have habd : dist a b = d := he'.2
      rcases Finset.mem_union.mp ha with haH | haI <;>
        rcases Finset.mem_union.mp hb with hbH | hbI
      · exfalso
        apply hdH
        apply (mem_nonDiameterDistances H d).mpr
        refine ⟨⟨a, haH, b, hbH, hab, habd⟩, ?_⟩
        obtain ⟨_, hdlt, _⟩ := (ThreeInteriorCounting.mem_nonDiameterDistances_iff_positive X d).mp hd
        exact hdim ▸ hdlt
      · apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr
        refine ⟨b, hbI, Finset.mem_image.mpr ⟨a, ?_, Sym2.eq_swap⟩⟩
        exact Finset.mem_filter.mpr ⟨haH, (dist_comm b a).trans habd⟩
      · apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr
        exact ⟨a, haI, Finset.mem_image.mpr ⟨b, Finset.mem_filter.mpr ⟨hbH, habd⟩, rfl⟩⟩
      · apply Finset.mem_union_left
        exact Finset.mem_filter.mpr ⟨(mk_mem_pairs I a b).mpr ⟨haI, hbI, hab⟩, habd⟩
  obtain ⟨u, hu⟩ := Finset.card_pos.mp (show 0 < I.card by omega)
  have hr : 0 < ‖u‖ := norm_pos_iff.mpr (hoff u hu)
  have hnormI : ∀ z ∈ I, dist z (0 : Plane) = ‖u‖ := by
    intro z hz
    obtain ⟨g, hg⟩ := exists_stabilizer_map H I R hH hR hcircle hinterior hoff hq u z hu hz
    rw [dist_zero_right, ← hg, norm_rotate]
  have hPI : P.card ≤ 4 := by
    have hbound := chord_capacity I 0 ‖u‖ d hr hnormI
    exact hI ▸ hbound
  have hF : ∑ z ∈ I, (F z).card ≤ 8 := by
    calc
      _ ≤ ∑ z ∈ I, 2 := by
        apply Finset.sum_le_sum
        intro z hz
        calc
          _ ≤ (H.filter (fun h => dist z h = d)).card := Finset.card_image_le
          _ = 2 := (radial_saturation H I R hH hR hcircle hinterior hoff hq z hz).2 d hd
      _ = 8 := by simp [hI]
  change Q.card ≤ 12
  calc
    Q.card ≤ (P ∪ I.biUnion F).card := Finset.card_le_card hsub
    _ ≤ P.card + (I.biUnion F).card := Finset.card_union_le _ _
    _ ≤ P.card + ∑ z ∈ I, (F z).card := Nat.add_le_add_left Finset.card_biUnion_le _
    _ ≤ 12 := by omega

/-- For at least eight hull vertices the complete even lower-support branch
has an actual occurring nondiameter distance with inherited multiplicity at most
configuration size. Only the six-hull-vertex endpoint remains outside this theorem. -/
theorem exists_distance_of_eight_le_hull_card (H I : Finset Plane) (R : ℝ)
    (hH : 8 ≤ H.card) (heven : Even H.card) (hR : 0 < R)
    (hcircle : ∀ h ∈ H, ‖h‖ = R) (hI : I.card = 4)
    (hinterior : ∀ z ∈ I, z ∈ interior (convexHull ℝ (H : Set Plane)))
    (hoff : ∀ z ∈ I, z ≠ 0)
    (hq : 2 * (nonDiameterDistances (H ∪ I)).card = H.card) :
    (H ∪ I).card = H.card + 4 ∧ ∃ d : ℝ,
      0 < d ∧ d < Metric.diam ((H ∪ I : Finset Plane) : Set Plane) ∧
      (∃ a ∈ H ∪ I, ∃ b ∈ H ∪ I, dist a b = d) ∧
      1 ≤ multiplicity (H ∪ I) d ∧ multiplicity (H ∪ I) d ≤ H.card + 4 := by
  classical
  have hHsix : 6 ≤ H.card := by omega
  have hHne : H.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨horder, horbit⟩ := hull_is_full_stabilizer_orbit H I R hHsix hR hcircle hI hinterior hoff hq
  have hcardT := hull_card_eq_twice_support_add_two H R hHne hR hcircle (horder ▸ heven) horbit
  let S := nonDiameterDistances (H ∪ I)
  let T := nonDiameterDistances H
  have hTsub : T ⊆ S := by
    intro d hd
    obtain ⟨⟨a, ha, b, hb, hab, habd⟩, hdlt⟩ := (mem_nonDiameterDistances H d).mp hd
    apply (mem_nonDiameterDistances (H ∪ I) d).mpr
    refine ⟨⟨a, Finset.mem_union_left I ha, b, Finset.mem_union_left I hb, hab, habd⟩, ?_⟩
    rw [diam_union_interiors H I hinterior]
    exact hdlt
  have hcardlt : T.card < S.card := by change (nonDiameterDistances H).card < (nonDiameterDistances (H ∪ I)).card; omega
  obtain ⟨d, hdS, hdT⟩ := Finset.exists_mem_notMem_of_card_lt_card hcardlt
  obtain ⟨hdpos, hdlt, a, ha, b, hb, habd⟩ :=
    (ThreeInteriorCounting.mem_nonDiameterDistances_iff_positive (H ∪ I) d).mp hdS
  have hmultpos : 1 ≤ multiplicity (H ∪ I) d := by
    apply Finset.one_le_card.mpr
    exact ⟨s(a,b), Finset.mem_filter.mpr ⟨(mk_mem_pairs _ _ _).mpr
      ⟨ha, hb, fun heq => by rw [heq, dist_self] at habd; linarith⟩, habd⟩⟩
  have hbound := multiplicity_le_twelve_of_not_mem_hull_support H I R d hHsix hR hcircle hI hinterior hoff hq hdS hdT
  refine ⟨card_union_four_interiors H I R hR hcircle hI hinterior,
    d, hdpos, hdlt, ⟨a, ha, b, hb, habd⟩, hmultpos, ?_⟩
  omega

private theorem primitive_cubic_displacement (g : Rotation) (hg : g ^ 3 = 1)
    (hne : g ≠ 1) : ‖(g : ℂ) - 1‖ ^ 2 = 3 := by
  have hc : (g : ℂ) ^ 3 = 1 := by
    simpa only [Circle.coe_pow, Circle.coe_one] using congrArg (fun z : Rotation => (z : ℂ)) hg
  have hf : ((g : ℂ) - 1) * ((g : ℂ) ^ 2 + (g : ℂ) + 1) = 0 := by
    calc
      _ = (g : ℂ) ^ 3 - 1 := by ring
      _ = 0 := by rw [hc]; ring
  have hq : (g : ℂ) ^ 2 + (g : ℂ) + 1 = 0 := by
    rcases mul_eq_zero.mp hf with h | h
    · exact False.elim (hne (Circle.ext (sub_eq_zero.mp h)))
    · exact h
  have hr := re_eq_neg_half_of_quadratic g hq
  have hn := Circle.normSq_coe g
  rw [Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im] at hn ⊢
  nlinarith

/-- The six-vertex endpoint of the original lower-support branch is impossible.
A cubic rotation and the half-turn supply hull chord squares `3R²` and `R²`.
Antipodal radial complementarity forces four distinct squared support values,
contradicting the actual three-class support; no reflection-axis certificate is assumed. -/
theorem six_hull_lower_support_false (H I : Finset Plane) (R : ℝ)
    (hH : H.card = 6) (hR : 0 < R) (hcircle : ∀ h ∈ H, ‖h‖ = R)
    (hI : I.card = 4)
    (hinterior : ∀ z ∈ I, z ∈ interior (convexHull ℝ (H : Set Plane)))
    (hoff : ∀ z ∈ I, z ≠ 0)
    (hq : 2 * (nonDiameterDistances (H ∪ I)).card = H.card) : False := by
  classical
  have hHsix : 6 ≤ H.card := by omega
  have hHne : H.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨horder, _horbit⟩ := hull_is_full_stabilizer_orbit H I R hHsix hR hcircle hI hinterior hoff hq
  have horder6 : order H = 6 := horder.trans hH
  have heven : Even (order H) := horder6 ▸ (show Even 6 from ⟨3, rfl⟩)
  have hsym : ∀ x ∈ H, -x ∈ H := fun x hx =>
    (mem_iff_neg_mem_of_even_order H hHne hR hcircle heven x).mp hx
  have hdiam : Metric.diam ((H ∪ I : Finset Plane) : Set Plane) = 2 * R :=
    (diam_union_interiors H I hinterior).trans (antipodal_diam H R hHne hR hcircle hsym)
  letI := finite_stabilizer H hHne hR hcircle
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Stabilizer H) 3
    (show 3 ∣ Nat.card (Stabilizer H) by change 3 ∣ order H; rw [horder6]; decide)
  have hg1 : g.val ≠ 1 := by
    intro heq
    have hgOne : g = 1 := Subtype.ext heq
    rw [hgOne, orderOf_one] at hg
    norm_num at hg
  have hgCube : g.val ^ 3 = 1 := by
    have hp := pow_orderOf_eq_one g
    rw [hg] at hp
    exact congrArg Subtype.val hp
  obtain ⟨p, hp⟩ := hHne
  let a := rotate g.val p
  have ha : a ∈ H := (g.property p).mpr hp
  have hsq : dist a p ^ 2 = 3 * R ^ 2 := by
    rw [dist_rotate_self, mul_pow, primitive_cubic_displacement g.val hgCube hg1, hcircle p hp]
  have hsum := parallelogram_law_with_norm ℝ a p
  rw [hcircle a ha, hcircle p hp] at hsum
  have hsidesq : dist (-a) p ^ 2 = R ^ 2 := by
    have heq : -a - p = -(a + p) := by abel
    rw [dist_eq_norm, heq, norm_neg]
    rw [dist_eq_norm] at hsq
    nlinarith only [hsum, hsq]
  have hside : dist (-a) p = R := by
    nlinarith [dist_nonneg (x := -a) (y := p)]
  let S := nonDiameterDistances (H ∪ I)
  have hScard : S.card = 3 := by dsimp only [S]; omega
  have hSpos : ∀ d ∈ S, 0 < d := by
    intro d hd
    exact ((ThreeInteriorCounting.mem_nonDiameterDistances_iff_positive (H ∪ I) d).mp hd).1
  have hmemSide : R ∈ S := by
    apply (ThreeInteriorCounting.mem_nonDiameterDistances_iff_positive (H ∪ I) R).mpr
    refine ⟨hR, ?_, -a, Finset.mem_union_left I (hsym a ha), p, Finset.mem_union_left I hp, hside⟩
    rw [hdiam]
    linarith
  have hmemLong : dist a p ∈ S := by
    apply (ThreeInteriorCounting.mem_nonDiameterDistances_iff_positive (H ∪ I) _).mpr
    refine ⟨?_, ?_, a, Finset.mem_union_left I ha, p, Finset.mem_union_left I hp, rfl⟩
    · nlinarith [dist_nonneg (x := a) (y := p), sq_pos_of_pos hR]
    · rw [hdiam]
      nlinarith [dist_nonneg (x := a) (y := p), sq_pos_of_pos hR]
  obtain ⟨u, hu⟩ := Finset.card_pos.mp (show 0 < I.card by omega)
  have huPos : 0 < ‖u‖ := norm_pos_iff.mpr (hoff u hu)
  have huLt : ‖u‖ < R := by
    simpa only [dist_zero_right] using dist_center_lt_radius H 0 hR
      (by simpa only [dist_zero_right] using hcircle) (hinterior u hu)
  have hsat := radial_saturation H I R hHsix hR hcircle hinterior hoff hq u hu
  have hcomp : ∀ d ∈ S, ∃ e ∈ S, d ^ 2 + e ^ 2 = 2 * (R ^ 2 + ‖u‖ ^ 2) := by
    intro d hd
    change d ∈ nonDiameterDistances (H ∪ I) at hd
    rw [← hsat.1] at hd
    obtain ⟨b, hb, hbd⟩ := Finset.mem_image.mp hd
    refine ⟨dist u (-b), ?_, ?_⟩
    · change dist u (-b) ∈ nonDiameterDistances (H ∪ I)
      rw [← hsat.1]
      exact Finset.mem_image.mpr ⟨-b, hsym b hb, rfl⟩
    · have hpar := parallelogram_law_with_norm ℝ b u
      rw [hcircle b hb] at hpar
      have heq : u - -b = b + u := by abel
      rw [← hbd, dist_comm u b, dist_eq_norm, dist_eq_norm, heq]
      nlinarith only [hpar]
  obtain ⟨e, he, hsumE⟩ := hcomp R hmemSide
  obtain ⟨f, hf, hsumF⟩ := hcomp (dist a p) hmemLong
  have hRx : 0 < R ^ 2 := sq_pos_of_pos hR
  have hurSq : 0 < ‖u‖ ^ 2 := sq_pos_of_pos huPos
  have huLtSq : ‖u‖ ^ 2 < R ^ 2 := (sq_lt_sq₀ (norm_nonneg u) hR.le).mpr huLt
  have hfe : f ^ 2 < R ^ 2 := by nlinarith [hsq]
  have hRe : R ^ 2 < e ^ 2 := by nlinarith
  have helong : e ^ 2 < dist a p ^ 2 := by nlinarith [hsq]
  let T := S.image (fun d => d ^ 2)
  have hsubset : {f ^ 2, R ^ 2, e ^ 2, dist a p ^ 2} ⊆ T := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Finset.mem_image.mpr ⟨f, hf, rfl⟩
    · exact Finset.mem_image.mpr ⟨R, hmemSide, rfl⟩
    · exact Finset.mem_image.mpr ⟨e, he, rfl⟩
    · exact Finset.mem_image.mpr ⟨dist a p, hmemLong, rfl⟩
  have hfour : ({f ^ 2, R ^ 2, e ^ 2, dist a p ^ 2} : Finset ℝ).card = 4 := by
    have hflong := hfe.trans (hRe.trans helong)
    have hfE := hfe.trans hRe
    have hRlong := hRe.trans helong
    simp [ne_of_lt hfe, ne_of_lt hfE, ne_of_lt hflong,
      ne_of_lt hRe, ne_of_lt hRlong, ne_of_lt helong]
  have hle := Finset.card_le_card hsubset
  have hleT : T.card ≤ S.card := Finset.card_image_le
  omega

/-- In the even, all-off-center, four-interior lower-support branch, the actual
configuration has `n` points and an occurring positive nondiameter distance whose
loop-free unordered multiplicity lies between one and `n`. The hull has `n-4`
vertices, with `10 ≤ n` guarding the natural subtraction. This is only this branch,
not the full four-interior Erdős statement. -/
theorem exists_distance_of_even_lower_support (n : ℕ) (H I : Finset Plane) (R : ℝ)
    (hn : 10 ≤ n) (heven : Even n) (hH : H.card = n - 4)
    (hR : 0 < R) (hcircle : ∀ h ∈ H, ‖h‖ = R) (hI : I.card = 4)
    (hinterior : ∀ z ∈ I, z ∈ interior (convexHull ℝ (H : Set Plane)))
    (hoff : ∀ z ∈ I, z ≠ 0)
    (hq : 2 * (nonDiameterDistances (H ∪ I)).card = H.card) :
    (H ∪ I).card = n ∧ ∃ d : ℝ,
      0 < d ∧ d < Metric.diam ((H ∪ I : Finset Plane) : Set Plane) ∧
      (∃ a ∈ H ∪ I, ∃ b ∈ H ∪ I, a ≠ b ∧ dist a b = d) ∧
      1 ≤ multiplicity (H ∪ I) d ∧ multiplicity (H ∪ I) d ≤ n := by
  have hsize : H.card + 4 = n := by omega
  have hEvenH : Even H.card := by
    obtain ⟨k, hk⟩ := heven
    exact ⟨k - 2, by omega⟩
  have hHsix : 6 ≤ H.card := by omega
  by_cases hsix : H.card = 6
  · exact False.elim (six_hull_lower_support_false H I R hsix hR hcircle hI hinterior hoff hq)
  · have hHeight : 8 ≤ H.card := by
      obtain ⟨k, hk⟩ := hEvenH
      omega
    obtain ⟨hcard, d, hdpos, hdlt, ⟨a, ha, b, hb, habd⟩, hmultpos, hbound⟩ :=
      exists_distance_of_eight_le_hull_card H I R hHeight hEvenH hR hcircle hI hinterior hoff hq
    refine ⟨hcard.trans hsize, d, hdpos, hdlt, ⟨a, ha, b, hb, ?_, habd⟩, hmultpos, hsize ▸ hbound⟩
    intro heq
    rw [heq, dist_self] at habd
    linarith

/-- The unrestricted geometric family is jointly inhabited at `n=10`:
six distinct unit-circle hull points and four distinct nonzero ambient-interior
points give an actual ten-point union. This does not assert the lower-support
equality, which the six-vertex endpoint theorem proves impossible. -/
theorem original_geometry_family_nonempty : ∃ (n : ℕ) (H I : Finset Plane) (R : ℝ),
    10 ≤ n ∧ Even n ∧ H.card = n - 4 ∧ I.card = 4 ∧ 0 < R ∧
    (∀ h ∈ H, ‖h‖ = R) ∧
    (∀ z ∈ I, z ∈ interior (convexHull ℝ (H : Set Plane))) ∧
    (∀ z ∈ I, z ≠ 0) ∧ (H ∪ I).card = n := by
  classical
  obtain ⟨H, u, v, hcard, hcircle, _hext, hu, _hv, _huv⟩ := rational_circle_fixture
  have hinf : (interior (convexHull ℝ (H : Set Plane))).Infinite :=
    infinite_of_mem_nhds u (isOpen_interior.mem_nhds hu)
  have hinfOff := hinf.sdiff (Set.finite_singleton (0 : Plane))
  obtain ⟨I, hsub, hI⟩ := hinfOff.exists_subset_card_eq 4
  have hinterior : ∀ z ∈ I, z ∈ interior (convexHull ℝ (H : Set Plane)) := by
    intro z hz
    exact (hsub hz).1
  have hoff : ∀ z ∈ I, z ≠ 0 := by
    intro z hz
    simpa only [Set.mem_singleton_iff] using (hsub hz).2
  have hc : ∀ h ∈ H, ‖h‖ = (1 : ℝ) := by
    simpa only [dist_zero_right] using hcircle
  refine ⟨10, H, I, 1, by decide, ⟨5, by decide⟩, ?_, hI, by norm_num,
    hc, hinterior, hoff, ?_⟩
  · simpa using hcard
  · rw [card_union_four_interiors H I 1 (by norm_num) hc hI hinterior, hcard]

end

end Erdos132.FourInteriorLowerSupport
