import Erdos.Erdos132.FourInteriorOddTail
import Erdos.Erdos132.FiniteCircleCompletion
import Erdos.Erdos132.RobustProjectionGrid
import Erdos.Erdos132.RadialGridTransport

set_option autoImplicit false

open scoped Pointwise

namespace Erdos132.RobustCircleFamily

open TwoInteriorCircle FourInteriorLowerSupport CircleRotation

/-- Any number of distinct ambient-interior points adds its actual cardinality
 to the cyclic hull, without tagged copies or overlaps. -/
theorem card_union_interiors (H I : Finset Plane) (R : ℝ)
    (hR : 0 < R) (hcircle : ∀ h ∈ H, ‖h‖ = R)
    (hinterior : ∀ z ∈ I, z ∈ interior (convexHull ℝ (H : Set Plane))) :
    (H ∪ I).card = H.card + I.card := by
  classical
  have hdisjoint : Disjoint H I := by
    apply Finset.disjoint_left.mpr
    intro z hzH hzI
    exact ThreeInteriorCounting.interior_not_mem_circle H R z hR hcircle
      (hinterior z hzI) hzH
  exact Finset.card_union_of_disjoint hdisjoint

/-- At least two actual interior points ensure that one is not the center. -/
theorem exists_nonzero_of_two_le_card (I : Finset Plane) (hI : 2 ≤ I.card) :
    ∃ p ∈ I, p ≠ 0 := by
  classical
  by_contra hnone
  have hsub : I ⊆ {0} := by
    intro p hp
    have hp0 : p = 0 := by
      by_contra hne
      exact hnone ⟨p, hp, hne⟩
    simp [hp0]
  have hcard := Finset.card_le_card hsub
  simp only [Finset.card_singleton] at hcard
  omega

/-- Reserving one actual diameter pair gives twice the strict support cardinality
 at most the actual number of points minus two. -/
theorem twice_support_le_of_pair_budget (n q : ℕ) (hn : 2 ≤ n)
    (hbudget : q * (n + 1) + 1 ≤ n.choose 2) : 2 * q + 2 ≤ n := by
  have hchoose : 2 * n.choose 2 ≤ n * (n - 1) := by
    rw [Nat.choose_two_right]
    exact Nat.mul_div_le _ _
  have hb := (Nat.mul_le_mul_left 2 hbudget).trans hchoose
  have hsub : n - 1 + 1 = n := by omega
  by_contra hnot
  have hq : n - 1 ≤ 2 * q := by omega
  have hmul := Nat.mul_le_mul_right (n + 1) hq
  nlinarith

/-- The genuine contrary multiplicity branch gives a nonzero interior radial
 map of capacity two, at most `(k-2)/2` missing strict classes, and a double fiber.
 Both parities and center-present interior sets are allowed. -/
theorem contrary_radial_budget (N k : ℕ) (H I : Finset Plane) (R : ℝ)
    (hk : 2 ≤ k) (hN : k + 2 ≤ N) (hcard : H.card = N) (hI : I.card = k)
    (hR : 0 < R) (hcircle : ∀ h ∈ H, ‖h‖ = R)
    (hinterior : ∀ z ∈ I, z ∈ interior (convexHull ℝ (H : Set Plane)))
    (hlarge : ∀ d ∈ nonDiameterDistances (H ∪ I), N + k + 1 ≤ multiplicity (H ∪ I) d) :
    (H ∪ I).card = N + k ∧
    2 * (nonDiameterDistances (H ∪ I)).card + 2 ≤ N + k ∧
    ∃ p ∈ I, p ≠ 0 ∧ 0 < ‖p‖ ∧ ‖p‖ < R ∧
      H.image (fun h => dist p h) ⊆ nonDiameterDistances (H ∪ I) ∧
      (∀ d : ℝ, (H.filter fun h => dist p h = d).card ≤ 2) ∧
      (nonDiameterDistances (H ∪ I) \ H.image (fun h => dist p h)).card ≤ (k - 2) / 2 ∧
      ∃ a ∈ H, ∃ b ∈ H, a ≠ b ∧ dist p a = dist p b := by
  classical
  have hunion : (H ∪ I).card = N + k := by
    rw [card_union_interiors H I R hR hcircle hinterior, hcard, hI]
  have hbudget := nonDiameter_pair_budget (H ∪ I) (by omega)
    (by simpa only [hunion] using hlarge)
  have hq := twice_support_le_of_pair_budget (N + k) _ (by omega)
    (by simpa only [hunion] using hbudget)
  obtain ⟨p, hp, hp0⟩ := exists_nonzero_of_two_le_card I (by omega)
  have hmap := FourInteriorOddTail.radial_mem_union H I R (by omega) hR hcircle hinterior hp
  have hcap : ∀ d : ℝ, (H.filter fun h => dist p h = d).card ≤ 2 := by
    intro d
    simpa only [dist_comm] using radial_card_le_two H 0 p R d
      (by simpa only [dist_zero_right] using hcircle) hp0
  have himage : H.image (fun h => dist p h) ⊆ nonDiameterDistances (H ∪ I) := by
    intro d hd
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hd
    exact hmap h hh
  have hlower := Finset.card_le_mul_card_image_of_maps_to
    (fun h hh => Finset.mem_image.mpr ⟨h, hh, rfl⟩ :
      ∀ h ∈ H, dist p h ∈ H.image (fun h => dist p h)) 2 (fun d _ => hcap d)
  rw [hcard] at hlower
  have hmissing : (nonDiameterDistances (H ∪ I) \ H.image (fun h => dist p h)).card ≤ (k - 2) / 2 := by
    have hc := Finset.card_sdiff_add_card_eq_card himage
    omega
  have hdouble : ∃ a ∈ H, ∃ b ∈ H, a ≠ b ∧ dist p a = dist p b := by
    by_contra hnone
    have hinj : Set.InjOn (fun h => dist p h) (H : Set Plane) := by
      intro a ha b hb heq
      by_contra hab
      exact hnone ⟨a, ha, b, hb, hab, heq⟩
    have hc := Finset.card_image_of_injOn hinj
    have hu := Finset.card_le_card himage
    rw [hcard] at hc
    omega
  refine ⟨hunion, hq, p, hp, hp0, norm_pos_iff.mpr hp0, ?_, himage, hcap, hmissing, hdouble⟩
  simpa only [dist_zero_right] using dist_center_lt_radius H 0 hR
    (by simpa only [dist_zero_right] using hcircle) (hinterior p hp)

/-- At the original quadratic threshold, the contrary branch supplies a dense
 finite circle subgroup completion, actual strict completion chords, and the
 radial missing-class budget needed by `RadialGridTransport`. This is a derived
 obstruction, not a certificate assumed of the input configuration. -/
theorem contrary_completion (N k : ℕ) (H I : Finset Plane) (R : ℝ)
    (hk : 2 ≤ k) (hN : 1000 * (k + 1) ^ 2 ≤ N)
    (hcard : H.card = N) (hI : I.card = k)
    (hR : 0 < R) (hcircle : ∀ h ∈ H, ‖h‖ = R)
    (hinterior : ∀ z ∈ I, z ∈ interior (convexHull ℝ (H : Set Plane)))
    (hlarge : ∀ d ∈ nonDiameterDistances (H ∪ I), N + k + 1 ≤ multiplicity (H ∪ I) d) :
    ∃ m : ℕ, N ≤ m ∧ m ≤ N + k + 1 ∧ 3 ≤ m ∧
    ∃ v ∈ H, ∃ p ∈ I, p ≠ 0 ∧ 0 < ‖p‖ ∧ ‖p‖ < R ∧
      (∀ h ∈ H, ∃ j : Fin m,
        h = rotate (Circle.exp (2 * Real.pi * (j : ℝ) / (m : ℝ))) v) ∧
      (∃ a ∈ H, ∃ b ∈ H, a ≠ b ∧ dist p a = dist p b) ∧
      (nonDiameterDistances (H ∪ I) \ H.image (fun h => dist p h)).card ≤ (k - 2) / 2 ∧
      (∀ ell : ℕ, 1 ≤ ell → ell < m / 2 →
        2 * R * Real.sin (Real.pi * (ell : ℝ) / (m : ℝ)) ∈ nonDiameterDistances (H ∪ I)) ∧
      Metric.diam ((H ∪ I : Finset Plane) : Set Plane) =
        2 * R * Real.sin (Real.pi * ((m / 2 : ℕ) : ℝ) / (m : ℝ)) := by
  classical
  have hKsq : k + 1 ≤ (k + 1) ^ 2 := by nlinarith
  have hNk : k + 2 ≤ N := by omega
  have hNlarge : 2 * (k + 1) < N := by omega
  obtain ⟨_, hq, p, hp, hp0, hpnorm, hpR, _, _, hmissing, hdouble⟩ :=
    contrary_radial_budget N k H I R hk hNk hcard hI hR hcircle hinterior hlarge
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < H.card)
  obtain ⟨A, hOne, hAcard, hA⟩ := exists_hull_coefficients H R v hR hcircle hv
  have hsub : A ⊆ A / A := by
    intro a ha
    exact Finset.mem_div.mpr ⟨a, ha, 1, hOne, div_one a⟩
  have hlow := Finset.card_le_card hsub
  have hbound := quotient_support_card_le H I R v A hR hcircle hv hOne hA
  have hupper : (A / A).card ≤ N + k + 1 := by omega
  have hsmall : 2 * (A / A).card < 3 * A.card := by omega
  obtain ⟨K, hK⟩ := FourInteriorOddTail.exists_subgroup_of_small_quotient A ⟨1, hOne⟩ hsmall
  have hcarrier : (K : Set Rotation) = ((A / A : Finset Rotation) : Set Rotation) := by
    ext g
    exact hK g
  have hfinite : (K : Set Rotation).Finite := by
    rw [hcarrier]
    exact (A / A).finite_toSet
  let m := (A / A).card
  have hm : 3 ≤ m := by dsimp only [m]; omega
  have hcardK : Nat.card K = m := by
    change Nat.card ↥(K : Set Rotation) = m
    rw [hcarrier]
    simp only [Nat.card_coe_set_eq, Set.ncard_coe_finset, m]
  have horbit : ∀ h ∈ H, ∃ g : K, h = rotate g.val v := by
    intro h hh
    obtain ⟨g, hg⟩ := exists_rotation_map hR (hcircle v hv) (hcircle h hh)
    have hgA : g ∈ A := (hA g).mpr (hg ▸ hh)
    exact ⟨⟨g, (hK g).mpr (hsub hgA)⟩, hg.symm⟩
  have hdense : m < 2 * H.card := by dsimp only [m]; omega
  have hc := FiniteCircleCompletion.finite_circle_completion m hm K hfinite hcardK
    R hR v (hcircle v hv) H horbit hdense
  have hoccupied : ∀ h ∈ H, ∃ j : Fin m,
      h = rotate (Circle.exp (2 * Real.pi * (j : ℝ) / (m : ℝ))) v := by
    intro h hh
    obtain ⟨g, hg⟩ := horbit h hh
    obtain ⟨j, hj⟩ := (hc.1 g.val).mp g.property
    exact ⟨j, by rw [hj]; exact hg⟩
  refine ⟨m, by dsimp only [m]; omega, hupper, hm, v, hv, p, hp, hp0,
    hpnorm, hpR, hoccupied, hdouble, hmissing, ?_, ?_⟩
  · intro ell hell htop
    obtain ⟨a, ha, b, hb, hab, hd⟩ := hc.2.2.2.1 ell hell htop.le
    have hstrict := (hc.2.2.2.2.2 ell hell htop).2
    apply (mem_nonDiameterDistances _ _).mpr
    refine ⟨⟨a, Finset.mem_union_left I ha, b, Finset.mem_union_left I hb, hab, hd⟩, ?_⟩
    rw [diam_union_interiors H I hinterior]
    exact hstrict
  · rw [diam_union_interiors H I hinterior]
    exact hc.2.2.2.2.1

/-- Positive-radius chord lengths are injective on the strict half-polygon
 index range; this counts distinct lengths rather than vertex copies. -/
theorem strict_chord_injOn (m : ℕ) (hm : 3 ≤ m) (R : ℝ) (hR : 0 < R) :
    Set.InjOn (fun ell : ℕ => 2 * R * Real.sin (Real.pi * (ell : ℝ) / (m : ℝ)))
      (Finset.Icc 1 (m / 2 - 1) : Set ℕ) := by
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hangle : ∀ ell ∈ (Finset.Icc 1 (m / 2 - 1) : Finset ℕ),
      Real.pi * (ell : ℝ) / (m : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    intro ell hell
    have hb := Finset.mem_Icc.mp hell
    have hhalf : 2 * ell ≤ m := by omega
    have hhalfR : 2 * (ell : ℝ) ≤ (m : ℝ) := by exact_mod_cast hhalf
    constructor
    · have hnonneg : 0 ≤ Real.pi * (ell : ℝ) / (m : ℝ) := by positivity
      linarith [Real.pi_pos]
    · apply (div_le_iff₀ hmpos).mpr
      nlinarith [Real.pi_pos]
  intro a ha b hb heq
  have hsin : Real.sin (Real.pi * (a : ℝ) / (m : ℝ)) =
      Real.sin (Real.pi * (b : ℝ) / (m : ℝ)) := by nlinarith
  have hang := Real.strictMonoOn_sin.injOn (hangle a ha) (hangle b hb) hsin
  have hcast : (a : ℝ) = (b : ℝ) := by
    have hmul := (div_left_inj' (ne_of_gt hmpos)).mp hang
    nlinarith [Real.pi_pos]
  exact_mod_cast hcast

/-- Intermediary finite counting bridge: a shared-axis transport implication
 sends every unmatched strict chord injectively into the actual missing support.
 This premise is discharged by geometric transport in the original consumer. -/
theorem unmatched_card_le_missing_of_transport (m : ℕ) (hm : 3 ≤ m)
    (R : ℝ) (hR : 0 < R) (H : Finset Plane) (p : Plane) (S : Finset ℝ)
    (t : ℤ) (r : ℝ)
    (hsupport : ∀ ell : ℕ, 1 ≤ ell → ell < m / 2 →
      2 * R * Real.sin (Real.pi * (ell : ℝ) / (m : ℝ)) ∈ S)
    (htransport : ∀ h ∈ H, ∀ ell : ℕ, 1 ≤ ell → ell < m / 2 →
      dist p h = 2 * R * Real.sin (Real.pi * (ell : ℝ) / (m : ℝ)) →
      RobustProjectionGrid.Matched m t r ell) :
    (RobustProjectionGrid.unmatched m t r).card ≤
      (S \ H.image (fun h => dist p h)).card := by
  classical
  apply Finset.card_le_card_of_injOn
    (fun ell : ℕ => 2 * R * Real.sin (Real.pi * (ell : ℝ) / (m : ℝ)))
  · intro ell hell
    obtain ⟨hindex, hnot⟩ := Finset.mem_filter.mp hell
    have hb := Finset.mem_Icc.mp hindex
    have htop : ell < m / 2 := by omega
    apply Finset.mem_sdiff.mpr
    refine ⟨hsupport ell hb.1 htop, ?_⟩
    intro himage
    obtain ⟨h, hh, heq⟩ := Finset.mem_image.mp himage
    exact hnot (htransport h hh ell hb.1 htop heq)
  · intro a ha b hb heq
    exact strict_chord_injOn m hm R hR
      (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 heq

/-- Original arbitrary-k inputs yield either the actual occurring strict distance
 witness or a fully derived completion with a bounded radial support deficit.
 No analytic certificate is assumed; eliminating the second branch is the named
 downstream obligation of `RadialGridTransport` and `RobustProjectionGrid`. -/
theorem original_input_reduction_zero (N k : ℕ) (H I : Finset Plane) (R : ℝ)
    (hk : 2 ≤ k) (hN : 1000 * (k + 1) ^ 2 ≤ N)
    (hcard : H.card = N) (hI : I.card = k)
    (hR : 0 < R) (hcircle : ∀ h ∈ H, ‖h‖ = R)
    (hinterior : ∀ z ∈ I, z ∈ interior (convexHull ℝ (H : Set Plane))) :
    (H ∪ I).card = N + k ∧
    ((∃ d : ℝ, 0 < d ∧ d < Metric.diam ((H ∪ I : Finset Plane) : Set Plane) ∧
      1 ≤ multiplicity (H ∪ I) d ∧ multiplicity (H ∪ I) d ≤ N + k) ∨
    ∃ m : ℕ, N ≤ m ∧ m ≤ N + k + 1 ∧ 3 ≤ m ∧
    ∃ v ∈ H, ∃ p ∈ I, p ≠ 0 ∧ 0 < ‖p‖ ∧ ‖p‖ < R ∧
      (∀ h ∈ H, ∃ j : Fin m,
        h = rotate (Circle.exp (2 * Real.pi * (j : ℝ) / (m : ℝ))) v) ∧
      (∃ a ∈ H, ∃ b ∈ H, a ≠ b ∧ dist p a = dist p b) ∧
      (nonDiameterDistances (H ∪ I) \ H.image (fun h => dist p h)).card ≤ (k - 2) / 2 ∧
      (∀ ell : ℕ, 1 ≤ ell → ell < m / 2 →
        2 * R * Real.sin (Real.pi * (ell : ℝ) / (m : ℝ)) ∈ nonDiameterDistances (H ∪ I)) ∧
      Metric.diam ((H ∪ I : Finset Plane) : Set Plane) =
        2 * R * Real.sin (Real.pi * ((m / 2 : ℕ) : ℝ) / (m : ℝ))) := by
  classical
  have hunion : (H ∪ I).card = N + k := by
    rw [card_union_interiors H I R hR hcircle hinterior, hcard, hI]
  refine ⟨hunion, ?_⟩
  by_cases hwitness : ∃ d : ℝ,
      0 < d ∧ d < Metric.diam ((H ∪ I : Finset Plane) : Set Plane) ∧
      1 ≤ multiplicity (H ∪ I) d ∧ multiplicity (H ∪ I) d ≤ N + k
  · exact Or.inl hwitness
  · apply Or.inr
    have hlarge : ∀ d ∈ nonDiameterDistances (H ∪ I), N + k + 1 ≤ multiplicity (H ∪ I) d := by
      intro d hd
      obtain ⟨⟨a, ha, b, hb, hab, habd⟩, hlt⟩ := (mem_nonDiameterDistances _ d).mp hd
      have hpos : 0 < d := habd ▸ dist_pos.mpr hab
      have hmult : 1 ≤ multiplicity (H ∪ I) d := by
        apply Finset.card_pos.mpr
        exact ⟨s(a,b), Finset.mem_filter.mpr
          ⟨(mk_mem_pairs _ a b).mpr ⟨ha, hb, hab⟩, habd⟩⟩
      have hnot : ¬ multiplicity (H ∪ I) d ≤ N + k := by
        intro hbound
        exact hwitness ⟨d, hpos, hlt, hmult, hbound⟩
      omega
    exact contrary_completion N k H I R hk hN hcard hI hR hcircle hinterior hlarge

/-- Translation of the original arbitrary-center, arbitrary-positive-radius
 family preserves the actual witness and produces the same dense completion
 obstruction in translated coordinates. The conclusion is still a reduction,
 not the final family theorem until its completion branch is eliminated. -/
theorem original_input_reduction (N k : ℕ) (H I : Finset Plane) (O : Plane) (R : ℝ)
    (hk : 2 ≤ k) (hN : 1000 * (k + 1) ^ 2 ≤ N)
    (hcard : H.card = N) (hI : I.card = k)
    (hR : 0 < R) (hcircle : ∀ h ∈ H, dist h O = R)
    (hinterior : ∀ z ∈ I, z ∈ interior (convexHull ℝ (H : Set Plane))) :
    let H0 := H.image (fun h => h - O)
    let I0 := I.image (fun p => p - O)
    (H ∪ I).card = N + k ∧
    ((∃ d : ℝ, 0 < d ∧ d < Metric.diam ((H ∪ I : Finset Plane) : Set Plane) ∧
      1 ≤ multiplicity (H ∪ I) d ∧ multiplicity (H ∪ I) d ≤ N + k) ∨
    ∃ m : ℕ, N ≤ m ∧ m ≤ N + k + 1 ∧ 3 ≤ m ∧
    ∃ v ∈ H0, ∃ p ∈ I0, p ≠ 0 ∧ 0 < ‖p‖ ∧ ‖p‖ < R ∧
      (∀ h ∈ H0, ∃ j : Fin m,
        h = rotate (Circle.exp (2 * Real.pi * (j : ℝ) / (m : ℝ))) v) ∧
      (∃ a ∈ H0, ∃ b ∈ H0, a ≠ b ∧ dist p a = dist p b) ∧
      (nonDiameterDistances (H0 ∪ I0) \ H0.image (fun h => dist p h)).card ≤ (k - 2) / 2 ∧
      (∀ ell : ℕ, 1 ≤ ell → ell < m / 2 →
        2 * R * Real.sin (Real.pi * (ell : ℝ) / (m : ℝ)) ∈ nonDiameterDistances (H0 ∪ I0)) ∧
      Metric.diam ((H0 ∪ I0 : Finset Plane) : Set Plane) =
        2 * R * Real.sin (Real.pi * ((m / 2 : ℕ) : ℝ) / (m : ℝ))) := by
  classical
  let f : Plane → Plane := fun h => h - O
  have hf : Isometry f := fun a b => by simp [f, edist_dist]
  have hH0 : (H.image f).card = N :=
    (Finset.card_image_of_injective H hf.injective).trans hcard
  have hI0 : (I.image f).card = k :=
    (Finset.card_image_of_injective I hf.injective).trans hI
  have hcircle0 : ∀ h ∈ H.image f, ‖h‖ = R := by
    intro h hh
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hh
    exact hcircle a ha
  have hinterior0 : ∀ p ∈ I.image f,
      p ∈ interior (convexHull ℝ ((H.image f : Finset Plane) : Set Plane)) := by
    intro p hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    exact sub_mem_interior_hull H O a (hinterior a ha)
  have hr := original_input_reduction_zero N k (H.image f) (I.image f) R
    hk hN hH0 hI0 hR hcircle0 hinterior0
  have himage : H.image f ∪ I.image f = (H ∪ I).image f :=
    (Finset.image_union (f := f) H I).symm
  have hunion : (H ∪ I).card = N + k := by
    rw [himage, Finset.card_image_of_injective _ hf.injective] at hr
    exact hr.1
  refine ⟨hunion, ?_⟩
  rcases hr.2 with hwitness | hobstruction
  · obtain ⟨d, hpos, hlt, hmult, hbound⟩ := hwitness
    rw [himage, multiplicity_image_isometry _ f hf] at hmult hbound
    rw [himage, Finset.coe_image, hf.diam_image] at hlt
    exact Or.inl ⟨d, hpos, hlt, hmult, hbound⟩
  · exact Or.inr hobstruction

/-- The original center-zero circle family has an actual positive strict
 subdiameter distance occurring between one and N+k unordered distinct pairs. -/
theorem original_circle_family_zero (N k : ℕ) (H I : Finset Plane) (R : ℝ)
    (hk : 2 ≤ k) (hN : 1000 * (k + 1) ^ 2 ≤ N)
    (hcard : H.card = N) (hI : I.card = k)
    (hR : 0 < R) (hcircle : ∀ h ∈ H, ‖h‖ = R)
    (hinterior : ∀ z ∈ I, z ∈ interior (convexHull ℝ (H : Set Plane))) :
    (H ∪ I).card = N + k ∧
    ∃ d : ℝ, 0 < d ∧ d < Metric.diam ((H ∪ I : Finset Plane) : Set Plane) ∧
      1 ≤ multiplicity (H ∪ I) d ∧ multiplicity (H ∪ I) d ≤ N + k := by
  classical
  obtain ⟨hunion, hbranches⟩ := original_input_reduction_zero N k H I R
    hk hN hcard hI hR hcircle hinterior
  refine ⟨hunion, ?_⟩
  rcases hbranches with hwitness | hobstruction
  · exact hwitness
  · obtain ⟨m, hNm, _, hm, v, hvH, p, _, _, hp, hpR,
        hoccupied, hdouble, hmissing, hsupport, _⟩ := hobstruction
    obtain ⟨a, ha, b, hb, hab, heq⟩ := hdouble
    have hcanonical : ∀ h ∈ H, ∃ j : Fin m,
        RadialGridTransport.canonicalVertex m v j = h := by
      intro h hh
      obtain ⟨j, hj⟩ := hoccupied h hh
      exact ⟨j, hj.symm⟩
    obtain ⟨t, _, hr0, hr1, htransport⟩ :=
      RadialGridTransport.occupied_radial_grid_transport m hm R hR v p
        (hcircle v hvH) hp hpR H hcanonical a b ha hb hab heq
    have hfinite := unmatched_card_le_missing_of_transport m hm R hR H p
      (nonDiameterDistances (H ∪ I)) t (‖p‖ / R) hsupport (by
        intro h hh ell hlo hhi hd
        obtain ⟨j, hj⟩ := hcanonical h hh
        refine ⟨j.val, Finset.mem_range.mpr j.isLt, ?_⟩
        exact (htransport j ell hhi.le).mp (by simpa only [hj] using hd))
    have hbound := hfinite.trans hmissing
    have hmore := RobustProjectionGrid.more_than_budget_unmatched k m t (‖p‖ / R)
      hk (hN.trans hNm) hr0 hr1
    exact False.elim (Nat.not_lt_of_ge hbound hmore)

/-- For arbitrary center and positive radius, the actual union has N+k points
 and an occurring positive strict subdiameter distance of multiplicity 1..N+k.
 No completion, spectral, radial, or symmetry certificate is assumed. -/
theorem original_circle_family (N k : ℕ) (H I : Finset Plane) (O : Plane) (R : ℝ)
    (hk : 2 ≤ k) (hN : 1000 * (k + 1) ^ 2 ≤ N)
    (hcard : H.card = N) (hI : I.card = k)
    (hR : 0 < R) (hcircle : ∀ h ∈ H, dist h O = R)
    (hinterior : ∀ z ∈ I, z ∈ interior (convexHull ℝ (H : Set Plane))) :
    (H ∪ I).card = N + k ∧
    ∃ d : ℝ, 0 < d ∧ d < Metric.diam ((H ∪ I : Finset Plane) : Set Plane) ∧
      1 ≤ multiplicity (H ∪ I) d ∧ multiplicity (H ∪ I) d ≤ N + k := by
  classical
  let f : Plane → Plane := fun h => h - O
  have hf : Isometry f := fun a b => by simp [f, edist_dist]
  have hH0 : (H.image f).card = N :=
    (Finset.card_image_of_injective H hf.injective).trans hcard
  have hI0 : (I.image f).card = k :=
    (Finset.card_image_of_injective I hf.injective).trans hI
  have hcircle0 : ∀ h ∈ H.image f, ‖h‖ = R := by
    intro h hh
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hh
    exact hcircle a ha
  have hinterior0 : ∀ p ∈ I.image f,
      p ∈ interior (convexHull ℝ ((H.image f : Finset Plane) : Set Plane)) := by
    intro p hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    exact sub_mem_interior_hull H O a (hinterior a ha)
  obtain ⟨hunion0, d, hpos, hlt, hmult, hbound⟩ :=
    original_circle_family_zero N k (H.image f) (I.image f) R
      hk hN hH0 hI0 hR hcircle0 hinterior0
  have himage : H.image f ∪ I.image f = (H ∪ I).image f :=
    (Finset.image_union (f := f) H I).symm
  rw [himage, Finset.card_image_of_injective _ hf.injective] at hunion0
  rw [himage, multiplicity_image_isometry _ f hf] at hmult hbound
  rw [himage, Finset.coe_image, hf.diam_image] at hlt
  exact ⟨hunion0, d, hpos, hlt, hmult, hbound⟩


/-- A concrete circle family above the original threshold jointly satisfies all
 geometric hypotheses, including two distinct ambient interiors and the center.
 The fixture uses genuine sets and applies the full theorem to the same objects. -/
theorem original_geometry_fixture_application :
    ∃ (N : ℕ) (H I : Finset Plane), 1000 * (2 + 1) ^ 2 ≤ N ∧ H.card = N ∧ I.card = 2 ∧
      (0 : Plane) ∈ I ∧ (∀ h ∈ H, ‖h‖ = 5) ∧
      (∀ p ∈ I, p ∈ interior (convexHull ℝ (H : Set Plane))) ∧
      (H ∪ I).card = N + 2 ∧
      ∃ d : ℝ, 0 < d ∧ d < Metric.diam ((H ∪ I : Finset Plane) : Set Plane) ∧
        1 ≤ multiplicity (H ∪ I) d ∧ multiplicity (H ∪ I) d ≤ N + 2 := by
  classical
  let v : Plane := WithLp.toLp 2 ![5, 0]
  have hv : ‖v‖ = (5 : ℝ) := by
    norm_num [v, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  have hv0 : v ≠ 0 := ne_zero_of_norm_eq (by norm_num) hv
  let Q : ZMod 9000 → Plane := fun j => rotate (ZMod.toCircle j) v
  have hQinj : Function.Injective Q :=
    (rotate_coeff_injective v hv0).comp ZMod.injective_toCircle
  let C := Finset.univ.image Q
  have hCcard : C.card = 9000 := by
    rw [Finset.card_image_of_injective _ hQinj]
    simp
  let a : Plane := WithLp.toLp 2 ![3, 4]
  let b : Plane := WithLp.toLp 2 ![-3, 4]
  let c : Plane := WithLp.toLp 2 ![3, -4]
  let d : Plane := WithLp.toLp 2 ![-3, -4]
  let H : Finset Plane := C ∪ {a, b, c, d}
  let p : Plane := WithLp.toLp 2 ![1, 0]
  let I : Finset Plane := {0, p}
  have hN : 1000 * (2 + 1) ^ 2 ≤ H.card := by
    have hsub : C ⊆ H := Finset.subset_union_left
    have hbound := Finset.card_le_card hsub
    omega
  have hI : I.card = 2 := by
    norm_num [I, p, Finset.card_insert_of_notMem, WithLp.ext_iff, funext_iff, Fin.forall_fin_two]
  have hcircle : ∀ x ∈ H, ‖x‖ = 5 := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxC | hxS
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hxC
      exact (norm_rotate _ v).trans hv
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hxS
      rcases hxS with rfl | rfl | rfl | rfl <;>
        norm_num [a, b, c, d, EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.sqrt_eq_iff_mul_self_eq]
  have hcorners : ∀ u ∈ ({-3, 3} : Finset ℝ), ∀ w ∈ ({-4, 4} : Finset ℝ),
      WithLp.toLp 2 ![u, w] ∈ H := by
    intro u hu w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hw
    rcases hu with rfl | rfl <;> rcases hw with rfl | rfl <;> simp [H, a, b, c, d]
  have hinterior : ∀ x ∈ I, x ∈ interior (convexHull ℝ (H : Set Plane)) := by
    intro x hx
    apply CircleFixtures.rectangle_mem_interior H (r := 3) (s := 4)
      (by norm_num) (by norm_num) hcorners
    · simp only [I, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> norm_num [p]
    · simp only [I, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> norm_num [p]
  have hresult := original_circle_family H.card 2 H I 0 5 (by decide) hN rfl hI
    (by norm_num) (by simpa only [dist_zero_right] using hcircle) hinterior
  exact ⟨H.card, H, I, hN, rfl, hI, by simp [I], hcircle, hinterior, hresult⟩

example : 2 * (5 : ℕ) + 2 ≤ 12 :=
  twice_support_le_of_pair_budget 12 5 (by decide) (by decide)

example : ∃ p ∈ ({(0 : Plane), WithLp.toLp 2 ![1, 0]} : Finset Plane), p ≠ 0 := by
  apply exists_nonzero_of_two_le_card
  norm_num [Finset.card_insert_of_notMem, WithLp.ext_iff, funext_iff, Fin.forall_fin_two]

example : Set.InjOn
    (fun ell : ℕ => 2 * (1 : ℝ) * Real.sin (Real.pi * (ell : ℝ) / (4 : ℝ)))
    (Finset.Icc 1 (4 / 2 - 1) : Set ℕ) :=
  strict_chord_injOn 4 (by decide) 1 (by norm_num)

example : (RobustProjectionGrid.unmatched 4 0 0).card ≤
    (({2 * Real.sin (Real.pi / 4)} : Finset ℝ) \
      ({(0 : Plane)} : Finset Plane).image (fun h => dist (0 : Plane) h)).card := by
  apply unmatched_card_le_missing_of_transport 4 (by decide) 1 (by norm_num)
  · intro ell hlo hhi
    have hell : ell = 1 := by omega
    subst ell
    simp
  · intro h hh ell hlo hhi heq
    have hh0 : h = 0 := Finset.mem_singleton.mp hh
    have hell : ell = 1 := by omega
    subst h
    subst ell
    have hs : 0 < Real.sin (Real.pi / 4) := by
      rw [Real.sin_pi_div_four]
      positivity
    norm_num at heq

end Erdos132.RobustCircleFamily
