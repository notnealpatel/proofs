import Sorry.Erdos.Erdos132.FourInteriorLowerSupport
import Erdos.Erdos132.CircleFixtures

set_option autoImplicit false

open scoped BigOperators Pointwise

namespace Erdos132.FourInteriorOddTail

open TwoInteriorCircle FourInteriorLowerSupport CircleRotation

noncomputable section

attribute [local instance] Classical.decEq

/-- A four-point set has an off-center point, even when it contains the center. -/
theorem exists_nonzero_of_card_four (I : Finset Plane) (hI : I.card = 4) :
    ∃ p ∈ I, p ≠ 0 := by
  classical
  have herase : 0 < (I.erase 0).card := by
    have hbound : I.card ≤ (I.erase 0).card + 1 := by
      calc
        I.card ≤ (insert 0 (I.erase 0)).card := Finset.card_le_card (by
          intro x hx
          by_cases hx0 : x = 0
          · simp [hx0]
          · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hx0, hx⟩))
        _ ≤ (I.erase 0).card + 1 := Finset.card_insert_le _ _
    omega
  obtain ⟨p, hp⟩ := Finset.card_pos.mp herase
  exact ⟨p, (Finset.mem_erase.mp hp).2, (Finset.mem_erase.mp hp).1⟩

/-- All radial edges from any actual interior point occur strictly below the actual
union diameter; the assertion also holds for the center. -/
theorem radial_mem_union (H I : Finset Plane) (R : ℝ)
    (hH : 2 ≤ H.card) (hR : 0 < R) (hcircle : ∀ h ∈ H, ‖h‖ = R)
    (hinterior : ∀ z ∈ I, z ∈ interior (convexHull ℝ (H : Set Plane)))
    {p : Plane} (hp : p ∈ I) :
    ∀ h ∈ H, dist p h ∈ nonDiameterDistances (H ∪ I) := by
  intro h hh
  have hpH := ThreeInteriorCounting.interior_not_mem_circle H R p hR hcircle
    (hinterior p hp)
  apply (mem_nonDiameterDistances _ _).mpr
  refine ⟨⟨p, Finset.mem_union_right H hp, h, Finset.mem_union_left I hh,
    fun heq => hpH (heq.symm ▸ hh), rfl⟩, ?_⟩
  rw [diam_union_interiors H I hinterior]
  exact dist_lt_diam_hull H hH (hinterior p hp) (subset_convexHull ℝ _ hh)

/-- Odd hull order, radial capacity, and the actual unordered-pair budget force
exactly `(N+1)/2` nondiameter classes in the four-interior contrary branch. -/
theorem odd_four_support_of_budget (N q : ℕ) (hN : 15 ≤ N) (hodd : Odd N)
    (hlower : N ≤ 2 * q)
    (hbudget : q * (N + 5) + 1 ≤ (N + 4).choose 2) :
    2 * q = N + 1 := by
  have hchoose : 2 * (N + 4).choose 2 ≤ (N + 4) * (N + 3) := by
    rw [Nat.choose_two_right]
    have hsub : N + 4 - 1 = N + 3 := by omega
    rw [hsub]
    exact Nat.mul_div_le _ _
  have hbudget2 := (Nat.mul_le_mul_left 2 hbudget).trans hchoose
  have hupper : 2 * q < N + 3 := by
    by_contra h
    have hmul := Nat.mul_le_mul_right (N + 5) (le_of_not_gt h)
    nlinarith
  rcases hodd with ⟨k, hk⟩
  omega

/-- Under the genuine contrary multiplicity assumption, original center-allowed
geometry supplies one nonzero strict interior, exact support size, and the whole
support on that point's radial edges. No completion or analytic premise is used. -/
theorem contrary_radial_support (N : ℕ) (H I : Finset Plane) (R : ℝ)
    (hN : 15 ≤ N) (hodd : Odd N) (hcard : H.card = N) (hI : I.card = 4)
    (hR : 0 < R) (hcircle : ∀ h ∈ H, ‖h‖ = R)
    (hinterior : ∀ z ∈ I, z ∈ interior (convexHull ℝ (H : Set Plane)))
    (hlarge : ∀ d ∈ nonDiameterDistances (H ∪ I), N + 5 ≤ multiplicity (H ∪ I) d) :
    (H ∪ I).card = N + 4 ∧
    2 * (nonDiameterDistances (H ∪ I)).card = N + 1 ∧
    ∃ p ∈ I, p ≠ 0 ∧ 0 < ‖p‖ ∧ ‖p‖ < R ∧
      H.image (fun h => dist p h) = nonDiameterDistances (H ∪ I) ∧
      (∀ d ∈ nonDiameterDistances (H ∪ I), (H.filter fun h => dist p h = d).card ≤ 2) := by
  classical
  have hunion : (H ∪ I).card = N + 4 := by
    rw [card_union_four_interiors H I R hR hcircle hI hinterior, hcard]
  obtain ⟨p, hp, hp0⟩ := exists_nonzero_of_card_four I hI
  have hmap := radial_mem_union H I R (by omega) hR hcircle hinterior hp
  have hcap : ∀ d ∈ nonDiameterDistances (H ∪ I),
      (H.filter fun h => dist p h = d).card ≤ 2 := by
    intro d _hd
    simpa only [dist_comm] using radial_card_le_two H 0 p R d
      (by simpa only [dist_zero_right] using hcircle) hp0
  have hlower := Finset.card_le_mul_card_image_of_maps_to hmap 2 hcap
  have hbudget := nonDiameter_pair_budget (H ∪ I) (by omega)
    (by simpa only [hunion, Nat.add_assoc] using hlarge)
  have hq : 2 * (nonDiameterDistances (H ∪ I)).card = N + 1 :=
    odd_four_support_of_budget N _ hN hodd (by simpa only [hcard] using hlower)
      (by simpa only [hunion, Nat.add_assoc] using hbudget)
  have himage : H.image (fun h => dist p h) = nonDiameterDistances (H ∪ I) := by
    apply Finset.Subset.antisymm
    · intro d hd
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hd
      exact hmap h hh
    · intro d hd
      by_contra hmissing
      have hmapErase : ∀ h ∈ H, dist p h ∈ (nonDiameterDistances (H ∪ I)).erase d := by
        intro h hh
        exact Finset.mem_erase.mpr ⟨by
          intro heq
          exact hmissing (Finset.mem_image.mpr ⟨h, hh, heq⟩), hmap h hh⟩
      have hsmall := Finset.card_le_mul_card_image_of_maps_to hmapErase 2
        (fun e he => hcap e (Finset.mem_erase.mp he).2)
      have herase := Finset.card_erase_add_one hd
      omega
  refine ⟨hunion, hq, p, hp, hp0, norm_pos_iff.mpr hp0, ?_, himage, hcap⟩
  simpa only [dist_zero_right] using dist_center_lt_radius H 0 hR
    (by simpa only [dist_zero_right] using hcircle) (hinterior p hp)

private theorem quotient_fiber_large {G : Type*} [CommGroup G] (A : Finset G)
    (hsmall : 2 * (A / A).card < 3 * A.card) {b : G} (hb : b ∈ A / A) :
    A.card < 2 * (A.filter fun a => a * b ∈ A).card := by
  classical
  obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_div.mp hb
  let U := A.image (fun a => a / u)
  let V := A.image (fun a => a / v)
  have hU : U.card = A.card := Finset.card_image_of_injective _
    (fun a a' he => div_left_injective he)
  have hV : V.card = A.card := Finset.card_image_of_injective _
    (fun a a' he => div_left_injective he)
  have hsub : U ∪ V ⊆ A / A := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_div.mpr ⟨a, ha, u, hu, rfl⟩
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_div.mpr ⟨a, ha, v, hv, rfl⟩
  have hcard := Finset.card_union_add_card_inter U V
  have hbound := Finset.card_le_card hsub
  have hlarge : A.card < 2 * (U ∩ V).card := by omega
  have himage : (U ∩ V).image (fun x => x * u) =
      A.filter (fun a => a * (u / v)⁻¹ ∈ A) := by
    ext a
    constructor
    · intro ha
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨xu, xv⟩ := Finset.mem_inter.mp hx
      obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp xu
      obtain ⟨z, hz, hxz⟩ := Finset.mem_image.mp xv
      apply Finset.mem_filter.mpr
      constructor
      · simpa only [← hxy, div_mul_cancel] using hy
      · have he : x * u * (u / v)⁻¹ = z := by rw [← hxz]; simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        exact he ▸ hz
    · intro ha
      obtain ⟨haA, hab⟩ := Finset.mem_filter.mp ha
      apply Finset.mem_image.mpr
      refine ⟨a / u, Finset.mem_inter.mpr ⟨?_, ?_⟩, div_mul_cancel a u⟩
      · exact Finset.mem_image.mpr ⟨a, haA, rfl⟩
      · refine Finset.mem_image.mpr ⟨a * (u / v)⁻¹, hab, ?_⟩
        simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
        rw [mul_comm v u⁻¹]
        simp only [mul_assoc, mul_inv_cancel, mul_one]
  have hcardImage := Finset.card_image_of_injective (U ∩ V)
    (fun x y he => (mul_left_injective u) he)
  rw [himage] at hcardImage
  have hinv : (A.filter (fun a => a * (u / v)⁻¹ ∈ A)).card =
      (A.filter (fun a => a * (u / v) ∈ A)).card := by
    let F := A.filter (fun a => a * (u / v)⁻¹ ∈ A)
    have heq : F.image (fun a => a * (u / v)⁻¹) =
        A.filter (fun a => a * (u / v) ∈ A) := by
      ext a
      constructor
      · intro ha
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨hxA, hxb⟩ := Finset.mem_filter.mp hx
        exact Finset.mem_filter.mpr ⟨hxb, by simpa only [mul_assoc, inv_mul_cancel, mul_one] using hxA⟩
      · intro ha
        obtain ⟨haA, hab⟩ := Finset.mem_filter.mp ha
        exact Finset.mem_image.mpr ⟨a * (u / v), Finset.mem_filter.mpr
          ⟨hab, by simpa only [mul_assoc, mul_inv_cancel, mul_one] using haA⟩,
          by simp only [mul_assoc, mul_inv_cancel, mul_one]⟩
    have hc := Finset.card_image_of_injective F
      (fun x y he => (mul_left_injective (u / v)⁻¹) he)
    rw [heq] at hc
    exact hc.symm
  omega

/-- The elementary small-difference intersection argument: a finite quotient set
of size less than three halves of its original set is itself a subgroup carrier. -/
theorem exists_subgroup_of_small_quotient {G : Type*} [CommGroup G] (A : Finset G)
    (hA : A.Nonempty) (hsmall : 2 * (A / A).card < 3 * A.card) :
    ∃ K : Subgroup G, ∀ g : G, g ∈ K ↔ g ∈ A / A := by
  classical
  obtain ⟨a, ha⟩ := hA
  have hone : (1 : G) ∈ A / A := Finset.mem_div.mpr ⟨a, ha, a, ha, by simp⟩
  have hinv : ∀ b ∈ A / A, b⁻¹ ∈ A / A := by
    intro b hb
    obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_div.mp hb
    exact Finset.mem_div.mpr ⟨v, hv, u, hu, by simp [div_eq_mul_inv]⟩
  have hmul : ∀ b ∈ A / A, ∀ c ∈ A / A, b * c ∈ A / A := by
    intro b hb c hc
    let U := A.filter (fun a => a * b ∈ A)
    let V := A.filter (fun a => a * c⁻¹ ∈ A)
    have hU := quotient_fiber_large A hsmall hb
    have hV := quotient_fiber_large A hsmall (hinv c hc)
    have hsub : U ∪ V ⊆ A := Finset.union_subset
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have hbound := Finset.card_le_card hsub
    have hcard := Finset.card_union_add_card_inter U V
    have hpos : 0 < (U ∩ V).card := by dsimp only [U, V] at *; omega
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
    obtain ⟨hxU, hxV⟩ := Finset.mem_inter.mp hx
    exact Finset.mem_div.mpr ⟨x * b, (Finset.mem_filter.mp hxU).2,
      x * c⁻¹, (Finset.mem_filter.mp hxV).2,
      by simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]⟩
  let K : Subgroup G :=
    { carrier := {g | g ∈ A / A}
      one_mem' := hone
      inv_mem' := fun hb => hinv _ hb
      mul_mem' := fun hb hc => hmul _ hb _ hc }
  exact ⟨K, fun _ => Iff.rfl⟩

/-- The contrary branch of the original geometry has an actual hull-coefficient
quotient subgroup of size between `N` and `N+4`, containing every hull coefficient.
This is a finite circle-group completion, not yet an explicit cosine-grid completion. -/
theorem contrary_finite_completion (N : ℕ) (H I : Finset Plane) (R : ℝ)
    (hN : 15 ≤ N) (hodd : Odd N) (hcard : H.card = N) (hI : I.card = 4)
    (hR : 0 < R) (hcircle : ∀ h ∈ H, ‖h‖ = R)
    (hinterior : ∀ z ∈ I, z ∈ interior (convexHull ℝ (H : Set Plane)))
    (hlarge : ∀ d ∈ nonDiameterDistances (H ∪ I), N + 5 ≤ multiplicity (H ∪ I) d) :
    2 * (nonDiameterDistances (H ∪ I)).card = N + 1 ∧
    (∃ p ∈ I, p ≠ 0 ∧ 0 < ‖p‖ ∧ ‖p‖ < R ∧
      H.image (fun h => dist p h) = nonDiameterDistances (H ∪ I) ∧
      (∀ d ∈ nonDiameterDistances (H ∪ I), (H.filter fun h => dist p h = d).card ≤ 2) ∧
      ∃ a ∈ H, ∃ b ∈ H, a ≠ b ∧ dist p a = dist p b) ∧
    ∃ v ∈ H, ∃ A : Finset Rotation, ∃ K : Subgroup Rotation,
      1 ∈ A ∧ A.card = N ∧
      (∀ g : Rotation, g ∈ A ↔ rotate g v ∈ H) ∧
      A ⊆ A / A ∧ N ≤ (A / A).card ∧ (A / A).card ≤ N + 4 ∧
      (K : Set Rotation).Finite ∧ (∀ g : Rotation, g ∈ K ↔ g ∈ A / A) := by
  classical
  obtain ⟨_hunion, hq, p, hp, hp0, hpnorm, hpR, himage, hcap⟩ :=
    contrary_radial_support N H I R hN hodd hcard hI hR hcircle hinterior hlarge
  have hdouble : ∃ a ∈ H, ∃ b ∈ H, a ≠ b ∧ dist p a = dist p b := by
    by_contra hnone
    have hinj : Set.InjOn (fun h => dist p h) (H : Set Plane) := by
      intro a ha b hb heq
      by_contra hab
      exact hnone ⟨a, ha, b, hb, hab, heq⟩
    have hc := Finset.card_image_of_injOn hinj
    rw [himage, hcard] at hc
    omega
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < H.card)
  obtain ⟨A, hOne, hAcard, hA⟩ := exists_hull_coefficients H R v hR hcircle hv
  have hsub : A ⊆ A / A := by
    intro a ha
    exact Finset.mem_div.mpr ⟨a, ha, 1, hOne, div_one a⟩
  have hlow := Finset.card_le_card hsub
  have hbound := quotient_support_card_le H I R v A hR hcircle hv hOne hA
  have hupper : (A / A).card ≤ N + 4 := by omega
  have hsmall : 2 * (A / A).card < 3 * A.card := by omega
  obtain ⟨K, hK⟩ := exists_subgroup_of_small_quotient A ⟨1, hOne⟩ hsmall
  have hcarrier : (K : Set Rotation) = ((A / A : Finset Rotation) : Set Rotation) := by
    ext g
    exact hK g
  have hfinite : (K : Set Rotation).Finite := by
    rw [hcarrier]
    exact (A / A).finite_toSet
  exact ⟨hq, ⟨p, hp, hp0, hpnorm, hpR, himage, hcap, hdouble⟩,
    v, hv, A, K, hOne, hAcard.trans hcard, hA, hsub, by omega, hupper, hfinite, hK⟩

/-- Original center-allowed four-interior geometry yields the requested actual
nondiameter witness OR a precise derived finite-circle completion obstruction.
The obstruction is a conclusion, never an additional premise. This is a partial
reduction, not the full odd-tail distance theorem. -/
theorem original_input_reduction (N : ℕ) (H I : Finset Plane) (R : ℝ)
    (hN : 15 ≤ N) (hodd : Odd N) (hcard : H.card = N) (hI : I.card = 4)
    (hR : 0 < R) (hcircle : ∀ h ∈ H, ‖h‖ = R)
    (hinterior : ∀ z ∈ I, z ∈ interior (convexHull ℝ (H : Set Plane))) :
    (H ∪ I).card = N + 4 ∧
    ((∃ d : ℝ, 0 < d ∧ d < Metric.diam ((H ∪ I : Finset Plane) : Set Plane) ∧
      1 ≤ multiplicity (H ∪ I) d ∧ multiplicity (H ∪ I) d ≤ N + 4) ∨
    ((∀ d ∈ nonDiameterDistances (H ∪ I), N + 5 ≤ multiplicity (H ∪ I) d) ∧
      2 * (nonDiameterDistances (H ∪ I)).card = N + 1 ∧
      (∃ p ∈ I, p ≠ 0 ∧ 0 < ‖p‖ ∧ ‖p‖ < R ∧
        H.image (fun h => dist p h) = nonDiameterDistances (H ∪ I) ∧
        (∀ d ∈ nonDiameterDistances (H ∪ I), (H.filter fun h => dist p h = d).card ≤ 2) ∧
        ∃ a ∈ H, ∃ b ∈ H, a ≠ b ∧ dist p a = dist p b) ∧
      ∃ v ∈ H, ∃ A : Finset Rotation, ∃ K : Subgroup Rotation,
        1 ∈ A ∧ A.card = N ∧
        (∀ g : Rotation, g ∈ A ↔ rotate g v ∈ H) ∧
        A ⊆ A / A ∧ N ≤ (A / A).card ∧ (A / A).card ≤ N + 4 ∧
        (K : Set Rotation).Finite ∧ (∀ g : Rotation, g ∈ K ↔ g ∈ A / A))) := by
  classical
  have hunion : (H ∪ I).card = N + 4 := by
    rw [card_union_four_interiors H I R hR hcircle hI hinterior, hcard]
  refine ⟨hunion, ?_⟩
  by_cases hwitness : ∃ d : ℝ,
      0 < d ∧ d < Metric.diam ((H ∪ I : Finset Plane) : Set Plane) ∧
        1 ≤ multiplicity (H ∪ I) d ∧ multiplicity (H ∪ I) d ≤ N + 4
  · exact Or.inl hwitness
  · apply Or.inr
    have hlarge : ∀ d ∈ nonDiameterDistances (H ∪ I),
        N + 5 ≤ multiplicity (H ∪ I) d := by
      intro d hd
      obtain ⟨⟨a, ha, b, hb, hab, habd⟩, hlt⟩ := (mem_nonDiameterDistances _ d).mp hd
      have hpos : 0 < d := habd ▸ dist_pos.mpr hab
      have hmult : 1 ≤ multiplicity (H ∪ I) d := by
        apply Finset.card_pos.mpr
        exact ⟨s(a,b), Finset.mem_filter.mpr
          ⟨(mk_mem_pairs _ a b).mpr ⟨ha, hb, hab⟩, habd⟩⟩
      have hnot : ¬ multiplicity (H ∪ I) d ≤ N + 4 := by
        intro hbound
        exact hwitness ⟨d, hpos, hlt, hmult, hbound⟩
      omega
    exact ⟨hlarge, contrary_finite_completion N H I R hN hodd hcard hI hR hcircle hinterior hlarge⟩

set_option maxHeartbeats 400000 in
/-- A concrete radius-65 fifteen-vertex cyclic hull and four distinct ambient
interiors, including the center, jointly satisfy the original odd-tail hypotheses.
The same original-input reduction is applied, yielding its witness-or-completion
alternative; this fixture does not assert that the completion branch is impossible. -/
theorem original_geometry_fixture_application :
    ∃ (H I : Finset Plane), H.card = 15 ∧ I.card = 4 ∧ (0 : Plane) ∈ I ∧
      (∀ h ∈ H, ‖h‖ = 65) ∧
      (∀ p ∈ I, p ∈ interior (convexHull ℝ (H : Set Plane))) ∧
      (H ∪ I).card = 19 ∧
      ((∃ d : ℝ, 0 < d ∧ d < Metric.diam ((H ∪ I : Finset Plane) : Set Plane) ∧
        1 ≤ multiplicity (H ∪ I) d ∧ multiplicity (H ∪ I) d ≤ 19) ∨
      (2 * (nonDiameterDistances (H ∪ I)).card = 16 ∧
        ∃ v ∈ H, ∃ A : Finset Rotation, ∃ K : Subgroup Rotation,
          1 ∈ A ∧ A.card = 15 ∧
          (∀ g : Rotation, g ∈ A ↔ rotate g v ∈ H) ∧
          A ⊆ A / A ∧ 15 ≤ (A / A).card ∧ (A / A).card ≤ 19 ∧
          (K : Set Rotation).Finite ∧ (∀ g : Rotation, g ∈ K ↔ g ∈ A / A))) := by
  classical
  let a : Plane := WithLp.toLp 2 ![39, 52]
  let b : Plane := WithLp.toLp 2 ![-39, 52]
  let c : Plane := WithLp.toLp 2 ![39, -52]
  let d : Plane := WithLp.toLp 2 ![-39, -52]
  let e : Plane := WithLp.toLp 2 ![52, 39]
  let f : Plane := WithLp.toLp 2 ![-52, 39]
  let g : Plane := WithLp.toLp 2 ![52, -39]
  let h : Plane := WithLp.toLp 2 ![-52, -39]
  let i : Plane := WithLp.toLp 2 ![65, 0]
  let j : Plane := WithLp.toLp 2 ![-65, 0]
  let k : Plane := WithLp.toLp 2 ![0, 65]
  let l : Plane := WithLp.toLp 2 ![0, -65]
  let m : Plane := WithLp.toLp 2 ![25, 60]
  let n : Plane := WithLp.toLp 2 ![-25, 60]
  let o : Plane := WithLp.toLp 2 ![25, -60]
  let H : Finset Plane := {a, b, c, d, e, f, g, h, i, j, k, l, m, n, o}
  let p : Plane := WithLp.toLp 2 ![1, 0]
  let q : Plane := WithLp.toLp 2 ![0, 1]
  let s : Plane := WithLp.toLp 2 ![1, 1]
  let I : Finset Plane := {0, p, q, s}
  have hcard : H.card = 15 := by
    norm_num [H, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o,
      Finset.card_insert_of_notMem, WithLp.ext_iff, funext_iff, Fin.forall_fin_two]
  have hI : I.card = 4 := by
    norm_num [I, p, q, s, Finset.card_insert_of_notMem,
      WithLp.ext_iff, funext_iff, Fin.forall_fin_two]
  have hcircle : ∀ x ∈ H, ‖x‖ = 65 := by
    intro x hx
    have hsq : ‖x‖ ^ 2 = 4225 := by
      simp only [H, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl <;>
        norm_num [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two,
          a, b, c, d, e, f, g, h, i, j, k, l, m, n, o]
    nlinarith only [hsq, norm_nonneg x]
  have hcorners : ∀ u ∈ ({-39, 39} : Finset ℝ), ∀ v ∈ ({-52, 52} : Finset ℝ),
      WithLp.toLp 2 ![u, v] ∈ H := by
    intro u hu v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> simp [H, a, b, c, d]
  have hinterior : ∀ x ∈ I, x ∈ interior (convexHull ℝ (H : Set Plane)) := by
    intro x hx
    apply CircleFixtures.rectangle_mem_interior H (r := 39) (s := 52)
      (by norm_num) (by norm_num) hcorners
    · simp only [I, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> norm_num [p, q, s]
    · simp only [I, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> norm_num [p, q, s]
  obtain ⟨hunion, hresult⟩ := original_input_reduction 15 H I 65 (by decide)
    (by decide) hcard hI (by norm_num) hcircle hinterior
  refine ⟨H, I, hcard, hI, by simp [I], hcircle, hinterior, hunion, ?_⟩
  rcases hresult with hwitness | hobstruction
  · exact Or.inl hwitness
  · exact Or.inr ⟨hobstruction.2.1, hobstruction.2.2.2⟩

example : ∃ p ∈ ({(0 : Plane), WithLp.toLp 2 ![1, 0],
    WithLp.toLp 2 ![0, 1], WithLp.toLp 2 ![1, 1]} : Finset Plane), p ≠ 0 := by
  apply exists_nonzero_of_card_four
  norm_num [Finset.card_insert_of_notMem, WithLp.ext_iff, funext_iff, Fin.forall_fin_two]

example : 2 * (8 : ℕ) = 15 + 1 :=
  odd_four_support_of_budget 15 8 (by decide) (by decide) (by decide) (by decide)

example : ∃ K : Subgroup Rotation, ∀ g : Rotation,
    g ∈ K ↔ g ∈ ({1} : Finset Rotation) / {1} := by
  apply exists_subgroup_of_small_quotient {1} (by simp)
  norm_num

end

end Erdos132.FourInteriorOddTail
