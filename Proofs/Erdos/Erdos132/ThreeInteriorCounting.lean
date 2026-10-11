import Erdos.Erdos132.TwoInteriorCircle

set_option autoImplicit false

open scoped BigOperators

namespace Erdos132.ThreeInteriorCounting

open Erdos132.TwoInteriorCircle

/-- The inherited non-diameter support is exactly the occurring positive distances
strictly below the actual diameter; no zero-distance class is included. -/
theorem mem_nonDiameterDistances_iff_positive (X : Finset Plane) (d : ℝ) :
    d ∈ nonDiameterDistances X ↔ 0 < d ∧ d < Metric.diam (X : Set Plane) ∧
      ∃ a ∈ X, ∃ b ∈ X, dist a b = d := by
  constructor
  · intro hd
    obtain ⟨⟨a, ha, b, hb, hab, habd⟩, hlt⟩ := (mem_nonDiameterDistances X d).mp hd
    exact ⟨habd ▸ dist_pos.mpr hab, hlt, a, ha, b, hb, habd⟩
  · rintro ⟨hpos, hlt, a, ha, b, hb, habd⟩
    have hab : a ≠ b := by
      intro heq
      rw [heq, dist_self] at habd
      linarith
    exact (mem_nonDiameterDistances X d).mpr ⟨⟨a, ha, b, hb, hab, habd⟩, hlt⟩

/-- A strict interior point of a positive-radius cyclic hull is not a hull vertex. -/
theorem interior_not_mem_circle (H : Finset Plane) (R : ℝ) (p : Plane)
    (hR : 0 < R) (hcircle : ∀ h ∈ H, ‖h‖ = R)
    (hp : p ∈ interior (convexHull ℝ (H : Set Plane))) : p ∉ H := by
  have hc : ∀ h ∈ H, dist h (0 : Plane) = R := by
    simpa only [dist_zero_right] using hcircle
  have hpR := dist_center_lt_radius H 0 hR hc hp
  intro hpH
  exact (ne_of_lt hpR) (hc p hpH)

/-- Three pairwise distinct strict interior points add exactly three points to a cyclic hull. -/
theorem card_insert_three_interiors (H : Finset Plane) (R : ℝ) (u v w : Plane)
    (hR : 0 < R) (hcircle : ∀ h ∈ H, ‖h‖ = R)
    (hu : u ∈ interior (convexHull ℝ (H : Set Plane)))
    (hv : v ∈ interior (convexHull ℝ (H : Set Plane)))
    (hw : w ∈ interior (convexHull ℝ (H : Set Plane)))
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    (insert u (insert v (insert w H))).card = H.card + 3 := by
  classical
  have huH := interior_not_mem_circle H R u hR hcircle hu
  have hvH := interior_not_mem_circle H R v hR hcircle hv
  have hwH := interior_not_mem_circle H R w hR hcircle hw
  simp [Finset.card_insert_of_notMem, huH, hvH, hwH, huv, huw, hvw, Nat.add_assoc]

/-- Adding three hull-interior points preserves the actual metric diameter. -/
theorem diam_insert_three_interiors (H : Finset Plane) (u v w : Plane)
    (hu : u ∈ interior (convexHull ℝ (H : Set Plane)))
    (hv : v ∈ interior (convexHull ℝ (H : Set Plane)))
    (hw : w ∈ interior (convexHull ℝ (H : Set Plane))) :
    Metric.diam ((insert u (insert v (insert w H)) : Finset Plane) : Set Plane) =
      Metric.diam (H : Set Plane) := by
  classical
  have hsub : ((insert u (insert v (insert w H)) : Finset Plane) : Set Plane) ⊆
      convexHull ℝ (H : Set Plane) := by
    intro p hp
    simp only [Finset.mem_coe, Finset.mem_insert] at hp
    rcases hp with rfl | rfl | rfl | hp
    · exact interior_subset hu
    · exact interior_subset hv
    · exact interior_subset hw
    · exact subset_convexHull ℝ (H : Set Plane) hp
  apply le_antisymm
  · exact Metric.diam_le_of_forall_dist_le Metric.diam_nonneg
      (fun _ hx _ hy => dist_le_diam_hull H (hsub hx) (hsub hy))
  · exact Metric.diam_mono (by intro p hp; simp [hp])
      (insert u (insert v (insert w H))).finite_toSet.isBounded

/-- Odd order, the radial capacity lower bound, and the diameter-reserving unordered-pair
budget force exactly twice as many hull vertices as non-diameter distance classes. -/
theorem odd_size_of_pair_budget (n q : ℕ) (hn : 9 ≤ n) (ho : Odd n)
    (hlower : n - 3 ≤ 2 * q) (hb : q * (n + 1) + 1 ≤ n.choose 2) :
    n - 3 = 2 * q ∧ 3 ≤ q := by
  have hchoose : 2 * n.choose 2 ≤ n * (n - 1) := by
    rw [Nat.choose_two_right]
    exact Nat.mul_div_le _ _
  have hbudget2 : 2 * (q * (n + 1) + 1) ≤ n * (n - 1) :=
    (Nat.mul_le_mul_left 2 hb).trans hchoose
  have hsub : n - 1 + 1 = n := by omega
  have hupper : 2 * q ≤ n - 2 := by
    by_contra h
    have hq : n - 1 ≤ 2 * q := by omega
    have hmul := Nat.mul_le_mul_right (n + 1) hq
    nlinarith
  rcases ho with ⟨k, hk⟩
  omega

example : (9 : ℕ) - 3 = 2 * 3 ∧ 3 ≤ (3 : ℕ) :=
  odd_size_of_pair_budget 9 3 (by decide) ⟨4, by decide⟩ (by decide) (by decide)

/-- The original geometric premises have a joint concrete model at order nine.
The contrary multiplicity premise is deliberately not part of this consistency witness. -/
theorem original_geometry_fixture :
    ∃ (n : ℕ) (H : Finset Plane) (R : ℝ) (u v w : Plane),
      9 ≤ n ∧ Odd n ∧ H.card = n - 3 ∧ 0 < R ∧
      (∀ h ∈ H, ‖h‖ = R) ∧ u ≠ v ∧ u ≠ w ∧ v ≠ w ∧
      u ∈ interior (convexHull ℝ (H : Set Plane)) ∧
      v ∈ interior (convexHull ℝ (H : Set Plane)) ∧
      w ∈ interior (convexHull ℝ (H : Set Plane)) := by
  obtain ⟨H, u, v, hcard, hcircle, _hext, hu, hv, huv⟩ := rational_circle_fixture
  let w := midpoint ℝ u v
  have hw : w ∈ interior (convexHull ℝ (H : Set Plane)) :=
    (convex_convexHull ℝ (H : Set Plane)).interior.midpoint_mem hu hv
  have huw : u ≠ w := by
    intro heq
    exact huv ((midpoint_eq_left_iff ℝ).mp heq.symm)
  have hvw : v ≠ w := by
    intro heq
    exact huv ((midpoint_eq_right_iff ℝ).mp heq.symm)
  refine ⟨9, H, 1, u, v, w, by decide, ?_, ?_, by norm_num, ?_, huv, huw, hvw, hu, hv, hw⟩
  · exact ⟨4, by norm_num⟩
  · simpa using hcard
  · simpa only [dist_zero_right] using hcircle

/-- For odd order at least nine, the contrary multiplicity hypothesis forces exact
counting saturation on the actual positive non-diameter support. The three original
interior points increase the cardinality by three and preserve the positive diameter.
Every off-center one has that entire radial support, with every radial fiber of size two.
No off-center condition on all three interiors is assumed or concluded. -/
theorem counting_saturation (n : ℕ) (H : Finset Plane) (R : ℝ) (u v w : Plane)
    (hn : 9 ≤ n) (hodd : Odd n) (hH : H.card = n - 3) (hR : 0 < R)
    (hcircle : ∀ h ∈ H, ‖h‖ = R)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hu : u ∈ interior (convexHull ℝ (H : Set Plane)))
    (hv : v ∈ interior (convexHull ℝ (H : Set Plane)))
    (hw : w ∈ interior (convexHull ℝ (H : Set Plane)))
    (hlarge : ∀ d : ℝ, 0 < d →
      d < Metric.diam ((insert u (insert v (insert w H)) : Finset Plane) : Set Plane) →
      (∃ a ∈ insert u (insert v (insert w H)),
        ∃ b ∈ insert u (insert v (insert w H)), dist a b = d) →
      n + 1 ≤ multiplicity (insert u (insert v (insert w H))) d) :
    let X := insert u (insert v (insert w H))
    let S := nonDiameterDistances X
    X.card = n ∧ Metric.diam (X : Set Plane) = Metric.diam (H : Set Plane) ∧
      0 < Metric.diam (H : Set Plane) ∧ H.card = 2 * S.card ∧
      n = 2 * S.card + 3 ∧ 3 ≤ S.card ∧
      ∀ z ∈ ({u, v, w} : Finset Plane), z ≠ 0 →
        H.image (fun h => dist h z) = S ∧
        (∀ d ∈ S, (H.filter fun h => dist h z = d).card = 2) ∧
        (∀ h ∈ H, (H.filter fun b => dist b z = dist h z).card = 2) := by
  classical
  let X := insert u (insert v (insert w H))
  let S := nonDiameterDistances X
  let I : Finset Plane := {u, v, w}
  change X.card = n ∧ Metric.diam (X : Set Plane) = Metric.diam (H : Set Plane) ∧
    0 < Metric.diam (H : Set Plane) ∧ H.card = 2 * S.card ∧
    n = 2 * S.card + 3 ∧ 3 ≤ S.card ∧
    ∀ z ∈ I, z ≠ 0 → H.image (fun h => dist h z) = S ∧
      (∀ d ∈ S, (H.filter fun h => dist h z = d).card = 2) ∧
      (∀ h ∈ H, (H.filter fun b => dist b z = dist h z).card = 2)
  have hHtwo : 2 ≤ H.card := by omega
  have hcardX : X.card = n := by
    have hc := card_insert_three_interiors H R u v w hR hcircle hu hv hw huv huw hvw
    change X.card = H.card + 3 at hc
    omega
  have hdiam : Metric.diam (X : Set Plane) = Metric.diam (H : Set Plane) :=
    diam_insert_three_interiors H u v w hu hv hw
  have hdiampos : 0 < Metric.diam (H : Set Plane) := diam_pos H hHtwo
  have hcircle0 : ∀ h ∈ H, dist h (0 : Plane) = R := by
    simpa only [dist_zero_right] using hcircle
  have hsub : H ⊆ X := by
    intro h hh
    simp [X, hh]
  have hinterior : ∀ z ∈ I, z ∈ interior (convexHull ℝ (H : Set Plane)) := by
    intro z hz
    simp only [I, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact hu
    · exact hv
    · exact hw
  have hmemX : ∀ z ∈ I, z ∈ X := by
    intro z hz
    simp only [I, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl <;> simp [X]
  have hmap : ∀ z ∈ I, ∀ h ∈ H, dist h z ∈ S := by
    intro z hz h hh
    have hzH := interior_not_mem_circle H R z hR hcircle (hinterior z hz)
    have hhz : h ≠ z := fun heq => hzH (heq ▸ hh)
    apply (mem_nonDiameterDistances X (dist h z)).mpr
    refine ⟨⟨h, hsub hh, z, hmemX z hz, hhz, rfl⟩, ?_⟩
    rw [hdiam, dist_comm]
    exact dist_lt_diam_hull H hHtwo (hinterior z hz)
      (subset_convexHull ℝ (H : Set Plane) hh)
  have hcap : ∀ z ∈ I, z ≠ 0 → ∀ d ∈ S,
      (H.filter fun h => dist h z = d).card ≤ 2 := by
    intro z _hz hz0 d _hd
    exact radial_card_le_two H 0 z R d hcircle0 hz0
  have hoff : ∃ z ∈ I, z ≠ 0 := by
    by_cases hu0 : u = 0
    · refine ⟨v, by simp [I], ?_⟩
      intro hv0
      exact huv (hu0.trans hv0.symm)
    · exact ⟨u, by simp [I], hu0⟩
  obtain ⟨z, hz, hz0⟩ := hoff
  have hlower : H.card ≤ 2 * S.card :=
    Finset.card_le_mul_card_image_of_maps_to (hmap z hz) 2 (hcap z hz hz0)
  have hlargeS : ∀ d ∈ nonDiameterDistances X, X.card + 1 ≤ multiplicity X d := by
    intro d hd
    obtain ⟨hpos, hlt, hoccurs⟩ := (mem_nonDiameterDistances_iff_positive X d).mp hd
    rw [hcardX]
    exact hlarge d hpos hlt hoccurs
  have hbudget := nonDiameter_pair_budget X (by omega) hlargeS
  have hbudgetn : S.card * (n + 1) + 1 ≤ n.choose 2 := by
    simpa only [hcardX] using hbudget
  obtain ⟨hsize, hq⟩ := odd_size_of_pair_budget n S.card hn hodd
    (by omega : n - 3 ≤ 2 * S.card) hbudgetn
  have hcardS : H.card = 2 * S.card := hH.trans hsize
  have hnq : n = 2 * S.card + 3 := by omega
  refine ⟨hcardX, hdiam, hdiampos, hcardS, hnq, hq, ?_⟩
  intro z hz hz0
  have hfibers : ∀ d ∈ S, (H.filter fun h => dist h z = d).card = 2 :=
    saturated_fibers H S (fun h => dist h z) (hmap z hz) (hcap z hz hz0) hcardS
  have hsupport : H.image (fun h => dist h z) = S := by
    apply Finset.Subset.antisymm
    · intro d hd
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hd
      exact hmap z hz h hh
    · intro d hd
      have hpos : 0 < (H.filter fun h => dist h z = d).card := by
        rw [hfibers d hd]
        decide
      obtain ⟨h, hh⟩ := Finset.card_pos.mp hpos
      have hmem := Finset.mem_filter.mp hh
      exact Finset.mem_image.mpr ⟨h, hmem.1, hmem.2⟩
  refine ⟨hsupport, hfibers, ?_⟩
  intro h hh
  exact hfibers (dist h z) (hmap z hz h hh)

end Erdos132.ThreeInteriorCounting
