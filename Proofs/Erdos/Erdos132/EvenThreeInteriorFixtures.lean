import Erdos.Erdos132.CircleFixtures
import Erdos.Erdos132.EvenThreeInteriorCircle

set_option autoImplicit false

namespace Erdos132.EvenThreeInteriorFixtures

open Erdos132.TwoInteriorCircle

/-- The original even theorem's hypotheses are jointly inhabited at n = 10,
by the rational-circle fixture; invoking the public arbitrary-center theorem
on that same model produces its asserted genuine small-multiplicity distance. -/
theorem original_hypotheses_with_witness : ∃ (H : Finset Plane) (z w v : Plane),
    H.card = 7 ∧ (∀ h ∈ H, dist h (0 : Plane) = 5) ∧
    (∀ h ∈ H, h ∈ (convexHull ℝ (H : Set Plane)).extremePoints ℝ) ∧
    z ∈ interior (convexHull ℝ (H : Set Plane)) ∧
    w ∈ interior (convexHull ℝ (H : Set Plane)) ∧
    v ∈ interior (convexHull ℝ (H : Set Plane)) ∧ z ≠ w ∧ z ≠ v ∧ w ≠ v ∧
    (insert z (insert w (insert v H))).card = 10 ∧
    ∃ d : ℝ, 0 < d ∧ d < Metric.diam ((insert z (insert w (insert v H)):Finset Plane):Set Plane) ∧
      1 ≤ multiplicity (insert z (insert w (insert v H))) d ∧
      multiplicity (insert z (insert w (insert v H))) d ≤ 10 := by
  obtain ⟨H,z,w,v,hcard,hcircle,hext,hz,hw,hv,hzw,hzv,hwv⟩ :=
    CircleFixtures.rational_three_interior_fixture
  have hclaim := EvenThreeInteriorCircle.even_three_interior_circle 10 H 0 z w v 5
    (by decide) (by decide) (by norm_num; exact hcard) hcircle hext hz hw hv hzw hzv hwv
  exact ⟨H,z,w,v,hcard,hcircle,hext,hz,hw,hv,hzw,hzv,hwv,hclaim⟩

/-- Rational stereographic parametrization of the radius-five circle.
For rational t both coordinates are rational. -/
noncomputable def circle_point (t : ℝ) : Plane :=
  WithLp.toLp 2 ![5 * (1 - t^2) / (1 + t^2), 10 * t / (1 + t^2)]

example : circle_point 0 = WithLp.toLp 2 ![5, 0] := by norm_num [circle_point]
example : circle_point 1 = WithLp.toLp 2 ![0, 5] := by norm_num [circle_point]

/-- Every stereographic parameter gives an actual point on the radius-five circle. -/
theorem circle_point_norm (t : ℝ) : ‖circle_point t‖ = 5 := by
  have hd : 1 + t^2 ≠ 0 := by positivity
  have hsq : ‖circle_point t‖ ^ 2 = 25 := by
    simp only [circle_point, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    norm_num
    field_simp
    simp only [sq_abs]
    ring
  nlinarith [norm_nonneg (circle_point t)]

/-- The stereographic circle parametrization is injective. -/
theorem circle_point_injective : Function.Injective circle_point := by
  have hden : ∀ t : ℝ, 1 + t^2 ≠ 0 := by intro t; positivity
  have hx : ∀ t : ℝ, 5 + circle_point t 0 = 10 / (1 + t^2) := by
    intro t
    change 5 + 5 * (1 - t^2) / (1 + t^2) = 10 / (1 + t^2)
    field_simp
    <;> ring
  have hxy : ∀ t : ℝ, circle_point t 1 = t * (5 + circle_point t 0) := by
    intro t
    rw [hx]
    change 10 * t / (1 + t^2) = t * (10 / (1 + t^2))
    ring
  intro t u he
  have he0 := congrArg (fun p : Plane => p 0) he
  have he1 := congrArg (fun p : Plane => p 1) he
  have hnon : 5 + circle_point t 0 ≠ 0 := by rw [hx]; exact div_ne_zero (by norm_num) (hden t)
  apply mul_right_cancel₀ hnon
  calc
    t * (5 + circle_point t 0) = circle_point t 1 := (hxy t).symm
    _ = circle_point u 1 := he1
    _ = u * (5 + circle_point u 0) := hxy u
    _ = u * (5 + circle_point t 0) := by rw [he0]

/-- Joint nonvacuity for every n at least ten: retain the rational seven-point
polygon and enlarge it by distinct rationally parametrized circle points.
The three original ambient interiors remain interior after enlargement. -/
theorem original_hypotheses_all_sizes (n : ℕ) (hn : 10 ≤ n) :
    ∃ (H : Finset Plane) (z w v : Plane), H.card = n - 3 ∧
    (∀ h ∈ H, dist h (0 : Plane) = 5) ∧
    (∀ h ∈ H, h ∈ (convexHull ℝ (H : Set Plane)).extremePoints ℝ) ∧
    z ∈ interior (convexHull ℝ (H : Set Plane)) ∧
    w ∈ interior (convexHull ℝ (H : Set Plane)) ∧
    v ∈ interior (convexHull ℝ (H : Set Plane)) ∧ z ≠ w ∧ z ≠ v ∧ w ≠ v := by
  classical
  obtain ⟨H₀,z,w,v,hcard₀,hcircle₀,hext₀,hz₀,hw₀,hv₀,hzw,hzv,hwv⟩ :=
    CircleFixtures.rational_three_interior_fixture
  let P : ℕ → Plane := fun k => circle_point k
  have hPinj : Function.Injective P := by
    intro k l he
    exact Nat.cast_injective (circle_point_injective he)
  have hPinf : (Set.range P).Infinite := Set.infinite_range_of_injective hPinj
  obtain ⟨T, hT, hTcard⟩ := (hPinf.sdiff H₀.finite_toSet).exists_subset_card_eq (n - 10)
  let H := H₀ ∪ T
  have hdis : Disjoint H₀ T := Finset.disjoint_left.mpr (fun h hh₀ hhT => (hT hhT).2 hh₀)
  have hcard : H.card = n - 3 := by
    dsimp only [H]
    rw [Finset.card_union_of_disjoint hdis, hcard₀, hTcard]
    omega
  have hcircle : ∀ h ∈ H, dist h (0 : Plane) = 5 := by
    intro h hh
    rcases Finset.mem_union.mp hh with hh₀ | hhT
    · exact hcircle₀ h hh₀
    · obtain ⟨k, hk⟩ := (hT hhT).1
      rw [← hk, dist_zero_right]
      exact circle_point_norm k
  have hsub : (H₀ : Set Plane) ⊆ (H : Set Plane) := by
    intro h hh
    exact Finset.mem_union_left _ hh
  have hInt : interior (convexHull ℝ (H₀ : Set Plane)) ⊆
      interior (convexHull ℝ (H : Set Plane)) := interior_mono (convexHull_mono hsub)
  have hext : ∀ h ∈ H, h ∈ (convexHull ℝ (H : Set Plane)).extremePoints ℝ := by
    intro h hh
    have hball : convexHull ℝ (H : Set Plane) ⊆ Metric.closedBall (0 : Plane) 5 :=
      convexHull_min (by intro a ha; simpa [Metric.mem_closedBall, hcircle a ha])
        (convex_closedBall 0 5)
    apply inter_extremePoints_subset_extremePoints_of_subset hball
    exact ⟨subset_convexHull ℝ _ hh,
      StrictConvexSpace.sphere_subset_extremePoints_closedBall 0 (by norm_num)
        (by simpa [Metric.mem_sphere] using hcircle h hh)⟩
  exact ⟨H,z,w,v,hcard,hcircle,hext,hInt hz₀,hInt hw₀,hInt hv₀,hzw,hzv,hwv⟩

/-- At every even n at least ten the original hypotheses and the conclusion
are jointly inhabited; this applies the universal public theorem to the same
all-size circle fixture, not to an impossible contrary counting premise. -/
theorem original_hypotheses_every_even_size (n : ℕ) (hn : 10 ≤ n) (hEven : Even n) :
    ∃ (H : Finset Plane) (z w v : Plane), H.card = n - 3 ∧
    (∀ h ∈ H, dist h (0 : Plane) = 5) ∧
    (∀ h ∈ H, h ∈ (convexHull ℝ (H : Set Plane)).extremePoints ℝ) ∧
    z ∈ interior (convexHull ℝ (H : Set Plane)) ∧
    w ∈ interior (convexHull ℝ (H : Set Plane)) ∧
    v ∈ interior (convexHull ℝ (H : Set Plane)) ∧ z ≠ w ∧ z ≠ v ∧ w ≠ v ∧
    (insert z (insert w (insert v H))).card = n ∧
    ∃ d : ℝ, 0 < d ∧ d < Metric.diam ((insert z (insert w (insert v H)):Finset Plane):Set Plane) ∧
      1 ≤ multiplicity (insert z (insert w (insert v H))) d ∧
      multiplicity (insert z (insert w (insert v H))) d ≤ n := by
  obtain ⟨H,z,w,v,hcard,hcircle,hext,hz,hw,hv,hzw,hzv,hwv⟩ :=
    original_hypotheses_all_sizes n hn
  have hclaim := EvenThreeInteriorCircle.even_three_interior_circle n H 0 z w v 5
    hn hEven hcard hcircle hext hz hw hv hzw hzv hwv
  exact ⟨H,z,w,v,hcard,hcircle,hext,hz,hw,hv,hzw,hzv,hwv,hclaim⟩

end Erdos132.EvenThreeInteriorFixtures
