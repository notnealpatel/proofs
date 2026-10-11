import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Convex.Strict.Extreme
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Data.Sym.Card

set_option autoImplicit false

open scoped BigOperators Pointwise

namespace Erdos132.TwoInteriorCircle

/-- The ordinary two-dimensional Euclidean plane, with its canonical norm and metric. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Distinct unordered pairs from a finite set, with the two orientations identified. -/
noncomputable def pairs {α : Type*} (X : Finset α) : Finset (Sym2 α) := by
  classical
  exact X.offDiag.image Sym2.mk.uncurry

/-- The ordinary distance attached to an unordered pair. -/
noncomputable def pairDist {α : Type*} [PseudoMetricSpace α] : Sym2 α → ℝ :=
  Sym2.lift ⟨dist, dist_comm⟩

/-- True multiplicity of a distance among distinct unordered pairs of a finite set. -/
noncomputable def multiplicity {α : Type*} [PseudoMetricSpace α]
    (X : Finset α) (d : ℝ) : ℕ := by
  classical
  exact ((pairs X).filter fun e => pairDist e = d).card

/-- Ground-truth characterization: an unordered pair belongs exactly when both endpoints
belong and are distinct. -/
theorem mk_mem_pairs {α : Type*} (X : Finset α) (a b : α) :
    s(a, b) ∈ pairs X ↔ a ∈ X ∧ b ∈ X ∧ a ≠ b := by
  classical
  simp only [pairs, Finset.mem_image, Finset.mem_offDiag]
  constructor
  · rintro ⟨⟨x, y⟩, ⟨hx, hy, hxy⟩, he⟩
    rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hx, hy, hxy⟩
    · exact ⟨hy, hx, Ne.symm hxy⟩
  · rintro ⟨ha, hb, hab⟩
    exact ⟨(a, b), ⟨ha, hb, hab⟩, rfl⟩

/-- The pair finset has exactly the usual binomial cardinality. -/
theorem card_pairs {α : Type*} (X : Finset α) :
    (pairs X).card = X.card.choose 2 := by
  classical
  exact Sym2.card_image_offDiag X

/-- Ground-truth reduction of unordered-pair distance to ordinary distance. -/
theorem pairDist_mk {α : Type*} [PseudoMetricSpace α] (a b : α) :
    pairDist s(a, b) = dist a b := rfl

example : multiplicity ({(0 : ℝ), 1} : Finset ℝ) 1 = 1 := by
  classical
  have hp : pairs ({(0 : ℝ), 1} : Finset ℝ) = {s((0 : ℝ), 1)} := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      simp only [mk_mem_pairs, Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]
      aesop
  rw [multiplicity, hp]
  simp [Finset.filter_singleton, pairDist_mk, Real.dist_eq]

/-- A point in the open interior is strictly closer to every point of a set than any
positive uniform upper bound for all distances in that set. -/
theorem dist_lt_of_mem_interior {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} {p y : E} {D : ℝ} (hD : 0 < D)
    (hbound : ∀ a ∈ K, ∀ b ∈ K, dist a b ≤ D)
    (hp : p ∈ interior K) (hy : y ∈ K) : dist p y < D := by
  by_cases hpy : p = y
  · simpa [hpy] using hD
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
  have hq : q ∈ K := hball (by simpa only [Metric.mem_ball, hqp] using htε)
  have hqy : dist q y = (1 + t) * dist p y := by
    rw [dist_eq_norm, dist_eq_norm]
    have hv : q - y = (1 + t) • (p - y) := by
      dsimp [q]
      module
    rw [hv, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < 1 + t)]
  have hpos : 0 < dist p y := dist_pos.mpr hpy
  have hle := hbound q hq y hy
  rw [hqy] at hle
  nlinarith

/-- Convexification does not increase the diameter of a finite set. -/
theorem dist_le_diam_hull (H : Finset Plane) {x y : Plane}
    (hx : x ∈ convexHull ℝ (H : Set Plane))
    (hy : y ∈ convexHull ℝ (H : Set Plane)) :
    dist x y ≤ Metric.diam (H : Set Plane) := by
  obtain ⟨a, ha, b, hb, hle⟩ := convexHull_exists_dist_ge2 hx hy
  exact hle.trans (Metric.dist_le_diam_of_mem H.finite_toSet.isBounded ha hb)

/-- The diameter of a finite set equals the diameter of its convex hull. -/
theorem diam_convexHull (H : Finset Plane) :
    Metric.diam (convexHull ℝ (H : Set Plane)) = Metric.diam (H : Set Plane) := by
  apply le_antisymm
  · exact Metric.diam_le_of_forall_dist_le Metric.diam_nonneg
      (fun _ hx _ hy => dist_le_diam_hull H hx hy)
  · obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp H.finite_toSet.isBounded
    have hbound : Bornology.IsBounded (convexHull ℝ (H : Set Plane)) := by
      apply Metric.isBounded_iff.mpr
      exact ⟨C, fun x hx y hy => by
        obtain ⟨a, ha, b, hb, hle⟩ := convexHull_exists_dist_ge2 hx hy
        exact hle.trans (hC ha hb)⟩
    exact Metric.diam_mono (subset_convexHull ℝ (H : Set Plane)) hbound

/-- Any hull containing two distinct vertices has positive diameter. -/
theorem diam_pos (H : Finset Plane) (hcard : 2 ≤ H.card) :
    0 < Metric.diam (H : Set Plane) := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < H.card)
  exact (dist_pos.mpr hab).trans_le
    (Metric.dist_le_diam_of_mem H.finite_toSet.isBounded ha hb)

/-- Strict interiority gives the strict hull-diameter inequality, including an
interior-interior pair when the second interior point is used as `y`. -/
theorem dist_lt_diam_hull (H : Finset Plane) (hcard : 2 ≤ H.card)
    {p y : Plane} (hp : p ∈ interior (convexHull ℝ (H : Set Plane)))
    (hy : y ∈ convexHull ℝ (H : Set Plane)) :
    dist p y < Metric.diam (H : Set Plane) :=
  dist_lt_of_mem_interior (diam_pos H hcard)
    (fun _ hx _ hy' => dist_le_diam_hull H hx hy') hp hy

/-- The open convex-hull interior of points on a positive-radius circle lies
strictly inside its disk; this is derived, not an extra theorem hypothesis. -/
theorem dist_center_lt_radius (H : Finset Plane) (O : Plane) {R : ℝ}
    (hR : 0 < R) (hcircle : ∀ h ∈ H, dist h O = R)
    {p : Plane} (hp : p ∈ interior (convexHull ℝ (H : Set Plane))) :
    dist p O < R := by
  have hsub : convexHull ℝ (H : Set Plane) ⊆ Metric.closedBall O R :=
    convexHull_min (fun h hh => (hcircle h hh).le) (convex_closedBall O R)
  have hi := interior_mono hsub hp
  rw [interior_closedBall O (ne_of_gt hR)] at hi
  exact hi

/-- Two circles with distinct centers have at most two common points, expressed
as the radial distance-fiber capacity for any finite cyclic planar set. -/
theorem radial_card_le_two (H : Finset Plane) (O p : Plane) (R d : ℝ)
    (hcircle : ∀ h ∈ H, dist h O = R) (hp : p ≠ O) :
    (H.filter fun h => dist h p = d).card ≤ 2 := by
  classical
  let F := H.filter fun h => dist h p = d
  by_cases hF : 1 < F.card
  · obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hF
    have ha' := Finset.mem_filter.mp ha
    have hb' := Finset.mem_filter.mp hb
    have hsub : F ⊆ {a, b} := by
      intro c hc
      have hc' := Finset.mem_filter.mp hc
      have he := EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two
        (V := Plane) (by simp [finrank_euclideanSpace]) hp hab
        ha'.2 hb'.2 hc'.2 (hcircle a ha'.1) (hcircle b hb'.1) (hcircle c hc'.1)
      simpa only [Finset.mem_insert, Finset.mem_singleton] using he
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  · dsimp [F] at hF
    omega

/-- Augmenting a cyclic hull by two distinct strict interior points adds exactly two
points; neither of the new points is a hull vertex. -/
theorem card_insert_interiors (H : Finset Plane) (O z w : Plane) {R : ℝ}
    (hR : 0 < R) (hcircle : ∀ h ∈ H, dist h O = R)
    (hz : z ∈ interior (convexHull ℝ (H : Set Plane)))
    (hw : w ∈ interior (convexHull ℝ (H : Set Plane))) (hzw : z ≠ w) :
    (insert z (insert w H)).card = H.card + 2 := by
  classical
  have hzR := dist_center_lt_radius H O hR hcircle hz
  have hwR := dist_center_lt_radius H O hR hcircle hw
  have hzH : z ∉ H := fun hzH => (ne_of_lt hzR) (hcircle z hzH)
  have hwH : w ∉ H := fun hwH => (ne_of_lt hwR) (hcircle w hwH)
  simp [Finset.card_insert_of_notMem, hzH, hwH, hzw, Nat.add_assoc]

/-- Adding hull-interior points leaves the actual diameter unchanged. -/
theorem diam_insert_interiors (H : Finset Plane) (z w : Plane)
    (hz : z ∈ interior (convexHull ℝ (H : Set Plane)))
    (hw : w ∈ interior (convexHull ℝ (H : Set Plane))) :
    Metric.diam ((insert z (insert w H) : Finset Plane) : Set Plane) = Metric.diam (H : Set Plane) := by
  classical
  have hsub : ((insert z (insert w H) : Finset Plane) : Set Plane) ⊆ convexHull ℝ (H : Set Plane) := by
    intro p hp
    simp only [Finset.mem_coe, Finset.mem_insert] at hp
    rcases hp with rfl | rfl | hp
    · exact interior_subset hz
    · exact interior_subset hw
    · exact subset_convexHull ℝ (H : Set Plane) hp
  apply le_antisymm
  · exact Metric.diam_le_of_forall_dist_le Metric.diam_nonneg
      (fun _ hx _ hy => dist_le_diam_hull H (hsub hx) (hsub hy))
  · exact Metric.diam_mono (by intro p hp; simp [hp])
      (insert z (insert w H)).finite_toSet.isBounded

/-- Every nonempty finite planar set attains its actual metric diameter. -/
theorem exists_diameter_pair (H : Finset Plane) (hH : H.Nonempty) :
    ∃ a ∈ H, ∃ b ∈ H, dist a b = Metric.diam (H : Set Plane) := by
  classical
  obtain ⟨⟨a, b⟩, hab, hmax⟩ := (H ×ˢ H).exists_max_image
    (fun p : Plane × Plane => dist p.1 p.2) (hH.product hH)
  have ha := (Finset.mem_product.mp hab).1
  have hb := (Finset.mem_product.mp hab).2
  refine ⟨a, ha, b, hb, le_antisymm
    (Metric.dist_le_diam_of_mem H.finite_toSet.isBounded ha hb) ?_⟩
  exact Metric.diam_le_of_forall_dist_le dist_nonneg
    (fun x hx y hy => hmax (x, y) (Finset.mem_product.mpr ⟨hx, hy⟩))

/-- The occurring non-diameter distances of a finite planar set. -/
noncomputable def nonDiameterDistances (X : Finset Plane) : Finset ℝ := by
  classical
  exact ((pairs X).image pairDist).filter fun d => d < Metric.diam (X : Set Plane)

/-- Ground-truth membership in the distance set uses an actual pair and ordinary distance. -/
theorem mem_nonDiameterDistances (X : Finset Plane) (d : ℝ) :
    d ∈ nonDiameterDistances X ↔
      (∃ a ∈ X, ∃ b ∈ X, a ≠ b ∧ dist a b = d) ∧
        d < Metric.diam (X : Set Plane) := by
  classical
  simp only [nonDiameterDistances, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨e, he, hed⟩, hd⟩
    induction e using Sym2.ind with
    | _ a b =>
      have hp := (mk_mem_pairs X a b).mp he
      exact ⟨⟨a, hp.1, b, hp.2.1, hp.2.2, hed⟩, hd⟩
  · rintro ⟨⟨a, ha, b, hb, hab, hdist⟩, hd⟩
    exact ⟨⟨s(a, b), (mk_mem_pairs X a b).mpr ⟨ha, hb, hab⟩, hdist⟩, hd⟩

/-- The off-center radial family maps to occurring non-diameter lengths, so the
circle-intersection capacity forces at least half as many length classes as hull points. -/
theorem hull_card_le_twice_nonDiameter_card (H : Finset Plane) (O z w : Plane)
    (R : ℝ) (hcard : 2 ≤ H.card) (hcircle : ∀ h ∈ H, dist h O = R)
    (hz : z ∈ interior (convexHull ℝ (H : Set Plane)))
    (hw : w ∈ interior (convexHull ℝ (H : Set Plane))) (hzO : z ≠ O) :
    H.card ≤ 2 * (nonDiameterDistances (insert z (insert w H))).card := by
  classical
  have hnot : z ∉ H := by
    intro hzH
    obtain ⟨a, ha, b, hb, hdist⟩ := exists_diameter_pair H
      (Finset.card_pos.mp (by omega : 0 < H.card))
    -- The circle condition supplies the needed disjointness, via strict disk interiority.
    have hR : 0 < R := by
      have haR := hcircle a ha
      have hbR := hcircle b hb
      by_contra hn
      have hRa : R = 0 := le_antisymm (le_of_not_gt hn) (haR ▸ dist_nonneg)
      have haO : a = O := dist_eq_zero.mp (haR.trans hRa)
      have hbO : b = O := dist_eq_zero.mp (hbR.trans hRa)
      have hD := diam_pos H hcard
      rw [← hdist, haO, hbO, dist_self] at hD
      exact (lt_irrefl 0) hD
    exact (ne_of_lt (dist_center_lt_radius H O hR hcircle hz)) (hcircle z hzH)
  apply Finset.card_le_mul_card_image_of_maps_to (f := fun h => dist h z)
  · intro h hh
    apply (mem_nonDiameterDistances _ _).mpr
    refine ⟨⟨h, by simp [hh], z, by simp, Ne.symm (fun he => hnot (he ▸ hh)), rfl⟩, ?_⟩
    rw [diam_insert_interiors H z w hz hw, dist_comm]
    exact dist_lt_diam_hull H hcard hz (subset_convexHull ℝ (H : Set Plane) hh)
  · intro d hd
    exact radial_card_le_two H O z R d hcircle hzO

/-- All unordered pair multiplicities in the non-diameter classes sum to the
number of non-diameter pairs; the interior pair is included. -/
theorem sum_nonDiameter_multiplicity (X : Finset Plane) :
    ∑ d ∈ nonDiameterDistances X, multiplicity X d =
      ((pairs X).filter fun e => pairDist e < Metric.diam (X : Set Plane)).card := by
  classical
  let Q := (pairs X).filter fun e => pairDist e < Metric.diam (X : Set Plane)
  have hmap : ∀ e ∈ Q, pairDist e ∈ nonDiameterDistances X := by
    intro e he
    have he' := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨e, he'.1, rfl⟩, he'.2⟩
  have hsum := Finset.card_eq_sum_card_fiberwise hmap
  rw [hsum]
  apply Finset.sum_congr rfl
  intro d hd
  have hd' := (Finset.mem_filter.mp hd).2
  unfold multiplicity
  congr 1
  ext e
  simp only [Q, Finset.mem_filter]
  constructor
  · rintro ⟨he, hed⟩
    exact ⟨⟨he, hed ▸ hd'⟩, hed⟩
  · rintro ⟨⟨he, hlt⟩, hed⟩
    exact ⟨he, hed⟩

/-- Under the contrary multiplicity hypothesis, all-pair counting reserves at
least one diameter pair and gives the exact binomial budget. -/
theorem nonDiameter_pair_budget (X : Finset Plane) (hcard : 2 ≤ X.card)
    (hlarge : ∀ d ∈ nonDiameterDistances X, X.card + 1 ≤ multiplicity X d) :
    (nonDiameterDistances X).card * (X.card + 1) + 1 ≤ X.card.choose 2 := by
  classical
  let Q := (pairs X).filter fun e => pairDist e < Metric.diam (X : Set Plane)
  have hQ : Q.card < (pairs X).card := by
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.filter_subset _ _, ?_⟩
    obtain ⟨a, ha, b, hb, hdist⟩ := exists_diameter_pair X
      (Finset.card_pos.mp (by omega : 0 < X.card))
    have hab : a ≠ b := by
      intro he
      have hD := diam_pos X hcard
      rw [← hdist, he, dist_self] at hD
      exact (lt_irrefl 0) hD
    have he : s(a, b) ∈ pairs X := (mk_mem_pairs X a b).mpr ⟨ha, hb, hab⟩
    intro hEq
    have hmem : s(a, b) ∈ Q := hEq ▸ he
    have hlt := (Finset.mem_filter.mp hmem).2
    rw [pairDist_mk, hdist] at hlt
    exact (lt_irrefl _) hlt
  have hsum : (nonDiameterDistances X).card * (X.card + 1) ≤ Q.card := by
    rw [← sum_nonDiameter_multiplicity]
    calc
      _ = ∑ _d ∈ nonDiameterDistances X, (X.card + 1) := by simp
      _ ≤ _ := Finset.sum_le_sum hlarge
  rw [card_pairs] at hQ
  omega

/-- The radial lower bound and the pair budget force the even equality size;
in particular there are at least three non-diameter classes at the minimum size eight. -/
theorem even_size_of_pair_budget (n q : ℕ) (hn : 8 ≤ n)
    (hlower : n - 2 ≤ 2 * q) (hbudget : q * (n + 1) + 1 ≤ n.choose 2) :
    n = 2 * (q + 1) ∧ 3 ≤ q := by
  have hchoose : 2 * n.choose 2 ≤ n * (n - 1) := by
    rw [Nat.choose_two_right]
    exact Nat.mul_div_le _ _
  have hbudget2 : 2 * (q * (n + 1) + 1) ≤ n * (n - 1) :=
    (Nat.mul_le_mul_left 2 hbudget).trans hchoose
  have hsub : n - 1 + 1 = n := by omega
  have hupper : n ≤ 2 * q + 2 := by omega
  have hreverse : 2 * q + 2 ≤ n := by
    by_contra h
    have hq : n - 1 ≤ 2 * q := by omega
    have hmul := Nat.mul_le_mul_right (n + 1) hq
    nlinarith
  constructor
  · omega
  · omega

example : 8 = 2 * (3 + 1) ∧ 3 ≤ (3 : ℕ) :=
  even_size_of_pair_budget 8 3 (by decide) (by decide) (by decide)


/-- Exact total cardinality saturates each fiber of a capacity-two map. -/
theorem saturated_fibers {α β : Type*} [DecidableEq β] (H : Finset α) (T : Finset β) (f : α → β)
    (hmap : ∀ a ∈ H, f a ∈ T)
    (hcap : ∀ b ∈ T, (H.filter fun a => f a = b).card ≤ 2)
    (hcard : H.card = 2 * T.card) :
    ∀ b ∈ T, (H.filter fun a => f a = b).card = 2 := by
  classical
  have hsum : ∑ b ∈ T, (H.filter fun a => f a = b).card = ∑ _b ∈ T, (2 : ℕ) := by
    rw [← Finset.card_eq_sum_card_fiberwise hmap, hcard]
    simp [Nat.mul_comm]
  exact (Finset.sum_eq_sum_iff_of_le hcap).mp hsum

/-- The even equality size makes the pair budget an equality. -/
theorem choose_even_equality (n q : ℕ) (hn : n = 2 * (q + 1)) : n.choose 2 = q * (n + 1) + 1 := by
  have hs : n - 1 = 2 * q + 1 := by omega
  have hm : n * (n - 1) = 2 * (q * (n + 1) + 1) := by
    rw [hs, hn]
    ring
  rw [Nat.choose_two_right, hm]
  omega

/-- The contrary hypothesis and radial lower bound force equality in every pair budget. -/
theorem equality_structure (X : Finset Plane) (hn : 8 ≤ X.card)
    (hlower : X.card - 2 ≤ 2 * (nonDiameterDistances X).card)
    (hlarge : ∀ d ∈ nonDiameterDistances X, X.card + 1 ≤ multiplicity X d) :
    X.card = 2 * ((nonDiameterDistances X).card + 1) ∧
    3 ≤ (nonDiameterDistances X).card ∧
    (∀ d ∈ nonDiameterDistances X, multiplicity X d = X.card + 1) ∧
    ((pairs X).filter fun e => ¬pairDist e < Metric.diam (X : Set Plane)).card = 1 := by
  classical
  let T := nonDiameterDistances X
  let N := (pairs X).filter fun e => pairDist e < Metric.diam (X : Set Plane)
  let D := (pairs X).filter fun e => ¬pairDist e < Metric.diam (X : Set Plane)
  have hbudget := nonDiameter_pair_budget X (by omega) hlarge
  obtain ⟨heven, hq⟩ := even_size_of_pair_budget X.card T.card hn hlower hbudget
  have hchoose := choose_even_equality X.card T.card heven
  have hsplit : N.card + D.card = X.card.choose 2 := by
    rw [← card_pairs X]
    exact Finset.card_filter_add_card_filter_not _
  have hN : T.card * (X.card + 1) ≤ N.card := by
    rw [← sum_nonDiameter_multiplicity]
    calc
      _ = ∑ _d ∈ T, (X.card + 1) := by simp
      _ ≤ _ := Finset.sum_le_sum hlarge
  have hD : 1 ≤ D.card := by
    obtain ⟨a,ha,b,hb,hdist⟩ := exists_diameter_pair X
      (Finset.card_pos.mp (by omega : 0 < X.card))
    have hab : a ≠ b := by
      intro he
      have hpos := diam_pos X (by omega)
      rw [← hdist, he, dist_self] at hpos
      exact (lt_irrefl 0) hpos
    apply Nat.succ_le_of_lt
    apply Finset.card_pos.mpr
    refine ⟨s(a,b), Finset.mem_filter.mpr ⟨(mk_mem_pairs X a b).mpr ⟨ha,hb,hab⟩, ?_⟩⟩
    simp [pairDist_mk, hdist]
  have hNeq : N.card = T.card * (X.card + 1) := by omega
  have hDeq : D.card = 1 := by omega
  have hsum : ∑ _d ∈ T, (X.card + 1) = ∑ d ∈ T, multiplicity X d := by
    rw [sum_nonDiameter_multiplicity]
    simpa using hNeq.symm
  have hsaturated := (Finset.sum_eq_sum_iff_of_le hlarge).mp hsum
  exact ⟨heven, hq, fun d hd => (hsaturated d hd).symm, hDeq⟩

/-- A fixed-axis point is uniquely determined by its norm and distance to the axis point. -/
theorem fixed_fiber_unique {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u x y : E)
    (hx : (Submodule.reflection (ℝ ∙ u)) x = x)
    (hnorm : ‖y‖ = ‖x‖) (hdist : dist y u = dist x u) : y = x := by
  have hspan : x ∈ ℝ ∙ u := (Submodule.reflection_eq_self_iff x).mp hx
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hspan
  have hip : inner ℝ y u = inner ℝ x u := by
    have hy := norm_sub_sq_real y u
    have hx' := norm_sub_sq_real x u
    rw [dist_eq_norm, dist_eq_norm] at hdist
    rw [hdist, hnorm] at hy
    nlinarith
  have hxy : inner ℝ y x = inner ℝ x x := by
    calc
      inner ℝ y x = a * inner ℝ y u := by rw [← ha, inner_smul_right]
      _ = a * inner ℝ x u := by rw [hip]
      _ = inner ℝ x x := by rw [← ha, inner_smul_right]
  have hzero : ‖y - x‖ ^ 2 = 0 := by
    rw [norm_sub_sq_real, hnorm, hxy, real_inner_self_eq_norm_sq]
    ring
  exact sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (y-x)]))


/-- Saturated radial fibers force a fixed-point-free reflection permutation of the hull. -/
theorem reflection_preserves_saturated_hull (H : Finset Plane) (u : Plane) (R : ℝ)
    (hu : u ≠ 0) (hcircle : ∀ h ∈ H, ‖h‖ = R)
    (hsat : ∀ h ∈ H, (H.filter fun b => dist b u = dist h u).card = 2)
    (h : Plane) (hh : h ∈ H) :
    (Submodule.reflection (ℝ ∙ u)) h ∈ H ∧
      (Submodule.reflection (ℝ ∙ u)) h ≠ h := by
  classical
  let r := Submodule.reflection (ℝ ∙ u)
  have hfixu : r u = u := Submodule.reflection_mem_subspace_eq_self
    (Submodule.mem_span_singleton.mpr ⟨1, one_smul ℝ u⟩)
  obtain ⟨b, hb, hbh⟩ := Finset.exists_mem_ne
    (by rw [hsat h hh]; decide : 1 < (H.filter fun b => dist b u = dist h u).card) h
  have hb' := Finset.mem_filter.mp hb
  have hnot : r h ≠ h := by
    intro hfix
    exact hbh (fixed_fiber_unique u h b hfix
      ((hcircle b hb'.1).trans (hcircle h hh).symm) hb'.2)
  have hrd : dist (r h) u = dist h u := by
    simpa only [hfixu] using r.dist_map h u
  have hnorm : dist (r h) 0 = R := by
    rw [dist_zero_right, r.norm_map]
    exact hcircle h hh
  have he := EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two
    (V := Plane) (p₁ := h) (p₂ := r h)
    (by simp [finrank_euclideanSpace]) hu hnot.symm
    rfl hrd hb'.2
    (by simpa only [dist_zero_right] using hcircle h hh) hnorm
    (by simpa only [dist_zero_right] using hcircle b hb'.1)
  rcases he with he | he
  · exact False.elim (hbh he)
  · exact ⟨he ▸ hb'.1, hnot⟩


/-- Two nonzero reflection axes swapping the same distinct endpoints are collinear. -/
theorem common_axis_of_swap (u v A B : Plane) (hu : u ≠ 0) (hAB : A ≠ B)
    (huA : (Submodule.reflection (ℝ ∙ u)) A = B)
    (huB : (Submodule.reflection (ℝ ∙ u)) B = A)
    (hvA : (Submodule.reflection (ℝ ∙ v)) A = B)
    (hvB : (Submodule.reflection (ℝ ∙ v)) B = A) : ∃ b : ℝ, b • u = v := by
  have hinner : ∀ t : Plane,
      (Submodule.reflection (ℝ ∙ t)) A = B →
      (Submodule.reflection (ℝ ∙ t)) B = A → inner ℝ (A-B) t = 0 := by
    intro t htA htB
    have hn : (Submodule.reflection (ℝ ∙ t)) (A-B) = -(A-B) := by
      rw [map_sub, htA, htB]
      abel
    have ho : (Submodule.reflection (ℝ ∙ t)ᗮ) (A-B) = A-B := by
      rw [Submodule.reflection_orthogonal_apply, hn, neg_neg]
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.mp
      ((Submodule.reflection_eq_self_iff (A-B)).mp ho)
  haveI : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [finrank_euclideanSpace]⟩
  exact Submodule.mem_span_singleton.mp
    (Submodule.mem_span_singleton_of_inner_eq_zero_of_inner_eq_zero
      (sub_ne_zero.mpr hAB) hu (hinner v hvA hvB) (hinner u huA huB))

/-- Opposite centers with equal radial supports and saturated fibers force central symmetry. -/
theorem central_symmetry_of_opposite_support (H : Finset Plane) (u : Plane) (R : ℝ)
    (hu : u ≠ 0) (hcircle : ∀ h ∈ H, ‖h‖ = R)
    (hsat : ∀ h ∈ H, (H.filter fun b => dist b u = dist h u).card = 2)
    (hsupport : ∀ h ∈ H, ∃ k ∈ H, dist k (-u) = dist h u) :
    ∀ h ∈ H, -h ∈ H := by
  intro h hh
  let r := Submodule.reflection (ℝ ∙ u)
  obtain ⟨k,hk,hkd⟩ := hsupport h hh
  have hrk := reflection_preserves_saturated_hull H u R hu hcircle hsat k hk
  have hfixu : r u = u := Submodule.reflection_mem_subspace_eq_self
    (Submodule.mem_span_singleton.mpr ⟨1, one_smul ℝ u⟩)
  have hfixnu : r (-u) = -u := by rw [map_neg, hfixu]
  have hrd : dist (r k) (-u) = dist h u := by
    calc
      _ = dist (r k) (r (-u)) := by rw [hfixnu]
      _ = dist k (-u) := r.dist_map k (-u)
      _ = _ := hkd
  have hnegd : dist (-h) (-u) = dist h u := dist_neg_neg h u
  have he := EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two
    (V := Plane) (p₁ := k) (p₂ := r k) (p := -h)
    (by simp [finrank_euclideanSpace]) (neg_ne_zero.mpr hu) hrk.2.symm
    hkd hrd hnegd
    (by simpa only [dist_zero_right] using hcircle k hk)
    (by rw [dist_zero_right, r.norm_map]; exact hcircle k hk)
    (by simpa only [dist_zero_right, norm_neg] using hcircle h hh)
  rcases he with he | he
  · exact he ▸ hk
  · exact he ▸ hrk.1

/-- A real affine map permuting a finite set with at least two points has slope ±1. -/
theorem finite_affine_slope (S : Finset ℝ) (hc : 2 ≤ S.card) (a c : ℝ)
    (him : S.image (fun x => a*x+c) = S) : a = 1 ∨ a = -1 := by
  classical
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  let l := S.min' hne
  let u := S.max' hne
  have hlu : l < u := S.min'_lt_max'_of_card (by omega)
  have hl : l ∈ S := S.min'_mem hne
  have hu : u ∈ S := S.max'_mem hne
  have hb : ∀ x ∈ S, l ≤ x ∧ x ≤ u := by
    intro x hx
    exact ⟨S.min'_le x hx, S.le_max' x hx⟩
  have hf : ∀ x ∈ S, a*x+c ∈ S := by
    intro x hx
    rw [← him]
    exact Finset.mem_image.mpr ⟨x,hx,rfl⟩
  obtain ⟨x,hx,hfx⟩ := Finset.mem_image.mp (him.symm ▸ hl)
  obtain ⟨y,hy,hfy⟩ := Finset.mem_image.mp (him.symm ▸ hu)
  rcases le_total 0 a with hpos | hneg
  · have hupper := sub_le_sub (hb (a*u+c) (hf u hu)).2 (hb (a*l+c) (hf l hl)).1
    have hlower := mul_le_mul_of_nonneg_left
      (sub_le_sub (hb y hy).2 (hb x hx).1) hpos
    have hspan : a * (y-x) = u-l := by rw [← hfx, ← hfy]; ring
    rw [hspan] at hlower
    left
    nlinarith
  · have hupper := sub_le_sub (hb (a*l+c) (hf l hl)).2 (hb (a*u+c) (hf u hu)).1
    have hlower := mul_le_mul_of_nonneg_left
      (sub_le_sub (hb x hx).2 (hb y hy).1) (neg_nonneg.mpr hneg)
    have hspan : (-a) * (x-y) = u-l := by rw [← hfx, ← hfy]; ring
    rw [hspan] at hlower
    right
    nlinarith

example : ({0,1} : Finset ℝ).image (fun x => (-1)*x+1) = {0,1} := by
  ext x
  simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨y, rfl | rfl, rfl⟩ <;> norm_num
  · rintro (rfl | rfl)
    · exact ⟨1, Or.inr rfl, by norm_num⟩
    · exact ⟨0, Or.inl rfl, by norm_num⟩

/-- Squared radial distances at collinear centers are related by a real affine map. -/
theorem radial_square_affine (h u : Plane) (R b : ℝ) (hR : ‖h‖ = R) :
    dist h (b • u)^2 = b * dist h u^2 + (1-b)*R^2 + (b^2-b)*‖u‖^2 := by
  rw [dist_eq_norm, dist_eq_norm, norm_sub_sq_real, norm_sub_sq_real,
    inner_smul_right, norm_smul, Real.norm_eq_abs, hR]
  rw [mul_pow, sq_abs]
  ring

/-- Equal radial supports at distinct collinear centers force opposite centers. -/
theorem opposite_centers_of_support (H : Finset Plane) (u : Plane) (R b : ℝ)
    (hcircle : ∀ h ∈ H, ‖h‖ = R) (hb : b ≠ 1)
    (hcard : 2 ≤ (H.image fun h => dist h u ^ 2).card)
    (hsupport : (H.image fun h => dist h (b • u)^2) =
      (H.image fun h => dist h u^2)) : b = -1 := by
  classical
  let c := (1-b)*R^2 + (b^2-b)*‖u‖^2
  have hmap : (H.image fun h => dist h u^2).image (fun x => b*x+c) =
      H.image (fun h => dist h u^2) := by
    rw [Finset.image_image]
    calc
      _ = H.image (fun h => dist h (b • u)^2) := by
        apply Finset.image_congr
        intro h hh
        simpa only [Function.comp_apply, c, add_assoc] using
          (radial_square_affine h u R b (hcircle h hh)).symm
      _ = _ := hsupport
  rcases finite_affine_slope (H.image fun h => dist h u^2) hcard b c hmap with h | h
  · exact False.elim (hb h)
  · exact h

/-- Every positive chord length on a circle has at most one unordered pair per vertex. -/
theorem chord_capacity (H : Finset Plane) (O : Plane) (R d : ℝ)
    (hR : 0 < R) (hcircle : ∀ h ∈ H, dist h O = R) : multiplicity H d ≤ H.card := by
  classical
  let Q := (pairs H).filter fun e => pairDist e = d
  have hm : ∀ e ∈ Q, 2 ≤ (H.bipartiteAbove (fun e h => h ∈ e) e).card := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      have hp := (mk_mem_pairs H a b).mp (Finset.mem_filter.mp he).1
      have hfilter : H.bipartiteAbove (fun e h => h ∈ e) s(a,b) = {a,b} := by
        ext h
        simp only [Finset.bipartiteAbove, Finset.mem_filter, Finset.mem_insert,
          Finset.mem_singleton, Sym2.mem_iff]
        aesop
      rw [hfilter, Finset.card_pair hp.2.2]
  have hn : ∀ h ∈ H, (Q.bipartiteBelow (fun e h => h ∈ e) h).card ≤ 2 := by
    intro h hh
    have hne : h ≠ O := by
      intro he
      have hc := hcircle h hh
      rw [he, dist_self] at hc
      linarith
    have hsub : Q.bipartiteBelow (fun e h => h ∈ e) h ⊆
        (H.filter fun b => dist b h = d).image (fun b => s(h,b)) := by
      intro e he
      have hq := Finset.mem_filter.mp he
      have he' := Finset.mem_filter.mp hq.1
      induction e using Sym2.ind with
      | _ a b =>
        have hp := (mk_mem_pairs H a b).mp he'.1
        have hd : dist a b = d := he'.2
        have hem : h = a ∨ h = b := by simpa using hq.2
        rcases hem with rfl | rfl
        · exact Finset.mem_image.mpr ⟨b, Finset.mem_filter.mpr
            ⟨hp.2.1, by simpa only [dist_comm] using hd⟩, rfl⟩
        · exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨hp.1, hd⟩,
            Sym2.eq_swap⟩
    calc
      _ ≤ ((H.filter fun b => dist b h = d).image (fun b => s(h,b))).card :=
        Finset.card_le_card hsub
      _ ≤ (H.filter fun b => dist b h = d).card := Finset.card_image_le
      _ ≤ 2 := radial_card_le_two H O h R d hcircle hne
  have hc : Q.card • (2 : ℕ) ≤ H.card • (2 : ℕ) :=
    Finset.card_nsmul_le_card_nsmul (fun (e : Sym2 Plane) (h : Plane) => h ∈ e) hm hn
  change Q.card ≤ H.card
  simpa only [smul_eq_mul] using (Nat.mul_le_mul_right_iff (by decide : 0 < 2)).mp hc

/-- Away from the center radius and the interior-interior distance, a centered configuration has multiplicity at most hull size plus two. -/
theorem center_multiplicity_bound (H : Finset Plane) (O v : Plane) (R d : ℝ)
    (hR : 0 < R) (hcircle : ∀ h ∈ H, dist h O = R) (hv : v ≠ O)
    (hdR : d ≠ R) (hdv : d ≠ dist O v) :
    multiplicity (insert O (insert v H)) d ≤ H.card + 2 := by
  classical
  let Q := (pairs (insert O (insert v H))).filter fun e => pairDist e = d
  let P := (pairs H).filter fun e => pairDist e = d
  let S := (H.filter fun h => dist h v = d).image fun h => s(v,h)
  have hsub : Q ⊆ P ∪ S := by
    intro e he
    have he' := Finset.mem_filter.mp he
    induction e using Sym2.ind with
    | _ a b =>
      have hp := (mk_mem_pairs (insert O (insert v H)) a b).mp he'.1
      have hd : dist a b = d := he'.2
      have ha : a = O ∨ a = v ∨ a ∈ H := by simpa using hp.1
      have hb : b = O ∨ b = v ∨ b ∈ H := by simpa using hp.2.1
      rcases ha with rfl | rfl | ha <;> rcases hb with rfl | rfl | hb
      · exact False.elim (hp.2.2 rfl)
      · exact False.elim (hdv hd.symm)
      · have hc := hcircle b hb
        exact False.elim (hdR (hd.symm.trans (dist_comm _ b |>.trans hc)))
      · exact False.elim (hdv (hd.symm.trans (dist_comm _ _)))
      · exact False.elim (hp.2.2 rfl)
      · apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨b, Finset.mem_filter.mpr
          ⟨hb, (dist_comm b _).trans hd⟩, rfl⟩
      · exact False.elim (hdR (hd.symm.trans (hcircle a ha)))
      · apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, hd⟩, Sym2.eq_swap⟩
      · apply Finset.mem_union_left
        exact Finset.mem_filter.mpr ⟨(mk_mem_pairs H a b).mpr ⟨ha,hb,hp.2.2⟩, hd⟩
  have hP : P.card ≤ H.card := chord_capacity H O R d hR hcircle
  have hS : S.card ≤ 2 := (Finset.card_image_le).trans
    (radial_card_le_two H O v R d hcircle hv)
  change Q.card ≤ H.card + 2
  calc
    _ ≤ (P ∪ S).card := Finset.card_le_card hsub
    _ ≤ P.card + S.card := Finset.card_union_le P S
    _ ≤ _ := Nat.add_le_add hP hS

/-- A centered configuration with uniformly oversized classes has at most two nondiameter distances. -/
theorem center_support_card_le_two (H : Finset Plane) (O v : Plane) (R : ℝ)
    (hR : 0 < R) (hcircle : ∀ h ∈ H, dist h O = R) (hv : v ≠ O)
    (hlarge : ∀ d ∈ nonDiameterDistances (insert O (insert v H)),
      H.card + 3 ≤ multiplicity (insert O (insert v H)) d) :
    (nonDiameterDistances (insert O (insert v H))).card ≤ 2 := by
  classical
  have hsub : nonDiameterDistances (insert O (insert v H)) ⊆ {R, dist O v} := by
    intro d hd
    by_cases hdR : d = R
    · simp [hdR]
    by_cases hdv : d = dist O v
    · simp [hdv]
    have hupper := center_multiplicity_bound H O v R d hR hcircle hv hdR hdv
    have hlower := hlarge d hd
    omega
  exact (Finset.card_le_card hsub).trans
    (by simpa only [Finset.card_singleton] using
      Finset.card_insert_le R ({dist O v} : Finset ℝ))

/-- An interior radial distance is a genuine nondiameter distance. -/
theorem radial_mem (H : Finset Plane) (O z w : Plane) (R : ℝ)
    (hcard : 2 ≤ H.card) (hR : 0 < R) (hcircle : ∀ h ∈ H, dist h O = R)
    (hz : z ∈ interior (convexHull ℝ (H : Set Plane)))
    (hw : w ∈ interior (convexHull ℝ (H : Set Plane))) (h : Plane) (hh : h ∈ H) :
    dist h z ∈ nonDiameterDistances (insert z (insert w H)) := by
  classical
  have hnot : z ∉ H := fun hmem =>
    (ne_of_lt (dist_center_lt_radius H O hR hcircle hz)) (hcircle z hmem)
  apply (mem_nonDiameterDistances _ _).mpr
  refine ⟨⟨h, by simp [hh], z, by simp, Ne.symm (fun he => hnot (he ▸ hh)), rfl⟩, ?_⟩
  rw [diam_insert_interiors H z w hz hw, dist_comm]
  exact dist_lt_diam_hull H hcard hz (subset_convexHull ℝ (H : Set Plane) hh)

/-- Saturated radial fibers cover exactly the common nondiameter support. -/
theorem saturated_radial_support (H : Finset Plane) (O z w : Plane) (R : ℝ)
    (hcard : 2 ≤ H.card) (hR : 0 < R) (hcircle : ∀ h ∈ H, dist h O = R)
    (hz : z ∈ interior (convexHull ℝ (H : Set Plane)))
    (hw : w ∈ interior (convexHull ℝ (H : Set Plane))) (hzO : z ≠ O)
    (heq : H.card = 2 * (nonDiameterDistances (insert z (insert w H))).card) :
    (∀ d ∈ nonDiameterDistances (insert z (insert w H)),
      (H.filter fun h => dist h z = d).card = 2) ∧
    H.image (fun h => dist h z) = nonDiameterDistances (insert z (insert w H)) := by
  classical
  let T := nonDiameterDistances (insert z (insert w H))
  have hmap : ∀ h ∈ H, dist h z ∈ T := radial_mem H O z w R hcard hR hcircle hz hw
  have hs := saturated_fibers H T (fun h => dist h z) hmap
    (fun d _ => radial_card_le_two H O z R d hcircle hzO) heq
  refine ⟨hs, ?_⟩
  ext d
  constructor
  · rintro hd
    obtain ⟨h,hh,rfl⟩ := Finset.mem_image.mp hd
    exact hmap h hh
  · intro hd
    obtain ⟨h,hh⟩ := Finset.card_pos.mp (by rw [hs d hd]; decide :
      0 < (H.filter fun h => dist h z = d).card)
    exact Finset.mem_image.mpr ⟨h, (Finset.mem_filter.mp hh).1, (Finset.mem_filter.mp hh).2⟩

/-- A saturated reflection swaps the endpoints of a unique diameter. -/
theorem reflection_swaps_unique_diameter (H : Finset Plane) (u : Plane) (R : ℝ)
    (hu : u ≠ 0) (hcircle : ∀ h ∈ H, ‖h‖ = R)
    (hsat : ∀ h ∈ H, (H.filter fun b => dist b u = dist h u).card = 2)
    (A B : Plane) (hA : A ∈ H) (hB : B ∈ H)
    (hunique : ∀ a ∈ H, ∀ b ∈ H, dist a b = dist A B → s(a,b) = s(A,B)) :
    (Submodule.reflection (ℝ ∙ u)) A = B ∧
    (Submodule.reflection (ℝ ∙ u)) B = A := by
  let r := Submodule.reflection (ℝ ∙ u)
  have hrA := reflection_preserves_saturated_hull H u R hu hcircle hsat A hA
  have hrB := reflection_preserves_saturated_hull H u R hu hcircle hsat B hB
  have he := hunique (r A) hrA.1 (r B) hrB.1 (r.dist_map A B)
  rcases Sym2.eq_iff.mp he with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · exact False.elim (hrA.2 ha)
  · exact ⟨ha,hb⟩

/-- A centrally symmetric circle with a unique diameter has at most two vertices. -/
theorem central_unique_card_le_two (H : Finset Plane) (R : ℝ)
    (hR : 0 < R) (hcircle : ∀ h ∈ H, ‖h‖ = R)
    (hsym : ∀ h ∈ H, -h ∈ H) (A B : Plane) (hA : A ∈ H)
    (hAB : dist A B = Metric.diam (H : Set Plane))
    (hunique : ∀ a ∈ H, ∀ b ∈ H, dist a b = dist A B → s(a,b) = s(A,B)) :
    H.card ≤ 2 := by
  classical
  have hd : ∀ h ∈ H, dist h (-h) = Metric.diam (H : Set Plane) := by
    intro h hh
    have hnorm : dist h (-h) = 2*R := by
      rw [dist_eq_norm, sub_neg_eq_add, ← two_smul ℝ h, norm_smul,
        Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ)<2), hcircle h hh]
    apply le_antisymm
    · exact Metric.dist_le_diam_of_mem H.finite_toSet.isBounded hh (hsym h hh)
    · rw [hnorm]
      apply Metric.diam_le_of_forall_dist_le (by positivity)
      intro x hx y hy
      calc
        dist x y ≤ dist x 0 + dist 0 y := dist_triangle x 0 y
        _ = 2*R := by simp [hcircle x hx, hcircle y hy, dist_eq_norm, two_mul]
  have hsub : H ⊆ {A,B} := by
    intro h hh
    have he := hunique h hh (-h) (hsym h hh) ((hd h hh).trans hAB.symm)
    rcases Sym2.eq_iff.mp he with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · simp [ha]
    · simp [ha]
  exact (Finset.card_le_card hsub).trans
    (by simpa only [Finset.card_singleton] using Finset.card_insert_le A ({B}:Finset Plane))

/-- The equality case is impossible for two distinct interior points of a centered circle. -/
theorem zero_center_contrary (H : Finset Plane) (z w : Plane) (R : ℝ)
    (hH : 6 ≤ H.card) (hR : 0 < R) (hcircle : ∀ h ∈ H, ‖h‖ = R)
    (hz : z ∈ interior (convexHull ℝ (H : Set Plane)))
    (hw : w ∈ interior (convexHull ℝ (H : Set Plane))) (hzw : z ≠ w) (hz0 : z ≠ 0)
    (hlarge : ∀ d ∈ nonDiameterDistances (insert z (insert w H)),
      (insert z (insert w H)).card + 1 ≤ multiplicity (insert z (insert w H)) d) : False := by
  classical
  let X := insert z (insert w H)
  let T := nonDiameterDistances X
  have hcircle' : ∀ h ∈ H, dist h (0 : Plane) = R := by
    simpa only [dist_zero_right] using hcircle
  have hXcard := card_insert_interiors H 0 z w hR hcircle' hz hw hzw
  have hlower := hull_card_le_twice_nonDiameter_card H 0 z w R (by omega) hcircle' hz hw hz0
  have hN : 8 ≤ X.card := by dsimp [X]; omega
  obtain ⟨heven,hq,hmu,hD⟩ := equality_structure X hN (by dsimp [X]; omega) hlarge
  have heq : H.card = 2*T.card := by dsimp [X, T] at *; omega
  have hw0 : w ≠ 0 := by
    intro he
    have hXe : insert (0 : Plane) (insert z H) = X := by
      simp only [X, he, Finset.insert_comm]
    have hc := center_support_card_le_two H 0 z R hR hcircle' hz0
      (by intro d hd; rw [hXe] at hd ⊢; have hl := hlarge d hd
          change H.card + 3 ≤ multiplicity (insert z (insert w H)) d
          omega)
    rw [hXe] at hc
    omega
  have hsZ := saturated_radial_support H 0 z w R (by omega) hR hcircle' hz hw hz0 heq
  have hsW : (∀ d ∈ T, (H.filter fun h => dist h w = d).card = 2) ∧
      H.image (fun h => dist h w) = T := by
    simpa only [Finset.insert_comm] using
      saturated_radial_support H 0 w z R (by omega) hR hcircle' hw hz hw0
        (by simpa only [Finset.insert_comm] using heq)
  have hsatZ : ∀ h ∈ H, (H.filter fun b => dist b z = dist h z).card = 2 :=
    fun h hh => hsZ.1 _ (radial_mem H 0 z w R (by omega) hR hcircle' hz hw h hh)
  have hsatW : ∀ h ∈ H, (H.filter fun b => dist b w = dist h w).card = 2 := by
    intro h hh
    apply hsW.1
    rw [← hsW.2]
    exact Finset.mem_image.mpr ⟨h,hh,rfl⟩
  obtain ⟨A,hA,B,hB,hAB⟩ := exists_diameter_pair H (Finset.card_pos.mp (by omega))
  have hABne : A ≠ B := by
    intro he
    have hp := diam_pos H (by omega)
    rw [← hAB,he,dist_self] at hp
    exact (lt_irrefl 0) hp
  have hdiam : Metric.diam (X : Set Plane) = Metric.diam (H : Set Plane) :=
    diam_insert_interiors H z w hz hw
  have hmemD : ∀ a ∈ H, ∀ b ∈ H, dist a b = Metric.diam (H : Set Plane) →
      s(a,b) ∈ (pairs X).filter fun e => ¬pairDist e < Metric.diam (X : Set Plane) := by
    intro a ha b hb hab
    have hne : a ≠ b := by
      intro he
      have hp := diam_pos H (by omega)
      rw [← hab,he,dist_self] at hp
      exact (lt_irrefl 0) hp
    apply Finset.mem_filter.mpr
    refine ⟨(mk_mem_pairs X a b).mpr ⟨by simp [X,ha],by simp [X,hb],hne⟩, ?_⟩
    simp [pairDist_mk,hab,hdiam]
  have hunique : ∀ a ∈ H, ∀ b ∈ H, dist a b = dist A B → s(a,b) = s(A,B) := by
    intro a ha b hb hab
    exact Finset.card_le_one.mp (le_of_eq hD) _ (hmemD a ha b hb (hab.trans hAB))
      _ (hmemD A hA B hB hAB)
  have hswapZ := reflection_swaps_unique_diameter H z R hz0 hcircle hsatZ A B hA hB hunique
  have hswapW := reflection_swaps_unique_diameter H w R hw0 hcircle hsatW A B hA hB hunique
  obtain ⟨b,hb⟩ := common_axis_of_swap z w A B hz0 hABne
    hswapZ.1 hswapZ.2 hswapW.1 hswapW.2
  have hb1 : b ≠ 1 := by
    intro he
    rw [he,one_smul] at hb
    exact hzw hb
  have hsq : (H.image fun h => dist h w^2) = H.image (fun h => dist h z^2) := by
    have he := congrArg (fun S : Finset ℝ => S.image fun d => d^2)
      (hsW.2.trans hsZ.2.symm)
    simpa only [Finset.image_image,Function.comp_def] using he
  have hsqcard : (H.image fun h => dist h z^2).card = T.card := by
    have hinj : Set.InjOn (fun d : ℝ => d^2) (H.image fun h => dist h z) := by
      intro a ha b hb hab
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hb
      nlinarith [dist_nonneg (x:=x) (y:=z),dist_nonneg (x:=y) (y:=z)]
    have hc := Finset.card_image_of_injOn hinj
    calc
      _ = ((H.image fun h => dist h z).image fun d => d^2).card := by
        rw [Finset.image_image]; rfl
      _ = (H.image fun h => dist h z).card := hc
      _ = T.card := congrArg Finset.card hsZ.2
  have hbneg : b = -1 := opposite_centers_of_support H z R b hcircle hb1
    (by rw [hsqcard]; omega) (by rw [hb]; exact hsq)
  have hwneg : w = -z := by rw [← hb,hbneg,neg_one_smul]
  have hsupport : ∀ h ∈ H, ∃ k ∈ H, dist k (-z) = dist h z := by
    intro h hh
    have hd : dist h z ∈ T := radial_mem H 0 z w R (by omega) hR hcircle' hz hw h hh
    rw [← hsW.2] at hd
    obtain ⟨k,hk,hkd⟩ := Finset.mem_image.mp hd
    exact ⟨k,hk,by simpa only [hwneg] using hkd⟩
  have hsym := central_symmetry_of_opposite_support H z R hz0 hcircle hsatZ hsupport
  have hc := central_unique_card_le_two H R hR hcircle hsym A B hA hAB hunique
  omega

/-- Two distinct interior points of a circle with at least six hull points yield a nondiameter distance occurring between one and the total number of points times. -/
theorem zero_center_witness (H : Finset Plane) (z w : Plane) (R : ℝ)
    (hH : 6 ≤ H.card) (hR : 0 < R) (hcircle : ∀ h ∈ H, ‖h‖ = R)
    (hz : z ∈ interior (convexHull ℝ (H : Set Plane)))
    (hw : w ∈ interior (convexHull ℝ (H : Set Plane))) (hzw : z ≠ w) :
    ∃ d : ℝ, 0 < d ∧ d < Metric.diam ((insert z (insert w H):Finset Plane):Set Plane) ∧
      1 ≤ multiplicity (insert z (insert w H)) d ∧
      multiplicity (insert z (insert w H)) d ≤ (insert z (insert w H)).card := by
  classical
  by_contra hno
  have hlarge : ∀ d ∈ nonDiameterDistances (insert z (insert w H)),
      (insert z (insert w H)).card + 1 ≤ multiplicity (insert z (insert w H)) d := by
    intro d hd
    obtain ⟨⟨a,ha,b,hb,hab,hdist⟩,hlt⟩ := (mem_nonDiameterDistances _ _).mp hd
    have hpos : 0 < d := hdist ▸ dist_pos.mpr hab
    have hm : 1 ≤ multiplicity (insert z (insert w H)) d := by
      apply Nat.succ_le_of_lt
      apply Finset.card_pos.mpr
      exact ⟨s(a,b),Finset.mem_filter.mpr ⟨(mk_mem_pairs _ a b).mpr ⟨ha,hb,hab⟩,hdist⟩⟩
    by_contra hsmall
    exact hno ⟨d,hpos,hlt,hm,by omega⟩
  by_cases hz0 : z = 0
  · have hw0 : w ≠ 0 := by intro he; exact hzw (hz0.trans he.symm)
    apply zero_center_contrary H w z R hH hR hcircle hw hz hzw.symm hw0
    simpa only [Finset.insert_comm] using hlarge
  · exact zero_center_contrary H z w R hH hR hcircle hz hw hzw hz0 hlarge

/-- Isometries preserve genuine unordered distinct-pair multiplicity. -/
theorem multiplicity_image_isometry (X : Finset Plane) (f : Plane → Plane)
    (hf : Isometry f) (d : ℝ) : multiplicity (X.image f) d = multiplicity X d := by
  classical
  symm
  unfold Erdos132.TwoInteriorCircle.multiplicity
  apply Finset.card_bij (fun e _ => Sym2.map f e)
  · intro e he
    induction e using Sym2.ind with
    | _ a b =>
      have hq := Finset.mem_filter.mp he
      have hp := (mk_mem_pairs X a b).mp hq.1
      apply Finset.mem_filter.mpr
      exact ⟨(mk_mem_pairs _ _ _).mpr ⟨Finset.mem_image.mpr ⟨a,hp.1,rfl⟩,
        Finset.mem_image.mpr ⟨b,hp.2.1,rfl⟩,fun hab => hp.2.2 (hf.injective hab)⟩,
        (hf.dist_eq a b).trans hq.2⟩
  · intro a ha b hb hab
    exact Sym2.map.injective hf.injective hab
  · intro e he
    induction e using Sym2.ind with
    | _ a b =>
      have hq := Finset.mem_filter.mp he
      have hp := (mk_mem_pairs _ a b).mp hq.1
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp.1
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hp.2.1
      refine ⟨s(x,y),Finset.mem_filter.mpr ⟨(mk_mem_pairs X x y).mpr
        ⟨hx,hy,fun he => hp.2.2 (congrArg f he)⟩, ?_⟩,rfl⟩
      exact (hf.dist_eq x y).symm.trans hq.2

/-- Translation preserves membership in ambient hull interior. -/
theorem sub_mem_interior_hull (H : Finset Plane) (O z : Plane)
    (hz : z ∈ interior (convexHull ℝ (H : Set Plane))) :
    z-O ∈ interior (convexHull ℝ ((H.image fun h => h-O) : Set Plane)) := by
  classical
  have hset : ((H.image fun h => h-O) : Set Plane) = (-O) +ᵥ (H : Set Plane) := by
    rw [Finset.coe_image]
    ext p
    simp only [Set.mem_image, Set.mem_vadd_set]
    constructor
    · rintro ⟨h,hh,rfl⟩
      exact ⟨h,hh,by simp [sub_eq_add_neg,add_comm]⟩
    · rintro ⟨h,hh,rfl⟩
      exact ⟨h,hh,by simp [sub_eq_add_neg,add_comm]⟩
  rw [hset,convexHull_vadd,interior_vadd]
  exact ⟨z,hz,by simp [sub_eq_add_neg,add_comm]⟩

/-- Two distinct ambient-interior points of a circle with at least six hull vertices admit a genuine small-multiplicity nondiameter distance. -/
theorem circle_witness (H : Finset Plane) (O z w : Plane) (R : ℝ)
    (hH : 6 ≤ H.card) (hR : 0 < R) (hcircle : ∀ h ∈ H, dist h O = R)
    (hz : z ∈ interior (convexHull ℝ (H : Set Plane)))
    (hw : w ∈ interior (convexHull ℝ (H : Set Plane))) (hzw : z ≠ w) :
    ∃ d : ℝ, 0 < d ∧ d < Metric.diam ((insert z (insert w H):Finset Plane):Set Plane) ∧
      1 ≤ multiplicity (insert z (insert w H)) d ∧
      multiplicity (insert z (insert w H)) d ≤ (insert z (insert w H)).card := by
  classical
  let f : Plane → Plane := fun h => h-O
  have hf : Isometry f := fun a b => by simp [f,edist_dist]
  have hcard : (H.image f).card = H.card := Finset.card_image_of_injective H hf.injective
  have hcircle' : ∀ h ∈ H.image f, ‖h‖ = R := by
    intro h hh
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hh
    exact hcircle a ha
  obtain ⟨d,hpos,hlt,hm,hbound⟩ := zero_center_witness (H.image f) (f z) (f w) R
    (by rw [hcard]; exact hH) hR hcircle'
    (sub_mem_interior_hull H O z hz) (sub_mem_interior_hull H O w hw)
    (fun he => hzw (hf.injective he))
  have himage : insert (f z) (insert (f w) (H.image f)) = (insert z (insert w H)).image f := by
    simp only [Finset.image_insert]
  rw [himage] at hlt hm hbound
  rw [multiplicity_image_isometry _ f hf] at hm hbound
  rw [Finset.card_image_of_injective _ hf.injective] at hbound
  rw [Finset.coe_image,hf.diam_image] at hlt
  exact ⟨d,hpos,hlt,hm,hbound⟩

/-- The universal two-interior cyclic-hull theorem: the configuration has n points and a genuine nondiameter distance of multiplicity between one and n. -/
theorem two_interior_circle (n : ℕ) (H : Finset Plane) (O z w : Plane) (R : ℝ)
    (hn : 8 ≤ n) (hH : H.card = n-2) (hcircle : ∀ h ∈ H, dist h O = R)
    (_hextreme : ∀ h ∈ H, h ∈ (convexHull ℝ (H : Set Plane)).extremePoints ℝ)
    (hz : z ∈ interior (convexHull ℝ (H : Set Plane)))
    (hw : w ∈ interior (convexHull ℝ (H : Set Plane))) (hzw : z ≠ w) :
    (insert z (insert w H)).card = n ∧
    ∃ d : ℝ, 0 < d ∧ d < Metric.diam ((insert z (insert w H):Finset Plane):Set Plane) ∧
      1 ≤ multiplicity (insert z (insert w H)) d ∧
      multiplicity (insert z (insert w H)) d ≤ n := by
  classical
  have hH6 : 6 ≤ H.card := by omega
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp (show 1 < H.card by omega)
  have hR : 0 < R := by
    have hnon : 0 ≤ R := (hcircle a ha) ▸ dist_nonneg
    have hne : R ≠ 0 := by
      intro he
      have haO : a = O := dist_eq_zero.mp ((hcircle a ha).trans he)
      have hbO : b = O := dist_eq_zero.mp ((hcircle b hb).trans he)
      exact hab (haO.trans hbO.symm)
    exact lt_of_le_of_ne hnon (Ne.symm hne)
  have hc : (insert z (insert w H)).card = n := by
    rw [card_insert_interiors H O z w hR hcircle hz hw hzw]
    omega
  refine ⟨hc,?_⟩
  obtain ⟨d,hpos,hlt,hm,hbound⟩ := circle_witness H O z w R hH6 hR hcircle hz hw hzw
  exact ⟨d,hpos,hlt,hm,by rwa [hc] at hbound⟩

/-- A concrete six-point rational unit-circle model has two distinct ambient-interior points. -/
theorem rational_circle_fixture : ∃ (H : Finset Plane) (z w : Plane), H.card = 6 ∧
    (∀ h ∈ H, dist h (0 : Plane) = 1) ∧
    (∀ h ∈ H, h ∈ (convexHull ℝ (H : Set Plane)).extremePoints ℝ) ∧
    z ∈ interior (convexHull ℝ (H : Set Plane)) ∧
    w ∈ interior (convexHull ℝ (H : Set Plane)) ∧ z ≠ w := by
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
  have hcircle : ∀ h ∈ H, dist h (0 : Plane) = 1 := by
    intro h hh
    have hs : ‖h‖^2 = 1 := by
      simp only [H,Finset.mem_insert,Finset.mem_singleton] at hh
      rcases hh with rfl | rfl | rfl | rfl | rfl | rfl <;>
        norm_num [EuclideanSpace.norm_sq_eq,Fin.sum_univ_two,A,B,C,D,E,F]
    simp only [dist_zero_right]
    nlinarith [norm_nonneg h]
  have hA : A ∈ affineSpan ℝ (H : Set Plane) := subset_affineSpan ℝ _ (by simp [H])
  have hB : B ∈ affineSpan ℝ (H : Set Plane) := subset_affineSpan ℝ _ (by simp [H])
  have hC : C ∈ affineSpan ℝ (H : Set Plane) := subset_affineSpan ℝ _ (by simp [H])
  have htop : affineSpan ℝ (H : Set Plane) = ⊤ := by
    apply top_unique
    intro p hp
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
  have hnon : (interior (convexHull ℝ (H : Set Plane))).Nonempty :=
    interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr htop
  obtain ⟨z,hz⟩ := hnon
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp isOpen_interior z hz
  let w := z + (ε/2) • A
  have hnA : ‖A‖ = 1 := by simpa only [dist_zero_right] using hcircle A (by simp [H])
  have hdw : dist w z = ε/2 := by
    calc
      dist w z = ‖(ε/2) • A‖ := by simp [w,dist_eq_norm]
      _ = ε/2 := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by linarith : 0 < ε/2),hnA,mul_one]
  have hw : w ∈ interior (convexHull ℝ (H : Set Plane)) :=
    hball (by rw [Metric.mem_ball,hdw]; linarith)
  have hzw : w ≠ z := dist_pos.mp (by rw [hdw]; linarith)
  have hext : ∀ h ∈ H, h ∈ (convexHull ℝ (H : Set Plane)).extremePoints ℝ := by
    intro h hh
    have hsub : convexHull ℝ (H : Set Plane) ⊆ Metric.closedBall (0 : Plane) 1 :=
      convexHull_min (by intro a ha; simpa [Metric.mem_closedBall,hcircle a ha])
        (convex_closedBall 0 1)
    apply inter_extremePoints_subset_extremePoints_of_subset hsub
    exact ⟨subset_convexHull ℝ _ hh,
      StrictConvexSpace.sphere_subset_extremePoints_closedBall 0 (by norm_num)
        (by simpa [Metric.mem_sphere] using hcircle h hh)⟩
  exact ⟨H,z,w,hcard,hcircle,hext,hz,hw,hzw.symm⟩

end Erdos132.TwoInteriorCircle
