import Erdos.Erdos132.ThreeInteriorCounting

set_option autoImplicit false

open scoped BigOperators

namespace Erdos132.OneInteriorCircle

open Erdos132.TwoInteriorCircle
open Erdos132.ThreeInteriorCounting

/-- Inserting a strict interior point into a positive-radius cyclic hull adds one point. -/
theorem card_insert_interior (H : Finset Plane) (O p : Plane) (R : ℝ)
    (hR : 0 < R) (hcircle : ∀ h ∈ H, dist h O = R)
    (hp : p ∈ interior (convexHull ℝ (H : Set Plane))) :
    (insert p H).card = H.card + 1 := by
  classical
  have hpH : p ∉ H := by
    intro hmem
    exact (ne_of_lt (dist_center_lt_radius H O hR hcircle hp)) (hcircle p hmem)
  rw [Finset.card_insert_of_notMem hpH]

/-- Inserting a strict hull-interior point preserves the actual metric diameter. -/
theorem diam_insert_interior (H : Finset Plane) (p : Plane)
    (hp : p ∈ interior (convexHull ℝ (H : Set Plane))) :
    Metric.diam ((insert p H : Finset Plane) : Set Plane) = Metric.diam (H : Set Plane) := by
  classical
  have hsub : ((insert p H : Finset Plane) : Set Plane) ⊆
      convexHull ℝ (H : Set Plane) := by
    intro x hx
    simp only [Finset.mem_coe, Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact interior_subset hp
    · exact subset_convexHull ℝ (H : Set Plane) hx
  apply le_antisymm
  · exact Metric.diam_le_of_forall_dist_le Metric.diam_nonneg
      (fun _ hx _ hy => dist_le_diam_hull H (hsub hx) (hsub hy))
  · exact Metric.diam_mono (by intro x hx; simp [hx])
      (insert p H).finite_toSet.isBounded

/-- A distance other than the radius gains no pairs when the circle center is inserted. -/
theorem center_insert_multiplicity_le (H : Finset Plane) (O : Plane) (R d : ℝ)
    (hcircle : ∀ h ∈ H, dist h O = R) (hdR : d ≠ R) :
    multiplicity (insert O H) d ≤ multiplicity H d := by
  classical
  apply Finset.card_le_card
  intro e he
  have he' := Finset.mem_filter.mp he
  induction e using Sym2.ind with
  | _ a b =>
      have hp := (mk_mem_pairs (insert O H) a b).mp he'.1
      have hd : dist a b = d := he'.2
      have ha : a = O ∨ a ∈ H := by simpa using hp.1
      have hb : b = O ∨ b ∈ H := by simpa using hp.2.1
      apply Finset.mem_filter.mpr
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact False.elim (hp.2.2 (ha.trans hb.symm))
      · have hdistR : dist a b = R := by
          rw [ha, dist_comm]
          exact hcircle b hb
        exact False.elim (hdR (hd.symm.trans hdistR))
      · have hdistR : dist a b = R := by
          rw [hb]
          exact hcircle a ha
        exact False.elim (hdR (hd.symm.trans hdistR))
      · exact ⟨(mk_mem_pairs H a b).mpr ⟨ha, hb, hp.2.2⟩, hd⟩

/-- The pair budget alone makes twice the number of lower classes smaller than the
number of hull vertices in a one-interior configuration. -/
theorem twice_support_lt_hull_card (m q : ℕ) (hm : 8 ≤ m)
    (hbudget : q * (m + 2) + 1 ≤ (m + 1).choose 2) : 2 * q < m := by
  rw [Nat.choose_two_right] at hbudget
  have hchoose : 2 * ((m + 1) * m / 2) ≤ (m + 1) * m := Nat.mul_div_le _ _
  have hbudget2 : 2 * (q * (m + 2) + 1) ≤ (m + 1) * m := by
    exact (Nat.mul_le_mul_left 2 hbudget).trans (by
      simpa only [Nat.add_sub_cancel] using hchoose)
  by_contra hnot
  have hmq : m ≤ 2 * q := by omega
  have hmul := Nat.mul_le_mul_right (m + 2) hmq
  nlinarith

/-- A one-interior centered cyclic configuration cannot have every occurring lower
class larger than the number of points. -/
theorem center_contrary (H : Finset Plane) (O : Plane) (R : ℝ)
    (hH : 8 ≤ H.card) (hR : 0 < R) (hcircle : ∀ h ∈ H, dist h O = R)
    (hO : O ∈ interior (convexHull ℝ (H : Set Plane)))
    (hlarge : ∀ d ∈ nonDiameterDistances (insert O H),
      (insert O H).card + 1 ≤ multiplicity (insert O H) d) : False := by
  classical
  let X := insert O H
  let D := Metric.diam (H : Set Plane)
  have hcardX : X.card = H.card + 1 := card_insert_interior H O O R hR hcircle hO
  have hdiam : Metric.diam (X : Set Plane) = D := diam_insert_interior H O hO
  have hsupport : nonDiameterDistances X ⊆ {R} := by
    intro d hd
    rw [Finset.mem_singleton]
    by_contra hdR
    have hu := center_insert_multiplicity_le H O R d hcircle hdR
    have hc := chord_capacity H O R d hR hcircle
    have hl := hlarge d hd
    change X.card + 1 ≤ multiplicity X d at hl
    change multiplicity X d ≤ multiplicity H d at hu
    omega
  have hpairsub : pairs H ⊆
      ((pairs H).filter fun e => pairDist e = R) ∪
      ((pairs H).filter fun e => pairDist e = D) := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      have hp := (mk_mem_pairs H a b).mp he
      have hle : dist a b ≤ D := Metric.dist_le_diam_of_mem H.finite_toSet.isBounded hp.1 hp.2.1
      by_cases heq : dist a b = D
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he, heq⟩)
      · have hlt : dist a b < D := lt_of_le_of_ne hle heq
        have hdmem : dist a b ∈ nonDiameterDistances X := by
          apply (mem_nonDiameterDistances _ _).mpr
          refine ⟨⟨a, by simp [X, hp.1], b, by simp [X, hp.2.1], hp.2.2, rfl⟩, ?_⟩
          rwa [hdiam]
        have hRdist : dist a b = R := by
          simpa only [Finset.mem_singleton] using hsupport hdmem
        exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he, hRdist⟩)
  have hRcap : ((pairs H).filter fun e => pairDist e = R).card ≤ H.card :=
    chord_capacity H O R R hR hcircle
  have hDcap : ((pairs H).filter fun e => pairDist e = D).card ≤ H.card :=
    chord_capacity H O R D hR hcircle
  have hpairs : H.card.choose 2 ≤ H.card + H.card := by
    rw [← card_pairs H]
    exact (Finset.card_le_card hpairsub).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add hRcap hDcap))
  rw [Nat.choose_two_right] at hpairs
  have hcalc : 2 * (H.card * (H.card - 1) / 2) ≤ 2 * (H.card + H.card) :=
    Nat.mul_le_mul_left 2 hpairs
  have hsub : H.card - 1 + 1 = H.card := by omega
  have heven : Even (H.card * (H.card - 1)) := by
    have he := Nat.even_mul_succ_self (H.card - 1)
    rw [hsub] at he
    simpa only [Nat.mul_comm] using he
  obtain ⟨k, hk⟩ := heven
  have hdiv : 2 * (H.card * (H.card - 1) / 2) = H.card * (H.card - 1) := by
    omega
  rw [hdiv] at hcalc
  nlinarith [hsub]

/-- A positive-radius cyclic hull with one strict interior point has a genuine
non-diameter distance whose multiplicity is at most the total number of points. -/
theorem one_interior_circle (m : ℕ) (H : Finset Plane) (O p : Plane) (R : ℝ)
    (hm : 8 ≤ m) (hH : H.card = m) (hcircle : ∀ h ∈ H, dist h O = R)
    (hp : p ∈ interior (convexHull ℝ (H : Set Plane))) :
    (insert p H).card = m + 1 ∧
    ∃ d : ℝ, 0 < d ∧ d < Metric.diam ((insert p H : Finset Plane) : Set Plane) ∧
      1 ≤ multiplicity (insert p H) d ∧
      multiplicity (insert p H) d ≤ (insert p H).card := by
  classical
  have hR : 0 < R := by
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (show 1 < H.card by omega)
    have hnon : 0 ≤ R := (hcircle a ha) ▸ dist_nonneg
    have hne : R ≠ 0 := by
      intro hzero
      have haO : a = O := dist_eq_zero.mp ((hcircle a ha).trans hzero)
      have hbO : b = O := dist_eq_zero.mp ((hcircle b hb).trans hzero)
      exact hab (haO.trans hbO.symm)
    exact lt_of_le_of_ne hnon (Ne.symm hne)
  let X := insert p H
  let T := nonDiameterDistances X
  have hcardX : X.card = m + 1 := by
    change (insert p H).card = m + 1
    rw [card_insert_interior H O p R hR hcircle hp, hH]
  refine ⟨hcardX, ?_⟩
  by_contra hno
  have hlarge : ∀ d ∈ T, X.card + 1 ≤ multiplicity X d := by
    intro d hd
    obtain ⟨hpos, hlt, a, ha, b, hb, habd⟩ :=
      (mem_nonDiameterDistances_iff_positive X d).mp hd
    have hmul : 1 ≤ multiplicity X d := by
      apply Nat.succ_le_of_lt
      apply Finset.card_pos.mpr
      have hab : a ≠ b := by
        intro heq
        rw [heq, dist_self] at habd
        linarith
      exact ⟨s(a, b), Finset.mem_filter.mpr
        ⟨(mk_mem_pairs X a b).mpr ⟨ha, hb, hab⟩, habd⟩⟩
    by_contra hsmall
    apply hno
    simpa only [X] using ⟨d, hpos, hlt, hmul, (by omega : multiplicity X d ≤ X.card)⟩
  by_cases hpO : p = O
  · subst p
    exact center_contrary H O R (by omega) hR hcircle hp hlarge
  · have hmap : ∀ h ∈ H, dist h p ∈ T := by
      intro h hh
      apply (mem_nonDiameterDistances _ _).mpr
      have hpH : p ∉ H := by
        intro hmem
        exact (ne_of_lt (dist_center_lt_radius H O hR hcircle hp)) (hcircle p hmem)
      refine ⟨⟨h, by simp [X, hh], p, by simp [X],
        fun heq => hpH (heq ▸ hh), rfl⟩, ?_⟩
      rw [diam_insert_interior H p hp, dist_comm]
      exact dist_lt_diam_hull H (by omega) hp
        (subset_convexHull ℝ (H : Set Plane) hh)
    have hlower : H.card ≤ 2 * T.card :=
      Finset.card_le_mul_card_image_of_maps_to hmap 2
        (fun d _ => radial_card_le_two H O p R d hcircle hpO)
    have hbudget := nonDiameter_pair_budget X (by omega) hlarge
    have hbudget' : T.card * (m + 2) + 1 ≤ (m + 1).choose 2 := by
      simpa only [hcardX] using hbudget
    have hupper := twice_support_lt_hull_card m T.card hm hbudget'
    omega

end Erdos132.OneInteriorCircle
