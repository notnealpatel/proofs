import Erdos.Erdos132.OneInteriorCircle
import Erdos.Erdos132.EvenThreeInteriorFixtures

set_option autoImplicit false

namespace Erdos132.OneInteriorReduction

open Erdos132.TwoInteriorCircle
open Erdos132.ThreeInteriorCounting
open Erdos132.OneInteriorCircle

example : ∃ (H : Finset Plane) (O p : Plane) (R : ℝ),
    8 ≤ H.card ∧ (∀ h ∈ H, dist h O = R) ∧
      p ∈ interior (convexHull ℝ (H : Set Plane)) := by
  obtain ⟨H, z, _w, _v, hcard, hcircle, _hextreme, hz, _hw, _hv, _hzw, _hzv, _hwv⟩ :=
    Erdos132.EvenThreeInteriorFixtures.original_hypotheses_all_sizes 11 (by omega)
  exact ⟨H, 0, z, 5, by omega, hcircle, hz⟩

/-- Adding a strict hull-interior point cannot remove an occurring non-diameter
length because it preserves the actual diameter. -/
theorem nonDiameterDistances_subset_insert (H : Finset Plane) (p : Plane)
    (hp : p ∈ interior (convexHull ℝ (H : Set Plane))) :
    nonDiameterDistances H ⊆ nonDiameterDistances (insert p H) := by
  intro d hd
  obtain ⟨⟨a, ha, b, hb, hab, hdist⟩, hlt⟩ := (mem_nonDiameterDistances H d).mp hd
  apply (mem_nonDiameterDistances _ _).mpr
  refine ⟨⟨a, by simp [ha], b, by simp [hb], hab, hdist⟩, ?_⟩
  rwa [diam_insert_interior H p hp]

/-- For odd total order, the contrary pair budget bounds the augmented lower
support (with the diameter class adjoined) by `n / 2`. -/
theorem odd_support_succ_le_half (n q : ℕ) (hn : 9 ≤ n) (hodd : Odd n)
    (hbudget : q * (n + 1) + 1 ≤ n.choose 2) : q + 1 ≤ n / 2 := by
  obtain ⟨s, hs⟩ := hodd
  rw [Nat.choose_two_right] at hbudget
  have hnform : n = 2 * s + 1 := by omega
  subst n
  have hhalf : (2 * s + 1) / 2 = s := by omega
  rw [hhalf]
  have hpred : 2 * s + 1 - 1 = 2 * s := by omega
  rw [hpred] at hbudget
  have hchoose : (2 * s + 1) * (2 * s) / 2 = (2 * s + 1) * s := by
    have heq : (2 * s + 1) * (2 * s) = 2 * ((2 * s + 1) * s) := by ring
    rw [heq]
    exact Nat.mul_div_cancel_left _ (by decide)
  rw [hchoose] at hbudget
  by_contra hnot
  have hsq : s ≤ q := by omega
  have hmul := Nat.mul_le_mul_right (2 * s + 2) hsq
  nlinarith

/-- Conditional odd-order reduction for one interior point. The hypothesis
`hvertices` says that `H` is the actual hull-vertex set; `hpH` separately records
the needed nonmembership of the interior point. The hypotheses `hlower` and
`hrigidity` are precisely the unformalized classical convex-distance lower bound
and its equality classification (as in Altman, and P. Fishburn, *Convex polygons
with few intervertex distances*, Computational Geometry 5(2), 1995, 65–93,
DOI 10.1016/0925-7721(94)00020-V). This theorem does not claim or prove those
source results. Given them explicitly, pair counting and support inclusion reduce
the conclusion to `one_interior_circle`. -/
theorem odd_one_interior_of_lower_bound_and_rigidity
    (n : ℕ) (H : Finset Plane) (p : Plane)
    (hn : 9 ≤ n) (hodd : Odd n) (hH : H.card = n - 1)
    (_hvertices : ∀ h ∈ H, h ∉ convexHull ℝ ((H.erase h : Finset Plane) : Set Plane))
    (hpH : p ∉ H)
    (hp : p ∈ interior (convexHull ℝ (H : Set Plane)))
    (hlower : H.card / 2 ≤ (nonDiameterDistances H).card + 1)
    (hrigidity : (nonDiameterDistances H).card + 1 = H.card / 2 →
      ∃ O : Plane, ∃ R : ℝ, ∀ h ∈ H, dist h O = R) :
    (insert p H).card = n ∧
    ∃ d : ℝ, 0 < d ∧ d < Metric.diam ((insert p H : Finset Plane) : Set Plane) ∧
      1 ≤ multiplicity (insert p H) d ∧ multiplicity (insert p H) d ≤ n := by
  classical
  let X := insert p H
  let k := (nonDiameterDistances H).card + 1
  let K := (nonDiameterDistances X).card + 1
  have hcardX : X.card = n := by
    dsimp [X]
    rw [Finset.card_insert_of_notMem hpH, hH]
    omega
  by_contra hno
  have hlarge : ∀ d ∈ nonDiameterDistances X, X.card + 1 ≤ multiplicity X d := by
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
    by_contra hnotlarge
    apply hno
    change X.card = n ∧ ∃ d : ℝ, 0 < d ∧ d < Metric.diam (X : Set Plane) ∧
      1 ≤ multiplicity X d ∧ multiplicity X d ≤ n
    exact ⟨hcardX, d, hpos, hlt, hmul, by omega⟩
  have hbudget := nonDiameter_pair_budget X (by omega) hlarge
  have hKupper : K ≤ n / 2 := by
    apply odd_support_succ_le_half n (nonDiameterDistances X).card hn hodd
    simpa only [hcardX] using hbudget
  have hsubset := nonDiameterDistances_subset_insert H p hp
  have hkK : k ≤ K := by
    dsimp [k, K]
    exact Nat.add_le_add_right (Finset.card_le_card hsubset) 1
  have hhalf : H.card / 2 = n / 2 := by
    rw [hH]
    obtain ⟨s, hs⟩ := hodd
    omega
  have hkeq : k = H.card / 2 := by
    dsimp [k] at hlower ⊢
    dsimp [k, K] at hkK hKupper
    omega
  obtain ⟨O, R, hcircle⟩ := hrigidity hkeq
  obtain ⟨hclaimCard, d, hpos, hlt, hmul, hbound⟩ :=
    one_interior_circle (n - 1) H O p R (by omega) hH hcircle hp
  apply hno
  refine ⟨hcardX, d, hpos, hlt, hmul, ?_⟩
  simpa only [X, hcardX] using hbound

end Erdos132.OneInteriorReduction
