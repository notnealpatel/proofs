import Erdos.Erdos132.CircleRotation
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Data.Finset.Sort

set_option autoImplicit false

open Erdos132.TwoInteriorCircle
open Erdos132.CircleRotation

namespace Erdos132.CircleShortChord

private theorem coordinates (x : Plane) {R : ℝ} (hR : 0 < R) (hx : ‖x‖ = R) :
    x 0 = R * Real.cos (Complex.arg (encode x)) ∧
    x 1 = R * Real.sin (Complex.arg (encode x)) := by
  have hn : ‖encode x‖ = R := (norm_encode x).trans hx
  have hz : encode x ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hn
    linarith
  have hc := Complex.cos_arg hz
  have hs := Complex.sin_arg (encode x)
  rw [hn] at hc hs
  constructor
  · simpa [encode, mul_comm] using (eq_div_iff hR.ne').mp hc |>.symm
  · simpa [encode, mul_comm] using (eq_div_iff hR.ne').mp hs |>.symm

private theorem angle_inj {x y : Plane} {R : ℝ} (hR : 0 < R)
    (hx : ‖x‖ = R) (hy : ‖y‖ = R)
    (h : Complex.arg (encode x) = Complex.arg (encode y)) : x = y := by
  obtain ⟨hx0, hx1⟩ := coordinates x hR hx
  obtain ⟨hy0, hy1⟩ := coordinates y hR hy
  ext i
  fin_cases i
  · change x 0 = y 0
    rw [hx0, hy0, h]
  · change x 1 = y 1
    rw [hx1, hy1, h]

private theorem chord_sq {x y : Plane} {R : ℝ} (hR : 0 < R)
    (hx : ‖x‖ = R) (hy : ‖y‖ = R) :
    dist x y ^ 2 = 2 * R ^ 2 *
      (1 - Real.cos (Complex.arg (encode y) - Complex.arg (encode x))) := by
  obtain ⟨hx0, hx1⟩ := coordinates x hR hx
  obtain ⟨hy0, hy1⟩ := coordinates y hR hy
  have hn := EuclideanSpace.real_norm_sq_eq (x - y)
  simp only [Fin.sum_univ_two, PiLp.sub_apply] at hn
  rw [dist_eq_norm, hn]
  simp only [hx0, hx1, hy0, hy1, Real.cos_sub]
  have htx := Real.sin_sq_add_cos_sq (Complex.arg (encode x))
  have hty := Real.sin_sq_add_cos_sq (Complex.arg (encode y))
  nlinarith [htx, hty]

private theorem chord_le {x y : Plane} {R : ℝ} (hR : 0 < R)
    (hx : ‖x‖ = R) (hy : ‖y‖ = R)
    (hc : 1 / 2 ≤ Real.cos (Complex.arg (encode y) - Complex.arg (encode x))) :
    dist x y ≤ R := by
  have hs := chord_sq hR hx hy
  have hb : dist x y ^ 2 ≤ R ^ 2 := by nlinarith [sq_nonneg R]
  nlinarith [@dist_nonneg Plane _ x y]

/-- Six or more distinct points on a positive-radius origin circle contain a
positive chord no longer than the radius, including equality for a regular hexagon. -/
theorem exists_short_chord (H : Finset Plane) (R : ℝ) (hR : 0 < R)
    (hcircle : ∀ x ∈ H, ‖x‖ = R) (hcard : 6 ≤ H.card) :
    ∃ x ∈ H, ∃ y ∈ H, x ≠ y ∧ 0 < dist x y ∧ dist x y ≤ R := by
  classical
  obtain ⟨K, hKH, hK⟩ := Finset.le_card_iff_exists_subset_card.mp hcard
  let S : Finset ℝ := K.image (fun x => Complex.arg (encode x))
  have hS : S.card = 6 := by
    rw [Finset.card_image_of_injOn]
    · exact hK
    · intro x hx y hy hxy
      exact angle_inj hR (hcircle x (hKH hx)) (hcircle y (hKH hy)) hxy
  let e : Fin 6 ≃o S := S.orderIsoOfFin hS
  have hex : ∀ i : Fin 6, ∃ x ∈ K, Complex.arg (encode x) = (e i : ℝ) := by
    intro i
    exact Finset.mem_image.mp (e i).property
  choose p hp hangle using hex
  have hpH (i : Fin 6) : p i ∈ H := hKH (hp i)
  have hnorm (i : Fin 6) : ‖p i‖ = R := hcircle (p i) (hpH i)
  have hstrict {i j : Fin 6} (hij : i < j) : (e i : ℝ) < (e j : ℝ) :=
    e.strictMono hij
  have hne {i j : Fin 6} (hij : i < j) : p i ≠ p j := by
    intro heq
    have ha := congrArg (fun x => Complex.arg (encode x)) heq
    rw [hangle i, hangle j] at ha
    exact (hstrict hij).ne ha
  by_contra hnone
  have hfar {i j : Fin 6} (hij : i < j) : R < dist (p i) (p j) := by
    apply lt_of_not_ge
    intro hle
    exact hnone ⟨p i, hpH i, p j, hpH j, hne hij, dist_pos.mpr (hne hij), hle⟩
  have hgap {i j : Fin 6} (hij : i < j) : Real.pi / 3 < (e j : ℝ) - (e i : ℝ) := by
    by_contra hnot
    have hd : (e j : ℝ) - (e i : ℝ) ≤ Real.pi / 3 := le_of_not_gt hnot
    have hnonneg : 0 ≤ (e j : ℝ) - (e i : ℝ) := sub_nonneg.mpr (hstrict hij).le
    have hc := Real.cos_le_cos_of_nonneg_of_le_pi hnonneg
      (show Real.pi / 3 ≤ Real.pi by linarith [Real.pi_pos]) hd
    rw [Real.cos_pi_div_three] at hc
    have hle := chord_le hR (hnorm i) (hnorm j) (by simpa only [hangle] using hc)
    exact (not_le_of_gt (hfar hij)) hle
  have hwrap : Real.pi / 3 < 2 * Real.pi + (e (0 : Fin 6) : ℝ) - (e (5 : Fin 6) : ℝ) := by
    by_contra hnot
    have hd : 2 * Real.pi - ((e (5 : Fin 6) : ℝ) - (e (0 : Fin 6) : ℝ)) ≤ Real.pi / 3 := by
      linarith [le_of_not_gt hnot]
    have hlo := Complex.neg_pi_lt_arg (encode (p 0))
    have hhi := Complex.arg_le_pi (encode (p 5))
    rw [hangle] at hlo hhi
    have hnonneg : 0 ≤ 2 * Real.pi - ((e (5 : Fin 6) : ℝ) - (e (0 : Fin 6) : ℝ)) := by
      linarith
    have hc := Real.cos_le_cos_of_nonneg_of_le_pi hnonneg
      (show Real.pi / 3 ≤ Real.pi by linarith [Real.pi_pos]) hd
    rw [Real.cos_pi_div_three, Real.cos_two_pi_sub] at hc
    have hle := chord_le hR (hnorm 0) (hnorm 5) (by simpa only [hangle] using hc)
    exact (not_le_of_gt (hfar (show (0 : Fin 6) < 5 by decide))) hle
  have h01 := hgap (show (0 : Fin 6) < 1 by decide)
  have h12 := hgap (show (1 : Fin 6) < 2 by decide)
  have h23 := hgap (show (2 : Fin 6) < 3 by decide)
  have h34 := hgap (show (3 : Fin 6) < 4 by decide)
  have h45 := hgap (show (4 : Fin 6) < 5 by decide)
  linarith

/-- The six exact unit-hexagon coordinates jointly realize the circle and cardinality
hypotheses, and two adjacent vertices have distance exactly one. -/
theorem unit_hexagon_fixture : ∃ H : Finset Plane, (∀ x ∈ H, ‖x‖ = 1) ∧ H.card = 6 ∧
    ∃ x ∈ H, ∃ y ∈ H, x ≠ y ∧ dist x y = 1 := by
  classical
  let t : ℝ := Real.sqrt 3 / 2
  let a : Plane := WithLp.toLp 2 ![1, 0]
  let b : Plane := WithLp.toLp 2 ![1/2, t]
  let c : Plane := WithLp.toLp 2 ![-1/2, t]
  let d : Plane := WithLp.toLp 2 ![-1, 0]
  let e : Plane := WithLp.toLp 2 ![-1/2, -t]
  let f : Plane := WithLp.toLp 2 ![1/2, -t]
  have ht : t ^ 2 = 3 / 4 := by
    dsimp [t]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have htpos : 0 < t := by dsimp [t]; positivity
  have norm_one (x : Plane) (hx : x 0 ^ 2 + x 1 ^ 2 = 1) : ‖x‖ = 1 := by
    have hn := EuclideanSpace.real_norm_sq_eq x
    simp only [Fin.sum_univ_two] at hn
    nlinarith [norm_nonneg x]
  have ha : ‖a‖ = 1 := norm_one a (by dsimp [a]; norm_num)
  have hb : ‖b‖ = 1 := norm_one b (by dsimp [b]; nlinarith [ht])
  have hc : ‖c‖ = 1 := norm_one c (by dsimp [c]; nlinarith [ht])
  have hd : ‖d‖ = 1 := norm_one d (by dsimp [d]; norm_num)
  have he : ‖e‖ = 1 := norm_one e (by dsimp [e]; nlinarith [ht])
  have hf : ‖f‖ = 1 := norm_one f (by dsimp [f]; nlinarith [ht])
  let H : Finset Plane := {a, b, c, d, e, f}
  refine ⟨H, ?_, ?_, b, ?_, c, ?_, ?_, ?_⟩
  · intro x hx
    simp only [H, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
    · exact hd
    · exact he
    · exact hf
  · have htneg : t ≠ -t := by linarith
    norm_num [H, a, b, c, d, e, f, (WithLp.toLp_injective 2).eq_iff,
      funext_iff, Fin.forall_fin_two, htpos.ne', htneg, htneg.symm]
  · simp [H]
  · simp [H]
  · intro h
    have h0 := congrArg (fun x : Plane => x 0) h
    norm_num [b, c] at h0
  · rw [dist_eq_norm]
    apply norm_one
    change (1/2 - (-1/2) : ℝ)^2 + (t-t)^2 = 1
    norm_num

example : ∃ H : Finset Plane, 0 < (1 : ℝ) ∧
    (∀ x ∈ H, ‖x‖ = 1) ∧ 6 ≤ H.card := by
  obtain ⟨H, hcircle, hcard, _⟩ := unit_hexagon_fixture
  exact ⟨H, by norm_num, hcircle, by omega⟩

end Erdos132.CircleShortChord
