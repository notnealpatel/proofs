import Erdos.Erdos132.CircleRotation
import Mathlib.GroupTheory.Perm.Cycle.Type

set_option autoImplicit false

open Erdos132.TwoInteriorCircle

namespace Erdos132.CircleRotation

/-- A nonidentity unit-circle coefficient whose square is one is the half-turn. -/
theorem eq_neg_one_of_sq_eq_one (g : Rotation) (hg : g ^ 2 = 1) (hne : g ≠ 1) :
    g = -1 := by
  have hs : (g : ℂ) ^ 2 = 1 := by
    simpa only [Circle.coe_pow, Circle.coe_one] using congrArg (fun z : Rotation => (z : ℂ)) hg
  have hf : ((g : ℂ) - 1) * ((g : ℂ) + 1) = 0 := by
    calc
      _ = (g : ℂ) ^ 2 - 1 := by ring
      _ = 0 := by rw [hs]; ring
  rcases mul_eq_zero.mp hf with h | h
  · exact False.elim (hne (Circle.ext (sub_eq_zero.mp h)))
  · apply Circle.ext
    exact eq_neg_of_add_eq_zero_left h

/-- Every nonidentity member of a full stabilizer of order two is the half-turn. -/
theorem eq_neg_one_of_order_eq_two (H : Finset Plane) (horder : order H = 2)
    (g : Stabilizer H) (hne : g.val ≠ 1) : g.val = -1 := by
  apply eq_neg_one_of_sq_eq_one g.val _ hne
  have hp : g ^ 2 = 1 := by
    have hp' := pow_card_eq_one' (x := g)
    change g ^ order H = 1 at hp'
    simpa only [horder] using hp'
  exact congrArg Subtype.val hp

/-- Even order of the full stabilizer forces the actual half-turn to preserve the hull. -/
theorem neg_one_mem_stabilizer_of_even_order (H : Finset Plane) {R : ℝ}
    (hH : H.Nonempty) (hR : 0 < R) (hcircle : ∀ x ∈ H, ‖x‖ = R)
    (heven : Even (order H)) : (-1 : Rotation) ∈ Stabilizer H := by
  letI := finite_stabilizer H hH hR hcircle
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Stabilizer H) 2
    (even_iff_two_dvd.mp heven)
  have hne : g.val ≠ 1 := by
    intro heq
    have hg1 : g = 1 := Subtype.ext heq
    rw [hg1, orderOf_one] at hg
    norm_num at hg
  have hp : g.val ^ 2 = 1 := by
    have hp' := pow_orderOf_eq_one g
    rw [hg] at hp'
    exact congrArg Subtype.val hp'
  rw [← eq_neg_one_of_sq_eq_one g.val hp hne]
  exact g.property

/-- An even full rotation order makes hull membership invariant under antipodes. -/
theorem mem_iff_neg_mem_of_even_order (H : Finset Plane) {R : ℝ}
    (hH : H.Nonempty) (hR : 0 < R) (hcircle : ∀ x ∈ H, ‖x‖ = R)
    (heven : Even (order H)) (x : Plane) : x ∈ H ↔ -x ∈ H := by
  have hm := neg_one_mem_stabilizer_of_even_order H hH hR hcircle heven
  simpa only [rotate_neg_one] using (hm x).symm

/-- For a positive circular hull with full rotation order two, the preserving
 coefficients are exactly the identity and the half-turn; both genuinely occur. -/
theorem mem_stabilizer_iff_of_order_eq_two (H : Finset Plane) {R : ℝ}
    (hH : H.Nonempty) (hR : 0 < R) (hcircle : ∀ x ∈ H, ‖x‖ = R)
    (horder : order H = 2) (g : Rotation) :
    g ∈ Stabilizer H ↔ g = 1 ∨ g = -1 := by
  constructor
  · intro hg
    by_cases hg1 : g = 1
    · exact Or.inl hg1
    · exact Or.inr (eq_neg_one_of_order_eq_two H horder ⟨g, hg⟩ hg1)
  · rintro (rfl | rfl)
    · exact (Stabilizer H).one_mem
    · apply neg_one_mem_stabilizer_of_even_order H hH hR hcircle
      rw [horder]
      decide

/-- Every coefficient in a full stabilizer of order three has cube one. -/
theorem cube_eq_one_of_order_eq_three (H : Finset Plane) (horder : order H = 3)
    (g : Stabilizer H) : g.val ^ 3 = 1 := by
  have hp : g ^ 3 = 1 := by
    have hp' := pow_card_eq_one' (x := g)
    change g ^ order H = 1 at hp'
    simpa only [horder] using hp'
  exact congrArg Subtype.val hp

/-- Nonidentity coefficients in an order-three full stabilizer satisfy the cyclotomic quadratic. -/
theorem quadratic_eq_zero_of_order_eq_three (H : Finset Plane) (horder : order H = 3)
    (g : Stabilizer H) (hne : g.val ≠ 1) :
    (g.val : ℂ) ^ 2 + (g.val : ℂ) + 1 = 0 := by
  have hc : (g.val : ℂ) ^ 3 = 1 := by
    simpa only [Circle.coe_pow, Circle.coe_one] using
      congrArg (fun z : Rotation => (z : ℂ)) (cube_eq_one_of_order_eq_three H horder g)
  have hf : ((g.val : ℂ) - 1) * ((g.val : ℂ) ^ 2 + (g.val : ℂ) + 1) = 0 := by
    calc
      _ = (g.val : ℂ) ^ 3 - 1 := by ring
      _ = 0 := by rw [hc]; ring
  rcases mul_eq_zero.mp hf with h | h
  · exact False.elim (hne (Circle.ext (sub_eq_zero.mp h)))
  · exact h

/-- A unit-circle coefficient satisfying the cubic cyclotomic quadratic has real part `-1/2`. -/
theorem re_eq_neg_half_of_quadratic (g : Rotation)
    (hq : (g : ℂ) ^ 2 + (g : ℂ) + 1 = 0) : (g : ℂ).re = -(1 / 2 : ℝ) := by
  have hn := Circle.normSq_coe g
  simp only [Complex.normSq_apply] at hn
  have hr := congrArg Complex.re hq
  have hi := congrArg Complex.im hq
  simp only [pow_two, Complex.add_re, Complex.mul_re, Complex.one_re,
    Complex.zero_re] at hr
  simp only [pow_two, Complex.add_im, Complex.mul_im, Complex.one_im,
    Complex.zero_im] at hi
  by_cases hb : (g : ℂ).im = 0
  · rw [hb] at hn hr
    nlinarith
  · have hf : (2 * (g : ℂ).re + 1) * (g : ℂ).im = 0 := by nlinarith only [hi]
    have ha := (mul_eq_zero.mp hf).resolve_right hb
    linarith

/-- Every nonidentity coefficient of an order-three full stabilizer has real part `-1/2`. -/
theorem re_eq_neg_half_of_order_eq_three (H : Finset Plane) (horder : order H = 3)
    (g : Stabilizer H) (hne : g.val ≠ 1) : (g.val : ℂ).re = -(1 / 2 : ℝ) :=
  re_eq_neg_half_of_quadratic g.val (quadratic_eq_zero_of_order_eq_three H horder g hne)

/-- The coefficient displacement of a cubic nonidentity rotation has squared norm three. -/
theorem norm_sub_one_sq_of_order_eq_three (H : Finset Plane) (horder : order H = 3)
    (g : Stabilizer H) (hne : g.val ≠ 1) : ‖(g.val : ℂ) - 1‖ ^ 2 = 3 := by
  have hn := Circle.normSq_coe g.val
  have hr := re_eq_neg_half_of_order_eq_three H horder g hne
  rw [Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im] at hn ⊢
  nlinarith

/-- An order-three nonidentity stabilizer rotation has squared displacement three times
 the squared radius; the formula also holds at the origin. -/
theorem dist_rotate_sq_of_order_eq_three (H : Finset Plane) (horder : order H = 3)
    (g : Stabilizer H) (hne : g.val ≠ 1) (x : Plane) :
    dist x (rotate g.val x) ^ 2 = 3 * ‖x‖ ^ 2 := by
  rw [dist_comm, dist_rotate_self, mul_pow,
    norm_sub_one_sq_of_order_eq_three H horder g hne]

/-- Any two distinct points of one genuine full-stabilizer orbit in the plane have
 squared distance three times the squared radius of the orbit base point. The plane
 action here is the canonical restriction of the coefficient rotation action. -/
theorem dist_sq_of_mem_orbit_order_eq_three (H : Finset Plane) (horder : order H = 3)
    (x y z : Plane) (hy : y ∈ MulAction.orbit (Stabilizer H) x)
    (hz : z ∈ MulAction.orbit (Stabilizer H) x) (hyz : y ≠ z) :
    dist y z ^ 2 = 3 * ‖x‖ ^ 2 := by
  obtain ⟨g, hg⟩ := hy
  obtain ⟨k, hk⟩ := hz
  change rotate g.val x = y at hg
  change rotate k.val x = z at hk
  let q : Stabilizer H := g⁻¹ * k
  have htransport : rotate g.val (rotate q.val x) = z := by
    rw [← rotate_mul]
    change rotate (g.val * (g.val⁻¹ * k.val)) x = z
    simpa only [mul_inv_cancel_left] using hk
  have hq : q.val ≠ 1 := by
    intro hq1
    rw [hq1, rotate_one, hg] at htransport
    exact hyz htransport
  calc
    dist y z ^ 2 = dist (rotate g.val x) (rotate g.val (rotate q.val x)) ^ 2 := by
      rw [hg, htransport]
    _ = dist x (rotate q.val x) ^ 2 := by rw [(rotate_isometry g.val).dist_eq]
    _ = 3 * ‖x‖ ^ 2 := dist_rotate_sq_of_order_eq_three H horder q hq x

/-- Three pairwise distinct points in one genuine order-three full-stabilizer orbit
 form an equilateral triangle, expressed as equality of all three side lengths. -/
theorem equilateral_of_mem_orbit_order_eq_three (H : Finset Plane) (horder : order H = 3)
    (x y z w : Plane) (hy : y ∈ MulAction.orbit (Stabilizer H) x)
    (hz : z ∈ MulAction.orbit (Stabilizer H) x)
    (hw : w ∈ MulAction.orbit (Stabilizer H) x)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) :
    dist y z = dist y w ∧ dist y z = dist z w := by
  have hyzsq := dist_sq_of_mem_orbit_order_eq_three H horder x y z hy hz hyz
  have hywsq := dist_sq_of_mem_orbit_order_eq_three H horder x y w hy hw hyw
  have hzwsq := dist_sq_of_mem_orbit_order_eq_three H horder x z w hz hw hzw
  constructor
  · exact (sq_eq_sq₀ dist_nonneg dist_nonneg).mp (hyzsq.trans hywsq.symm)
  · exact (sq_eq_sq₀ dist_nonneg dist_nonneg).mp (hyzsq.trans hzwsq.symm)

/-- The squared-distance conclusion for the existing actual action on hull vertices. -/
theorem dist_sq_of_mem_hull_orbit_order_eq_three (H : Finset Plane)
    (horder : order H = 3) (x y z : {p // p ∈ H})
    (hy : y ∈ MulAction.orbit (Stabilizer H) x)
    (hz : z ∈ MulAction.orbit (Stabilizer H) x) (hyz : y ≠ z) :
    dist y.val z.val ^ 2 = 3 * ‖x.val‖ ^ 2 := by
  apply dist_sq_of_mem_orbit_order_eq_three H horder x.val y.val z.val
  · obtain ⟨g, hg⟩ := hy
    exact ⟨g, congrArg Subtype.val hg⟩
  · obtain ⟨g, hg⟩ := hz
    exact ⟨g, congrArg Subtype.val hg⟩
  · intro heq
    exact hyz (Subtype.ext heq)

/-- Three distinct hull vertices in one actual hull orbit form an equilateral triangle. -/
theorem equilateral_of_mem_hull_orbit_order_eq_three (H : Finset Plane)
    (horder : order H = 3) (x y z w : {p // p ∈ H})
    (hy : y ∈ MulAction.orbit (Stabilizer H) x)
    (hz : z ∈ MulAction.orbit (Stabilizer H) x)
    (hw : w ∈ MulAction.orbit (Stabilizer H) x)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) :
    dist y.val z.val = dist y.val w.val ∧ dist y.val z.val = dist z.val w.val := by
  have hyzsq := dist_sq_of_mem_hull_orbit_order_eq_three H horder x y z hy hz hyz
  have hywsq := dist_sq_of_mem_hull_orbit_order_eq_three H horder x y w hy hw hyw
  have hzwsq := dist_sq_of_mem_hull_orbit_order_eq_three H horder x z w hz hw hzw
  constructor
  · exact (sq_eq_sq₀ dist_nonneg dist_nonneg).mp (hyzsq.trans hywsq.symm)
  · exact (sq_eq_sq₀ dist_nonneg dist_nonneg).mp (hyzsq.trans hzwsq.symm)

private theorem exists_cubic_coefficient : ∃ (g : Rotation), g ^ 3 = 1 ∧ g ≠ 1 ∧
    (g : ℂ) ^ 2 + (g : ℂ) + 1 = 0 := by
  have hs : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  let z : ℂ := ⟨-(1 / 2), Real.sqrt 3 / 2⟩
  have hn : Complex.normSq z = 1 := by
    simp only [Complex.normSq_apply, z]
    nlinarith only [hs]
  let g : Rotation := ⟨z, mem_sphere_zero_iff_norm.mpr (by rw [Complex.norm_def, hn]; norm_num)⟩
  have hq : (g : ℂ) ^ 2 + (g : ℂ) + 1 = 0 := by
    apply Complex.ext
    · simp only [pow_two, Complex.add_re, Complex.mul_re, Complex.one_re,
        Complex.zero_re]
      change (- (1 / 2 : ℝ)) * (-(1 / 2)) - (Real.sqrt 3 / 2) *
        (Real.sqrt 3 / 2) + -(1 / 2) + 1 = 0
      nlinarith only [hs]
    · simp [g, z, pow_two, Complex.mul_im]
      ring
  have hc : g ^ 3 = 1 := by
    apply Circle.ext
    simp only [Circle.coe_pow, Circle.coe_one]
    calc
      (g : ℂ) ^ 3 = ((g : ℂ) - 1) * ((g : ℂ) ^ 2 + (g : ℂ) + 1) + 1 := by ring
      _ = 1 := by rw [hq]; ring
  have hg : g ≠ 1 := by
    intro h
    have hr := congrArg (fun t : Rotation => (t : ℂ).re) h
    norm_num [g, z] at hr
  exact ⟨g, hc, hg, hq⟩

example : ∃ (H : Finset Plane) (R : ℝ) (a b c : Plane),
    H.Nonempty ∧ 0 < R ∧ (∀ x ∈ H, ‖x‖ = R) ∧ order H = 3 ∧
    a ∈ H ∧ b ∈ H ∧ c ∈ H ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    b ∈ MulAction.orbit (Stabilizer H) a ∧ c ∈ MulAction.orbit (Stabilizer H) a := by
  classical
  obtain ⟨g, hc, hg, _hq⟩ := exists_cubic_coefficient
  let a : Plane := WithLp.toLp 2 ![1, 0]
  let b := rotate g a
  let c := rotate (g ^ 2) a
  let H : Finset Plane := {a, b, c}
  have ha : ‖a‖ = 1 := by
    norm_num [a, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  have ha0 : a ≠ 0 := ne_zero_of_norm_eq (by norm_num) ha
  have hg2 : g ^ 2 ≠ 1 := by
    intro hs
    apply hg
    calc
      g = g ^ 3 := by rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, hs, one_mul]
      _ = 1 := hc
  have hgg2 : g ≠ g ^ 2 := by
    intro he
    have he' : g * 1 = g * g := by simpa only [mul_one, pow_two] using he
    exact hg (mul_left_cancel he').symm
  have hab : a ≠ b := by
    intro he
    apply hg
    exact (rotate_coeff_injective a ha0 (by simpa only [rotate_one] using he.symm))
  have hac : a ≠ c := by
    intro he
    apply hg2
    exact (rotate_coeff_injective a ha0 (by simpa only [rotate_one] using he.symm))
  have hbc : b ≠ c := fun he => hgg2 (rotate_coeff_injective a ha0 he)
  have hH : H.Nonempty := by simp [H]
  have hcircle : ∀ x ∈ H, ‖x‖ = (1 : ℝ) := by
    intro x hx
    simp only [H, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact (norm_rotate g a).trans ha
    · exact (norm_rotate (g ^ 2) a).trans ha
  have hgb : rotate g b = c := by
    change rotate g (rotate g a) = rotate (g ^ 2) a
    rw [← rotate_mul, pow_two]
  have hgc : rotate g c = a := by
    change rotate g (rotate (g ^ 2) a) = a
    rw [← rotate_mul, ← pow_succ', show (2 + 1 : ℕ) = 3 from rfl, hc, rotate_one]
  have hm : g ∈ Stabilizer H := by
    apply (mem_stabilizer_iff_image H g).mpr
    change ({a, b, c} : Finset Plane).image (rotate g) = {a, b, c}
    simp only [Finset.image_insert, Finset.image_singleton]
    change {b, rotate g b, rotate g c} = {a, b, c}
    rw [hgb, hgc]
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hcard : H.card = 3 := by simp [H, hab, hac, hbc]
  have hd : order H ∣ 3 := by
    rw [← hcard]
    exact order_dvd_card H hH (by norm_num) hcircle
  have ho : order H = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with ho | ho
    · have hp := pow_card_eq_one' (x := (⟨g, hm⟩ : Stabilizer H))
      change (⟨g, hm⟩ : Stabilizer H) ^ order H = 1 at hp
      rw [ho, pow_one] at hp
      exact False.elim (hg (congrArg Subtype.val hp))
    · exact ho
  refine ⟨H, 1, a, b, c, hH, by norm_num, hcircle, ho, by simp [H],
    by simp [H], by simp [H], hab, hac, hbc, ?_, ?_⟩
  · exact ⟨⟨g, hm⟩, rfl⟩
  · exact ⟨(⟨g, hm⟩ : Stabilizer H) ^ 2, rfl⟩

example : ∃ (H : Finset Plane) (R : ℝ) (g : Stabilizer H),
    H.Nonempty ∧ 0 < R ∧ (∀ x ∈ H, ‖x‖ = R) ∧
    order H = 2 ∧ Even (order H) ∧ g.val ≠ 1 := by
  classical
  let a : Plane := WithLp.toLp 2 ![1, 0]
  let H : Finset Plane := {a, -a}
  have ha : ‖a‖ = 1 := by
    norm_num [a, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  have hane : a ≠ -a := by
    intro he
    have he0 := congrArg (fun x : Plane => x 0) he
    norm_num [a] at he0
  have hH : H.Nonempty := by simp [H]
  have hcircle : ∀ x ∈ H, ‖x‖ = (1 : ℝ) := by
    intro x hx
    simp only [H, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · simpa only [norm_neg] using ha
  have hm : (-1 : Rotation) ∈ Stabilizer H := by
    intro x
    simp only [rotate_neg_one, H, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (hx | hx)
      · right
        exact (neg_eq_iff_eq_neg.mp hx)
      · left
        exact neg_injective hx
    · rintro (rfl | rfl) <;> simp
  have hg : (-1 : Rotation) ≠ 1 := by
    intro he
    have hr := congrArg (fun t : Rotation => (t : ℂ).re) he
    norm_num at hr
  have hcard : H.card = 2 := by simp [H, hane]
  have hd : order H ∣ 2 := by
    rw [← hcard]
    exact order_dvd_card H hH (by norm_num) hcircle
  have ho : order H = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with ho | ho
    · have hp := pow_card_eq_one' (x := (⟨-1, hm⟩ : Stabilizer H))
      change (⟨-1, hm⟩ : Stabilizer H) ^ order H = 1 at hp
      rw [ho, pow_one] at hp
      exact False.elim (hg (congrArg Subtype.val hp))
    · exact ho
  exact ⟨H, 1, ⟨-1, hm⟩, hH, by norm_num, hcircle, ho, ho.symm ▸ by decide, hg⟩

end Erdos132.CircleRotation
