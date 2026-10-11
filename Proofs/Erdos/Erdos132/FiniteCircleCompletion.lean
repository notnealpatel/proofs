import Erdos.Erdos132.CircleRotation
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option autoImplicit false

open Erdos132.TwoInteriorCircle Erdos132.CircleRotation
open scoped Real

namespace Erdos132.FiniteCircleCompletion

private theorem root_enumeration (m : ℕ) [NeZero m] (g : Circle) (hp : g ^ m = 1) :
    ∃ j : ZMod m, ZMod.toCircle j = g := by
  let w : rootsOfUnity m Circle := ⟨toUnits g, (mem_rootsOfUnity' m _).mpr hp⟩
  obtain ⟨j, hj⟩ := (bijective_rootsOfUnityAddChar m).surjective w
  exact ⟨j, congrArg (fun z : rootsOfUnity m Circle => (z.val : Circle)) hj⟩

private theorem subgroup_enumeration (m : ℕ) [NeZero m] (K : Subgroup Circle)
    [Finite K] (hc : Nat.card K = m) :
    ∀ g : Circle, g ∈ K ↔ ∃ j : ZMod m, ZMod.toCircle j = g := by
  classical
  letI := Fintype.ofFinite K
  let T : Finset Circle := Finset.univ.image (fun g : K => g.val)
  let U : Finset Circle := Finset.univ.image (ZMod.toCircle (N := m))
  have hT : T.card = m := by
    rw [Finset.card_image_of_injective _ Subtype.val_injective]
    simpa only [Finset.card_univ, Nat.card_eq_fintype_card] using hc
  have hU : U.card = m := by
    rw [Finset.card_image_of_injective _ ZMod.injective_toCircle]
    simp
  have hsub : T ⊆ U := by
    intro g hg
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hg
    have hp : k.val ^ m = 1 := by
      have hh := pow_card_eq_one' (x := k)
      rw [hc] at hh
      exact congrArg Subtype.val hh
    obtain ⟨j, hj⟩ := root_enumeration m k.val hp
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩
  have heq : T = U := Finset.eq_of_subset_of_card_le hsub (by omega)
  intro g
  have hm : g ∈ T ↔ g ∈ K := by simp [T]
  rw [← hm, heq]
  simp [U]

private theorem circle_fin (m : ℕ) [NeZero m] (j : Fin m) :
    ZMod.toCircle (j.val : ZMod m) = Circle.exp (2 * π * (j : ℝ) / (m : ℝ)) := by
  rw [ZMod.toCircle_eq_circleExp, ZMod.val_natCast_of_lt j.isLt]
  congr 1
  ring

/-- A finite subgroup of order `m` consists exactly of the canonical coefficients
`exp(2πj/m)`, with the standard, unpermuted indices `j : Fin m`. -/
theorem canonical_subgroup (m : ℕ) (hm : 3 ≤ m) (K : Subgroup Rotation)
    (hfinite : (K : Set Rotation).Finite) (hcard : Nat.card K = m) (g : Rotation) :
    g ∈ K ↔ ∃ j : Fin m, Circle.exp (2 * π * (j : ℝ) / (m : ℝ)) = g := by
  letI : NeZero m := ⟨by omega⟩
  letI : Finite K := hfinite
  rw [subgroup_enumeration m K hcard]
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨⟨j.val, ZMod.val_lt j⟩, ?_⟩
    rw [← circle_fin]
    simpa only [ZMod.natCast_zmod_val] using hj
  · rintro ⟨j, hj⟩
    exact ⟨(j.val : ZMod m), (circle_fin m j).trans hj⟩

private theorem point_fin_injective (m : ℕ) [NeZero m] (v : Plane) (hv : v ≠ 0) :
    Function.Injective (fun j : Fin m => rotate (Circle.exp (2 * π * (j : ℝ) / (m : ℝ))) v) := by
  intro i j hij
  have hc := rotate_coeff_injective v hv hij
  rw [← circle_fin, ← circle_fin] at hc
  have hz := ZMod.injective_toCircle hc
  have hval := congrArg ZMod.val hz
  simpa only [ZMod.val_natCast_of_lt i.isLt, ZMod.val_natCast_of_lt j.isLt,
    Fin.ext_iff] using hval

private theorem angle_bounds (m k : ℕ) (hm : 0 < m) (hk : k ≤ m / 2) :
    0 ≤ π * (k : ℝ) / (m : ℝ) ∧ π * (k : ℝ) / (m : ℝ) ≤ π / 2 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hkR : (2 : ℝ) * k ≤ m := by exact_mod_cast (show 2 * k ≤ m by omega)
  constructor
  · positivity
  · apply (div_le_iff₀ hmR).mpr
    nlinarith [Real.pi_pos]

private theorem chord (m k : ℕ) [NeZero m] (hk : k < m) (v : Plane) :
    dist (rotate (ZMod.toCircle (k : ZMod m)) v) v =
      2 * ‖v‖ * Real.sin (π * (k : ℝ) / (m : ℝ)) := by
  have hm : (0 : ℝ) < m := by exact_mod_cast (NeZero.pos m)
  have hkR : (k : ℝ) ≤ m := by exact_mod_cast hk.le
  have hangle : 0 ≤ π * (k : ℝ) / (m : ℝ) := by positivity
  have hangle' : π * (k : ℝ) / (m : ℝ) ≤ π := by
    apply (div_le_iff₀ hm).mpr
    nlinarith [Real.pi_pos]
  rw [dist_rotate_self, ZMod.toCircle_natCast]
  have he : (2 * (π : ℂ) * Complex.I * (k : ℂ) / (m : ℂ)) =
      Complex.I * ((2 * π * (k : ℝ) / (m : ℝ) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [he, Complex.norm_exp_I_mul_ofReal_sub_one]
  have hhalf : (2 * π * (k : ℝ) / (m : ℝ)) / 2 = π * (k : ℝ) / (m : ℝ) := by ring
  rw [hhalf, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num)
    (Real.sin_nonneg_of_nonneg_of_le_pi hangle hangle'))]
  ring

private theorem shifted_dist (m : ℕ) [NeZero m] (i s : ZMod m) (v : Plane) :
    dist (rotate (ZMod.toCircle (i + s)) v) (rotate (ZMod.toCircle i) v) =
      2 * ‖v‖ * Real.sin (π * (s.val : ℝ) / (m : ℝ)) := by
  rw [AddChar.map_add_eq_mul, rotate_mul, (rotate_isometry _).dist_eq]
  simpa only [ZMod.natCast_zmod_val] using chord m s.val (ZMod.val_lt s) v

private theorem sin_bound (m k : ℕ) (hm : 3 ≤ m) (hk : k < m) :
    Real.sin (π * (k : ℝ) / (m : ℝ)) ≤ Real.sin (π * ((m / 2 : ℕ) : ℝ) / (m : ℝ)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have htop := angle_bounds m (m / 2) (by omega) le_rfl
  have hmono : ∀ d : ℕ, d ≤ m / 2 →
      Real.sin (π * (d : ℝ) / (m : ℝ)) ≤ Real.sin (π * ((m / 2 : ℕ) : ℝ) / (m : ℝ)) := by
    intro d hd
    have hb := angle_bounds m d (by omega) hd
    apply Real.strictMonoOn_sin.monotoneOn
      ⟨by linarith [Real.pi_pos], hb.2⟩ ⟨by linarith [Real.pi_pos], htop.2⟩
    apply (div_le_div_iff_of_pos_right hmR).mpr
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hd) Real.pi_pos.le
  by_cases hsmall : k ≤ m / 2
  · exact hmono k hsmall
  · let d := m - k
    have hfold : d ≤ m / 2 := by dsimp only [d]; omega
    have hsum : (k : ℝ) + (d : ℝ) = m := by
      exact_mod_cast (show k + d = m by dsimp only [d]; omega)
    have he : π * (d : ℝ) / (m : ℝ) = π - π * (k : ℝ) / (m : ℝ) := by
      rw [show (d : ℝ) = (m : ℝ) - (k : ℝ) by linarith]
      field_simp
    have hh := hmono d hfold
    rw [he, Real.sin_pi_sub] at hh
    exact hh

private theorem dense_shift (m : ℕ) [NeZero m] (J : Finset (ZMod m))
    (hdense : m < 2 * J.card) (s : ZMod m) : ∃ i ∈ J, i + s ∈ J := by
  classical
  let T := J.image (fun j => j - s)
  have hT : T.card = J.card := Finset.card_image_of_injective _ (sub_left_injective (b := s))
  have hbound : (J ∪ T).card ≤ m := by
    calc
      _ ≤ Fintype.card (ZMod m) := Finset.card_le_univ _
      _ = m := ZMod.card m
  have hcount := Finset.card_union_add_card_inter J T
  have hpos : 0 < (J ∩ T).card := by omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  obtain ⟨hiJ, hiT⟩ := Finset.mem_inter.mp hi
  obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hiT
  refine ⟨i, hiJ, ?_⟩
  have he : i + s = j := by rw [← hji, sub_add_cancel]
  exact he ▸ hj

/-- A dense subset of an orbit of a finite circle subgroup has canonical occupied
indices, realizes every positive completion chord, and has the actual completion
diameter. Both parities, every positive radius, and every orientation are included. -/
theorem finite_circle_completion (m : ℕ) (hm : 3 ≤ m) (K : Subgroup Rotation)
    (hfinite : (K : Set Rotation).Finite) (hcard : Nat.card K = m)
    (R : ℝ) (hR : 0 < R) (v : Plane) (hv : ‖v‖ = R) (H : Finset Plane)
    (horbit : ∀ h ∈ H, ∃ g : K, h = rotate g.val v) (hdense : m < 2 * H.card) :
    let P : Fin m → Plane := fun j => rotate (Circle.exp (2 * π * (j : ℝ) / (m : ℝ))) v
    (∀ g : Rotation, g ∈ K ↔ ∃ j : Fin m, Circle.exp (2 * π * (j : ℝ) / (m : ℝ)) = g) ∧
    Function.Injective P ∧
    (∃ J : Finset (Fin m), J.card = H.card ∧ J.image P = H) ∧
    (∀ ell : ℕ, 1 ≤ ell → ell ≤ m / 2 →
      ∃ a ∈ H, ∃ b ∈ H, a ≠ b ∧ dist a b = 2 * R * Real.sin (π * (ell : ℝ) / (m : ℝ))) ∧
    Metric.diam (H : Set Plane) = 2 * R * Real.sin (π * ((m / 2 : ℕ) : ℝ) / (m : ℝ)) ∧
    (∀ ell : ℕ, 1 ≤ ell → ell < m / 2 →
      0 < 2 * R * Real.sin (π * (ell : ℝ) / (m : ℝ)) ∧
      2 * R * Real.sin (π * (ell : ℝ) / (m : ℝ)) < Metric.diam (H : Set Plane)) := by
  classical
  letI : NeZero m := ⟨by omega⟩
  letI : Finite K := hfinite
  let P : Fin m → Plane := fun j => rotate (Circle.exp (2 * π * (j : ℝ) / (m : ℝ))) v
  let Q : ZMod m → Plane := fun j => rotate (ZMod.toCircle j) v
  have hv0 : v ≠ 0 := ne_zero_of_norm_eq hR hv
  have hP : Function.Injective P := point_fin_injective m v hv0
  have hQ : Function.Injective Q := (rotate_coeff_injective v hv0).comp ZMod.injective_toCircle
  have hsurj : ∀ h ∈ H, ∃ j : Fin m, P j = h := by
    intro h hh
    obtain ⟨g, hg⟩ := horbit h hh
    obtain ⟨j, hj⟩ := (canonical_subgroup m hm K hfinite hcard g.val).mp g.property
    exact ⟨j, by dsimp only [P]; rw [hj, ← hg]⟩
  let J := Finset.univ.filter (fun j : Fin m => P j ∈ H)
  have hJimage : J.image P = H := by
    ext h
    constructor
    · rintro hh
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hh
      exact (Finset.mem_filter.mp hj).2
    · intro hh
      obtain ⟨j, hj⟩ := hsurj h hh
      exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj ▸ hh⟩, hj⟩
  have hJcard : J.card = H.card := by
    rw [← hJimage, Finset.card_image_of_injective _ hP]
  let U := Finset.univ.filter (fun j : ZMod m => Q j ∈ H)
  have hUimage : U.image Q = H := by
    ext h
    constructor
    · intro hh
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hh
      exact (Finset.mem_filter.mp hj).2
    · intro hh
      obtain ⟨j, hj⟩ := hsurj h hh
      have he : Q (j.val : ZMod m) = h := by
        dsimp only [Q]
        rw [circle_fin]
        exact hj
      exact Finset.mem_image.mpr ⟨(j.val : ZMod m),
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, he ▸ hh⟩, he⟩
  have hUcard : U.card = H.card := by
    rw [← hUimage, Finset.card_image_of_injective _ hQ]
  have hrealize : ∀ ell : ℕ, 1 ≤ ell → ell ≤ m / 2 →
      ∃ a ∈ H, ∃ b ∈ H, a ≠ b ∧ dist a b = 2 * R * Real.sin (π * (ell : ℝ) / (m : ℝ)) := by
    intro ell hell helltop
    have hellm : ell < m := by omega
    obtain ⟨i, hi, his⟩ := dense_shift m U (by omega) (ell : ZMod m)
    have hs0 : (ell : ZMod m) ≠ 0 := by
      intro he
      have heval := congrArg ZMod.val he
      rw [ZMod.val_natCast_of_lt hellm, ZMod.val_zero] at heval
      omega
    have hneq : Q (i + (ell : ZMod m)) ≠ Q i := by
      intro he
      have he' := hQ he
      have hs : (ell : ZMod m) = 0 := by simpa using he'
      exact hs0 hs
    refine ⟨Q (i + (ell : ZMod m)), (Finset.mem_filter.mp his).2,
      Q i, (Finset.mem_filter.mp hi).2, hneq, ?_⟩
    have hd := shifted_dist m i (ell : ZMod m) v
    simpa only [Q, ZMod.val_natCast_of_lt hellm, hv] using hd
  let D : ℝ := 2 * R * Real.sin (π * ((m / 2 : ℕ) : ℝ) / (m : ℝ))
  have hDbounds := angle_bounds m (m / 2) (by omega) le_rfl
  have hDnonneg : 0 ≤ D := mul_nonneg (by positivity)
    (Real.sin_nonneg_of_nonneg_of_le_pi hDbounds.1 (by linarith [Real.pi_pos]))
  have hpair : ∀ a ∈ H, ∀ b ∈ H, dist a b ≤ D := by
    intro a ha b hb
    rw [← hUimage] at ha hb
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
    have he : i + (j - i) = j := by abel
    have hd := shifted_dist m i (j - i) v
    rw [he, hv] at hd
    rw [dist_comm]
    change dist (rotate (ZMod.toCircle j) v) (rotate (ZMod.toCircle i) v) ≤ D
    rw [hd]
    exact mul_le_mul_of_nonneg_left (sin_bound m (j - i).val hm (ZMod.val_lt _)) (by positivity)
  have hdiamle : Metric.diam (H : Set Plane) ≤ D := by
    apply Metric.diam_le_of_forall_dist_le hDnonneg
    exact hpair
  obtain ⟨a, ha, b, hb, _, hab⟩ := hrealize (m / 2) (by omega) le_rfl
  have hdiamge : D ≤ Metric.diam (H : Set Plane) := by
    change 2 * R * Real.sin (π * ((m / 2 : ℕ) : ℝ) / (m : ℝ)) ≤ _
    rw [← hab]
    exact Metric.dist_le_diam_of_mem H.finite_toSet.isBounded ha hb
  have hdiam : Metric.diam (H : Set Plane) = D := le_antisymm hdiamle hdiamge
  refine ⟨canonical_subgroup m hm K hfinite hcard, hP, ⟨J, hJcard, hJimage⟩,
    hrealize, hdiam, ?_⟩
  intro ell hell helltop
  have hb := angle_bounds m ell (by omega) helltop.le
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hpos : 0 < π * (ell : ℝ) / (m : ℝ) := by
    have hellR : (0 : ℝ) < ell := by exact_mod_cast (show 0 < ell by omega)
    positivity
  have hsinpos : 0 < Real.sin (π * (ell : ℝ) / (m : ℝ)) :=
    Real.sin_pos_of_pos_of_lt_pi hpos (by linarith [Real.pi_pos])
  have hanglelt : π * (ell : ℝ) / (m : ℝ) < π * ((m / 2 : ℕ) : ℝ) / (m : ℝ) := by
    apply (div_lt_div_iff_of_pos_right hmR).mpr
    exact mul_lt_mul_of_pos_left (by exact_mod_cast helltop) Real.pi_pos
  have hsinlt := Real.strictMonoOn_sin ⟨by linarith [Real.pi_pos], hb.2⟩
    ⟨by linarith [Real.pi_pos], hDbounds.2⟩ hanglelt
  refine ⟨mul_pos (by positivity) hsinpos, ?_⟩
  rw [hdiam]
  exact mul_lt_mul_of_pos_left hsinlt (by positivity)

/-- The full canonical unit square jointly satisfies all generic premises, and
applying the completion theorem to that same square realizes its chords and diameter. -/
theorem unit_square_application :
    ∃ (K : Subgroup Rotation) (v : Plane) (H : Finset Plane),
      (K : Set Rotation).Finite ∧ Nat.card K = 4 ∧ ‖v‖ = (1 : ℝ) ∧ H.card = 4 ∧
      (∀ h ∈ H, ∃ g : K, h = rotate g.val v) ∧ 4 < 2 * H.card ∧
      (∀ ell : ℕ, 1 ≤ ell → ell ≤ 2 → ∃ a ∈ H, ∃ b ∈ H,
        a ≠ b ∧ dist a b = 2 * Real.sin (π * (ell : ℝ) / 4)) ∧
      Metric.diam (H : Set Plane) = 2 := by
  classical
  let K : Subgroup Circle :=
    { carrier := {g | g ^ 4 = 1}
      one_mem' := by simp
      mul_mem' := by intro a b ha hb; simp only [Set.mem_ofPred_eq] at *; rw [mul_pow, ha, hb, one_mul]
      inv_mem' := by intro a ha; simp only [Set.mem_ofPred_eq] at *; rw [inv_pow, ha, inv_one] }
  have hpow : ∀ j : ZMod 4, (ZMod.toCircle j) ^ 4 = 1 := by
    intro j
    rw [← AddChar.map_nsmul_eq_pow]
    have hz : (4 : ZMod 4) = 0 := by decide
    simp only [nsmul_eq_mul, Nat.cast_ofNat, hz, zero_mul, AddChar.map_zero_eq_one]
  let f : ZMod 4 → K := fun j => ⟨ZMod.toCircle j, hpow j⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      exact ZMod.injective_toCircle (congrArg Subtype.val hij)
    · intro g
      obtain ⟨j, hj⟩ := root_enumeration 4 g.val g.property
      exact ⟨j, Subtype.ext hj⟩
  letI : Finite K := Finite.of_surjective f hf.surjective
  have hfinite : (K : Set Rotation).Finite := Set.toFinite _
  have hcard : Nat.card K = 4 := by
    rw [← Nat.card_congr (Equiv.ofBijective f hf)]
    simp
  let v : Plane := WithLp.toLp 2 ![1, 0]
  have hv : ‖v‖ = (1 : ℝ) := by
    norm_num [v, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  have hv0 : v ≠ 0 := ne_zero_of_norm_eq (by norm_num) hv
  let Q : ZMod 4 → Plane := fun j => rotate (ZMod.toCircle j) v
  let H := Finset.univ.image Q
  have hQinj : Function.Injective Q :=
    (rotate_coeff_injective v hv0).comp ZMod.injective_toCircle
  have hHcard : H.card = 4 := by
    change (Finset.univ.image Q).card = 4
    rw [Finset.card_image_of_injective _ hQinj]
    simp
  have horbit : ∀ h ∈ H, ∃ g : K, h = rotate g.val v := by
    intro h hh
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hh
    exact ⟨f j, rfl⟩
  have hcompletion := finite_circle_completion 4 (by decide) K hfinite hcard
    1 (by norm_num) v hv H horbit (by omega)
  have hrealize := hcompletion.2.2.2.1
  have hdiam := hcompletion.2.2.2.2.1
  have he : π * (2 : ℝ) / 4 = π / 2 := by ring
  norm_num only [Nat.reduceDiv, Nat.cast_ofNat, mul_one, he, Real.sin_pi_div_two] at hdiam
  refine ⟨K, v, H, hfinite, hcard, hv, hHcard, horbit, by omega, ?_, hdiam⟩
  intro ell hell htop
  simpa only [Nat.reduceDiv, Nat.cast_ofNat, mul_one] using hrealize ell hell htop

end Erdos132.FiniteCircleCompletion
