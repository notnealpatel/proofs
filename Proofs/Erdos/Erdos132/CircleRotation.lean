import Erdos.Erdos132.TwoInteriorCircle
import Mathlib.Analysis.Complex.Circle
import Mathlib.GroupTheory.GroupAction.CardCommute

set_option autoImplicit false

open scoped BigOperators
open Erdos132.TwoInteriorCircle

namespace Erdos132.CircleRotation

/-- Origin rotations, represented by their norm-one complex coefficients. -/
abbrev Rotation := Circle

/-- The two real coordinates encoded as a complex number (points remain in `Plane`). -/
def encode (x : Plane) : ℂ := ⟨x 0, x 1⟩

example (x : Plane) : (encode x).re = x 0 := rfl
example (x : Plane) : (encode x).im = x 1 := rfl

/-- Encoding preserves equality of planar points. -/
theorem encode_injective : Function.Injective encode := by
  intro x y h
  ext i
  fin_cases i
  · exact congrArg Complex.re h
  · exact congrArg Complex.im h

/-- Encoding preserves the Euclidean norm. -/
theorem norm_encode (x : Plane) : ‖encode x‖ = ‖x‖ := by
  have hc := Complex.sq_norm (encode x)
  have hp := EuclideanSpace.real_norm_sq_eq x
  simp only [Fin.sum_univ_two, encode, Complex.normSq_apply] at hc hp
  have hsq : ‖encode x‖ ^ 2 = ‖x‖ ^ 2 := by
    dsimp only [encode]
    nlinarith only [hc, hp]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- The actual coefficient-linear planar rotation. -/
noncomputable def rotate (g : Rotation) (x : Plane) : Plane :=
  WithLp.toLp 2 ![(g : ℂ).re * x 0 - (g : ℂ).im * x 1,
    (g : ℂ).im * x 0 + (g : ℂ).re * x 1]

example (g : Rotation) (x : Plane) :
    rotate g x 0 = (g : ℂ).re * x 0 - (g : ℂ).im * x 1 := rfl
example (g : Rotation) (x : Plane) :
    rotate g x 1 = (g : ℂ).im * x 0 + (g : ℂ).re * x 1 := rfl

/-- Planar rotation corresponds exactly to coefficient multiplication. -/
theorem encode_rotate (g : Rotation) (x : Plane) :
    encode (rotate g x) = (g : ℂ) * encode x := by
  apply Complex.ext <;> simp [encode, rotate, Complex.mul_re, Complex.mul_im] <;> ring

/-- The identity coefficient acts identically. -/
@[simp] theorem rotate_one (x : Plane) : rotate 1 x = x := by
  apply encode_injective
  simp [encode_rotate]

/-- Coefficient multiplication is composition of the planar rotations. -/
theorem rotate_mul (g k : Rotation) (x : Plane) :
    rotate (g * k) x = rotate g (rotate k x) := by
  apply encode_injective
  simp [encode_rotate, mul_assoc]

/-- Rotations preserve addition. -/
theorem rotate_add (g : Rotation) (x y : Plane) :
    rotate g (x + y) = rotate g x + rotate g y := by
  ext i
  fin_cases i <;> simp [rotate] <;> ring

/-- Rotations preserve subtraction. -/
theorem rotate_sub (g : Rotation) (x y : Plane) :
    rotate g (x - y) = rotate g x - rotate g y := by
  ext i
  fin_cases i <;> simp [rotate] <;> ring

/-- Rotations preserve the Euclidean norm. -/
theorem norm_rotate (g : Rotation) (x : Plane) : ‖rotate g x‖ = ‖x‖ := by
  rw [← norm_encode, encode_rotate, norm_mul, Circle.norm_coe, one_mul, norm_encode]

/-- Every coefficient acts by an actual isometry of the ordinary plane. -/
theorem rotate_isometry (g : Rotation) : Isometry (rotate g) := by
  apply Isometry.of_dist_eq
  intro x y
  simp only [dist_eq_norm, ← rotate_sub, norm_rotate]

/-- The coefficient rotations form a group action on the ordinary plane. -/
noncomputable instance : MulAction Rotation Plane where
  smul := rotate
  one_smul := rotate_one
  mul_smul := rotate_mul

example (g : Rotation) (x : Plane) : g • x = rotate g x := rfl

/-- A rotation fixing a nonzero point is the identity. -/
theorem point_fixed_imp_one (g : Rotation) (x : Plane) (hx : x ≠ 0)
    (hfix : rotate g x = x) : g = 1 := by
  have he : encode x ≠ 0 := by
    intro he
    apply hx
    apply encode_injective
    exact he
  apply Circle.ext
  have h := congrArg encode hfix
  rw [encode_rotate] at h
  exact (mul_right_cancel₀ he (h.trans (one_mul (encode x)).symm))

/-- The full subgroup of coefficients preserving the finite planar set. -/
noncomputable def Stabilizer (H : Finset Plane) : Subgroup Rotation where
  carrier := {g | ∀ x, rotate g x ∈ H ↔ x ∈ H}
  one_mem' := by simp
  mul_mem' := by
    intro g k hg hk x
    rw [rotate_mul, hg, hk]
  inv_mem' := by
    intro g hg x
    have h := hg (rotate g⁻¹ x)
    simpa only [← rotate_mul, mul_inv_cancel, rotate_one] using h.symm

/-- Ground-truth membership in the full rotation subgroup. -/
theorem mem_stabilizer_iff (H : Finset Plane) (g : Rotation) :
    g ∈ Stabilizer H ↔ ∀ x, rotate g x ∈ H ↔ x ∈ H := Iff.rfl

/-- Full subgroup membership is exactly preservation of the finite set by image. -/
theorem mem_stabilizer_iff_image (H : Finset Plane) (g : Rotation) :
    g ∈ Stabilizer H ↔ H.image (rotate g) = H := by
  classical
  constructor
  · intro hg
    ext y
    constructor
    · rintro hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact (hg x).2 hx
    · intro hy
      refine Finset.mem_image.mpr ⟨rotate g⁻¹ y, ?_, ?_⟩
      · exact (hg (rotate g⁻¹ y)).1 (by simpa [← rotate_mul] using hy)
      · simp [← rotate_mul]
  · intro hi x
    constructor
    · intro hx
      have hi' := congrArg (fun S : Finset Plane => rotate g x ∈ S) hi
      have hex : rotate g x ∈ H.image (rotate g) := hi'.mpr hx
      obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp hex
      have hyx : y = x := (rotate_isometry g).injective heq
      simpa [hyx] using hy
    · intro hx
      rw [← hi]
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

/-- The order of the full origin-rotation subgroup, independent of finite instances. -/
noncomputable def order (H : Finset Plane) : ℕ := Nat.card (Stabilizer H)

example (H : Finset Plane) : order H = Nat.card (Stabilizer H) := rfl

/-- Evaluation at any nonzero point distinguishes rotation coefficients. -/
theorem rotate_coeff_injective (x : Plane) (hx : x ≠ 0) :
    Function.Injective (fun g : Rotation => rotate g x) := by
  intro g k h
  have he : encode x ≠ 0 := by
    intro he
    exact hx (encode_injective he)
  apply Circle.ext
  apply mul_right_cancel₀ he
  simpa only [encode_rotate] using congrArg encode h

/-- The full stabilizer is finite when the nonempty set lies on a positive-radius circle. -/
theorem finite_stabilizer (H : Finset Plane) {R : ℝ} (hH : H.Nonempty)
    (hR : 0 < R) (hcircle : ∀ x ∈ H, ‖x‖ = R) : Finite (Stabilizer H) := by
  obtain ⟨x, hx⟩ := hH
  have hx0 : x ≠ 0 := by
    intro hx0
    have hr := hcircle x hx
    rw [hx0, norm_zero] at hr
    linarith
  let ev : Stabilizer H → {x // x ∈ H} :=
    fun g => ⟨rotate g.val x, (g.property x).2 hx⟩
  apply Finite.of_injective ev
  intro g k heq
  apply Subtype.ext
  exact rotate_coeff_injective x hx0 (congrArg Subtype.val heq)

/-- The full rotation group acts on the vertices of the preserved finite set. -/
noncomputable instance hullAction (H : Finset Plane) :
    MulAction (Stabilizer H) {x // x ∈ H} where
  smul g x := ⟨rotate g.val x.val, (g.property x.val).2 x.property⟩
  one_smul x := Subtype.ext (rotate_one x.val)
  mul_smul g k x := Subtype.ext (rotate_mul g.val k.val x.val)

example (H : Finset Plane) (g : Stabilizer H) (x : {x // x ∈ H}) :
    (g • x).val = rotate g.val x.val := rfl

private theorem card_dvd_of_free (G X : Type*) [Group G] [MulAction G X]
    [Finite G] [Finite X] (hfree : ∀ g : G, ∀ x : X, g • x = x → g = 1) :
    Nat.card G ∣ Nat.card X := by
  have hs : ∀ x : X, MulAction.stabilizer G x = ⊥ := by
    intro x
    apply le_antisymm
    · intro g hg
      exact Subgroup.mem_bot.mpr (hfree g x hg)
    · exact bot_le
  rw [Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd (G := G) (X := X) hs), Nat.card_prod]
  exact dvd_mul_left _ _

/-- The full rotation order divides the hull cardinality, with freeness derived geometrically. -/
theorem order_dvd_card (H : Finset Plane) {R : ℝ} (hH : H.Nonempty)
    (hR : 0 < R) (hcircle : ∀ x ∈ H, ‖x‖ = R) : order H ∣ H.card := by
  classical
  letI := finite_stabilizer H hH hR hcircle
  have hd := card_dvd_of_free (Stabilizer H) {x // x ∈ H} (by
    intro g x hfix
    apply Subtype.ext
    apply point_fixed_imp_one g.val x.val
    · intro hx0
      have hr := hcircle x.val x.property
      rw [hx0, norm_zero] at hr
      linarith
    · exact congrArg Subtype.val hfix)
  simpa only [order, Nat.card_eq_fintype_card, Fintype.card_coe] using hd

/-- A positive-radius point is not the origin. -/
theorem ne_zero_of_norm_eq {x : Plane} {R : ℝ} (hR : 0 < R)
    (hx : ‖x‖ = R) : x ≠ 0 := by
  intro hx0
  rw [hx0, norm_zero] at hx
  linarith

/-- Two points on the circle with subdiametral separation have nonzero sum. -/
theorem sum_ne_zero_of_dist_lt {a b : Plane} {R : ℝ}
    (ha : ‖a‖ = R) (hab : dist a b < 2 * R) : a + b ≠ 0 := by
  intro hsum
  have hb : b = -a := eq_neg_of_add_eq_zero_right hsum
  have hv : a - b = (2 : ℝ) • a := by
    rw [hb]
    module
  have hd : dist a b = 2 * R := by
    rw [dist_eq_norm, hv, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num), ha]
  linarith

/-- No nonidentity coefficient can fix an unordered subdiametral circle pair. -/
theorem pair_fixed_imp_one (H : Finset Plane) (g : Rotation) {R d : ℝ}
    (hR : 0 < R) (hcircle : ∀ x ∈ H, ‖x‖ = R)
    (hd : 0 < d) (hdR : d < 2 * R) (e : Sym2 Plane)
    (he : e ∈ pairs H) (hed : pairDist e = d)
    (hfix : Sym2.map (rotate g) e = e) : g = 1 := by
  induction e using Sym2.ind with
  | _ a b =>
    obtain ⟨ha, hb, hab⟩ := (mk_mem_pairs H a b).mp he
    have had : dist a b < 2 * R := by
      calc
        dist a b = d := hed
        _ < 2 * R := hdR
    rw [Sym2.map_mk, Sym2.eq_iff] at hfix
    rcases hfix with ⟨hga, hgb⟩ | ⟨hga, hgb⟩
    · exact point_fixed_imp_one g a (ne_zero_of_norm_eq hR (hcircle a ha)) hga
    · apply point_fixed_imp_one g (a + b)
      · exact sum_ne_zero_of_dist_lt (hcircle a ha) had
      · rw [rotate_add, hga, hgb, add_comm]

/-- The actual finite class of genuine unordered pairs at distance `d`. -/
noncomputable def distancePairs (H : Finset Plane) (d : ℝ) : Finset (Sym2 Plane) := by
  classical
  exact (pairs H).filter (fun e => pairDist e = d)

/-- Ground-truth membership in the distance-pair class. -/
theorem mem_distancePairs (H : Finset Plane) (d : ℝ) (e : Sym2 Plane) :
    e ∈ distancePairs H d ↔ e ∈ pairs H ∧ pairDist e = d := by
  classical
  exact Finset.mem_filter

/-- The distance-pair class counts the previously defined true multiplicity. -/
theorem card_distancePairs (H : Finset Plane) (d : ℝ) :
    (distancePairs H d).card = multiplicity H d := rfl

/-- An isometric rotation preserves unordered-pair distance. -/
theorem pairDist_map_rotate (g : Rotation) (e : Sym2 Plane) :
    pairDist (Sym2.map (rotate g) e) = pairDist e := by
  induction e using Sym2.ind with
  | _ a b => exact (rotate_isometry g).dist_eq a b

/-- Full stabilizer rotations carry the genuine distance-pair class into itself. -/
theorem map_mem_distancePairs (H : Finset Plane) (d : ℝ) (g : Stabilizer H)
    (e : Sym2 Plane) (he : e ∈ distancePairs H d) :
    Sym2.map (rotate g.val) e ∈ distancePairs H d := by
  rw [mem_distancePairs] at he ⊢
  refine ⟨?_, (pairDist_map_rotate g.val e).trans he.2⟩
  induction e using Sym2.ind with
  | _ a b =>
    obtain ⟨ha, hb, hab⟩ := (mk_mem_pairs H a b).mp he.1
    rw [Sym2.map_mk, mk_mem_pairs]
    exact ⟨(g.property a).2 ha, (g.property b).2 hb,
      (rotate_isometry g.val).injective.ne hab⟩

/-- The full group acts by the actual endpoint rotations on each distance-pair class. -/
noncomputable instance distancePairAction (H : Finset Plane) (d : ℝ) :
    MulAction (Stabilizer H) {e // e ∈ distancePairs H d} where
  smul g e := ⟨Sym2.map (rotate g.val) e.val, map_mem_distancePairs H d g e.val e.property⟩
  one_smul e := by
    apply Subtype.ext
    change Sym2.map (rotate 1) e.val = e.val
    induction e.val using Sym2.ind with
    | _ a b => simp
  mul_smul g k e := by
    apply Subtype.ext
    change Sym2.map (rotate (g.val * k.val)) e.val =
      Sym2.map (rotate g.val) (Sym2.map (rotate k.val) e.val)
    induction e.val using Sym2.ind with
    | _ a b => simp [rotate_mul]

example (H : Finset Plane) (d : ℝ) (g : Stabilizer H)
    (e : {e // e ∈ distancePairs H d}) :
    (g • e).val = Sym2.map (rotate g.val) e.val := rfl

/-- Full rotation order divides every subdiametral positive-distance multiplicity,
including zero multiplicity; pair freeness is proved rather than assumed. -/
theorem order_dvd_multiplicity (H : Finset Plane) {R d : ℝ} (hH : H.Nonempty)
    (hR : 0 < R) (hcircle : ∀ x ∈ H, ‖x‖ = R)
    (hd : 0 < d) (hdR : d < 2 * R) : order H ∣ multiplicity H d := by
  classical
  letI := finite_stabilizer H hH hR hcircle
  have hdiv := card_dvd_of_free (Stabilizer H) {e // e ∈ distancePairs H d} (by
    intro g e hfix
    apply Subtype.ext
    have he := (mem_distancePairs H d e.val).mp e.property
    exact pair_fixed_imp_one H g.val hR hcircle hd hdR e.val he.1 he.2
      (congrArg Subtype.val hfix))
  simpa only [order, Nat.card_eq_fintype_card, Fintype.card_coe, card_distancePairs] using hdiv

example : ∃ (H : Finset Plane) (R d : ℝ) (e : Sym2 Plane),
    H.Nonempty ∧ 0 < R ∧ (∀ x ∈ H, ‖x‖ = R) ∧ 0 < d ∧ d < 2 * R ∧
      e ∈ pairs H ∧ pairDist e = d ∧ Sym2.map (rotate 1) e = e := by
  classical
  let a : Plane := WithLp.toLp 2 ![1, 0]
  let b : Plane := WithLp.toLp 2 ![0, 1]
  have ha : ‖a‖ = 1 := by
    norm_num [a, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  have hb : ‖b‖ = 1 := by
    norm_num [b, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  have hab : a ≠ b := by
    intro h
    have hc := congrArg (fun x : Plane => x 0) h
    norm_num [a, b] at hc
  have hsq : (dist a b) ^ 2 = 2 := by
    rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
    norm_num [a, b, Fin.sum_univ_two]
  refine ⟨{a, b}, 1, dist a b, s(a, b), ?_, by norm_num, ?_,
    dist_pos.mpr hab, ?_, ?_, rfl, ?_⟩
  · simp
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  · nlinarith [dist_nonneg (x := a) (y := b)]
  · exact (mk_mem_pairs _ _ _).mpr ⟨by simp, by simp, hab⟩
  · simp

/-- Saturation of the chord capacity makes every vertex have exactly two neighbors. -/
theorem chord_neighbors_card_eq_two (H : Finset Plane) {R d : ℝ}
    (hR : 0 < R) (hcircle : ∀ x ∈ H, ‖x‖ = R) (hd : 0 < d)
    (hsat : multiplicity H d = H.card) :
    ∀ x ∈ H, (H.filter fun y => dist y x = d).card = 2 := by
  classical
  let Q := distancePairs H d
  have hdegree : ∀ x ∈ H,
      (Q.bipartiteBelow (fun e x => x ∈ e) x).card =
        (H.filter fun y => dist y x = d).card := by
    intro x hx
    have hset : Q.bipartiteBelow (fun e x => x ∈ e) x =
        (H.filter fun y => dist y x = d).image (fun y => s(x, y)) := by
      ext e
      simp only [Finset.bipartiteBelow, Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨he, hxe⟩
        have he' := (mem_distancePairs H d e).mp he
        induction e using Sym2.ind with
        | _ a b =>
          obtain ⟨ha, hb, hab⟩ := (mk_mem_pairs H a b).mp he'.1
          have habd : dist a b = d := he'.2
          rcases Sym2.mem_iff.mp hxe with rfl | rfl
          · exact ⟨b, ⟨hb, by simpa only [dist_comm] using habd⟩, rfl⟩
          · exact ⟨a, ⟨ha, habd⟩, Sym2.eq_swap⟩
      · rintro ⟨y, ⟨hy, hyd⟩, rfl⟩
        refine ⟨(mem_distancePairs H d _).mpr ⟨?_, ?_⟩, by simp⟩
        · apply (mk_mem_pairs H x y).mpr
          refine ⟨hx, hy, ?_⟩
          intro hxy
          rw [← hxy, dist_self] at hyd
          linarith
        · simpa only [pairDist_mk, dist_comm] using hyd
    rw [hset]
    exact Finset.card_image_of_injective _ (Sym2.mkEmbedding x).injective
  have hendpoints : ∀ e ∈ Q,
      (H.bipartiteAbove (fun e x => x ∈ e) e).card = 2 := by
    intro e he
    have he' := (mem_distancePairs H d e).mp he
    induction e using Sym2.ind with
    | _ a b =>
      obtain ⟨ha, hb, hab⟩ := (mk_mem_pairs H a b).mp he'.1
      have hset : H.bipartiteAbove (fun e x => x ∈ e) s(a, b) = {a, b} := by
        ext x
        simp only [Finset.bipartiteAbove, Finset.mem_filter, Finset.mem_insert,
          Finset.mem_singleton, Sym2.mem_iff]
        aesop
      rw [hset, Finset.card_pair hab]
  have hsum : ∑ x ∈ H, (H.filter fun y => dist y x = d).card = ∑ _x ∈ H, 2 := by
    calc
      _ = ∑ x ∈ H, (Q.bipartiteBelow (fun e x => x ∈ e) x).card := by
        apply Finset.sum_congr rfl
        intro x hx
        exact (hdegree x hx).symm
      _ = ∑ e ∈ Q, (H.bipartiteAbove (fun e x => x ∈ e) e).card :=
        (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
          (s := Q) (t := H) (r := fun e x => x ∈ e)).symm
      _ = ∑ _e ∈ Q, 2 := Finset.sum_congr rfl hendpoints
      _ = ∑ _x ∈ H, 2 := by
        simp only [Finset.sum_const, smul_eq_mul]
        rw [card_distancePairs, hsat]
  apply (Finset.sum_eq_sum_iff_of_le ?_).mp hsum
  intro x hx
  apply radial_card_le_two H 0 x R d
  · intro y hy
    simpa only [dist_zero_right] using hcircle y hy
  · exact ne_zero_of_norm_eq hR (hcircle x hx)

/-- With two chord neighbors at a vertex, every geometric chord neighbor belongs to the hull. -/
theorem mem_of_chord_neighbors_card_eq_two (H : Finset Plane) {R d : ℝ}
    (hR : 0 < R) (hcircle : ∀ x ∈ H, ‖x‖ = R)
    (hsat : ∀ x ∈ H, (H.filter fun y => dist y x = d).card = 2)
    {x y : Plane} (hx : x ∈ H) (hyR : ‖y‖ = R) (hyd : dist y x = d) : y ∈ H := by
  classical
  obtain ⟨a, b, hab, hf⟩ := Finset.card_eq_two.mp (hsat x hx)
  have ham : a ∈ H.filter (fun y => dist y x = d) := by rw [hf]; simp
  have hbm : b ∈ H.filter (fun y => dist y x = d) := by rw [hf]; simp
  have ha : a ∈ H ∧ dist a x = d := Finset.mem_filter.mp ham
  have hb : b ∈ H ∧ dist b x = d := Finset.mem_filter.mp hbm
  have he := EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two
    (V := Plane) (c₁ := x) (c₂ := 0) (p₁ := a) (p₂ := b) (p := y)
    (by simp [finrank_euclideanSpace]) (ne_zero_of_norm_eq hR (hcircle x hx)) hab
    ha.2 hb.2 hyd
    (by simpa only [dist_zero_right] using hcircle a ha.1)
    (by simpa only [dist_zero_right] using hcircle b hb.1)
    (by simpa only [dist_zero_right] using hyR)
  rcases he with rfl | rfl
  · exact ha.1
  · exact hb.1

/-- Encoding respects planar subtraction. -/
theorem encode_sub (a b : Plane) : encode (a - b) = encode a - encode b := by
  apply Complex.ext <;> rfl

/-- The displacement of a rotation has length equal to its coefficient displacement
multiplied by the point's radius. -/
theorem dist_rotate_self (g : Rotation) (x : Plane) :
    dist (rotate g x) x = ‖(g : ℂ) - 1‖ * ‖x‖ := by
  calc
    _ = ‖encode (rotate g x - x)‖ := by rw [dist_eq_norm, norm_encode]
    _ = ‖((g : ℂ) - 1) * encode x‖ := by
      rw [encode_sub, encode_rotate]
      congr 1
      ring
    _ = ‖(g : ℂ) - 1‖ * ‖x‖ := by rw [norm_mul, norm_encode]

/-- Equal positive-radius planar points are connected by an actual origin rotation. -/
theorem exists_rotation_map {a b : Plane} {R : ℝ} (hR : 0 < R)
    (ha : ‖a‖ = R) (hb : ‖b‖ = R) : ∃ g : Rotation, rotate g a = b := by
  have ha0 : encode a ≠ 0 := by
    intro he
    exact ne_zero_of_norm_eq hR ha (encode_injective he)
  let g : Rotation := ⟨encode b / encode a, by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_div, norm_encode, norm_encode, ha, hb, div_self (ne_of_gt hR)]⟩
  refine ⟨g, encode_injective ?_⟩
  rw [encode_rotate]
  change (encode b / encode a) * encode a = encode b
  exact div_mul_cancel₀ _ ha0

/-- The coefficient `-1` is the geometric half-turn. -/
@[simp] theorem rotate_neg_one (x : Plane) : rotate (-1) x = -x := by
  ext i
  fin_cases i <;> simp [rotate]

/-- Saturated positive subdiametral chords supply a genuine member of the FULL
rotation group taking their first endpoint to their second, neither identity nor half-turn. -/
theorem exists_stabilizer_map_of_saturated_chord (H : Finset Plane) {R d : ℝ}
    (hR : 0 < R) (hcircle : ∀ x ∈ H, ‖x‖ = R)
    (hd : 0 < d) (hdR : d < 2 * R) (hsat : multiplicity H d = H.card)
    {a b : Plane} (ha : a ∈ H) (hb : b ∈ H) (habd : dist a b = d) :
    ∃ g : Stabilizer H, rotate g.val a = b ∧ g.val ≠ 1 ∧ g.val ≠ -1 := by
  classical
  obtain ⟨g, hgab⟩ := exists_rotation_map hR (hcircle a ha) (hcircle b hb)
  have hneighbors := chord_neighbors_card_eq_two H hR hcircle hd hsat
  have hmaps : ∀ x ∈ H, rotate g x ∈ H := by
    intro x hx
    apply mem_of_chord_neighbors_card_eq_two H hR hcircle hneighbors hx
    · rw [norm_rotate]
      exact hcircle x hx
    · calc
        dist (rotate g x) x = ‖(g : ℂ) - 1‖ * R := by
          rw [dist_rotate_self, hcircle x hx]
        _ = dist (rotate g a) a := by rw [dist_rotate_self, hcircle a ha]
        _ = d := by rw [hgab, dist_comm, habd]
  have hsub : H.image (rotate g) ⊆ H := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact hmaps x hx
  have hpreserve : g ∈ Stabilizer H := by
    apply (mem_stabilizer_iff_image H g).mpr
    apply Finset.eq_of_subset_of_card_le hsub
    rw [Finset.card_image_of_injective H (rotate_isometry g).injective]
  refine ⟨⟨g, hpreserve⟩, hgab, ?_, ?_⟩
  · intro hg1
    change g = 1 at hg1
    have hab : a = b := by simpa only [hg1, rotate_one] using hgab
    rw [hab, dist_self] at habd
    linarith
  · intro hgneg
    change g = -1 at hgneg
    have hsum : a + b = 0 := by rw [← hgab, hgneg, rotate_neg_one]; simp
    exact sum_ne_zero_of_dist_lt (hcircle a ha) (habd.symm ▸ hdR) hsum

/-- Endpoints of every saturated positive subdiametral chord belong to one orbit
of the full rotation stabilizer. -/
theorem mem_orbit_of_saturated_chord (H : Finset Plane) {R d : ℝ}
    (hR : 0 < R) (hcircle : ∀ x ∈ H, ‖x‖ = R)
    (hd : 0 < d) (hdR : d < 2 * R) (hsat : multiplicity H d = H.card)
    {a b : Plane} (ha : a ∈ H) (hb : b ∈ H) (habd : dist a b = d) :
    (⟨b, hb⟩ : {x // x ∈ H}) ∈ MulAction.orbit (Stabilizer H) ⟨a, ha⟩ := by
  obtain ⟨g, hgab, hg1, hgneg⟩ :=
    exists_stabilizer_map_of_saturated_chord H hR hcircle hd hdR hsat ha hb habd
  exact ⟨g, Subtype.ext hgab⟩

example : ∃ (H : Finset Plane) (R d : ℝ) (a b : Plane),
    0 < R ∧ (∀ x ∈ H, ‖x‖ = R) ∧ 0 < d ∧ d < 2 * R ∧
      multiplicity H d = H.card ∧ a ∈ H ∧ b ∈ H ∧ dist a b = d := by
  classical
  let a : Plane := WithLp.toLp 2 ![1, 0]
  let b : Plane := WithLp.toLp 2 ![0, 1]
  let c : Plane := WithLp.toLp 2 ![-1, 0]
  let f : Plane := WithLp.toLp 2 ![0, -1]
  have hab : a ≠ b := by
    intro he
    have hc := congrArg encode he
    norm_num [Complex.ext_iff, encode, a, b] at hc
  have hac : a ≠ c := by
    intro he
    have hc := congrArg encode he
    norm_num [Complex.ext_iff, encode, a, c] at hc
  have haf : a ≠ f := by
    intro he
    have hc := congrArg encode he
    norm_num [Complex.ext_iff, encode, a, f] at hc
  have hbc : b ≠ c := by
    intro he
    have hc := congrArg encode he
    norm_num [Complex.ext_iff, encode, b, c] at hc
  have hbf : b ≠ f := by
    intro he
    have hc := congrArg encode he
    norm_num [Complex.ext_iff, encode, b, f] at hc
  have hcf : c ≠ f := by
    intro he
    have hc := congrArg encode he
    norm_num [Complex.ext_iff, encode, c, f] at hc
  have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have htwo : (2 : ℝ) ≠ Real.sqrt 2 := by nlinarith
  have hclass : distancePairs {a, b, c, f} (Real.sqrt 2) =
      {s(a, b), s(a, f), s(b, c), s(c, f)} := by
    ext e
    induction e using Sym2.ind with
    | _ x y =>
      simp only [mem_distancePairs, mk_mem_pairs, pairDist_mk, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨⟨hx, hy, hxy⟩, hdist⟩
        rcases hx with rfl | rfl | rfl | rfl <;>
          rcases hy with rfl | rfl | rfl | rfl <;>
          simp_all [a, b, c, f, dist_eq_norm,
            EuclideanSpace.norm_eq, Fin.sum_univ_two] <;>
          norm_num at * <;> contradiction
      · intro he
        simp only [Sym2.eq_iff] at he
        rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          simp_all [a, b, c, f, dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_two] <;>
          norm_num
  refine ⟨{a, b, c, f}, 1, Real.sqrt 2, a, b, by norm_num, ?_, ?_, ?_, ?_,
    by simp, by simp, ?_⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;>
      norm_num [a, b, c, f, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  · positivity
  · nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  · rw [← card_distancePairs, hclass]
    simp [Sym2.eq_iff, hab, hac, haf, hbc, hbf, hcf,
      hab.symm, hac.symm, haf.symm, hbc.symm, hbf.symm, hcf.symm]
  · norm_num [a, b, dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_two]

end Erdos132.CircleRotation
