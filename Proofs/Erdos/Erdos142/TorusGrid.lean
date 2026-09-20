/-
  Erdős Problem #142 — a modular-grid consumer of the finite-epsilon torus
  building block.

  Provenance: Elsholtz–Hunter–Proske–Sauermann (EHPS), "Improving Behrend's
  construction", arXiv:2406.12290v1, Proposition 2.2 and §5, Definition 5.1,
  together with the finite-epsilon modification verified in
  `Erdos.Erdos142.TorusBuildingBlock`.

  The torus building block `torusF_threeAP` states the three-term energy
  inequality for arbitrary real points `x y z` of the extended torus set whose
  coordinate differences `xᵢ + zᵢ - 2 yᵢ` are integers (the "integer wraps").
  This module constructs the canonical residue-grid consumer of that theorem:

  * the canonical real lift of `x : ZMod q × ZMod q` is the point
    `(x.1.val / q, x.2.val / q)` of the half-open unit square;
  * `torusGrid ε q` is the finite set of residues whose lift lies in `torusT ε`;
  * when `q > 0`, grid points `X, Y, Z` that form a three-term arithmetic
    progression `X + Z = 2 • Y` in the product group have integer coordinate
    wraps, so `torusF_threeAP` applies verbatim.

  The essential arithmetic bridge is the sound extraction of integer wraps
  from a congruence in `ZMod q` (the residue equality `X.1 + Z.1 = 2 * Y.1`
  forces `X.1.val + Z.1.val - 2 * Y.1.val` to be an integer multiple of `q`).

  This module only transports the building block to the residue grid; it makes
  no area, integration, or asymptotic-improvement claim.
-/

import Erdos.Erdos142.TorusBuildingBlock

set_option autoImplicit false

namespace Erdos142

/-- The canonical real lift of a residue `a : ZMod q`, normalized into the
half-open unit interval by dividing its least nonnegative representative by
`q`. -/
noncomputable def cyclicLift (q : ℕ) (a : ZMod q) : ℝ := (a.val : ℝ) / q

/-- The canonical real grid lift of `x : ZMod q × ZMod q`, applied coordinatewise.
Defining the lift through `cyclicLift` keeps the construction downstream-friendly
for products: every coordinate fact reduces to the one-dimensional lift. -/
noncomputable def torusLift (q : ℕ) (x : ZMod q × ZMod q) : ℝ × ℝ :=
  (cyclicLift q x.1, cyclicLift q x.2)

/-- The `torusT ε` grid as a set of residues of the torus square. -/
def torusGridSet (ε : ℝ) (q : ℕ) : Set (ZMod q × ZMod q) :=
  {x | torusT ε (torusLift q x)}

/-- The `torusT ε` grid as a finite set of residues of the torus square.
Finiteness is only available for positive modulus, so `q` carries a `NeZero`
instance (equivalently `q ≠ 0`). -/
noncomputable def torusGrid (ε : ℝ) (q : ℕ) [NeZero q] :
    Finset (ZMod q × ZMod q) := by
  classical
  exact Finset.univ.filter fun x => torusT ε (torusLift q x)

/-- Ground truth for the one-dimensional lift: the residue `2` in `ZMod 5`
lifts to `2 / 5`. -/
example : cyclicLift 5 (2 : ZMod 5) = 2 / 5 := by
  have h : ((2 : ZMod 5)).val = 2 :=
    ZMod.val_natCast_of_lt (by norm_num : (2 : ℕ) < 5)
  simp only [cyclicLift, h]
  norm_num

/-- Ground truth for the product lift. -/
example : torusLift 5 ((2 : ZMod 5), (3 : ZMod 5)) = ((2 / 5 : ℝ), 3 / 5) := by
  have h2 : ((2 : ZMod 5)).val = 2 :=
    ZMod.val_natCast_of_lt (by norm_num : (2 : ℕ) < 5)
  have h3 : ((3 : ZMod 5)).val = 3 :=
    ZMod.val_natCast_of_lt (by norm_num : (3 : ℕ) < 5)
  simp only [torusLift, cyclicLift, h2, h3]
  norm_num

/-- Membership in the grid is exactly membership of the lift in `torusT ε`. -/
@[simp]
theorem mem_torusGridSet {ε : ℝ} {q : ℕ} {x : ZMod q × ZMod q} :
    x ∈ torusGridSet ε q ↔ torusT ε (torusLift q x) := Iff.rfl

/-- Membership in the finite grid is exactly membership of the lift in
`torusT ε`. -/
@[simp]
theorem mem_torusGrid {ε : ℝ} {q : ℕ} [NeZero q] {x : ZMod q × ZMod q} :
    x ∈ torusGrid ε q ↔ torusT ε (torusLift q x) := by
  classical
  simp [torusGrid]

/-- The finite grid and the set-valued grid describe the same set of residues;
this is the coercion bridge for downstream set-based counting arguments. -/
theorem coe_torusGrid (ε : ℝ) (q : ℕ) [NeZero q] :
    (torusGrid ε q : Set (ZMod q × ZMod q)) = torusGridSet ε q := by
  classical
  ext x
  simp [torusGrid, torusGridSet]

/-- The one-dimensional lift is nonnegative. -/
theorem cyclicLift_nonneg (q : ℕ) (a : ZMod q) : 0 ≤ cyclicLift q a := by
  unfold cyclicLift
  positivity

/-- The one-dimensional lift of a residue of `ZMod q` with `q > 0` is strictly
below one. -/
theorem cyclicLift_lt_one {q : ℕ} [NeZero q] (a : ZMod q) :
    cyclicLift q a < 1 := by
  unfold cyclicLift
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  rw [div_lt_one hq]
  exact_mod_cast ZMod.val_lt a

/-- The grid lift of a residue of `ZMod q` with `q > 0` lies in the half-open
unit square, matching the coordinate bounds of `torusT`. -/
theorem torusLift_coordinate_bounds {q : ℕ} [NeZero q]
    (x : ZMod q × ZMod q) :
    0 ≤ (torusLift q x).1 ∧ (torusLift q x).1 < 1 ∧
      0 ≤ (torusLift q x).2 ∧ (torusLift q x).2 < 1 :=
  ⟨cyclicLift_nonneg q x.1, cyclicLift_lt_one x.1,
    cyclicLift_nonneg q x.2, cyclicLift_lt_one x.2⟩

/-- **Residue congruence.** If `a + c = 2 * b` in `ZMod q`, then the least
nonnegative representatives satisfy `a.val + c.val ≡ 2 * b.val (mod q)`. -/
theorem val_add_modEq_two_mul {q : ℕ} [NeZero q] {a b c : ZMod q}
    (h : a + c = 2 * b) :
    (a.val + c.val) ≡ 2 * b.val [MOD q] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  rw [ZMod.natCast_zmod_val a, ZMod.natCast_zmod_val b, ZMod.natCast_zmod_val c]
  exact h

/-- **Integer-wrap extraction.** If `a + c = 2 * b` in `ZMod q` with `q > 0`,
then there is an integer `w` with
`a.val + c.val - 2 * b.val = w * q`: the residue equality makes the naive
representative combination an exact multiple of `q`. -/
theorem val_add_wrap {q : ℕ} [NeZero q] {a b c : ZMod q}
    (h : a + c = 2 * b) :
    ∃ w : ℤ, (a.val : ℤ) + c.val - 2 * (b.val : ℤ) = w * q := by
  have hmod := val_add_modEq_two_mul h
  have hdvd :
      (q : ℤ) ∣ ((2 * b.val : ℕ) : ℤ) - (((a.val + c.val : ℕ)) : ℤ) :=
    Nat.ModEq.dvd hmod
  obtain ⟨k, hk⟩ := hdvd
  refine ⟨-k, ?_⟩
  push_cast at hk ⊢
  linarith

/-- **Lifted integer wrap.** If `a + c = 2 * b` in `ZMod q` with `q > 0`, then
the real lifts satisfy `cyclicLift q a + cyclicLift q c - 2 * cyclicLift q b = w`
for some integer `w`, which is precisely the hypothesis `torusF_threeAP` needs. -/
theorem cyclicLift_add_wrap {q : ℕ} [NeZero q] {a b c : ZMod q}
    (h : a + c = 2 * b) :
    ∃ w : ℤ, cyclicLift q a + cyclicLift q c - 2 * cyclicLift q b = (w : ℝ) := by
  obtain ⟨w, hw⟩ := val_add_wrap h
  refine ⟨w, ?_⟩
  have hqR : (q : ℝ) ≠ 0 := by
    have hne : (q : ℕ) ≠ 0 := NeZero.ne q
    exact_mod_cast hne
  have hR : (a.val : ℝ) + (c.val : ℝ) - 2 * (b.val : ℝ) = (w : ℝ) * (q : ℝ) := by
    exact_mod_cast hw
  have hcomb :
      (a.val : ℝ) / (q : ℝ) + (c.val : ℝ) / (q : ℝ) -
          2 * ((b.val : ℝ) / (q : ℝ)) =
        ((a.val : ℝ) + (c.val : ℝ) - 2 * (b.val : ℝ)) / (q : ℝ) := by
    ring
  unfold cyclicLift
  rw [hcomb, hR, mul_div_cancel_right₀ (w : ℝ) hqR]

/-- **Two coordinate wraps from a product progression.** If `X + Z = 2 • Y` in
the product group `ZMod q × ZMod q` with `q > 0`, then the lifted coordinates
admit integer wraps `w₁` and `w₂` as required by `torusF_threeAP`. -/
theorem torusLift_wrap {q : ℕ} [NeZero q] {X Y Z : ZMod q × ZMod q}
    (hAP : X + Z = 2 • Y) :
    ∃ w₁ w₂ : ℤ,
      (torusLift q X).1 + (torusLift q Z).1 - 2 * (torusLift q Y).1 =
          (w₁ : ℝ) ∧
        (torusLift q X).2 + (torusLift q Z).2 - 2 * (torusLift q Y).2 =
          (w₂ : ℝ) := by
  have hfst : X.1 + Z.1 = 2 * Y.1 := by
    have h := congrArg Prod.fst hAP
    simpa [two_smul, two_mul] using h
  have hsnd : X.2 + Z.2 = 2 * Y.2 := by
    have h := congrArg Prod.snd hAP
    simpa [two_smul, two_mul] using h
  obtain ⟨w₁, hw₁⟩ := cyclicLift_add_wrap hfst
  obtain ⟨w₂, hw₂⟩ := cyclicLift_add_wrap hsnd
  exact ⟨w₁, w₂, by simpa only [torusLift] using hw₁,
    by simpa only [torusLift] using hw₂⟩

/-- **The lifted three-term energy inequality.** If `q > 0`, the lifted real
points of residues `X, Y, Z` of the torus square lie in `torusT ε`, and
`X + Z = 2 • Y` in the product group, then the energy inequality of
`torusF_threeAP` holds. This is the raw consumer of the building block; the grid
membership is stated through the lift rather than the residue finset. -/
theorem torusLift_threeAP_energy {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ 1 / 6)
    {q : ℕ} [NeZero q] {X Y Z : ZMod q × ZMod q}
    (hX : torusT ε (torusLift q X)) (hY : torusT ε (torusLift q Y))
    (hZ : torusT ε (torusLift q Z)) (hAP : X + Z = 2 • Y) :
    2 * torusF ε (torusLift q Y)
        + ((torusLift q X).1 - (torusLift q Z).1) ^ 2
        + ((torusLift q X).2 - (torusLift q Z).2) ^ 2 ≤
      torusF ε (torusLift q X) + torusF ε (torusLift q Z) := by
  obtain ⟨w₁, w₂, hw₁, hw₂⟩ := torusLift_wrap hAP
  exact torusF_threeAP hε hεle hX hY hZ hw₁ hw₂

/-- **The modular-grid three-term energy inequality (finite grid).** If `q > 0`,
the residues `X, Y, Z` of the torus square lie in the `torusT ε` grid, and
`X + Z = 2 • Y` in the product group, then the corresponding lifted real points
satisfy the energy inequality of `torusF_threeAP`. -/
theorem torusGrid_threeAP_energy {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ 1 / 6)
    {q : ℕ} [NeZero q] {X Y Z : ZMod q × ZMod q}
    (hX : X ∈ torusGrid ε q) (hY : Y ∈ torusGrid ε q)
    (hZ : Z ∈ torusGrid ε q) (hAP : X + Z = 2 • Y) :
    2 * torusF ε (torusLift q Y)
        + ((torusLift q X).1 - (torusLift q Z).1) ^ 2
        + ((torusLift q X).2 - (torusLift q Z).2) ^ 2 ≤
      torusF ε (torusLift q X) + torusF ε (torusLift q Z) := by
  rw [mem_torusGrid] at hX hY hZ
  exact torusLift_threeAP_energy hε hεle hX hY hZ hAP

/-- Set-valued form of the modular-grid three-term energy inequality, stated
with an explicit positivity hypothesis `0 < q`. -/
theorem torusGridSet_threeAP_energy {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ 1 / 6)
    {q : ℕ} (hq : 0 < q) {X Y Z : ZMod q × ZMod q}
    (hX : X ∈ torusGridSet ε q) (hY : Y ∈ torusGridSet ε q)
    (hZ : Z ∈ torusGridSet ε q) (hAP : X + Z = 2 • Y) :
    2 * torusF ε (torusLift q Y)
        + ((torusLift q X).1 - (torusLift q Z).1) ^ 2
        + ((torusLift q X).2 - (torusLift q Z).2) ^ 2 ≤
      torusF ε (torusLift q X) + torusF ε (torusLift q Z) := by
  haveI : NeZero q := ⟨hq.ne'⟩
  exact torusLift_threeAP_energy hε hεle hX hY hZ hAP

/-- Variant of the finite-grid energy inequality with the progression written
as `X + Z = Y + Y`, the ungrouped form of `2 • Y`. -/
theorem torusGrid_threeAP_energy_addadd {ε : ℝ} (hε : 0 < ε)
    (hεle : ε ≤ 1 / 6) {q : ℕ} [NeZero q] {X Y Z : ZMod q × ZMod q}
    (hX : X ∈ torusGrid ε q) (hY : Y ∈ torusGrid ε q)
    (hZ : Z ∈ torusGrid ε q) (hAP : X + Z = Y + Y) :
    2 * torusF ε (torusLift q Y)
        + ((torusLift q X).1 - (torusLift q Z).1) ^ 2
        + ((torusLift q X).2 - (torusLift q Z).2) ^ 2 ≤
      torusF ε (torusLift q X) + torusF ε (torusLift q Z) :=
  torusGrid_threeAP_energy hε hεle hX hY hZ (by rw [two_smul]; exact hAP)

#check @torusGrid_threeAP_energy
#print axioms torusGrid_threeAP_energy
#print axioms torusGridSet_threeAP_energy
#print axioms torusLift_wrap
#print axioms val_add_wrap
#print axioms cyclicLift_add_wrap

end Erdos142