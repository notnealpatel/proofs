/-
# √Δ-fine rings are fine

## Source

P. Danchev, O. Hasanzadeh, A. Moussavi, A. Javan, "√Δ-Fine Rings",
arXiv:2608.30734 (v2).  Problem `basic` (end of Section 4, "Group
Rings of √Δ-Fine and Generalized Fine Rings"), restated in Section 5
(Concluding Discussion) and in the Introduction.

Definitions (Introduction and Definition `def`, Section 2):

* `Δ(R)`: "an element `a ∈ R` belongs to `Δ(R)` exactly when `1 - ua`
  is a unit for every unit `u ∈ U(R)`."
* `√Δ(R)`: "all elements `x ∈ R` such that `x^n ∈ Δ(R)` for some
  `n ≥ 1`."
* A ring is *√Δ-fine* if every nonzero element can be written as a sum
  of a unit and an element of `√Δ(R)`; it is *fine* (Călugăreanu–Lam)
  if every nonzero element is a unit plus a nilpotent.

Verbatim problem (Problem `basic`):

> Is there a `√Δ`-fine ring which is *not* fine?

Section 5: "whether every `√Δ`-fine ring is necessarily fine remains an
open problem (Problem `basic`)".

## Status (2026-10-21)

Open in the paper.  This module answers it negatively: a ring is
`√Δ`-fine if and only if it is fine.  The argument is elementary:
in a `√Δ`-fine ring every element is a sum of units, so `Δ(R)` is a
two-sided ideal-like set (closed under addition and multiplication by
arbitrary elements on both sides, using Jacobson's lemma for right
multiplication); a nonzero `d ∈ Δ(R)` would give `d = u + a` with
`a^n ∈ Δ(R)`, whence `u^n ∈ Δ(R)`, `1 ∈ Δ(R)` and `R = 0`.  Hence
`Δ(R) = 0` and `√Δ(R) = Nil(R)`.

Computational sanity check (not proof): brute force on `ℤ/n`
(`2 ≤ n ≤ 40`), `𝔽₄`, `M₂(ℤ/4)`, `T₂(ℤ/4)`, `T₂(𝔽₅)`, `M₂(𝔽₅)`
agrees with the equivalence and with `Δ(R) = 0` for the `√Δ`-fine ones.
-/
import Mathlib

set_option autoImplicit false

universe u

namespace SqrtDeltaFineRings

open Finset

/-- `Δ(R)`: the elements `a` such that `1 - u * a` is a unit for every unit `u`
(Leroy–Matczuk; Introduction of arXiv:2608.30734). -/
def deltaSet (R : Type*) [Ring R] : Set R :=
  {a | ∀ u : Rˣ, IsUnit (1 - (u : R) * a)}

/-- `√Δ(R)`: the elements `x` with `x ^ n ∈ Δ(R)` for some `n ≥ 1`. -/
def sqrtDelta (R : Type*) [Ring R] : Set R :=
  {x | ∃ n : ℕ, 0 < n ∧ x ^ n ∈ deltaSet R}

/-- A ring is *fine* (Călugăreanu–Lam) if every nonzero element is a unit plus a
nilpotent. -/
def IsFineRing (R : Type*) [Ring R] : Prop :=
  ∀ r : R, r ≠ 0 → ∃ (u : Rˣ) (a : R), IsNilpotent a ∧ r = u + a

/-- A ring is *`√Δ`-fine* if every nonzero element is a unit plus an element of
`√Δ(R)` (Definition `def` of arXiv:2608.30734). -/
def IsSqrtDeltaFine (R : Type*) [Ring R] : Prop :=
  ∀ r : R, r ≠ 0 → ∃ (u : Rˣ), ∃ a ∈ sqrtDelta R, r = u + a

section Basic

variable {R : Type*} [Ring R]

/-- Jacobson's lemma: if `1 - x * y` is a unit then so is `1 - y * x`. -/
theorem isUnit_one_sub_mul_comm {x y : R} (h : IsUnit (1 - x * y)) :
    IsUnit (1 - y * x) := by
  obtain ⟨v, hv⟩ := h
  have hr : (1 - x * y) * (v⁻¹ : Rˣ) = 1 := by rw [← hv, Units.mul_inv]
  have hl : ((v⁻¹ : Rˣ) : R) * (1 - x * y) = 1 := by rw [← hv, Units.inv_mul]
  set c : R := ((v⁻¹ : Rˣ) : R)
  refine ⟨⟨1 - y * x, 1 + y * c * x, ?_, ?_⟩, rfl⟩
  · calc (1 - y * x) * (1 + y * c * x) = 1 - y * x + y * ((1 - x * y) * c) * x := by
          noncomm_ring
      _ = 1 := by rw [hr]; noncomm_ring
  · calc (1 + y * c * x) * (1 - y * x) = 1 - y * x + y * (c * (1 - x * y)) * x := by
          noncomm_ring
      _ = 1 := by rw [hl]; noncomm_ring

/-- `0 ∈ Δ(R)`. -/
theorem zero_mem_deltaSet : (0 : R) ∈ deltaSet R := by
  intro u
  simp

/-- `Δ(R)` is closed under addition. -/
theorem add_mem_deltaSet {a b : R} (ha : a ∈ deltaSet R) (hb : b ∈ deltaSet R) :
    a + b ∈ deltaSet R := by
  intro u
  obtain ⟨v, hv⟩ := ha u
  have hvb := hb (v⁻¹ * u)
  have heq : (1 - (u : R) * (a + b)) = (v : R) * (1 - ((v⁻¹ * u : Rˣ) : R) * b) := by
    rw [Units.val_mul, mul_sub, ← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul, mul_one,
      hv]
    noncomm_ring
  rw [heq]
  exact v.isUnit.mul hvb

/-- `Δ(R)` is closed under negation. -/
theorem neg_mem_deltaSet {a : R} (ha : a ∈ deltaSet R) : -a ∈ deltaSet R := by
  intro u
  have h := ha (-u)
  rwa [Units.val_neg, neg_mul, ← mul_neg] at h

/-- `Δ(R)` is closed under left multiplication by units. -/
theorem unit_mul_mem_deltaSet (v : Rˣ) {a : R} (ha : a ∈ deltaSet R) :
    (v : R) * a ∈ deltaSet R := by
  intro u
  have h := ha (u * v)
  rwa [Units.val_mul, mul_assoc] at h

/-- `Δ(R)` is closed under right multiplication by units (via Jacobson's lemma). -/
theorem mul_unit_mem_deltaSet (v : Rˣ) {a : R} (ha : a ∈ deltaSet R) :
    a * v ∈ deltaSet R := by
  intro u
  have h : IsUnit (1 - (v : R) * ((u : R) * a)) := by
    have h' := ha (v * u)
    rwa [Units.val_mul, mul_assoc] at h'
  have h2 := isUnit_one_sub_mul_comm h
  rwa [mul_assoc] at h2

/-- Nilpotent elements lie in `√Δ(R)`. -/
theorem mem_sqrtDelta_of_isNilpotent {a : R} (ha : IsNilpotent a) : a ∈ sqrtDelta R := by
  obtain ⟨n, hn⟩ := ha
  refine ⟨n + 1, Nat.succ_pos n, ?_⟩
  rw [pow_succ, hn, zero_mul]
  exact zero_mem_deltaSet

/-- If `a ∈ √Δ(R)` then `1 + a` is a unit. -/
theorem isUnit_one_add_of_mem_sqrtDelta {a : R} (ha : a ∈ sqrtDelta R) : IsUnit (1 + a) := by
  obtain ⟨n, -, hn⟩ := ha
  set s : R := ∑ i ∈ range n, (-a) ^ i
  have hgeom : (1 + a) * s = 1 - ((-1 : Rˣ) ^ n : Rˣ) * a ^ n := by
    have h := mul_neg_geom_sum (-a) n
    rw [sub_neg_eq_add, neg_pow] at h
    rw [h, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
  have hcomm : Commute (1 + a) s :=
    (Commute.one_left s).add_left
      (Commute.sum_right _ _ _ fun i _ => ((Commute.refl a).neg_right).pow_right i)
  have hunit : IsUnit ((1 + a) * s) := by
    rw [hgeom]
    exact hn _
  exact (hcomm.isUnit_mul_iff.mp hunit).1

end Basic

section Fine

variable {R : Type*} [Ring R]

/-- In a `√Δ`-fine ring, left and right multiplication by any element preserve `Δ(R)`:
every element is `0`, or `u + (1 + a) + (-1)`, a sum of three units. -/
theorem mul_mem_deltaSet_of_isSqrtDeltaFine (hR : IsSqrtDeltaFine R) (r : R) {d : R}
    (hd : d ∈ deltaSet R) : r * d ∈ deltaSet R ∧ d * r ∈ deltaSet R := by
  by_cases hr : r = 0
  · subst hr
    simp only [zero_mul, mul_zero, and_self]
    exact zero_mem_deltaSet
  obtain ⟨u, a, ha, hra⟩ := hR r hr
  obtain ⟨w, hw⟩ := isUnit_one_add_of_mem_sqrtDelta ha
  have hsum : r = (u : R) + (w : R) + ((-1 : Rˣ) : R) := by
    rw [hra, hw, Units.val_neg, Units.val_one]
    abel
  constructor
  · rw [hsum, add_mul, add_mul]
    exact add_mem_deltaSet (add_mem_deltaSet (unit_mul_mem_deltaSet u hd)
      (unit_mul_mem_deltaSet w hd)) (unit_mul_mem_deltaSet _ hd)
  · rw [hsum, mul_add, mul_add]
    exact add_mem_deltaSet (add_mem_deltaSet (mul_unit_mem_deltaSet u hd)
      (mul_unit_mem_deltaSet w hd)) (mul_unit_mem_deltaSet _ hd)

/-- In a `√Δ`-fine ring, `Δ(R) = {0}`. -/
theorem deltaSet_eq_singleton_zero_of_isSqrtDeltaFine (hR : IsSqrtDeltaFine R) :
    deltaSet R = {0} := by
  ext d
  simp only [Set.mem_singleton_iff]
  refine ⟨fun hd => ?_, fun hd => hd ▸ zero_mem_deltaSet⟩
  by_contra hd0
  obtain ⟨u, a, ⟨n, -, hn⟩, hda⟩ := hR d hd0
  -- `(d - a) ^ k - (-a) ^ k ∈ Δ(R)` for every `k`.
  have hind : ∀ k : ℕ, (d - a) ^ k - (-a) ^ k ∈ deltaSet R := by
    intro k
    induction k with
    | zero =>
      rw [pow_zero, pow_zero, sub_self]
      exact zero_mem_deltaSet
    | succ k ih =>
      have heq : (d - a) ^ (k + 1) - (-a) ^ (k + 1)
          = ((d - a) ^ k - (-a) ^ k) * (d - a) + (-a) ^ k * d := by
        rw [pow_succ, pow_succ]
        noncomm_ring
      rw [heq]
      exact add_mem_deltaSet (mul_mem_deltaSet_of_isSqrtDeltaFine hR _ ih).2
        (mul_mem_deltaSet_of_isSqrtDeltaFine hR _ hd).1
  have hneg : (-a) ^ n ∈ deltaSet R := by
    rw [neg_pow]
    have h := unit_mul_mem_deltaSet ((-1 : Rˣ) ^ n) hn
    rwa [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one] at h
  have hu : (d - a) = (u : R) := by rw [hda]; abel
  have hun : (u : R) ^ n ∈ deltaSet R := by
    have h := add_mem_deltaSet (hind n) hneg
    rwa [sub_add_cancel, hu] at h
  have hone : (1 : R) ∈ deltaSet R := by
    have h := unit_mul_mem_deltaSet (u ^ n)⁻¹ hun
    rwa [← Units.val_pow_eq_pow_val, Units.inv_mul] at h
  have hzero : IsUnit (0 : R) := by
    have h := hone 1
    rwa [Units.val_one, mul_one, sub_self] at h
  apply hd0
  rw [← mul_one d, ← isUnit_zero_iff.mp hzero, mul_zero]

/-- In a `√Δ`-fine ring, `√Δ(R)` is exactly the set of nilpotent elements. -/
theorem sqrtDelta_eq_setOf_isNilpotent_of_isSqrtDeltaFine (hR : IsSqrtDeltaFine R) :
    sqrtDelta R = {x | IsNilpotent x} := by
  ext x
  refine ⟨fun hx => ?_, fun hx => mem_sqrtDelta_of_isNilpotent hx⟩
  obtain ⟨n, -, hn⟩ := hx
  rw [deltaSet_eq_singleton_zero_of_isSqrtDeltaFine hR, Set.mem_singleton_iff] at hn
  exact ⟨n, hn⟩

/-- **Answer to Problem `basic` of arXiv:2608.30734.**  A ring is `√Δ`-fine if and only
if it is fine (every nonzero element is a unit plus a nilpotent). -/
theorem isSqrtDeltaFine_iff_isFineRing (R : Type*) [Ring R] :
    IsSqrtDeltaFine R ↔ IsFineRing R := by
  constructor
  · intro hR r hr
    obtain ⟨u, a, ha, hra⟩ := hR r hr
    rw [sqrtDelta_eq_setOf_isNilpotent_of_isSqrtDeltaFine hR] at ha
    exact ⟨u, a, ha, hra⟩
  · intro hR r hr
    obtain ⟨u, a, ha, hra⟩ := hR r hr
    exact ⟨u, a, mem_sqrtDelta_of_isNilpotent ha, hra⟩

/-- **Problem `basic` of arXiv:2608.30734, answered negatively.**  There is no ring
that is `√Δ`-fine but not fine. -/
theorem not_exists_isSqrtDeltaFine_and_not_isFineRing :
    ¬ ∃ (R : Type u) (_ : Ring R), IsSqrtDeltaFine R ∧ ¬ IsFineRing R := by
  rintro ⟨R, _, hR, hnot⟩
  exact hnot ((isSqrtDeltaFine_iff_isFineRing R).mp hR)

end Fine

section Examples

/-- Ground truth: `Δ(ℤ/4) = {0, 2}` (it equals the Jacobson radical `2ℤ/4`). -/
example : deltaSet (ZMod 4) = {0, 2} := by
  ext x
  simp only [deltaSet, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  revert x
  decide

/-- Ground truth: `2 ∈ √Δ(ℤ/4)` (it is nilpotent), while `1 ∉ √Δ(ℤ/4)`. -/
example : (2 : ZMod 4) ∈ sqrtDelta (ZMod 4) ∧ (1 : ZMod 4) ∉ sqrtDelta (ZMod 4) := by
  refine ⟨mem_sqrtDelta_of_isNilpotent ⟨2, by decide⟩, ?_⟩
  rintro ⟨n, -, hn⟩
  have h := hn 1
  rw [one_pow, Units.val_one, mul_one, sub_self] at h
  exact absurd h (by decide)

/-- Ground truth: `ℤ/4` is not fine, since `2` is not a unit plus a nilpotent. -/
example : ¬ IsFineRing (ZMod 4) := by
  intro h
  obtain ⟨u, a, ha, h2⟩ := h 2 (by decide)
  have hunit : IsUnit ((u : ZMod 4) + a) :=
    ha.isUnit_add_left_of_commute u.isUnit (Commute.all a u)
  rw [← h2] at hunit
  exact absurd hunit (by decide)

/-- Non-vacuity: the field `ℤ/3` is `√Δ`-fine (every nonzero element is a unit plus `0`),
so the hypothesis of the main theorems is satisfiable. -/
example : IsSqrtDeltaFine (ZMod 3) := by
  intro r hr
  exact ⟨Units.mk0 r hr, 0, mem_sqrtDelta_of_isNilpotent IsNilpotent.zero, by simp⟩

end Examples

end SqrtDeltaFineRings
