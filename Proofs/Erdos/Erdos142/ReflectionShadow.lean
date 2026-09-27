/-
  Erdős Problem #142 — the reflection shadow and difference-source cardinal bound.

  This file records two exact finite combinatorial facts used by the
  reflection-shadow route for Erdős Problem #142.  Nothing here is asymptotic:
  both statements are about an arbitrary finite set `A : Finset ℤ`.

  * `reflectionShadow A` is the nontrivial reflection of `A` across its own
    points: the values `2 * a - b` with `a, b ∈ A` and `a ≠ b`.  If `A` is
    three-term-arithmetic-progression-free then `A` and its shadow are disjoint,
    because `b + (2 * a - b) = a + a` is a forbidden progression.

  * `differenceSources A d` collects the left endpoints of the pairs at distance
    `d` in `A`.  For `d ≠ 0` and `A` progression-free, the sources and their
    `d`-translate are disjoint subsets of `A` of equal size, so twice the source
    count is at most `A.card`.
-/

import Mathlib.Combinatorics.Additive.AP.Three.Defs
import Mathlib.Tactic

set_option autoImplicit false

open Finset

namespace Erdos142

/-- The nontrivial reflection shadow of `A`: all values `2 * a - b` with
`a, b ∈ A` and `a ≠ b`.  Equivalently, `z` lies in the shadow exactly when
`b, a, z` is a three-term arithmetic progression with endpoints `b` and `z` and
midpoint `a`, for distinct `a, b`. -/
def reflectionShadow (A : Finset ℤ) : Finset ℤ :=
  ((A ×ˢ A).filter (fun p : ℤ × ℤ => p.1 ≠ p.2)).image (fun p => 2 * p.1 - p.2)

/-- Membership in the reflection shadow: `z = 2 * a - b` for distinct
`a, b ∈ A`. -/
theorem mem_reflectionShadow {A : Finset ℤ} {z : ℤ} :
    z ∈ reflectionShadow A ↔ ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ 2 * a - b = z := by
  simp [reflectionShadow, Finset.mem_image, Finset.mem_filter, Finset.mem_product, and_assoc]

/-- A three-term-arithmetic-progression-free finite set of integers is disjoint
from its nontrivial reflection shadow.  The decisive equation is
`b + (2 * a - b) = a + a`, which forces `b = a`, contradicting `a ≠ b`. -/
theorem disjoint_reflectionShadow {A : Finset ℤ} (hA : ThreeAPFree (A : Set ℤ)) :
    Disjoint A (reflectionShadow A) := by
  rw [Finset.disjoint_left]
  intro z hzA hzShadow
  obtain ⟨a, ha, b, hb, hab, haz⟩ := mem_reflectionShadow.1 hzShadow
  have hprog : b + z = a + a := by rw [← haz]; ring
  have hba : b = a := hA hb ha hzA hprog
  exact hab hba.symm

/-- The sources at distance `d` in `A`: the elements `x ∈ A` with `x + d ∈ A`.
These are the left endpoints of the `d`-separated pairs inside `A`. -/
def differenceSources (A : Finset ℤ) (d : ℤ) : Finset ℤ :=
  A.filter (fun x => x + d ∈ A)

/-- Membership in the set of difference sources. -/
theorem mem_differenceSources {A : Finset ℤ} {d x : ℤ} :
    x ∈ differenceSources A d ↔ x ∈ A ∧ x + d ∈ A := by
  simp [differenceSources]

/-- For a nonzero difference `d` and a three-term-arithmetic-progression-free
`A`, twice the number of sources at distance `d` is at most `A.card`.  The
sources and their `d`-translate are disjoint: a common element would give
`x, x + d, x + 2 * d ∈ A` with `x + (x + 2 * d) = (x + d) + (x + d)`, forcing
`x = x + d` and hence `d = 0`. -/
theorem two_mul_card_differenceSources_le {A : Finset ℤ} {d : ℤ} (hd : d ≠ 0)
    (hA : ThreeAPFree (A : Set ℤ)) :
    2 * (differenceSources A d).card ≤ A.card := by
  set S := differenceSources A d
  set E := S.image (fun x => x + d)
  have hEcard : E.card = S.card :=
    Finset.card_image_of_injective S (add_left_injective d)
  have hSsub : S ⊆ A := fun x hx => (mem_differenceSources.1 hx).1
  have hEsub : E ⊆ A := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨x, hxS, rfl⟩ := hy
    exact (mem_differenceSources.1 hxS).2
  have hdisj : Disjoint S E := by
    rw [Finset.disjoint_left]
    intro y hyS hyE
    rw [Finset.mem_image] at hyE
    obtain ⟨x, hxS, hxy⟩ := hyE
    have hxA : x ∈ A := (mem_differenceSources.1 hxS).1
    have hyA : y ∈ A := (mem_differenceSources.1 hyS).1
    have hydA : y + d ∈ A := (mem_differenceSources.1 hyS).2
    have hprog : x + (y + d) = y + y := by rw [← hxy]; ring
    have hxy_eq : x = y := hA hxA hyA hydA hprog
    have hd0 : d = 0 := by omega
    exact hd hd0
  have hUnion : S ∪ E ⊆ A := Finset.union_subset hSsub hEsub
  have hcard : (S ∪ E).card ≤ A.card := Finset.card_le_card hUnion
  rw [Finset.card_union_of_disjoint hdisj, hEcard] at hcard
  calc
    2 * S.card = S.card + S.card := by ring
    _ ≤ A.card := hcard

/-- The undoubled form of `two_mul_card_differenceSources_le`. -/
theorem card_differenceSources_le_half {A : Finset ℤ} {d : ℤ} (hd : d ≠ 0)
    (hA : ThreeAPFree (A : Set ℤ)) :
    (differenceSources A d).card ≤ A.card / 2 := by
  have h := two_mul_card_differenceSources_le hd hA
  omega

/-- Ground-truth check: the shadow of `{1, 3, 5}` is `{-3, -1, 1, 5, 7, 9}`. -/
example : reflectionShadow ({1, 3, 5} : Finset ℤ) = ({-3, -1, 1, 5, 7, 9} : Finset ℤ) := by
  decide

/-- Satisfiability of the disjointness hypothesis at a concrete progression-free
set. -/
example : ThreeAPFree (({0, 1, 3} : Finset ℤ) : Set ℤ) := by decide

/-- Satisfiability of the disjointness conclusion at a concrete progression-free
set. -/
example : Disjoint ({0, 1, 3} : Finset ℤ) (reflectionShadow ({0, 1, 3} : Finset ℤ)) :=
  disjoint_reflectionShadow (by decide)

/-- Satisfiability of the cardinal bound at a concrete progression-free set:
`{0, 1, 3}` has a single source at distance `1`, and `2 * 1 ≤ 3`. -/
example : 2 * (differenceSources ({0, 1, 3} : Finset ℤ) 1).card ≤
    ({0, 1, 3} : Finset ℤ).card :=
  two_mul_card_differenceSources_le (d := 1) (by norm_num) (by decide)

end Erdos142