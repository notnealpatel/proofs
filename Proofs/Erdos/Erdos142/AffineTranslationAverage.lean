/-
  Erdős Problem #142 — finite affine-translation averaging.

  Over a finite additive commutative group `G`, a direction `b : G`, a
  horizon `N : ℕ`, and a finite set `S : Finset G`, the *affine preimage* at
  translation `a` is the set of indices `n < N` whose translated point
  `a + n • b` lies in `S`.

  The exact double count below computes the total incidence of these
  preimages: summing `#(preimage a)` over every `a : G` counts the pairs
  `(a, n)` with `n < N` and `a + n • b ∈ S`.  For each fixed `n`, the map
  `a ↦ a + n • b` is a bijection of `G`, so exactly `#S` translations
  contribute; the total is therefore `N * #S`.

  The averaging/capacity consequence is the finite pigeonhole bound: if every
  affine preimage has at most `r` elements, then `N * #S ≤ #G * r`.  Its
  arithmetic-progression corollary takes `r` to be `rothNumberNat N` whenever
  every preimage is 3-AP-free.

  These are reusable finite counting statements.  They do not prove the
  asymptotic assertion of Erdős Problem #142.
-/

import Mathlib.Combinatorics.Additive.AP.Three.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit false

open Finset

namespace Erdos142

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The affine preimage of `S` at translation `a`: the indices `n < N` with
`a + n • b ∈ S`. -/
def affinePreimage (S : Finset G) (N : ℕ) (b : G) (a : G) : Finset ℕ :=
  (Finset.range N).filter fun n => a + n • b ∈ S

/-- Membership in the affine preimage unfolds to a range bound and the
translation incidence. -/
theorem mem_affinePreimage {S : Finset G} {N : ℕ} {b a : G} {n : ℕ} :
    n ∈ affinePreimage S N b a ↔ n < N ∧ a + n • b ∈ S := by
  rw [affinePreimage, mem_filter, mem_range]

/-- Every affine preimage is contained in `range N`. -/
theorem affinePreimage_subset_range (S : Finset G) (N : ℕ) (b a : G) :
    affinePreimage S N b a ⊆ Finset.range N := by
  intro n hn
  exact mem_range.mpr (mem_affinePreimage.mp hn).1

/-- The affine preimage as a boolean count: its cardinality is the number of
indices `n < N` at which `a + n • b` lands in `S`. -/
theorem card_affinePreimage (S : Finset G) (N : ℕ) (b a : G) :
    (affinePreimage S N b a).card =
      ∑ n ∈ Finset.range N, (if a + n • b ∈ S then 1 else 0) := by
  rw [affinePreimage, card_filter]

variable [Fintype G]

/-- Translating the index of summation by a fixed `c` does not change the
total number of translations landing in `S`. -/
theorem sum_ite_add_right_eq_card (S : Finset G) (c : G) :
    (∑ a : G, (if a + c ∈ S then 1 else 0)) = S.card := by
  classical
  have hshift :
      (∑ a : G, (if a + c ∈ S then 1 else 0)) =
        ∑ a : G, (if a ∈ S then 1 else 0) :=
    Equiv.sum_comp (Equiv.addRight c) fun x : G => if x ∈ S then 1 else 0
  rw [hshift, ← card_filter (fun a : G => a ∈ S) Finset.univ]
  congr 1
  ext a
  simp

/-- **Exact affine-translation double count.** Summing the cardinalities of
the affine preimages over all translations equals `N * #S`. -/
theorem sum_card_affinePreimage (S : Finset G) (N : ℕ) (b : G) :
    (∑ a : G, (affinePreimage S N b a).card) = N * S.card := by
  classical
  simp_rw [card_affinePreimage]
  rw [Finset.sum_comm]
  simp_rw [sum_ite_add_right_eq_card]
  simp [Finset.sum_const, Finset.card_range]

/-- **Averaging/capacity bound.** If every affine preimage has cardinality at
most `r`, then the total incidence `N * #S` is at most `#G * r`. -/
theorem mul_card_le_card_mul_of_affinePreimage_card_le
    (S : Finset G) (N r : ℕ) (b : G)
    (h : ∀ a : G, (affinePreimage S N b a).card ≤ r) :
    N * S.card ≤ Fintype.card G * r := by
  calc
    N * S.card = ∑ a : G, (affinePreimage S N b a).card :=
      (sum_card_affinePreimage S N b).symm
    _ ≤ ∑ _a : G, r := sum_le_sum fun a _ => h a
    _ = Fintype.card G * r := by
      simp [Finset.sum_const, Finset.card_univ]

/-- **3-AP-free corollary.** If every affine preimage is 3-AP-free, then the
capacity bound holds with `r = rothNumberNat N`.  Each preimage lies in
`range N`, so the Roth number of the horizon bounds its size. -/
theorem mul_card_le_card_mul_rothNumberNat_of_threeAPFree
    (S : Finset G) (N : ℕ) (b : G)
    (h : ∀ a : G, ThreeAPFree ((affinePreimage S N b a : Finset ℕ) : Set ℕ)) :
    N * S.card ≤ Fintype.card G * rothNumberNat N := by
  refine mul_card_le_card_mul_of_affinePreimage_card_le S N (rothNumberNat N) b ?_
  intro a
  refine ThreeAPFree.le_rothNumberNat (affinePreimage S N b a) (h a) ?_ rfl
  intro x hx
  exact mem_range.mp ((affinePreimage_subset_range S N b a) hx)

/-- Ground truth: the empty set has empty preimages, and the identity holds. -/
example :
    (∑ a : ZMod 3, (affinePreimage (∅ : Finset (ZMod 3)) 4 1 a).card) = 0 := by
  rw [sum_card_affinePreimage]
  simp

/-- Ground truth for the double count in `ZMod 3` with `S = {0,1}`, `N = 3`,
and direction `1`: every preimage has two elements and the total is `6`. -/
example :
    (∑ a : ZMod 3, (affinePreimage ({0, 1} : Finset (ZMod 3)) 3 1 a).card) = 6 := by
  rw [sum_card_affinePreimage]
  norm_num

/-- Joint satisfiability of the double-count identity and the capacity bound
at the tight example `G = ZMod 3`, `S = {0,1}`, `N = 3`, `r = 2`. -/
example :
    (∑ a : ZMod 3, (affinePreimage ({0, 1} : Finset (ZMod 3)) 3 1 a).card) = 6 ∧
      3 * ({0, 1} : Finset (ZMod 3)).card ≤ Fintype.card (ZMod 3) * 2 := by
  refine ⟨?_, ?_⟩
  · rw [sum_card_affinePreimage]; norm_num
  · refine mul_card_le_card_mul_of_affinePreimage_card_le
      ({0, 1} : Finset (ZMod 3)) 3 2 1 ?_
    intro a
    fin_cases a <;> decide

/-- Joint satisfiability of the 3-AP-free corollary hypotheses: in `ZMod 3`
with `S = {0,1}`, `N = 3`, and direction `1`, every preimage is 3-AP-free and
the Roth-number capacity bound holds tightly. -/
example :
    (∀ a : ZMod 3,
        ThreeAPFree ((affinePreimage ({0, 1} : Finset (ZMod 3)) 3 1 a : Finset ℕ) : Set ℕ)) ∧
      3 * ({0, 1} : Finset (ZMod 3)).card ≤
        Fintype.card (ZMod 3) * rothNumberNat 3 := by
  have hfree : ∀ a : ZMod 3,
      ThreeAPFree ((affinePreimage ({0, 1} : Finset (ZMod 3)) 3 1 a : Finset ℕ) : Set ℕ) := by
    intro a
    fin_cases a <;> decide
  exact ⟨hfree,
    mul_card_le_card_mul_rothNumberNat_of_threeAPFree
      ({0, 1} : Finset (ZMod 3)) 3 1 hfree⟩

#check @affinePreimage
#check @mem_affinePreimage
#check @card_affinePreimage
#check @sum_ite_add_right_eq_card
#check @sum_card_affinePreimage
#check @mul_card_le_card_mul_of_affinePreimage_card_le
#check @mul_card_le_card_mul_rothNumberNat_of_threeAPFree

#print axioms sum_card_affinePreimage
#print axioms mul_card_le_card_mul_of_affinePreimage_card_le
#print axioms mul_card_le_card_mul_rothNumberNat_of_threeAPFree

end Erdos142