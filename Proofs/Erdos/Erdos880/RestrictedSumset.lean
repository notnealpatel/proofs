/-
  Erdős Problem #880 — restricted sumsets, the basic object.

  For h ≥ 1 and a set A, Hegyvári–Hennecart–Plagne [HHP07] write hA for
  the set of sums of h not-necessarily-distinct elements of A and h × A
  for the set of sums of h PAIRWISE DISTINCT elements of A ("restricted
  addition"; the same object is written A +̂ A in the Erdős–Heilbronn
  literature).  Mathlib has the unrestricted binary sumset as pointwise
  set addition `A + B`, but has no restricted sumset (checked against
  mathlib rev 11a4a72a, 2026-07-11), so this file defines the binary
  restricted sumset `A +ᵣ B` together with the small API needed by
  `Proofs.Erdos880.BurrErdos`:

    mem_restrictedSumset          membership unfolding (rfl)
    add_mem_restrictedSumset      introduction rule
    restrictedSumset_subset_add   A +ᵣ B ⊆ A + B
    restrictedSumset_mono         monotonicity in both arguments
    restrictedSumset_comm         commutativity (for commutative addition)

  The paper's 2 × A is `A +ᵣ A`.  The definition is kept in the ambient
  generality of a type with `Add` (the Erdős-880 application only uses
  `ℕ`), with the diagonal-distinctness convention a ≠ b — for `A = B`
  exactly "sums of two distinct elements of A".

  [HHP07] N. Hegyvári, F. Hennecart, A. Plagne, "Answer to a question by
  Burr and Erdős on restricted addition, and related results", Combin.
  Probab. Comput. 16 (2007), 747–756.  Local copy:
  References/Erdos-Burr/paper.txt (fetched from
  cmls.polytechnique.fr/perso/plagne/Erdos-Burr.pdf).
-/

import Mathlib.Algebra.Group.Pointwise.Set.Basic

namespace Erdos880

open Pointwise

variable {α : Type*}

/-- The *restricted sumset* of `A` and `B`: all sums `a + b` with `a ∈ A`,
    `b ∈ B` and `a ≠ b`.  For `A = B` this is the set of sums of two
    distinct elements of `A`, written `2 × A` by Hegyvári–Hennecart–Plagne
    and `A +̂ A` in the Erdős–Heilbronn literature. -/
def restrictedSumset [Add α] (A B : Set α) : Set α :=
  {n | ∃ a ∈ A, ∃ b ∈ B, a ≠ b ∧ a + b = n}

@[inherit_doc]
scoped infixl:65 " +ᵣ " => restrictedSumset

section Add

variable [Add α] {A A' B B' : Set α} {a b n : α}

/-- Membership in the restricted sumset, definitionally. -/
theorem mem_restrictedSumset :
    n ∈ A +ᵣ B ↔ ∃ a ∈ A, ∃ b ∈ B, a ≠ b ∧ a + b = n :=
  Iff.rfl

/-- Introduction rule: a sum of distinct elements lies in the restricted
    sumset. -/
theorem add_mem_restrictedSumset (ha : a ∈ A) (hb : b ∈ B) (hab : a ≠ b) :
    a + b ∈ A +ᵣ B :=
  ⟨a, ha, b, hb, hab, rfl⟩

/-- Dropping the distinctness constraint: the restricted sumset is
    contained in the (unrestricted, pointwise) sumset `A + B`. -/
theorem restrictedSumset_subset_add : A +ᵣ B ⊆ A + B := by
  rintro n ⟨a, ha, b, hb, -, rfl⟩
  exact Set.add_mem_add ha hb

/-- The restricted sumset is monotone in both arguments. -/
theorem restrictedSumset_mono (hA : A ⊆ A') (hB : B ⊆ B') :
    A +ᵣ B ⊆ A' +ᵣ B' := by
  rintro n ⟨a, ha, b, hb, hab, rfl⟩
  exact ⟨a, hA ha, b, hB hb, hab, rfl⟩

end Add

/-- For commutative addition the restricted sumset is symmetric in its
    arguments. -/
theorem restrictedSumset_comm [AddCommMagma α] (A B : Set α) :
    A +ᵣ B = B +ᵣ A := by
  ext n
  constructor <;> rintro ⟨a, ha, b, hb, hab, rfl⟩ <;>
    exact ⟨b, hb, a, ha, hab.symm, add_comm b a⟩

end Erdos880
