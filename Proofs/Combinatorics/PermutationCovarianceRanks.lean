import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace PermutationCovarianceRanks

/-- The first and last adjacent pairs have equal strict comparison signs. -/
def E2 (p : Equiv.Perm (Fin 6)) : Prop :=
  (p 0 < p 1) ↔ (p 4 < p 5)

/-- The triples in positions `(0,1,2)` and `(3,4,5)` have identical strict orders. -/
def E3 (p : Equiv.Perm (Fin 6)) : Prop :=
  ∀ i j : Fin 3,
    p ⟨i.val, by omega⟩ < p ⟨j.val, by omega⟩ ↔
      p ⟨i.val + 3, by omega⟩ < p ⟨j.val + 3, by omega⟩

/-- A six-label permutation avoids both forbidden order events. -/
def Accepted (p : Equiv.Perm (Fin 6)) : Prop := ¬ E2 p ∧ ¬ E3 p

instance (p : Equiv.Perm (Fin 6)) : Decidable (E2 p) := inferInstanceAs (Decidable (_ ↔ _))
instance (p : Equiv.Perm (Fin 6)) : Decidable (E3 p) :=
  inferInstanceAs (Decidable (∀ i j : Fin 3,
    p ⟨i.val, by omega⟩ < p ⟨j.val, by omega⟩ ↔
      p ⟨i.val + 3, by omega⟩ < p ⟨j.val + 3, by omega⟩))
instance (p : Equiv.Perm (Fin 6)) : Decidable (Accepted p) :=
  inferInstanceAs (Decidable (¬ E2 p ∧ ¬ E3 p))

/-- One-based rank of the label at position zero. -/
def endpointA (p : Equiv.Perm (Fin 6)) : ℕ := (p 0).val + 1

/-- One-based rank of the label at position five. -/
def endpointB (p : Equiv.Perm (Fin 6)) : ℕ := (p 5).val + 1

example : E2 (Equiv.refl (Fin 6)) := by decide
example : E3 (Equiv.refl (Fin 6)) := by decide
example : endpointA (Equiv.refl (Fin 6)) = 1 := rfl
example : endpointB (Equiv.refl (Fin 6)) = 6 := rfl
example : Accepted (Equiv.swap (0 : Fin 6) 1) := by decide

section Kernel

local instance : Fintype (Equiv.Perm (Fin 6)) := fintypePerm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- Exactly 280 actual permutations of six positions avoid both events. -/
theorem accepted_count_kernel : (Finset.univ.filter Accepted).card = 280 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- The centered endpoint-rank product sums to 1264 over the actual accepted permutations. -/
theorem accepted_signed_sum_kernel :
    (∑ p ∈ Finset.univ.filter Accepted,
      (2 * (endpointA p : ℤ) - 7) * (2 * (endpointB p : ℤ) - 7)) = 1264 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- The minimum/complementary-maximum endpoint weight sums to 1392. -/
theorem accepted_minmax_sum_kernel :
    (∑ p ∈ Finset.univ.filter Accepted,
      (min (endpointA p) (endpointB p) : ℤ) *
        (7 - (max (endpointA p) (endpointB p) : ℤ))) = 1392 := by
  decide

end Kernel

private theorem canonical_univ_eq :
    (Finset.univ : Finset (Equiv.Perm (Fin 6))) = @Finset.univ _ fintypePerm := by
  ext p
  simp only [Finset.mem_univ]

/-- Exactly 280 actual permutations avoid both forbidden events, with the canonical finite instance. -/
theorem accepted_count : (Finset.univ.filter Accepted).card = 280 := by
  rw [canonical_univ_eq]
  exact accepted_count_kernel

/-- The centered rank product sums to 1264, with the canonical finite instance. -/
theorem accepted_signed_sum :
    (∑ p ∈ Finset.univ.filter Accepted,
      (2 * (endpointA p : ℤ) - 7) * (2 * (endpointB p : ℤ) - 7)) = 1264 := by
  rw [canonical_univ_eq]
  exact accepted_signed_sum_kernel

/-- The minimum/complementary-maximum weight sums to 1392, with the canonical finite instance. -/
theorem accepted_minmax_sum :
    (∑ p ∈ Finset.univ.filter Accepted,
      (min (endpointA p) (endpointB p) : ℤ) *
        (7 - (max (endpointA p) (endpointB p) : ℤ))) = 1392 := by
  rw [canonical_univ_eq]
  exact accepted_minmax_sum_kernel

end PermutationCovarianceRanks
