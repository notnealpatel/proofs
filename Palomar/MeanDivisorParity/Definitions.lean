import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.ModEq

/-!
# Definitions for mean-divisor subset parity

This module contains the declarations shared byte-for-byte by the challenge and
solution modules.
-/

set_option autoImplicit false

open Finset

namespace Palomar.MeanDivisorParity

/-- `IsMeanDiv n S` says that `S` has an integer mean which divides `n`. -/
def IsMeanDiv (n : ℕ) (S : Finset ℕ) : Prop :=
  ∃ m, S.sum id = m * S.card ∧ m ∣ n

private lemma isMeanDiv_iff_bounded (n : ℕ) (S : Finset ℕ) :
    (∃ m ∈ Finset.range (n + S.sum id + 1), S.sum id = m * S.card ∧ m ∣ n) ↔
      IsMeanDiv n S := by
  constructor
  · rintro ⟨m, -, hm⟩
    exact ⟨m, hm⟩
  · rintro ⟨m, hsum, hdvd⟩
    rcases Nat.eq_zero_or_pos S.card with hc | hc
    · refine ⟨n, Finset.mem_range.mpr (by omega), ?_, dvd_rfl⟩
      rw [hc, Nat.mul_zero]
      rw [hc, Nat.mul_zero] at hsum
      exact hsum
    · have hle : m ≤ S.sum id := by
        rw [hsum]
        exact Nat.le_mul_of_pos_right m hc
      exact ⟨m, Finset.mem_range.mpr (by omega), hsum, hdvd⟩

/-- The mean-divisor predicate is decidable by bounding its mean witness. -/
instance (n : ℕ) (S : Finset ℕ) : Decidable (IsMeanDiv n S) :=
  decidable_of_iff _ (isMeanDiv_iff_bounded n S)

/-- The nonempty subsets of `{1, ..., n}` having an integer mean dividing `n`. -/
def meanDivSubsets (n : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 n).powerset.filter fun S => S.Nonempty ∧ IsMeanDiv n S

/-- The number of nonempty subsets of `{1, ..., n}` having integer mean dividing `n`. -/
def a (n : ℕ) : ℕ := (meanDivSubsets n).card

example : IsMeanDiv 4 {1, 3} := ⟨2, by decide, by decide⟩
example : a 0 = 0 := by decide
example : a 1 = 1 := by decide
example : a 4 = 5 := by decide
example : meanDivSubsets 4 = {{1}, {2}, {4}, {1, 3}, {1, 2, 3}} := by decide

end Palomar.MeanDivisorParity
