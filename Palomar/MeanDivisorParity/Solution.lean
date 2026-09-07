import Enumerative.MeanDivisors

/-!
# Mean-divisor subset parity

This module repeats the literal definitions and selected statements from
`Palomar.MeanDivisorParity.Challenge` without importing that module.  The
proofs transport the declarations already established in
`Enumerative.MeanDivisors`.
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

private lemma meanDivSubsets_eq_source (n : ℕ) :
    meanDivSubsets n = A114976.meanDivSubsets n := by
  unfold meanDivSubsets A114976.meanDivSubsets
  apply Finset.filter_congr
  intro S hS
  rfl

private lemma a_eq_source (n : ℕ) : a n = A114976.a n := by
  rw [a, A114976.a, meanDivSubsets_eq_source]

example : IsMeanDiv 4 {1, 3} := ⟨2, by decide, by decide⟩
example : a 0 = 0 := by decide
example : a 1 = 1 := by decide
example : a 4 = 5 := by decide
example : meanDivSubsets 4 = {{1}, {2}, {4}, {1, 3}, {1, 2, 3}} := by decide

/-- The mean-divisor subset count is congruent modulo two to the divisor count. -/
theorem a_modEq_card_divisors (n : ℕ) : a n ≡ n.divisors.card [MOD 2] := by
  rw [a_eq_source]
  exact A114976.a_modEq_card_divisors n

/-- At a nonzero input, the mean-divisor subset count is odd exactly for a square. -/
theorem odd_a_iff_isSquare {n : ℕ} (hn : n ≠ 0) : Odd (a n) ↔ IsSquare n := by
  rw [a_eq_source]
  exact A114976.odd_a_iff_isSquare hn

/-- The mean-divisor subset count equals two exactly at prime inputs. -/
theorem a_eq_two_iff_prime (n : ℕ) : a n = 2 ↔ n.Prime := by
  rw [a_eq_source]
  exact A114976.a_eq_two_iff_prime n

example : a 6 % 2 = (Nat.divisors 6).card % 2 := by decide
example : Odd (a 4) ∧ IsSquare (4 : ℕ) := ⟨⟨2, by decide⟩, ⟨2, by decide⟩⟩
example : a 5 = 2 ∧ (5 : ℕ).Prime := ⟨by decide, by decide⟩

#check @a_modEq_card_divisors
#check @odd_a_iff_isSquare
#check @a_eq_two_iff_prime
#print axioms Palomar.MeanDivisorParity.a_modEq_card_divisors
#print axioms Palomar.MeanDivisorParity.odd_a_iff_isSquare
#print axioms Palomar.MeanDivisorParity.a_eq_two_iff_prime

end Palomar.MeanDivisorParity
