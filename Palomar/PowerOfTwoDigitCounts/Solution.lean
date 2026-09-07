import Enumerative.PowerOfTwoDigitsCount

/-!
# Counting powers of two with ternary digits zero or one

This module repeats the challenge declarations without importing the challenge and
bridges them definitionally to the source development in
`Enumerative.PowerOfTwoDigitsCount`.
-/

set_option autoImplicit false

namespace Palomar.PowerOfTwoDigitCounts

/-- A natural number has only the ternary digits zero and one. -/
def TernaryZeroOne (m : ℕ) : Prop :=
  ∀ d ∈ Nat.digits 3 m, d ≤ 1

/-- The literal finite digit condition is decidable. -/
instance (m : ℕ) : Decidable (TernaryZeroOne m) := by
  unfold TernaryZeroOne
  infer_instance

/-- The number of exponents `n < N` for which the value `2 ^ n` has only ternary digits
zero and one. -/
def exponentCount (N : ℕ) : ℕ :=
  ((Finset.range N).filter fun n => TernaryZeroOne (2 ^ n)).card

/-- The low `D` ternary digits of `2 ^ n` are all zero or one. -/
def SieveAt (D n : ℕ) : Prop :=
  ∀ i < D, 2 ^ n / 3 ^ i % 3 ≤ 1

/-- The bounded low-digit condition is decidable. -/
instance (D n : ℕ) : Decidable (SieveAt D n) := by
  unfold SieveAt
  infer_instance

/-- The exponent residue classes modulo `2 * 3 ^ j` surviving the lowest `j + 1`
ternary-digit tests. -/
def sieveClasses (j : ℕ) : Finset ℕ :=
  (Finset.range (2 * 3 ^ j)).filter fun r => SieveAt (j + 1) r

example : TernaryZeroOne 1 := by decide
example : ¬ TernaryZeroOne 2 := by decide
example : TernaryZeroOne 4 := by decide
example : exponentCount 1 = 1 := by decide
example : exponentCount 3 = 2 := by decide
example : SieveAt 2 0 := by decide
example : sieveClasses 0 = {0} := by decide
example : sieveClasses 1 = {0, 2} := by decide

/-- At depth `j + 1`, exactly `2 ^ j` exponent classes modulo `2 * 3 ^ j` survive. -/
theorem card_sieveClasses (j : ℕ) :
    (sieveClasses j).card = 2 ^ j := by
  exact Erdos406.card_sieveClasses j

/-- For `1 ≤ N`, the number of exponents `n < N` whose value `2 ^ n` has only ternary
digits zero and one is at most `2 * N ^ (log base 3 of 2)`. This is the `λ = 1` case
of Lagarias (2009), Theorem 1.4, with the package's `n < N` boundary convention. -/
theorem card_erdos406_filter_le_rpow (N : ℕ) (hN : 1 ≤ N) :
    (exponentCount N : ℝ) ≤ 2 * (N : ℝ) ^ Real.logb 3 2 := by
  exact Erdos406.card_erdos406_filter_le_rpow N hN

example : (sieveClasses 3).card = 8 := by
  simpa using card_sieveClasses 3

example : (exponentCount 1 : ℝ) ≤ 2 * (1 : ℝ) ^ Real.logb 3 2 := by
  simpa using card_erdos406_filter_le_rpow 1 le_rfl

#check @card_sieveClasses
#check @card_erdos406_filter_le_rpow
#print axioms Palomar.PowerOfTwoDigitCounts.card_sieveClasses
#print axioms Palomar.PowerOfTwoDigitCounts.card_erdos406_filter_le_rpow

end Palomar.PowerOfTwoDigitCounts
