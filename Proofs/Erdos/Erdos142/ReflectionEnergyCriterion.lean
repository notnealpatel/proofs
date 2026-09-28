/-
  Erdős Problem #142 — the reflection energy criterion.

  `Erdos.Erdos142.ReflectionMassEnergy` supplies the two universal finite bounds
  behind the reflection route.  With `m = A.card`, `M = reflectionMass A L` the
  in-range reflection mass and `ν = reflectionMultiplicity A` the fixed-target
  multiplicity, those bounds are the mass bound `⌊(m-1)²/4⌋ ≤ M` and the energy
  bound `E := ∑_{c ∈ [0,L)} ν(c)² ≤ (m-1) * M`.

  This file records the *criterion* that turns them into a weighted energy
  inequality: if the cardinality condition

    `(m-1) * (m-N)² ≤ ((m-1)²/4) * F`

  holds for a weight `F : ℕ`, then

    `E * (m-N)² ≤ M² * F`.

  The proof multiplies the two universal bounds, `E ≤ (m-1) * M` and
  `⌊(m-1)²/4⌋ ≤ M`.  Every step is exact `ℕ` monotonicity: no division
  cancellation, no hypothesis `M > 0`, no hypothesis `m > N` and no
  arithmetic-progression-freeness is used or assumed.  The only hypothesis on `A`
  is `0 ≤ a < L` on its elements, inherited from the mass bound.

  The criterion's hypothesis is *derived* in the cardinality range `2 ≤ N`,
  `N < A.card`, `4 * A.card ≤ F`.  There `(m-N)² ≤ (m-1)² - 3`, and the
  elementary floor bound `(m-1)² - 3 ≤ 4 * ⌊(m-1)²/4⌋` yields the condition, so
  in that range the weighted energy inequality is unconditional.

  Scope.  This is a finite, conditional statement about one candidate step of the
  reflection route, with `F` in the role of the weight of that route's sufficient
  step `(O)`.  It verifies the candidate weighted energy inequality only in the
  cardinality range `4 * A.card ≤ F`; it does not prove the general step `(O)`,
  the candidate estimate `(C)`, or Erdős Problem #142, and it makes no claim that
  the criterion's hypothesis is necessary or sharp.
-/

import Erdos.Erdos142.ReflectionMassEnergy
import Mathlib.Tactic

set_option autoImplicit false

open Finset

namespace Erdos142

/-- **Reflection energy criterion.**  Let `A ⊆ [0,L)` be finite with `m = A.card`,
let `M` be its in-range reflection mass and let `E = ∑_{c ∈ [0,L)} ν(c)²` be the
energy of its fixed-target multiplicities.  If the cardinality condition
`(m-1) * (m-N)² ≤ (⌊(m-1)²/4⌋) * F` holds, then `E * (m-N)² ≤ M² * F`.

The proof multiplies the universal energy bound `E ≤ (m-1) * M` by `(m-N)²` and
the universal mass bound `⌊(m-1)²/4⌋ ≤ M` by `M * F`, so the condition supplies
exactly the missing factor.  This is a conditional criterion: the hypothesis is
not derived here, and no AP-freeness, positivity or nondegeneracy assumption is
used. -/
theorem sum_sq_mul_le_mass_sq_mul_of_card_condition (A : Finset ℤ) (L : ℤ) (N F : ℕ)
    (hA : ∀ a ∈ A, 0 ≤ a ∧ a < L)
    (hcond : (A.card - 1) * (A.card - N) ^ 2 ≤ ((A.card - 1) ^ 2 / 4) * F) :
    (∑ c ∈ Finset.Ico 0 L, (reflectionMultiplicity A c) ^ 2) * (A.card - N) ^ 2
      ≤ (reflectionMass A L) ^ 2 * F := by
  have hE : (∑ c ∈ Finset.Ico 0 L, (reflectionMultiplicity A c) ^ 2)
      ≤ (A.card - 1) * reflectionMass A L := sum_sq_multiplicity_le A L
  have hM : (A.card - 1) ^ 2 / 4 ≤ reflectionMass A L := card_le_reflectionMass A L hA
  calc (∑ c ∈ Finset.Ico 0 L, (reflectionMultiplicity A c) ^ 2) * (A.card - N) ^ 2
      ≤ ((A.card - 1) * reflectionMass A L) * (A.card - N) ^ 2 := Nat.mul_le_mul_right _ hE
    _ = reflectionMass A L * ((A.card - 1) * (A.card - N) ^ 2) := by ring
    _ ≤ reflectionMass A L * (((A.card - 1) ^ 2 / 4) * F) := Nat.mul_le_mul_left _ hcond
    _ = (reflectionMass A L * ((A.card - 1) ^ 2 / 4)) * F := by ring
    _ ≤ (reflectionMass A L * reflectionMass A L) * F :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hM)
    _ = reflectionMass A L ^ 2 * F := by ring

/-- **The cardinality condition in the range `4 * A.card ≤ F`.**  For a finite
`A : Finset ℤ` and naturals `N`, `F` with `2 ≤ N`, `N < A.card` and
`4 * A.card ≤ F`, the criterion's hypothesis holds:
`(m-1) * (m-N)² ≤ (⌊(m-1)²/4⌋) * F` for `m = A.card`.

Write `m = A.card ≥ 3`.  Since `N ≥ 2` we have `(m-N)² ≤ (m-2)²`, and
`(m-2)² + 3 ≤ (m-1)²`.  With `(m-1)² = 4 * ⌊(m-1)²/4⌋ + ((m-1)² mod 4)` and
`(m-1)² mod 4 ≤ 3`, this gives `(m-2)² ≤ 4 * ⌊(m-1)²/4⌋`; multiplying by
`m - 1 ≤ m` and then using `4 * m ≤ F` closes the chain.  The floor is handled by
`Nat.div_add_mod'`, so no division cancellation is used. -/
theorem card_condition_of_two_le_of_lt_card_of_four_mul_card_le (A : Finset ℤ) (N F : ℕ)
    (hN : 2 ≤ N) (hNm : N < A.card) (hF : 4 * A.card ≤ F) :
    (A.card - 1) * (A.card - N) ^ 2 ≤ ((A.card - 1) ^ 2 / 4) * F := by
  have hm3 : 3 ≤ A.card := by omega
  have hstep1 : (A.card - N) ^ 2 ≤ (A.card - 2) ^ 2 :=
    Nat.pow_le_pow_left (show A.card - N ≤ A.card - 2 by omega) 2
  have hstep2 : (A.card - 2) ^ 2 ≤ 4 * ((A.card - 1) ^ 2 / 4) := by
    have hsq : (A.card - 1) ^ 2 = (A.card - 2) ^ 2 + (2 * (A.card - 2) + 1) := by
      have hk : A.card - 1 = (A.card - 2) + 1 := by omega
      rw [hk]
      ring
    have hdiv := Nat.div_add_mod' ((A.card - 1) ^ 2) 4
    have hmod := Nat.mod_lt ((A.card - 1) ^ 2) (by norm_num : 0 < 4)
    omega
  calc (A.card - 1) * (A.card - N) ^ 2
      ≤ (A.card - 1) * (A.card - 2) ^ 2 := Nat.mul_le_mul_left _ hstep1
    _ ≤ (A.card - 1) * (4 * ((A.card - 1) ^ 2 / 4)) := Nat.mul_le_mul_left _ hstep2
    _ ≤ A.card * (4 * ((A.card - 1) ^ 2 / 4)) :=
        Nat.mul_le_mul_right _ (by omega : A.card - 1 ≤ A.card)
    _ = 4 * A.card * ((A.card - 1) ^ 2 / 4) := by ring
    _ ≤ F * ((A.card - 1) ^ 2 / 4) := Nat.mul_le_mul_right _ hF
    _ = ((A.card - 1) ^ 2 / 4) * F := by ring

/-- **Reflection energy criterion in the cardinality range `4 * A.card ≤ F`.**
Combining the criterion with the derived cardinality condition: for finite
`A ⊆ [0,L)` and naturals `N`, `F` with `2 ≤ N`, `N < A.card` and
`4 * A.card ≤ F`, the weighted energy inequality
`E * (m-N)² ≤ M² * F` holds with `m = A.card`, `M = reflectionMass A L` and
`E = ∑_{c ∈ [0,L)} ν(c)²`.

The bound `F ≥ 4 * A.card` is what restricts this to a cardinality range: it
says the weight `F` dominates four times the size of `A`. -/
theorem sum_sq_mul_le_mass_sq_mul_of_two_le_of_lt_card_of_four_mul_card_le
    (A : Finset ℤ) (L : ℤ) (N F : ℕ) (hA : ∀ a ∈ A, 0 ≤ a ∧ a < L)
    (hN : 2 ≤ N) (hNm : N < A.card) (hF : 4 * A.card ≤ F) :
    (∑ c ∈ Finset.Ico 0 L, (reflectionMultiplicity A c) ^ 2) * (A.card - N) ^ 2
      ≤ (reflectionMass A L) ^ 2 * F :=
  sum_sq_mul_le_mass_sq_mul_of_card_condition A L N F hA
    (card_condition_of_two_le_of_lt_card_of_four_mul_card_le A N F hN hNm hF)

/-! ## Ground truth and boundary audit

The examples below pin the criterion at a concrete `A ⊆ [0,L)`: they check that
the hypotheses of the criterion and of its cardinality-range corollary are
jointly satisfiable, that the criterion applies in a case where the corollary's
hypothesis `4 * A.card ≤ F` fails, and that the degenerate `N = A.card` case is
covered. -/

/-- The data of the audit: `A = {1,2,4,8}` inside `[0,9)` has `m = 4`, reflection
mass `M = 6` and energy `E = 12` (targets `0, 3, 6, 7` with multiplicities
`3, 1, 1, 1`). -/
example : reflectionMass ({1, 2, 4, 8} : Finset ℤ) 9 = 6 ∧
    (∑ c ∈ Finset.Ico (0 : ℤ) 9, (reflectionMultiplicity ({1, 2, 4, 8} : Finset ℤ) c) ^ 2)
      = 12 := by decide

/-- Joint satisfiability of every hypothesis of the cardinality-range criterion:
`A = {1,2,4,8}` inside `[0,9)`, `N = 2`, `F = 16 = 4 * 4`.  The conclusion reads
`E * 4 = 48 ≤ M² * 16 = 576`. -/
example : (∑ c ∈ Finset.Ico (0 : ℤ) 9, (reflectionMultiplicity ({1, 2, 4, 8} : Finset ℤ) c) ^ 2)
      * (4 - 2) ^ 2 ≤ (reflectionMass ({1, 2, 4, 8} : Finset ℤ) 9) ^ 2 * 16 :=
  sum_sq_mul_le_mass_sq_mul_of_two_le_of_lt_card_of_four_mul_card_le _
    9 2 16 (by decide) (by norm_num) (by decide) (by norm_num)

/-- The criterion is strictly more general than its cardinality-range corollary:
at `A = {1,2,4,8}` inside `[0,9)`, `N = 2` and `F = 6` the criterion's hypothesis
`(4-1) * (4-2)² = 12 ≤ 2 * 6 = 12` holds with equality, but the corollary's
hypothesis `4 * 4 ≤ 6` fails.  The conclusion `12 * 4 = 48 ≤ 36 * 6 = 216` is
still delivered by the criterion. -/
example : (∑ c ∈ Finset.Ico (0 : ℤ) 9, (reflectionMultiplicity ({1, 2, 4, 8} : Finset ℤ) c) ^ 2)
      * (4 - 2) ^ 2 ≤ (reflectionMass ({1, 2, 4, 8} : Finset ℤ) 9) ^ 2 * 6 :=
  sum_sq_mul_le_mass_sq_mul_of_card_condition _ 9 2 6 (by decide) (by norm_num)

/-- The degenerate `N = A.card` case: here `A.card - N = 0`, the criterion's
hypothesis is `(m-1) * 0 ≤ ⌊(m-1)²/4⌋ * F`, and the conclusion is `E * 0 ≤ M² * F`.
Both hold for every weight, including `F = 0`. -/
example : (∑ c ∈ Finset.Ico (0 : ℤ) 9, (reflectionMultiplicity ({1, 2, 4, 8} : Finset ℤ) c) ^ 2)
      * (4 - 4) ^ 2 ≤ (reflectionMass ({1, 2, 4, 8} : Finset ℤ) 9) ^ 2 * 0 :=
  sum_sq_mul_le_mass_sq_mul_of_card_condition _ 9 4 0 (by decide) (by norm_num)

end Erdos142
