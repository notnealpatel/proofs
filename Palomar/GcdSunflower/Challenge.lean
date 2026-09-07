import Mathlib.Algebra.IsPrimePow
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.AlmostPrime

/-!
# Gcd sunflower bound on an almost-prime layer

This is an independent statement surface for the classical reduction from
equal-pairwise-gcd patterns to sunflowers. `Nat.IsAlmostPrime k a` means that
`a ≠ 0` and that `a` has exactly `k` prime factors counted with multiplicity.
The theorem below concerns only one such uniform layer; it does not estimate
Erdős Problem #535 and does not assert a bound of the form `c_r ^ k`.
-/

set_option autoImplicit false

open scoped Nat

namespace Palomar.GcdSunflower

/-- Every two unordered pairs of distinct members of `S` have the same gcd. -/
def EqualPairwiseGcd (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
    a ≠ b → c ≠ d → Nat.gcd a b = Nat.gcd c d

/-- Equal-pairwise-gcd is decidable on a finite set of natural numbers. -/
instance decidableEqualPairwiseGcd (S : Finset ℕ) : Decidable (EqualPairwiseGcd S) := by
  unfold EqualPairwiseGcd
  infer_instance

/-- No `r`-element subset of `A` has equal pairwise gcd. -/
def GcdPatternFree (r : ℕ) (A : Finset ℕ) : Prop :=
  ∀ S ∈ A.powersetCard r, ¬ EqualPairwiseGcd S

/-- Pattern-freeness is decidable for a finite set of natural numbers. -/
instance decidableGcdPatternFree (r : ℕ) (A : Finset ℕ) : Decidable (GcdPatternFree r A) := by
  unfold GcdPatternFree
  infer_instance

/-- The prime-power divisibility layers of `a`, truncated to the finite ground
set `Fin (N + 1)`. -/
def layerSet (N a : ℕ) : Finset (Fin (N + 1)) :=
  {q ∈ Finset.univ | IsPrimePow (q : ℕ) ∧ (q : ℕ) ∣ a}

example : EqualPairwiseGcd ({2, 3, 5} : Finset ℕ) := by decide
example : ¬ EqualPairwiseGcd ({4, 6, 9} : Finset ℕ) := by decide
example : GcdPatternFree 3 ({2, 4, 3} : Finset ℕ) := by decide
example : ¬ GcdPatternFree 3 ({2, 3, 5} : Finset ℕ) := by decide
example : (⟨2, by omega⟩ : Fin 7) ∈ layerSet 6 6 := by decide

-- A nonempty model jointly satisfies every hypothesis at `r = 2`, `k = 1`.
example :
    2 ≤ 2 ∧
      (∀ a ∈ ({2} : Finset ℕ), Nat.IsAlmostPrime 1 a) ∧
      GcdPatternFree 2 ({2} : Finset ℕ) ∧
      ({2} : Finset ℕ).card ≤ (2 - 1) ^ 1 * 1 ! := by
  refine ⟨by decide, ?_, by decide, by decide⟩
  intro a ha
  simp only [Finset.mem_singleton] at ha
  subst a
  exact Nat.prime_two.isAlmostPrime_one

/-- If `r ≥ 2` and every member of `A` has exactly `k` prime factors counted
with multiplicity, then avoiding `r` distinct elements with equal pairwise gcd
forces `A.card ≤ (r - 1) ^ k * k !`. -/
theorem card_le_of_isAlmostPrime {r k : ℕ} (hr : 2 ≤ r) {A : Finset ℕ}
    (hA : ∀ a ∈ A, Nat.IsAlmostPrime k a) (hfree : GcdPatternFree r A) :
    A.card ≤ (r - 1) ^ k * k ! := by
  sorry

#check @Palomar.GcdSunflower.EqualPairwiseGcd
#check @Palomar.GcdSunflower.GcdPatternFree
#check @Palomar.GcdSunflower.layerSet
#check @Palomar.GcdSunflower.card_le_of_isAlmostPrime

end Palomar.GcdSunflower
