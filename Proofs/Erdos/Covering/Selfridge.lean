/-
  Selfridge's `p - 1` covering system adjacent to Erdős problem 273.

  Erdős problem 273 asks for a covering system with distinct moduli of
  the form `p - 1` for primes `p ≥ 5`.  That existence question remains
  open.  Selfridge found the nearby sharp certificate when `p = 3` is
  allowed.  The twelve moduli below are divisors of 360.

  The residue choices were independently recovered by an exact integer
  linear-programming search over all residue classes for the twelve
  moduli.  The proof below does not trust that search: kernel `decide`
  checks all 360 residues through `isCoveringSystem_iff`.
-/

import Mathlib
import Erdos.Covering.Basic

set_option autoImplicit false

namespace Erdos.Covering

/-- Every modulus occurring in `S` is one less than a prime at least `P`. -/
def ModuliOfPrimeMinusOne (P : ℕ) (S : Finset (ℕ × ℕ)) : Prop :=
  ∀ q ∈ S, ∃ p : ℕ, p.Prime ∧ P ≤ p ∧ q.2 = p - 1

-- Ground checks for the prime-minus-one predicate, including a negative case.
example : ModuliOfPrimeMinusOne 3 ({(0, 2), (1, 4)} : Finset (ℕ × ℕ)) := by
  intro q hq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl
  · exact ⟨3, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, by norm_num, by norm_num, by norm_num⟩

example : ¬ ModuliOfPrimeMinusOne 3 ({(0, 8)} : Finset (ℕ × ℕ)) := by
  intro h
  obtain ⟨p, hp, _hp3, hp8⟩ := h (0, 8) (by simp)
  have : p = 9 := by omega
  subst p
  norm_num at hp

/-- Selfridge's twelve residue classes, with distinct moduli among the
    divisors of 360 that are one less than a prime. -/
def selfridgeSystem : Finset (ℕ × ℕ) :=
  {(0, 2), (1, 4), (1, 6), (5, 10), (3, 12), (11, 18),
    (11, 30), (35, 36), (3, 40), (59, 60), (23, 72), (167, 180)}

-- Ground checks for the explicit data.
example : selfridgeSystem.card = 12 := by decide
example : selfridgeSystem.image Prod.snd = {2, 4, 6, 10, 12, 18, 30, 36, 40, 60, 72, 180} := by
  decide
example : ((167, 180) : ℕ × ℕ) ∈ selfridgeSystem := by decide

set_option maxRecDepth 100000 in
/-- Selfridge's explicit classes form a covering system.  Coverage is
    checked on the common period 360; all moduli and distinctness are
    checked in the same finite kernel computation. -/
theorem isCoveringSystem_selfridgeSystem : IsCoveringSystem selfridgeSystem :=
  (isCoveringSystem_iff 360 (by decide) (by decide)).mpr (by decide)

/-- Every modulus in Selfridge's system is `p - 1` for a prime `p ≥ 3`. -/
theorem moduliOfPrimeMinusOne_selfridgeSystem :
    ModuliOfPrimeMinusOne 3 selfridgeSystem := by
  intro q hq
  simp only [selfridgeSystem, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨3, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨11, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨13, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨19, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨31, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨37, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨41, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨61, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨73, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨181, by norm_num, by norm_num, by norm_num⟩

/-- Allowing the prime 3, there exists a distinct-modulus covering system
    all of whose moduli are one less than a prime.  This is only the
    Selfridge `p = 3` certificate and does not settle Erdős problem 273,
    whose lower bound on the primes is 5. -/
theorem exists_primeMinusOne_coveringSystem_of_three :
    ∃ S : Finset (ℕ × ℕ), IsCoveringSystem S ∧ ModuliOfPrimeMinusOne 3 S :=
  ⟨selfridgeSystem, isCoveringSystem_selfridgeSystem,
    moduliOfPrimeMinusOne_selfridgeSystem⟩

#check @ModuliOfPrimeMinusOne
#check @isCoveringSystem_selfridgeSystem
#check @moduliOfPrimeMinusOne_selfridgeSystem
#check @exists_primeMinusOne_coveringSystem_of_three

#print axioms isCoveringSystem_selfridgeSystem
#print axioms moduliOfPrimeMinusOne_selfridgeSystem
#print axioms exists_primeMinusOne_coveringSystem_of_three

end Erdos.Covering
