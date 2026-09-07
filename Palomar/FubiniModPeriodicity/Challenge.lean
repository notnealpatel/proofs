import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Totient

/-!
# Eventual periodicity of the Fubini numbers modulo a positive modulus

This is the independent statement surface for the Palomar package. The Fubini
(ordered Bell) numbers are defined here literally by the binomial recurrence
`F 0 = 1` and `F (n + 1) = ∑ i ≤ n, C(n + 1, i) F i`.
-/

set_option autoImplicit false

open Finset BigOperators

namespace Palomar.FubiniModPeriodicity

/-- The Fubini (ordered Bell) numbers, defined by their binomial recurrence. -/
def fubini : ℕ → ℕ
  | 0 => 1
  | n + 1 => ∑ i : Fin (n + 1), (n + 1).choose i.val * fubini i.val
termination_by n => n
decreasing_by exact i.isLt

example : fubini 0 = 1 := by simp only [fubini]
example : fubini 1 = 1 := by simp [fubini]

/-- For every positive modulus, the Fubini numbers are eventually periodic
modulo that modulus with a strictly positive period dividing Euler's totient. -/
theorem fubini_mod_eventuallyPeriodic (k : ℕ) (hk : 1 ≤ k) :
    ∃ N P : ℕ, P ∣ Nat.totient k ∧ 0 < P ∧
      ∀ n : ℕ, N ≤ n → fubini (n + P) ≡ fubini n [MOD k] := by
  sorry

/-- The hypotheses and conclusion remain meaningful at the smallest allowed
modulus `k = 1`; in particular the period supplied by the theorem is positive. -/
example : ∃ N P : ℕ, P ∣ Nat.totient 1 ∧ 0 < P ∧
    ∀ n : ℕ, N ≤ n → fubini (n + P) ≡ fubini n [MOD 1] :=
  fubini_mod_eventuallyPeriodic 1 (by norm_num)

#check @Palomar.FubiniModPeriodicity.fubini_mod_eventuallyPeriodic

end Palomar.FubiniModPeriodicity
