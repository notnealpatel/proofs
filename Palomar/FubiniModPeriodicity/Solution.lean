import Enumerative.FubiniMod

/-!
# Eventual periodicity of the Fubini numbers modulo a positive modulus

This module repeats the independent declarations from
`Palomar.FubiniModPeriodicity.Challenge` without importing that module. It
bridges the literal recurrence below to `A051293.fubini`, then transports the
Fubini-specific periodicity theorem proved in `Enumerative.FubiniMod`.
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

private theorem fubini_succ_eq_sum_range (n : ℕ) :
    fubini (n + 1) =
      ∑ i ∈ Finset.range (n + 1), (n + 1).choose i * fubini i := by
  conv_lhs => unfold fubini
  exact Fin.sum_univ_eq_sum_range
    (fun i => (n + 1).choose i * fubini i) (n + 1)

private theorem fubini_eq_project_fubini (n : ℕ) :
    fubini n = A051293.fubini n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp only [fubini, A051293.fubini_zero]
      | succ n =>
          rw [fubini_succ_eq_sum_range,
            A051293.fubini_succ_eq_sum_range]
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [ih i (Finset.mem_range.mp hi)]

/-- For every positive modulus, the Fubini numbers are eventually periodic
modulo that modulus with a strictly positive period dividing Euler's totient. -/
theorem fubini_mod_eventuallyPeriodic (k : ℕ) (hk : 1 ≤ k) :
    ∃ N P : ℕ, P ∣ Nat.totient k ∧ 0 < P ∧
      ∀ n : ℕ, N ≤ n → fubini (n + P) ≡ fubini n [MOD k] := by
  obtain ⟨N, P, hP_dvd, hP_pos, hperiod⟩ :=
    A000670.fubini_mod_eventuallyPeriodic_conjecture k hk
  refine ⟨N, P, hP_dvd, hP_pos, fun n hn => ?_⟩
  simpa only [fubini_eq_project_fubini] using hperiod n hn

/-- The hypotheses and conclusion remain meaningful at the smallest allowed
modulus `k = 1`; in particular the period supplied by the theorem is positive. -/
example : ∃ N P : ℕ, P ∣ Nat.totient 1 ∧ 0 < P ∧
    ∀ n : ℕ, N ≤ n → fubini (n + P) ≡ fubini n [MOD 1] :=
  fubini_mod_eventuallyPeriodic 1 (by norm_num)

#check @Palomar.FubiniModPeriodicity.fubini_mod_eventuallyPeriodic
#print axioms Palomar.FubiniModPeriodicity.fubini_mod_eventuallyPeriodic

end Palomar.FubiniModPeriodicity
