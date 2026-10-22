/-
# A004123: eventual periodicity modulo every positive integer

OEIS A004123, Peter Bala (Jul 08 2022); formula and recurrence by Vladeta
Jovovic (Mar 27 2003). The sum `Σ_m S₂(n,m) 2^m m!` is the integral
weighted-Stirling transform with weights `2^m`, so `φ(k)` is an eventual
period modulo every positive `k`.
This is a formula-level result, not a bijection with generalized weak orders.
-/
import Mathlib
import Enumerative.OrdinaryIntegralEGF

set_option autoImplicit false

open Finset

namespace Candidates.A004123BalaModEventually

/-! ## Definitions -/

/-- A004123, via the entry's formula `a(n) = Sum_{k=0..n} Stirling2(n,k) * 2^k * k!`
(the e.g.f. `1/(3 - 2 exp x)` expanded in `exp x - 1`). -/
def a (n : ℕ) : ℕ :=
  ∑ m ∈ range (n + 1), n.stirlingSecond m * 2 ^ m * m.factorial

/-- Example: the first eight terms of the OEIS DATA line. -/
example : (List.range 8).map a = [1, 2, 10, 74, 730, 9002, 133210, 2299754] := by
  decide

/-- Example: Jovovic's recurrence `a(n) = 2 Σ_{k=1..n} C(n,k) a(n-k)` at
`n = 1, …, 6`, an independent check of the definition. -/
example : ∀ n ∈ Finset.Icc 1 6,
    a n = 2 * ∑ k ∈ Finset.Icc 1 n, n.choose k * a (n - k) := by
  decide

/-- Bala's mod-7 example: from `a(2)` on, residues repeat with period `6 = φ(7)`
(checked on a window). -/
example : ∀ n ∈ Finset.Icc 2 8, a (n + 6) % 7 = a n % 7 := by
  decide

/-! ## Bridge to the repository's weighted Stirling transform -/

/-- `a` is the factorial-weighted Stirling transform of the ordinary coefficients
`m ↦ 2^m` of `G(y) = 1/(1 - 2y)`. -/
theorem cast_a_eq_weightedStirlingTransform (n : ℕ) :
    (a n : ℤ) = OrdinaryIntegralEGF.weightedStirlingTransform (fun m => 2 ^ m) n := by
  unfold a OrdinaryIntegralEGF.weightedStirlingTransform
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

/-! ## The conjecture -/

/-- For every positive `k`, `a(n+φ(k)) ≡ a(n) (mod k)` for all sufficiently
large `n` (Bala's A004123 conjecture). Since `φ(k)` is positive, the least
eventual period divides it. -/
theorem a_modEq_eventually (k : ℕ) (hk : 1 ≤ k) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → a (n + Nat.totient k) ≡ a n [MOD k] := by
  obtain ⟨N, hN⟩ :=
    OrdinaryIntegralEGF.weightedStirlingTransform_eventuallyPeriodic (fun m => 2 ^ m) k hk
  refine ⟨N, fun n hn => ?_⟩
  have hz := hN n hn
  rw [← cast_a_eq_weightedStirlingTransform, ← cast_a_eq_weightedStirlingTransform] at hz
  push_cast at hz
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mp hz

/-- Non-vacuity of the period: `φ(k)` is positive for every `k ≥ 1`, so the
conclusion of `a_modEq_eventually` is a genuine periodicity, not `a n ≡ a n`. -/
theorem totient_pos_of_one_le (k : ℕ) (hk : 1 ≤ k) : 0 < Nat.totient k :=
  Nat.totient_pos.mpr hk

end Candidates.A004123BalaModEventually
