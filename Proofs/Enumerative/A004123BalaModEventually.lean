/-
# A004123 — Bala: `a(n) mod k` is eventually periodic with period dividing `φ(k)`

## OEIS source (retrieved with `oeis show A004123`, 2026-10-21)

```
NAME:     Number of generalized weak orders on n points.
TERMS:    1,2,10,74,730,9002,133210,2299754,45375130,1007179562,...
FORMULA:  E.g.f. for sequence with offset 0: 1/(3-2*exp(x)).
FORMULA:  a(n) = Sum_{k=0..n} Stirling2(n, k)*(2^k)*k!.
FORMULA:  Recurrence: a(n) = 2*Sum_{k=1..n} binomial(n, k)*a(n-k), a(0)=1.
          - _Vladeta Jovovic_, Mar 27 2003
COMMENT (the conjecture):
  From _Peter Bala_, Jul 08 2022: (Start)
  Conjecture: Let k be a positive integer. The sequence obtained by reducing
  a(n) modulo k is eventually periodic with the period dividing
  phi(k) = A000010(k). For example, modulo 7 we obtain the sequence
  [1, 2, 3, 4, 2, 0, 0, 2, 3, 4, 2, 0, 0, 2, 3, 4, 2, 0, 0, ...] with an
  apparent period of 6 = phi(7) starting at a(2). Cf. A000670.
  More generally, we conjecture that the same property holds for integer
  sequences having an e.g.f. of the form G(exp(x) - 1), where G(x) is an
  integral power series. (End)
```

## Status

Triage: proved elsewhere.  The general `G(exp(x) - 1)` statement (factorial-
weighted Stirling transform of an arbitrary integer sequence) is already
proved in this repository as
`OrdinaryIntegralEGF.weightedStirlingTransform_eventuallyPeriodic`
(`Proofs/Enumerative/OrdinaryIntegralEGF.lean`).  A004123 is the instance
`g_m = 2^m`, since `1/(3 - 2e^x) = G(e^x - 1)` with `G(y) = 1/(1 - 2y)`.
The elementary argument: `k ∣ m!` for `m ≥ k` truncates the sum, and
`m! S(n,m) = ∑_j (-1)^(m-j) C(m,j) j^n`, whose powers `j^n` are eventually
`φ(k)`-periodic modulo `k` (Euler on the unit part, nilpotence on the rest).

Computational re-validation (2026-10-21, Python, bounded): for every
`1 ≤ k ≤ 120` and `n < 400`, `a(n + φ(k)) ≡ a(n) (mod k)` holds from
`n = 4` on (the latest start over that range); the mod-7 residues
`1,2,3,4,2,0,0,2,3,4,2,0,0,...` match Bala's comment.
-/
import Mathlib
import Enumerative.OrdinaryIntegralEGF

set_option autoImplicit false

open Finset

namespace Candidates.A004123BalaModEventually

/-! ## Definition layer -/

/-- A004123, via the entry's formula `a(n) = Sum_{k=0..n} Stirling2(n,k) * 2^k * k!`
(the e.g.f. `1/(3 - 2 exp x)` expanded in `exp x - 1`). -/
def a (n : ℕ) : ℕ :=
  ∑ m ∈ range (n + 1), n.stirlingSecond m * 2 ^ m * m.factorial

/-- Ground truth: the first eight terms of the OEIS DATA line. -/
example : (List.range 8).map a = [1, 2, 10, 74, 730, 9002, 133210, 2299754] := by
  decide

/-- Ground truth: Jovovic's recurrence `a(n) = 2 Σ_{k=1..n} C(n,k) a(n-k)` at
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

/-- **Bala's conjecture for A004123 (Peter Bala, Jul 08 2022).**

Verbatim: "Let k be a positive integer. The sequence obtained by reducing a(n)
modulo k is eventually periodic with the period dividing phi(k) = A000010(k)."

Formalized as: for every `k ≥ 1` there is a threshold `N` such that
`a(n + φ(k)) ≡ a(n) (mod k)` for all `n ≥ N`.  Since `φ(k) ≥ 1`, this says
exactly that the reduced sequence is eventually periodic and that its minimal
eventual period divides `φ(k)`.  The guard `1 ≤ k` is from the source. -/
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
