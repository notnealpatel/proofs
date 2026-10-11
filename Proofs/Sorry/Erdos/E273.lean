/-
  Erdős Problem #273 — covering systems with moduli of the form p − 1.
  Status: open.  Tier UA attack target (certificate slice on the repo's
  Covering layer).

  Verbatim statement (`goof erdos fetch 273`, pulled 2026-08-05):

    "Is there a covering system all of whose moduli are of the form
    $p-1$ for some primes $p\geq 5$?"

  DB remarks: Selfridge found an example using divisors of 360 if p = 3
  is allowed (i.e. modulus 2 allowed).  Comment (ideal_ombrer, Jul 2026,
  comment-sourced, unrefereed): any p ≥ 5 covering needs a modulus with
  p > 877 (BBMST distortion sieve applied to the 149 moduli with
  p ≤ 877), and ∑ 1/(p−1) ≥ 1 + exp(−3.36·10²¹) via Filaseta–Kalogirou.

  Repo adjacency: `Proofs/Erdos/Covering/Basic.lean` provides
  `Erdos.Covering.Covers`, `IsCoveringSystem` (Finset (ℕ × ℕ) of
  (residue, modulus) pairs, distinct moduli > 1) and the decidable
  characterization `covers_iff_forall_range` — the exact machinery for
  the Selfridge certificate.

  Mathlib inventory: `Nat.Prime`; nothing else needed.
-/
import Mathlib
import Erdos.Covering.Basic

set_option autoImplicit false

namespace ErdosCandidates.E273

open Erdos.Covering

/-- `ModuliOfPrimeMinusOne P S`: every modulus of the system `S` is
    `p − 1` for some prime `p` with `P ≤ p`.  (`p − 1` is safe: `p ≥ 5`
    keeps ℕ-subtraction honest.) -/
def ModuliOfPrimeMinusOne (P : ℕ) (S : Finset (ℕ × ℕ)) : Prop :=
  ∀ q ∈ S, ∃ p : ℕ, p.Prime ∧ P ≤ p ∧ q.2 = p - 1

/-- **Erdős #273 (OPEN)**: does a covering system exist with all moduli
    of the form `p − 1`, `p ≥ 5` prime?  Archived as the open boundary;
    the DB and comments suggest yes-but-hard (any example needs a
    modulus with `p > 877`).  Stated as the existence claim so that a
    future certificate closes it. -/
theorem erdos_273 :
    ∃ S : Finset (ℕ × ℕ), IsCoveringSystem S ∧ ModuliOfPrimeMinusOne 5 S := by
  sorry

/-- **Selfridge's certificate slice (the Tier-UA target)**: allowing
    `p = 3` (modulus 2), a covering system with all moduli of the form
    `p − 1` exists — Selfridge's example uses moduli among the divisors
    of 360 of the form p−1: 2, 4, 6, 10, 12, 18, 30, 36, 40, 60, 72,
    180 (p = 3, 5, 7, 11, 13, 19, 31, 37, 41, 61, 73, 181).

    Attack: find the explicit residue choices (Selfridge's table is
    reproduced in the covering-systems literature; a sage/SAT search
    over the 12 moduli is a fast probe — the C6-lesson gate from the
    candidates document applies: scale the `decide` on
    `covers_iff_forall_range` at L = 360 first).  Once residues are
    pinned, the proof is `decide` through
    `covers_iff_forall_range_lcm`, the same shape as
    `isCoveringSystem_erdosSystem`.  Effort S once the certificate is
    found. -/
theorem selfridge_p3_certificate :
    ∃ S : Finset (ℕ × ℕ), IsCoveringSystem S ∧ ModuliOfPrimeMinusOne 3 S := by
  sorry

/-- Sanity: the modulus pool below the 877-threshold is as claimed —
    `2, 4, 6, 10, 12` are all `p − 1` for primes `3, 5, 7, 11, 13`, and
    `8` is not of the form `p − 1` for `p` prime (9 is not prime).
    Guards the `ModuliOfPrimeMinusOne` def against off-by-one.
    -- PROVABLE (decide). -/
example : (∃ p : ℕ, p.Prime ∧ 3 ≤ p ∧ 12 = p - 1) ∧
    ¬(∃ p : ℕ, p.Prime ∧ 3 ≤ p ∧ 8 = p - 1) := by
  sorry

/-- Density necessary condition (elementary, provable): a covering
    system's moduli satisfy `∑ 1/m ≥ 1` (each class `a (mod m)` has
    density `1/m`; the union must have density 1).  Specialized here as
    the entry point for the `p > 877` obstruction: the sum over the
    admissible pool must reach 1.  Mathlib route: count residues in
    `[0, L)` covered by each class (`covers_iff_forall_range` +
    `Finset.card_biUnion_le`).  -- PROVABLE (target; effort S–M). -/
theorem covering_density_lower_bound (S : Finset (ℕ × ℕ))
    (h : IsCoveringSystem S) :
    1 ≤ ∑ q ∈ S, (1 : ℚ) / q.2 := by
  sorry

end ErdosCandidates.E273

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - DB statement matches file header verbatim; formalization as existence of S with
     IsCoveringSystem and ModuliOfPrimeMinusOne 5 is faithful.
   - IsCoveringSystem / Covers from Erdos.Covering.Basic confirmed: Finset (ℕ × ℕ) of
     (residue, modulus) pairs, distinct moduli > 1, coverage over ℤ.  Used consistently.
   - ModuliOfPrimeMinusOne def: P ≤ p with ℕ-subtraction p - 1 is safe since p ≥ 5 > 1.
   - Selfridge moduli verified: the 12 divisors of 360 of form p-1 (p ≥ 3 prime) are
     {2,4,6,10,12,18,30,36,40,60,72,180} for primes {3,5,7,11,13,19,31,37,41,61,73,181}.
     File listing matches exactly.
   - Example (12 = 13-1, 13 prime; 8 ≠ p-1 for prime p): verified (9 not prime).
   - Comment from ideal_ombrer correctly flagged as comment-sourced/unrefereed.
   - covering_density_lower_bound: standard folklore; correctly typed as ℚ-valued sum.
-/
