/-
  Erdős Problem #7 — odd covering systems.
  Status: verifiable (site status); no accepted proof.  Selfridge $2000
  for an explicit odd covering, Erdős $25 for nonexistence.
  Tier UB archive target on the repo's Covering layer.

  Verbatim statement (`goof erdos fetch 7`, pulled 2026-08-05):

    "Is there a distinct covering system all of whose moduli are odd?"

  DB remarks: Erdős–Selfridge (sometimes with Schinzel).  The stronger
  squarefree version is IMPOSSIBLE: Balister–Bollobás–Morris–
  Sahasrabudhe–Tiba [BBMST22] proved no covering system has all moduli
  odd AND squarefree.  Hough–Nielsen [HoNi19]: some modulus is
  divisible by 2 or 3 (simpler proof in BBMST22, which also shows: if
  an odd covering exists, lcm of moduli divisible by 9 or 15).
  Comment thread 2026: multiple AI-assisted "proofs" posted and
  rejected (jinooklee's sieve-monotonicity Lean attempt had a provably
  false axiom — sieveProd ≥ 1 by construction; the gebyjaff/Aristotle
  hybrid had unverified Hough–Nielsen bridging axioms).  Given the
  churn, a trusted formal statement has unusual audit value.

  Repo adjacency: `Proofs/Erdos/Covering/Basic.lean`
  (`IsCoveringSystem`, decidable coverage characterization);
  PLAN.md already tracks upstream `erdos_7` (sorry'd over
  `StrictCoveringSystem ℤ` in formal-conjectures) — this file's
  contribution is the decidable restatement plus the BBMST squarefree
  boundary.

  Mathlib inventory: `Odd`, `Squarefree` both present.
-/
import Mathlib
import Erdos.Covering.Basic

set_option autoImplicit false

namespace ErdosCandidates.E7

open Erdos.Covering

/-- `OddModuli S`: every modulus of the system is odd. -/
def OddModuli (S : Finset (ℕ × ℕ)) : Prop :=
  ∀ q ∈ S, Odd q.2

/-- **Erdős #7 (OPEN; Selfridge $2000 / Erdős $25)**: is there a
    distinct covering system all of whose moduli are odd?
    (`IsCoveringSystem` already carries distinctness of moduli and
    moduli > 1 — matching the "distinct covering system" convention the
    DB fixed via the Adenwalla comment.)  Stated as the existence
    claim; a future explicit certificate would close it by `decide`
    through `covers_iff_forall_range_lcm`. -/
theorem erdos_7 :
    ∃ S : Finset (ℕ × ℕ), IsCoveringSystem S ∧ OddModuli S := by
  sorry

/-- **BBMST squarefree impossibility** (BBMST22, Invent. Math.),
    archived: no covering system has all moduli odd and squarefree.
    The proof is a distortion-sieve argument far beyond current
    formalization reach — but the STATEMENT is the audit-valuable
    boundary given the 2026 churn of false proofs. -/
theorem bbmst_no_odd_squarefree (S : Finset (ℕ × ℕ))
    (h : IsCoveringSystem S) (hodd : OddModuli S) :
    ¬ ∀ q ∈ S, Squarefree q.2 := by
  sorry

/-- **Hough–Nielsen** (HoNi19; simpler proof in BBMST22), archived:
    in any covering system some modulus is divisible by 2 or 3. -/
theorem hough_nielsen (S : Finset (ℕ × ℕ)) (h : IsCoveringSystem S) :
    ∃ q ∈ S, 2 ∣ q.2 ∨ 3 ∣ q.2 := by
  sorry

/-- **BBMST lcm condition**, archived: if an odd covering system
    exists, the lcm of its moduli is divisible by 9 or by 15. -/
theorem bbmst_lcm_condition (S : Finset (ℕ × ℕ))
    (h : IsCoveringSystem S) (hodd : OddModuli S) :
    9 ∣ S.lcm Prod.snd ∨ 15 ∣ S.lcm Prod.snd := by
  sorry

/-- Sanity: the classical Erdős system (moduli 2, 3, 4, 6, 12) is a
    covering system but NOT odd — the two properties are jointly
    exhibited nowhere yet, which is the problem.  Uses the repo's
    proved `isCoveringSystem_erdosSystem`.
    -- PROVABLE (decide on the moduli list). -/
example : IsCoveringSystem erdosSystem ∧ ¬ OddModuli erdosSystem := by
  sorry

/-- Sanity (folklore density obstruction, from the Zeraoulia comment,
    self-contained): the lcm `L` of the moduli of any covering system
    satisfies `σ(L) ≥ 2L` (L is abundant or perfect) — since
    `∑_{d ∣ L, d > 1} 1/d ≥ 1`.  For an odd covering this forces
    `L ≥ 945` (smallest odd abundant number).  A clean elementary
    target on top of `covering_density_lower_bound`-style counting.
    -- PROVABLE (target; effort S–M). -/
theorem lcm_abundant (S : Finset (ℕ × ℕ)) (h : IsCoveringSystem S) :
    2 * S.lcm Prod.snd ≤ ∑ d ∈ (S.lcm Prod.snd).divisors, d := by
  sorry

end ErdosCandidates.E7

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - Verbatim statement matches DB fetch.
   - IsCoveringSystem (Basic.lean) carries one_lt_mod, injOn_mod (distinct moduli),
     covers — matching the "distinct covering system" convention fixed by Adenwalla.
   - erdosSystem and isCoveringSystem_erdosSystem both exist in Basic.lean and are
     used correctly.
   - OddModuli checks Odd q.2 (the modulus component) — correct.
   - BBMST squarefree impossibility, Hough-Nielsen (any covering system, not just odd),
     and BBMST lcm {9,15} condition all match DB sections faithfully.
   - Selfridge $2000 / Erdos $25 attribution matches Filaseta-Ford-Konyagin [FFK00]
     as reported in comments.
   - lcm_abundant (Zeraoulia comment) correctly states sigma(L) >= 2L.
   - Comment-thread churn (jinooklee false axiom, gebyjaff unverified bridging)
     accurately summarized.
-/
