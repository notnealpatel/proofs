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
  The historical dispatch tracked upstream `erdos_7` (sorry'd over
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
theorem erdosSystem_covering_not_odd :
    IsCoveringSystem erdosSystem ∧ ¬ OddModuli erdosSystem := by
  refine ⟨isCoveringSystem_erdosSystem, ?_⟩
  intro hodd
  have htwo : Odd (2 : ℕ) := hodd (0, 2) (by decide)
  exact (by decide : ¬ Odd (2 : ℕ)) htwo

example : IsCoveringSystem erdosSystem ∧ ¬ OddModuli erdosSystem :=
  erdosSystem_covering_not_odd

/-- A residue class modulo a positive divisor of `L` contains at most
`L / m` natural numbers below `L`, by injection into the quotient range. -/
theorem residue_card_le (L a m : ℕ) (hm : 0 < m) (hdvd : m ∣ L) :
    ((Finset.range L).filter (fun r => r % m = a % m)).card ≤ L / m := by
  apply le_trans (Finset.card_le_card_of_injOn (fun r : ℕ => r / m)
    (t := Finset.range (L / m)) ?_ ?_)
    (by simp)
  · intro r hr
    have hrL : r < L := Finset.mem_range.mp (Finset.mem_filter.mp hr).1
    apply Finset.mem_range.mpr
    apply (Nat.div_lt_iff_lt_mul hm).mpr
    simpa only [Nat.div_mul_cancel hdvd] using hrL
  · intro r hr s hs heq
    change r / m = s / m at heq
    have hrmod := (Finset.mem_filter.mp hr).2
    have hsmod := (Finset.mem_filter.mp hs).2
    have hrdecomp := Nat.mod_add_div r m
    have hsdecomp := Nat.mod_add_div s m
    rw [hrmod, heq] at hrdecomp
    rw [hsmod] at hsdecomp
    exact hrdecomp.symm.trans hsdecomp

/-- Sanity (folklore density obstruction, from the Zeraoulia comment,
    self-contained): the lcm `L` of the moduli of any covering system
    satisfies `σ(L) ≥ 2L` (L is abundant or perfect) — since
    `∑_{d ∣ L, d > 1} 1/d ≥ 1`.  For an odd covering this forces
    `L ≥ 945` (smallest odd abundant number).  A clean elementary
    target on top of `covering_density_lower_bound`-style counting.
    -- PROVABLE (target; effort S–M). -/
theorem lcm_abundant (S : Finset (ℕ × ℕ)) (h : IsCoveringSystem S) :
    2 * S.lcm Prod.snd ≤ ∑ d ∈ (S.lcm Prod.snd).divisors, d := by
  classical
  let L := S.lcm Prod.snd
  have hpos : ∀ q ∈ S, 0 < q.2 := fun q hq => lt_trans Nat.zero_lt_one (h.one_lt_mod q hq)
  have hL : 0 < L := by
    apply Nat.pos_of_ne_zero
    intro hzero
    obtain ⟨q, hq, hqzero⟩ := Finset.lcm_eq_zero_iff.mp hzero
    exact (hpos q hq).ne' hqzero
  have hdvd : ∀ q ∈ S, q.2 ∣ L := fun q hq => Finset.dvd_lcm hq
  let A := fun q : ℕ × ℕ => (Finset.range L).filter (fun r => r % q.2 = q.1 % q.2)
  have hcover : Finset.range L ⊆ S.biUnion A := by
    intro r hr
    obtain ⟨q, hq, hrq⟩ := (covers_iff_forall_range_lcm hpos).mp h.covers r hr
    exact Finset.mem_biUnion.mpr ⟨q, hq, Finset.mem_filter.mpr ⟨hr, hrq⟩⟩
  have hdensity : L ≤ ∑ q ∈ S, L / q.2 := by
    calc
      L = (Finset.range L).card := (Finset.card_range L).symm
      _ ≤ (S.biUnion A).card := Finset.card_le_card hcover
      _ ≤ ∑ q ∈ S, (A q).card := Finset.card_biUnion_le
      _ ≤ ∑ q ∈ S, L / q.2 := Finset.sum_le_sum fun q hq =>
        residue_card_le L q.1 q.2 (hpos q hq) (hdvd q hq)
  let D := S.image (fun q => L / q.2)
  have hinj : Set.InjOn (fun q : ℕ × ℕ => L / q.2) (S : Set (ℕ × ℕ)) := by
    intro q hq p hp heq
    apply h.injOn_mod hq hp
    calc
      q.2 = L / (L / q.2) := (Nat.div_div_self (hdvd q hq) hL.ne').symm
      _ = L / (L / p.2) := congrArg (fun e => L / e) heq
      _ = p.2 := Nat.div_div_self (hdvd p hp) hL.ne'
  have hsumD : ∑ e ∈ D, e = ∑ q ∈ S, L / q.2 := by
    exact Finset.sum_image hinj
  have hnot : L ∉ D := by
    intro hmem
    obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp hmem
    have hlt : L / q.2 < L := Nat.div_lt_self hL (h.one_lt_mod q hq)
    exact (ne_of_lt hlt) heq
  have hsubset : insert L D ⊆ L.divisors := by
    intro e he
    rcases Finset.mem_insert.mp he with heq | heD
    · subst e
      exact Nat.mem_divisors.mpr ⟨dvd_refl L, hL.ne'⟩
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp heD
      exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (hdvd q hq), hL.ne'⟩
  calc
    2 * L = L + L := by omega
    _ ≤ L + ∑ e ∈ D, e := Nat.add_le_add_left (hsumD.symm ▸ hdensity) L
    _ = ∑ e ∈ insert L D, e := by rw [Finset.sum_insert hnot]
    _ ≤ ∑ e ∈ L.divisors, e := Finset.sum_le_sum_of_subset hsubset

example : IsCoveringSystem erdosSystem := isCoveringSystem_erdosSystem

example : ((Finset.range 12).filter (fun r => r % 2 = 0 % 2)).card ≤ 12 / 2 :=
  residue_card_le 12 0 2 (by decide) (by decide)

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
