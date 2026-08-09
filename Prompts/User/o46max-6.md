# Handoff — Hu-gated campaigns: Pf3 probing and the CU chain

You are an orchestrator for a research session with the
principal mathematician on this project. Read this document
fully before acting. Session 5 (o46max-5) ended with two
campaigns cut and held; this session runs them.

## Session posture

You have latitude to propose directions and assess proof
state. Dispatch the two held campaigns on startup (they were
scoped and approved last session); confirm with the user
before creating or dispatching anything beyond them. The
user is the mathematician; you steer by their judgment.

## NEW DOCTRINE: human gates (`Hu` cards)

Session 5 ended the flat `Hu` ban. The doctrine now lives in
`system.md` and `.tasks/planner.tmpl` (both updated on
disk — they are authoritative over any memory of the old
rule). Summary:

- `Hu` cards are permitted for exactly three shapes:
  (1) mathematical verdicts that redirect campaigns,
  (2) result sign-off before anything is externally
  reportable, (3) metered-run/budget/semantics decisions.
  Everything else stays autonomous.
- Every `Hu` card carries a decision brief: evidence
  pointers, 2-3 options, a recommendation. Minutes to
  answer, never "review the campaign."
- `Hu` cards never auto-wire; they block ONLY the node(s)
  wired behind them. Work never silently stalls on one.

**Orchestrator handling:** `Hu` cards surface in
`goof tasks ready` with `agent: human`. They are the USER's
inbox — you MUST NOT dispatch them to agents, and you MUST
NOT block unrelated work on them. At startup, list any ready
`Hu` cards with a one-line status of their briefs; that is
the only startup prose the USER needs.

Live gates (all for Pl15): `Hu1` (run budget/semantics per
target), `Hu2` (kill sign-off — inert unless a
counterexample lands), `Hu3` (margin-verdict interpretation
and follow-on authorization). The Pl15 planner fills their
evidence sections and wires them; briefs are in the card
bodies.

## Startup

1. `goof tasks ready` — source of truth. Expected: `Pl15`,
   `Pl16` (both deps `[Im9]`, done). `Hu1`-`Hu3` are wired
   behind Pl15 and surface in `ready` only once briefed
   (that is the contract: ready Hu = awaiting the USER).
   Fix any `violations` first.
2. Dispatch `Pl15` and `Pl16` in parallel, each with a thin
   prompt and its card path. Nothing else.
3. Start the checkpoint loop (bottom of this doc).

Known tooling bug: `goof tasks add Pl_` auto-numbering
proposes stale IDs ("Pl5 already exists"). Workaround:
explicit IDs (`goof tasks add Pl17`). Friction logged at
`/tmp/goof/friction/f5exp-tasks-add-autonumber.md`. `Hu_`
auto-numbering works.

## Campaign 1: Pl15 — abelian direct factor probing

Card: `.tasks/f5exp/cards/Pl15.md` (self-contained; rewritten
session 5 with semantics policy, A-side census requirements,
kill protocol, and the three Hu gates).

Conjecture: rho_0(A x G) = rho_0(G) for finite abelian A.
Open; novel (<= direction unstated in literature). Pf3
session 4 refuted the in-frame proof program (Lemma D) and
found zero-margin survival in A_6: max eligible |Sigma| =
beta_0(A_6) = 972 EXACTLY. Full report:
`.tasks/f5exp/docs/Pf3-abelian-factor.md`.

The campaign builds a USER-run probing program computing both
sides of the A-vs-B diagnostic on A_5 through A_7 (decisive)
plus C_p x G products. Key discipline:

- Kill is cheap (lower-bound semantics); confirmation needs
  exhaustion (`exact`). The USER buys the tier per target at
  `Hu1`.
- A counterexample triggers the kill protocol: STOP, build
  the standalone brute-checked witness, gate on `Hu2`.
- The margin verdict routes through `Hu3` to a follow-on
  `Pl*` card cut-and-held, never auto-dispatched.
- Engine note (already in the card, agents get it wrong from
  memory): the Go engine (`cmd/sieve/internal/tpp/`) is
  input-agnostic; the extension point is the EXPORTER
  (`Scratch/GroupSieve/forge/export_tpp.sage`) for
  permutation-group input. Only A_7 is outside SmallGroups.

## Campaign 2: Pl16 — formalize the Cohn-Umans omega chain

Card: `.tasks/f5exp/cards/Pl16.md` (self-contained).
Declared tier-3 formalization-reference scope; the
formalization ledger with effort data is a primary
deliverable.

**Standing directive: NO UPSTREAMING.** No PRs, no PR prep,
no master-freshness checks, no Zulip. Upstreaming is the
USER's decision outside the campaign. This is written in the
card; hold the planner to it.

Goal: CU03 Thm 4.1 — (nmp)^(omega/3) <= sum d_i^omega for
TPP realizations — assembled from the sorry-free pillars
(Xlib/CharDegrees + BilinearComplexity rank calculus, omega
with 2 <= omega <= 3, R<2,2,2> = 7). Child order: sorry-debt
audit first (string counts are docstring-inflated; last real
count was 12, five days stale), then FDRep bridge, then
TPP => C[G] embedding, then Thm 4.1, then validation
burndown of the attackable Xlib sorries. Exact statements
from `.tasks/f5exp/docs/gr4-tpp-anchors.md`, never memory.

## Held for USER direction (do not card, do not prompt)

- The rho_0 x character-degree join over sieve survivors
  ("does rho_0 > 1 occur outside the wreath family?") —
  scoped in session 5 discussion, not carded. Arrives as a
  directive if the USER wants it.
- Anything on the o46max-5 USER-blocked list (erratum note,
  TPP docstring provenance, publication strategy) not
  already resolved by Pl16's no-upstream directive.

## Project conventions (unchanged)

- Lean 4 proofs: `~/p/proofs/Proofs/Proofs/`; library:
  `Proofs/Xlib/`; build with
  `flock .lake/agent.lock lake build` from
  `~/p/proofs/Proofs/` only. Never the parent directory.
- Sieve/forge programs: `Scratch/GroupSieve/`; Go: `cmd/`.
- Sieve computations are USER-run: agents deliver programs
  with space analysis, projected runtime,
  checkpoint/resume, progress prints, and the exact run
  command. `timeout 60 sage -c` single-fact probes only.
- Ground every claim with `sage`, `wiki`, `oeis`, `erdos`,
  `leandoc`, or primary sources in `References/`. Never
  training data.
- `Manuscripts/` is read-only. Agent prose goes to
  `.tasks/f5exp/docs/`.
- Quota doctrine: max 2 concurrent provers per campaign,
  staggered; `goof usage` + `goof sys` before any fan-out;
  embargo on quota pressure.
- Output to the USER stays EXTREMELY MINIMAL: card bodies
  and docs artifacts are the decision chain. Exceptions:
  proof or kill verdicts, any rho_0 > 1 flag, and ready
  `Hu` briefs.

## What NOT to do

- Do not dispatch `Hu` cards or block ungated work on them.
- Do not let any agent run probe/sieve computations beyond
  the calibration carve-outs in the cards.
- Do not permit upstreaming work anywhere in Pl16.
- Do not run `lake build` without the flock lock, or from
  any directory but `~/p/proofs/Proofs/`.
- Do not commit outside the checkpoint loop; subagents never
  commit.
- Do not treat a closed `Pl*` card as campaign completion —
  the planner's final return is the signal; gate follow-ons
  on terminal child cards.

## After startup

```
/loop 5m Run `git add .` and `git commit -m "all: o46max-6 checkpoint $(date)"`
```
