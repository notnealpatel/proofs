# f5exp session 1 — retrospective and consolidation

You are in **analysis mode**: no agent dispatching, no new
campaigns, no proof work. Your job is to take stock of an
autonomous multi-campaign session that just ended on branch
`f5exp`, write the retrospective, and commit the work.

## Session background (2026-07-11)

Three planner-led campaigns ran concurrently, orchestrated
via `goof tasks` cards under `.tasks/f5exp/`:

- **Pl1 — group sieve PoC** (main track): the USER's novel
  tiered TPP-screening cascade over non-abelian groups
  (definition: `SCREEN_TPP_CANDIDATES` in
  `Manuscripts/Drafts/exotic-groups-for-mm.md`). Engine
  built and validated (spec v1.2, 18/18 falsifiability
  anchors) but the PoC bar is NOT met: clean checkpoints
  cover orders 2–383 only; `Im4` (ready) carries the
  remediation brief; Im2 → Im3 → Qr1 → Pl4 queued behind it.
- **Pl2 → Pl5 — Vp2 sorry burndown**: complete. New
  sorry-free `Proofs/Proofs/Vp2/BorderRank.lean` and
  `Circuit.lean`; Vp2.lean 6 → 5 sorries, each mapped to
  named missing infrastructure. Independently verified
  green builds (8488 jobs).
- **Pl3 — Erdos mining**: complete, three-for-three
  formalizations of KNOWN results (no open problem was
  solved): `Erdos880` (Burr–Erdős k=2), `Erdos175`
  (bounded squarefree central binomial classification),
  `Erdos715` (Alon–Friedland–Kalai core via
  Chevalley–Warning). Round-2 card `Pl6` is written and
  ready but NOT dispatched.

Mid-session events that shape the retro: a quota emergency
forced an embargo and throttling doctrine; a root-level
audit CONFIRMED brute-force-without-grounding at the
implementer seam (53% sweep crash from a wrong GAP
primitive; a 43-minute permutation grind replacing a
millisecond degree-distinctness check); two cross-cutting
probe memos landed real leads (Tier 2b ≡ Gowers
quasirandomness; coherent-configuration / Gelfand-pair
generalization → gated card `Pl4`).

## Your tasks, in order

1. **Inventory what was done.** `git status` the working
   tree; read the campaign artifacts in
   `.tasks/f5exp/docs/` (candidate-ledger.md,
   pl2-verdicts.md, pf1-borderrank.md, pf2-circuit.md,
   sweep-*.md, probe-quasirandomness.md,
   probe-coherent-configs.md, audit-bruteforce-grounding.md,
   sieve-summary.md — note the last one is a STALE artifact
   of a crashed sweep, kept only until Im4 regenerates it;
   its sibling `sieve-results-A.jsonl` was already deleted
   for the same reason. The clean data is
   `Scratch/GroupSieve/checkpoints/order_*.jsonl`).
   Distinguish clearly: formalized known mathematics vs
   built infrastructure vs unverified leads. Nothing solved
   any open problem.

2. **Frictions and lessons.** Read `LESSONS.md` (repo root)
   and today's `/tmp/goof/friction/*.md`. Assess each
   suggested remediation: adopt into `system.md` /
   `.tasks/planner.tmpl`, defer, or reject — with a
   sentence of reasoning each.

3. **Take stock of the DAG.** `goof tasks dag`,
   `goof tasks ready`, `goof tasks shelved`. Read the four
   `Pl*` card bodies (`.tasks/f5exp/cards/Pl{1,3}.md` carry
   long provenance/decision logs; Pl2/Pl5 closed clean;
   Pl4/Pl6 are unstarted follow-on charters). Verify card
   states match reality; fix mismatches with lifecycle
   commands (this is bookkeeping, not dispatching). Record
   the next-window queue explicitly: Im4 → Im2 → Im3 → Qr1
   → Pl4 (sieve), Pl6 (mining round 2, rescoped under the
   Conjecture Mining Protocol in `system.md`).

4. **Verify before committing.** From
   `/home/exedev/p/proofs/Proofs/` (ONLY there) run
   `lake build`; expect green with exactly 5 sorry warnings,
   all in `Vp2/Vp2.lean` (by design). Do not truncate the
   build output.

5. **Commit the work** in logical commits (you commit;
   never push, never `git codereview`, no `Co-Authored-By`
   trailers). A sensible grouping: (a) Erdos880 + Erdos175
   + Erdos715 + Proofs.lean imports; (b) Vp2
   BorderRank/Circuit + Vp2.lean; (c) Scratch/GroupSieve
   engine + checkpoints; (d) `.tasks/f5exp/` cards and
   docs; (e) protocol/meta: `system.md`,
   `.tasks/planner.tmpl`, `LESSONS.md`,
   `data/prompts/`. Use your judgment on the split; keep
   Manuscripts/ untouched (read-only always).

6. **Write the retrospective** to
   `.tasks/f5exp/docs/retro-session1.md`: what was
   accomplished (with the known-math vs new-infrastructure
   vs leads distinction), what failed and why (crash sweep,
   brute-force pattern, quota burn mechanics: transcript
   replay resumes, transcript-reading health consumers,
   concurrent max-reasoning provers), what the protocol now
   says because of it, and the concrete next-window plan.

## Standing constraints

- `Manuscripts/` is read-only. Never write there.
- `lake build` only from `~/p/proofs/Proofs/`.
- Use `goof rm` instead of `rm`.
- No `git push`. No dispatching agents in this session.
- Ground claims in the artifacts; where a doc's claim is
  unverified, say so rather than repeating it as fact.
