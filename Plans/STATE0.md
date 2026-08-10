# STATE0 — index of the .tasks distillation

Distilled 2026-08-10 from `.tasks/f5exp/docs` (210 files),
`.tasks/main/docs` (53 files), and the 25 non-done task cards, before
deletion of `.tasks/**`. Every source file has a disposition line
(drop / extracted / move) in exactly one STATE file below. The set was
audited by a source-fidelity reviewer and two drop-verdict critics;
confirmed findings were repaired before commit.

Precedence: for facts about the tree (what compiles, what is
sorry-free), trust the tree and git history over any document. The
STATE files are the record of verdicts and decisions that never lived
in the tree — novelty judgments, kill witnesses, dead proof routes,
audit findings. `Plans/PLAN.md` remains the forward dispatch plan;
where a STATE file and PLAN.md disagree, the disagreement is recorded
explicitly in STATE3 rather than resolved.

## Shards

  STATE1  Novelty and prior art — sweep verdicts, per-result novelty
          sheets, Erdős ledger targets scored >= 3.
  STATE2  Audit debt — outstanding vacuity/style findings, sorry
          inventory, rescued erratum records (Conner–Waring, ShearEC
          n=4, ExtraspecialData drift).
  STATE3  Live queue and planning deltas — the 25 ready/active cards,
          binding specs (Mn1, Tb1, Aw1 dead-end route), PLAN.md deltas.
  STATE4  Conjecture inventory — open / killed / formalized, with kill
          witnesses; OEIS triage targets; Gelfand data discrepancy.
  STATE5  Formalization state deltas — Mathlib coverage verdicts
          (audited on v4.30.0-rc2; tree is now v4.33.0-rc1 — re-verify
          absence claims before use), unattempted targets.
  STATE6  Literature grounding — claim-to-source anchors, misquote
          finds, fetch gaps.
  STATE7  Publication triage — tiers with blockers, the falsified
          prior-art record, per-arc result summaries.
  STATE8  Residuals — rescued witnesses and campaign verdicts,
          dangling-pointer ledger, code relocations.

Caveat: STATE3's card entries support planner-level re-scoping, not
direct prover dispatch — operational card detail was deliberately not
preserved; re-ground against the tree when re-carding.

## Pre-deletion checklist (owner: Neal)

  1  Commit STATE0–STATE8.
  2  Moves per dispositions: seven `pf3-probes/*.sage` →
     `Programs/GroupTPP/` (`beta0-exact.sage` → its `forge/`;
     lemmaD/lemmaM2 dropped, verbatim in committed `lemma_sweep.sage`);
     `kernel-graph.mmd` → `Programs/GroupTPP/`;
     `route-d-aes-diffusion-witness.py` → `Programs/Unsorted/`.
  3  Code fixes: `Programs/GroupTPP/cmd/gelfandrank/main.go:71` writes
     to a `.tasks` path (breaks at runtime after deletion);
     `groupsieve.sage:853,857` and `cascade.sage:979,983` print
     `.tasks` paths.
  4  Repoint Lean headers citing `.tasks` docs to STATE files:
     `ConnerWaring.lean:26,42`, `ExtraspecialLattice.lean:121`,
     `ShearQuadraticRank.lean:45,736`, `STPPWreath.lean:1744`,
     `SchinzelSzekeres.lean:67,76`; low-severity comment refs in
     `verify_all_combos.sage:9` and historical `Prompts/` files are
     listed in STATE8.
  5  Standing errors surfaced by the audit, not yet fixed:
     `Formalize/A007691-coleman-practical.md` and
     `Formalize/INDEX:84-86` still carry the retracted
     first-formalization claim; PLAN.md's Erdős #1213 pigeonhole
     route is refuted (STATE3); Gelfand 367-vs-307 jsonl discrepancy
     unresolved (STATE4); `Prompts/Ref/MENTALMAP` factcheck errors
     unapplied (STATE8).
  6  Known losses, accepted: the BooleanRankGeneric three-way
     cross-check script (STATE2) and the Cj4-C7 PSL(2,27) Sage
     skeleton (STATE4) existed only in uncommitted scratch.
  7  Delete `.tasks/**` (done cards' outcomes are in git history).
