# PROTOCOL — shared working rules

Every Plans/ file assumes these rules. They govern lanes,
review, claim discipline, and precedence. Read this file
before reading or writing any other Plans/ file.

Sources: `git show 4901d3b:Plans/PLAN.md` section "PROTOCOL —
deltas of 2026-08-05"; `git show 4901d3b:Plans/STATE0.md`
precedence paragraph; `git show 4901d3b:Plans/STATE7.md`
provenance section (claim-discipline tags); reorganized
2026-08-10.


## Lane and review rules (2026-08-05)

  Lanes    `prover` = Fable 5 xhigh: scarce-by-cost; holds only the item
           with the largest gap between "stated" and any known formal
           route. `postdoc` = Opus 5 Max: throughput; literature-
           following routes, grindy lanes, statement archives.
  Review   Orchestrator-dispatched ONLY, after a writer lane halts:
           parallel vacuity-cop + reviewer, orchestrator applies fixes,
           one commit per lane, writers never commit. Lanes MUST NOT
           self-audit (prover/postdoc agent files carry the MUST NOT); a
           lane-relayed PASS is an unverified claim — re-audit it.
  Cop      vacuity-cop rung 5 (new): source-fidelity — hunt LLM
           mis-translation, hallucinated conjectures, and prose-to-
           formal divergence against PRIMARY sources (`oeis show`,
           fetched papers), never against the `Formalize/` card, which
           is itself an LLM relay.
  Writers  STYLE.md first; `flock .lake/agent.lock lake build`;
           systemd-run memory fence; `oeis show` ground truth before any
           Lean statement; halt-never-weaken.


## Precedence

For facts about the tree (what compiles, what is sorry-free),
trust the tree and git history over any document. The
idea-cut Plans/ files record verdicts and decisions that
never lived in the tree — novelty judgments, kill witnesses,
dead proof routes, audit findings. The dispatch queues live
in `Plans/erdos.md` and `Plans/covering-arc.md`; where two
Plans/ files disagree, the disagreement is recorded
explicitly in the relevant file rather than resolved.


## Claim-discipline tags

  [M]  Measured or retrieved directly (by the original
       orchestrator, or — where dated — by the named
       distillation against the tree at its commit);
       asserts transcription-verification at its date.
  [A]  Agent-reported, artifact fetched but not
       independently re-verified — a lead, re-fetch before
       citing.
  [O]  Open, nobody has checked.

Every "first formalization" in this corpus is [A] unless
marked otherwise and must be re-fetched before it appears
in a submission. Never upgrade [A] to fact.


## Sage and computational claims (2026-08-10)

ALL Sage-derived numerics in this repo's historical corpus
are unreviewed and hold [A]-computational status — Sage and
search output is never load-bearing. A kill, keep, or
publish decision requires a Lean certificate or two
independent implementations agreeing. Computation orients;
it never proves.


## Audit lesson (2026-08-10)

The dominant observed failure mode in this corpus is
inherited claims re-tagged as currently-verified without
re-running the check. Nine prior-art claims were believed
and turned out false (see `Plans/standing.md`); every failure
was a search or an inference standing in for a retrieval.
Any [M] tag asserts transcription-verification at its date,
and tree facts must be re-verified on read.
