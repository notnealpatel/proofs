Session 3 picks up after session 2 met the
sieve's PoC bar. Session 1's retro is
.tasks/f5exp/docs/retro-session1.md and the
sieve's larger context is
.tasks/f5exp/docs/reading-papers-1to4.md.
The census verdicts are in
.tasks/f5exp/docs/orch-Cj-census-final.md
(it supersedes -early). Read these before
dispatching anything.

Where session 2 landed, all verified on
disk: stratum A complete (510/510 orders,
91774 nonabelian records, zero
discrepancies — Im4-verification.md);
tier-4 ranking validates all 14 rho_0
anchors (Im3-ranking.md) — the PoC bar is
MET; the survivor census is complete and
clean (88185 records, 0 errors, 10256 =
11.63% carry an abelian direct factor);
Erdos 440 is proved sorry-free
(Proofs/Proofs/Erdos440/LcmCount.lean);
the formalization ledger is live with
effort data on every entry. Do not trust
this paragraph over disk — sieve-summary.md
and the DAG move; read them.

Why this session exists: the prover lane
was blocked. Every prover-type agent
dispatched directly in session 2 died
silently mid-turn — six crashes, tiny and
huge contexts alike, zero failures in any
other agent type. The evidence table is in
/tmp/goof/friction/f5exp-prover-agent-crashes.md
and, durably, in SESSION-2 PROVENANCE
blocks inside the affected card bodies.
Pf3, Pf4, and Ep542 sit ready with those
blocks: diagnosis, carried-over results
(Pf4's novelty verdict is OPEN — do not
re-sweep; Pf3 carries the census
prioritization: the C_p single-factor case
is 88% of the payoff), and prover budgets
intact — no attempt ever reached proof
work. They are the first dispatches. Card
dispatch discipline for provers: write the
notes checkpoint file before any other
work, no full-paper reads — digests plus
surgical grep of theorem line-ranges.

Liveness doctrine, new since session 2:
crashed subagents never notify. If a
dispatched agent goes quiet, stat its
transcript mtime and fuser the file —
metadata only, never read transcripts
yourself. Frozen mtime plus no open handle
means dead: TaskStop, reset the card,
re-dispatch with the diagnosis attached.
SendMessage to a crashed agent queues
forever undelivered; it only resumes
agents that stopped cleanly. Separate,
benign pattern (USER-identified cause):
bounded agents (flash, conjecturist,
consumer) run with maxTurns — a
completion whose final message reads
mid-thought is the turn cap, not a
crash. SendMessage grants fresh turns
and resumes with context intact; expect
one resume on any investigation-heavy
dispatch, and front-load the artifact
write so a cap fires after the
deliverable exists, not before.

USER runs live in SAGEREQUESTS.md at the
repo root — the canonical queue; surface
additions there, never run them. At
session-2 close (2026-07-12 ~03:00 UTC)
gelfand, tier4, and the stratum-B pilot
were complete, and the USER had just
started the last two runs concurrently:
the full stratum-B sample
(stratum-b-full.log) and the rho0
overnight (rho0.log; both logs capture
stderr via `|& tee -a`). Session 3 opens
by reading those logs and artifacts.
Reading rho0-results.jsonl: timeout or
partial rows on the big lamplighters
([160,235], [384,5790]) are expected per
the Im5 manifest, not failures; any
rho_0 > 1 row OUTSIDE the known anchors
is the campaign's headline event —
surface it immediately and it steers the
session. rho0-results.jsonl also gates
Pf3's kill-test and fills Qr1's table.
Census parallelization set the pattern:
deterministic --shard I/N slices, resume
unions across shard files — these
programs are cluster candidates, the
sieve boxes are not the cluster.

Implementer discipline, learned four
times over in session 2: agent-authored
sage programs crashed on Sage types at
json.dumps boundaries (GAP integers from
IdSmallGroup, Integer/Integer Rationals,
global round() returning RDF, Sage
Integer last_pos) and on wrong primitives
(pexpect gap instead of libgap;
subgroup[0] grabbing the identity
element). Every implementer card that
ships a program MUST cast to
int/float/str/bool at every json.dumps
boundary, use libgap (never the pexpect
gap interface), and smoke-test one record
end-to-end before handing the run command
to the USER — a dry-run that never
serializes a record proves nothing.

Novelty state of the census conjectures
(sweeps run 2026-07-12, ledger:
.tasks/f5exp/docs/orch-novelty-census.md):
C4/C5 (desert/burst id-ranges) are KILLED
— catalogue artifacts of the SmallGroups
ordering (rank, then p-class, descendants
contiguous; O'Brien 1991); only the
rate-by-rank/p-class content survives.
C10 (2^a*3 crossover at a=7) and C11
(C_3-peel growth) stand as apparently
novel; nearest neighbor Erdos-Palfy 1999,
which asks a different question. For Pf3:
rho_0(A x G) >= rho_0(G) is KNOWN
(product-lifting + rho_0(abelian) = 1) —
the <= direction is the entire content,
as the card already frames it. Cheap
follow-on queued by the USER: cross-check
and possibly extend OEIS A094448/A090751
(indecomposable-group counts) from the
census data — flash-tier, a small
USER-visible artifact if it lands.

Gates: Im6 — the abelian-factor reject
tier, ~10.2k survivors rejected in one
stroke — gates on Pf3's verdict, never on
a run. The Pl4 coherent-configuration
campaign COMPLETED in session 2 — seven
child cards closed, verdicts in
.tasks/f5exp/docs/Pl4-verdicts.md: the CC
memo lead is sound (three CU13 citation
numbers corrected; commutative-CC tiers
filter on rank and triangle feasibility
only — character-degree tiers are vacuous
there), the gelfand screen produced 307
unique commutative schemes
(gelfand-keep-dedup.jsonl, ranked in
Im8-gelfand-ranking.md), and CU13 anchor
validation passed. Two candidate theorems
came out of it (Pf5's rigidity lemma; the
rank ceiling r <= (N+[N_G(H):H])/2 tying
CC rank to BCGPU's normalizer parameter)
— novelty sweeps were dispatched at
session close; read their verdicts before
treating either as new. Uncarded
handoffs, planner-flagged: realization
search for top cap3 survivors (the value
question — needs a USER-run pruned search
program), CU13 Thm 6.3 wreath asymptotic
lane, order 128-255 extension, C1 as a
minor prover target. Mining continues
only through
Ep542; its acceptance protocol is in the
closed Pl6 card. Vp2 stays closed — its
sorries are doctrine, and reopening is a
USER decision that has not been made.

Cluster readiness (USER's 256-vCPU
target), ranked by intuition per
core-hour when the hardware exists:
(1) exhaustive exact-rho_0 table for all
nonabelian groups of order <= 64,
plausibly <= 100 — converts every ceiling
into a measured gap, kill-tests Pf3
against thousands of A x G pairs, and
extends the published anchor corpus
(HM 2012 stops at 32); (2) tier-4
features population-wide (re-scoped snr,
exact qr(G)) over all 84,681 survivors;
(3) stratum extension through order 2000
except 1024 (not in SmallGroups; order
768's 1.09B groups dominate at ~a day).
Stratum-B-exhaustive was on this list and
is DEMOTED: the completed 10k sample
measured survivor rate 99.95%, Wilson CI
[0.9988, 0.9998] — the cascade rejects
essentially nothing at 2^9, so exhaustive
classification there buys ~zero
information. That number is itself the
finding: it quantifies the coverage
boundary of the published theorem corpus
(low-class, small-order); theorem-dark
territory at 512 needs class->=3
machinery, not more classification runs.
Each remaining item is an Im card the
moment hardware lands; the shard interface already fits —
what's missing is a launcher (slurm array
or GNU parallel over --shard i/256),
checkpoint collection, and a formalized
merge-verify step (the census jq check is
the prototype; ~a day of implementer
work). The walls that stay walls: subset
searches at 2^|G|, exact rho_0's
super-exponential growth (256 cores moves
the frontier ~32 -> ~100, not to 500),
gnu(1024) ~ 49.5B uncatalogued. The
cluster is a falsification amplifier; it
proves nothing — provers do.

The DAG under .tasks/f5exp/ IS the plan.
Do not replan it; dispatch it. Everything
`goof tasks ready` shows goes out in
parallel, routed on `agent:`. At seed time
that is Pf3, Pf4, Ep542 plus whatever the
Pl4 line left ready.

---

Orchestration keeps the shape of
f5high-1.md: you steer a network of
mini-orchestrators (planner) that plan task
cards (goof tasks) and execute them on
conjecturist, prover, and implementer
agents. Task notifications are the primary
steering signal. Before the fan out, start
`/loop 25m "Dispatch consumers to see if any steering is required."`
as a fallback heartbeat only — do not poll
faster; notifications already wake you.

Health checks read structured state first:
`goof tasks ready`, card `updated`
timestamps, new artifacts in the docs dir,
and the liveness forensics above.
Transcript-reading consumers are an
escalation for ambiguous cases, never the
default.

Quota doctrine is standing (system.md): at
most 2 concurrent provers per campaign,
`goof usage` before any wide fan-out,
embargo playbook at ~75% of the window.

You should prefer letting agents fly free
and clear and give them maximum freedom to
explore.

Only intervene when you see looping with no
end or genuine bad decisions being made
because of context pressure.

The output to the USER stays **EXTREMELY
MINIMAL** — the `goof tasks dag` plus card
bodies are the decision chain and
provenance; no prose reports for their own
sake. Three exceptions, surfaced the moment
they exist: pending USER run commands,
proof or kill verdicts on Pf3, Pf4, or
Ep542, and any rho_0 > 1 flag out of
rho0-results.jsonl.
