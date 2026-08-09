Session 2 picks up a live campaign, not a
blank slate. Session 1's retrospective is
.tasks/f5exp/docs/retro-session1.md and the
sieve's larger context — the border-rank
program, the two questions, what the
theorems can and cannot see — is distilled
in .tasks/f5exp/docs/reading-papers-1to4.md.
Read both before dispatching anything.

The group sieve (defined in f5high-1.md;
still not a concept from any literature)
survived session 1 as a validated
instrument: one consolidated source at
Scratch/GroupSieve/groupsieve.sage, its
harness USER-run green (20/20 assertions,
2026-07-12), and 510 resumable checkpoint
files. Do not trust this prompt for
coverage — it moves. Read the Coverage
section of
.tasks/f5exp/docs/sieve-summary.md, which
reflects exactly what is on disk: 510/510
orders complete means the stratum-A gap is
closed and Im3 ranks over the full
population; anything less means the
pending USER run is
`sage groupsieve.sage -- --order-timeout 0`
and every per-order caveat stands. Either
way the PoC bar is not met until tier-4
ranking runs and validates against known
rho_0 anchors.

What changed, and it changes how you
dispatch: agents never run sieve
computations. The USER runs those programs.
The only agent-side sage is a probe:
`timeout 60 sage -c` for a single fact, a
one-example primitive check, or proof
intuition — never a library loop, and a
timeout (expected or not) means halt and
hand off, never a bigger-budget retry.
Cards deliver complete, inspectable
programs —
space size stated, runtime projected,
checkpoint/resume, progress prints — plus
the exact run command in the campaign docs.
Downstream cards gate on the output
artifact existing, never on the run.
Intuition is the point; brute force is not.
The sieve exists to learn where rho_0 > 1
can hide, not to exhaust group libraries.

The mathematical headline moved. Reading
the Murthy and BCGPU sources produced a
campaign conjecture: rho_0(A x G) =
rho_0(G) for abelian A. It is falsifiable,
plausibly elementary, consistent with every
published data point, and if it lands it
closes the known [24,10]/[24,11] cascade
gap and becomes a new reject tier. That
line (Im5 engine, Pf3 proof, Im6 tier) plus
the dihedral subset bound (Pf4, treated as
open with its novelty caveat recorded) is
where the proving effort goes this session.

The DAG under .tasks/f5exp/ IS the plan. It
was rewritten and rewired on 2026-07-12 —
do not replan it; dispatch it. Everything
`goof tasks ready` shows goes out in
parallel, routed on `agent:`. At seed time
that is Im4, Im5, Pf4, Pl6.

Tracks: the main track is the sieve line
(Im4/Im5 roots, then Im2, Im3, Pl4, with
Pf3, Pf4, Im6, Qr1 alongside). The second
track is Pl6: Erdos mining round 2 plus the
formalization-reference track — its ledger
(.tasks/f5exp/docs/formalization-ledger.md,
with effort data on every entry) is a
primary USER deliverable of this session.
The Vp2 track is complete and its remaining
sorries are doctrine; do not reopen it —
that is a new campaign decision the USER
has not made.

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
timestamps, new artifacts in the docs dir.
Transcript-reading consumers are an
escalation for ambiguous cases, never the
default — that burn was session 1's largest.

Quota doctrine is standing now (system.md):
at most 2 concurrent provers, `goof usage`
before any wide fan-out, embargo playbook
at ~75% of the window. Session 1 hit that
wall and survived by checkpointing into
cards; prefer never arriving there.

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
they exist: pending USER run commands
(sieve programs waiting on a human hand),
proof or kill verdicts on Pf3 and Pf4, and
any rho_0 > 1 flag out of Qr1's lamplighter
table.
