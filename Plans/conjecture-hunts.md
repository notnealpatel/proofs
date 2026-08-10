# Conjecture hunts — open problems to attack with proofs and counterexample searches

The campaign goal is novel proofs and counterexamples at scale.
A kill condition is a dispatchable counterexample-search spec.
Computational kill/support evidence herein is unreviewed
[A]-computational per Plans/PROTOCOL.md — a "killed" verdict
resting on one Sage run may be wrongly killed (a missed
discovery); re-verify before permanently abandoning or building
on any entry.

Sources: `git show 4901d3b:Plans/STATE4.md` sections "oeis
formalization triage", "probe verdicts"; `git show
4901d3b:Plans/STATE1.md` sections "calibration sweep P1",
"calibration sweep P3", "erdos burndown ledgers",
"corpus-vs-web conflicts", "verdict vocabularies"; reorganized
2026-08-10.

Matmul conjectures (GroupTPP, ω, lift law, census, Gelfand,
β₀, sieve) → matmul-search.md.
Erdős dispatch targets (the full target queue) →
erdos.md.


## verdict vocabularies

Three grading schemes were in use; all three are defined
only in the retired docs, so they are restated here.

Calibration sweep labels (P1/P2/P3, 2026-07-19/20):
KILLED — prior art located and read by an agent; cite,
don't prove. LIKELY-KNOWN — strong signal, exact statement
not verified in source. SURVIVOR — no prior found by either
sweep. OPEN-BET — restatement of a live open problem.
Corpus sweeps additionally used IMPLICIT (derivable from a
corpus source but not stated) and NOT-IN-CORPUS. Gate rule
(USER): nothing killed as published gets prover effort.

Census sweep vocabulary (2026-07-12): KNOWN /
FOLKLORE-DERIVABLE / DOCUMENTED-ARTIFACT /
PARTIALLY-ADJACENT / ADJACENT / NOT-FOUND.

Scoring rubric and sweep vocabulary: see Plans/erdos.md.


## calibration sweep P1 — monomial realizations

Substrate `Proofs/Xlib/MonomialRealization.lean`;
statements in `Proofs/Scratch/Sweep/P1_Monomial.lean`.
Notation: TPP = triple product property (CU03 =
arXiv:math/0307321); β(G) = TPP capacity.

| id | verdict | strongest pointer |
|----|---------|-------------------|
| c1 | KILLED | CU03 Thm 2.1/2.3 proof |
| c2 | KILLED | CU03 Lem 2.1 |
| c3 | KILLED | Murthy arXiv:0709.1223 Cor to Lem 4.1; CU03 Lem 3.1 |
| c4 | KILLED | CU03 Lem 3.1; Murthy Lem 4.5 |
| c5 | SURVIVOR (web) / IMPLICIT (corpus) | corpus: derivable from CU03 Thm 2.3 |
| c6 | SURVIVOR (web) / IMPLICIT (corpus) | CU03 uses the shape, never proves it forced |
| c7 | LIKELY-KNOWN | converse reading of CU03 Thm 2.1 |
| c8 | KILLED | CU03 Thm 2.1/2.3 |
| c9 | KILLED given c6 | CU03 Def 2.4; abelian case Murthy Cor 4.4 |
| c10 | SURVIVOR (both sweeps) | nearest: CU13 arXiv:1207.6528 §3 rescaling |

Surviving package c5+c6+c10 ("rigidity"): every abstract
monomial realization is, up to gauge, a Cohn-Umans TPP
realization. Both sweeps judged it
derivable-but-never-stated. Prover dispatch was left
PENDING USER RULING.


## calibration sweep P3 — isoclinism / char degrees

Substrate `Proofs/Xlib/IsoclinismInvariants.lean` +
`Proofs/Xlib/CharDegrees.lean`; statements in
`Proofs/Scratch/Sweep/P3_Isoclinism.lean`. All ten killed
or likely-known; zero survivors. D_x(G) = Σ dᵢ^x over
irreducible character degrees.

| id | verdict | strongest pointer |
|----|---------|-------------------|
| c1 | KILLED | Groupprops "Isoclinic groups have same proportions of degrees..." (wiki, unverified); traced to Hall 1940 / Leedham-Green-McKay |
| c2 | KILLED | corollary of c1 |
| c3 | KILLED | corollary of c1 proportionality |
| c4 | KILLED | textbook Irr(G×A) |
| c5 | KILLED | Isaacs, Character Theory, Cor 2.23 |
| c6 | KILLED | both sides detect abelianness |
| c7 | LIKELY-KNOWN | Meldrum, Wreath Products, 1995; Skuratovskii 2019; GAP-exact 9/9 |
| c8 | LIKELY-KNOWN | corollary of c7 order mismatch |
| c9 | KILLED | CKSU math/0511460, stated at x=ω; LEMMA NUMBER UNPINNED (2.4 vs 4.2) — verify before use |
| c10 | KILLED | CU03 Lem 2.4/3.2 + Hedtke arXiv:1107.5969 |

Salvage recorded despite zero novelty: (a) the c9 citation
is the cheap route to discharging the sorries
`stpp_capacity_le` and `stpp_capacity_le_of_wreath` in
`Proofs/GroupTPP/STPPWreath.lean`; (b) corrected stale claim —
IsoclinismInvariants and CharDegrees are sorry-free, and
WreathNg.lean's docstring saying otherwise is stale;
(c) heuristic: pick the isoclinism representative before
wreath amplification.


## corpus-vs-web conflicts

Corpus-vs-web conflicts worth remembering: the corpus
sweep (References/ only) said NOT-IN-CORPUS for p3
c1/c2/c3/c7/c8 and p2_c4, which the web sweep killed via
Groupprops/Meldrum/textbooks — corpus scope misses
standard sources, so a lone NOT-IN-CORPUS is weak evidence
of novelty. Conversely for p1_c5/c6 the web sweep found nothing
standalone where the corpus called it implicit; those
verdicts disagree in the novelty-favoring direction and
were held as survivors only via the merged reading. p1_c9's
corpus verdict is KNOWN (CU03 Def 2.4 + beta(G) definition),
not implicit; it was incorrectly grouped here.
Campaign-level calibration verdict: generic conjecture
sweeps do not scale; conjecturing pays only where formal
machinery meets the active search frontier (P2).


## oeis formalization triage

The triage doc scored 46 briefs. Verdict counts: 1
already-proved core (A319510), 1 trivial-go (A060938), 13
maybe, 31 out-of-reach/ill-posed. All cited Lean paths exist
in the tree but most are stale pre-reorg names (`Proofs/Xlib/`
is now `Proofs/GroupTPP/`, root-level files moved under
`Proofs/Enumerative/`, `Proofs/Erdos175/` under
`Proofs/Erdos/`) [M].

Actionable targets absent from the target queue
(`Plans/erdos.md`) — the real at-risk state:

- A060938 (max irrep degree supermultiplicative,
  a(m)a(n) <= a(mn)): rated TRIVIAL on top of
  `Proofs/GroupTPP/CharDegreesMul.lean` [M]. One-step target,
  no plan entry anywhere.
- A061256 (Euler transform of sigma = commuting-pairs
  conjugacy classes of S_n): rated MAYBE, "highest
  payoff-to-risk in the group cluster", infra at
  `Proofs/GroupTPP/HigherCommProb.lean` [M]. No plan entry.
- A319510 (rank a(n) = a(4n) via E_n ~ E_{4n} curve iso):
  core already proved in `Proofs/Scratch/CongrCurveIso.lean`
  [M]; literal rank statement blocked on Mordell-Weil rank
  missing from Mathlib. Needs promotion out of Scratch;
  untracked.
- A085805 (perm of D_k character table nonzero iff
  k = 4 mod 16): MAYBE but its verification run was aborted;
  gated on a compute re-run before any proof attempt.
- Secondary notes preserved from the triage: A046098 core is
  proved (`Proofs/Erdos/Erdos175/NotSquarefree.lean` [M]) —
  extend, do not restart; A236397 flags a capset definition
  as highest-leverage shared def work; A332077's adjacent
  Erdos-Rado classical bound is a separate MAYBE card;
  A230528's honest next step is a witness-search program;
  A391599's definition + small-n exact values are actionable
  even though the sharp constant is out of reach.

Parked out-of-reach A-numbers (open problems or missing
foundations; low loss if forgotten): A000001, A000041,
A000670 (two briefs), A002106, A002804, A003313, A005245,
A005432, A005520, A007691 (two), A031507, A039669, A046057,
A060748, A062733, A076142, A083207 (one of two), A089654,
A090052, A094870, A161682, A230528, A236397, A250109, A273929,
A323653, A332077, A391599.


## erdos burndown ledgers

Erdos burndown ledger data (score 3/4/5 lists, corrected
score distribution, ZFC-independent list, external
formalizations, suspect entries needing adjudication, and
APSSV26b caveat): see Plans/erdos.md, sections "Erdos
burndown scoring" through "Suspect entries needing human
adjudication".
