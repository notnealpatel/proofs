# STATE1 — novelty and prior art

Distilled 2026-08-10 from the novelty / prior-art working
docs under `.tasks/f5exp/docs/` and `.tasks/main/docs/`,
superseding them. Those directories are being deleted; this
file preserves the verdicts that exist nowhere in the
committed tree.

Epistemic status: none of the 30 source files carries
per-claim [M]/[A]/[O] tags. The P1-P3 glossary declares all
its verdicts "RECORD-GRADE (agent sweeps, sources read by
agents, not re-verified by the principal)". Treat every
verdict and citation below as [A] — agent-reported, to be
re-fetched before it appears in any submission. The
campaign's believed-then-falsified prior-art history (nine
falsified claims, all caught by retrieval, never by
reasoning) is preserved by the triage-publishability shard;
it is the calibration for how much to trust this file.

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

Erdos burndown score (0-5), for a Lean-formalizable win:
5 — settled by an explicit small finite witness a
`decide`/`native_decide` check could verify, or a short
self-contained elementary proof. 4 — elementary known
proof, one to a few pages, standard Mathlib facts.
3 — resolution known and readable but needs moderate
infrastructure; a special case is still respectable.
2 — serious machinery; only a toy fragment formalizable.
1 — statement hard to even state in Lean, or 30+ page
hard analysis. 0 — not a sensible formal target (incl.
ZFC-independent). Ground rules: quote erdosproblems.com,
never assert resolution history from memory;
`formalized=yes` means only that the statement exists in
google-deepmind/formal-conjectures; honest verdicts beat
volume. Problem 20 is already formalized in this repo.

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

## calibration sweep P2 — rank calculus over F₂

Substrate `Proofs/Proofs/BilinearComplexity/RankCalculus.lean`
plus stabilizer Sage scripts; statements in
`Proofs/Scratch/Sweep/P2_RankCalculus.lean`. identityTriad
= vec(I)⊗vec(I)⊗vec(I) as a rank-1 term of ⟨n,n,n⟩.

| id | verdict | strongest pointer |
|----|---------|-------------------|
| c1 | KILLED | de Groote 1978 Thm 3.3-3.4; Burichenko arXiv:2210.16565 Prop 3 |
| c2 | KILLED | CGLVW arXiv:1811.05511 Thm 5.1(ii) |
| c3 | LIKELY-KNOWN | CILO arXiv:1610.08364 §3; BILR arXiv:1801.00843 §5.1 |
| c4 | KILLED (web) / NOT-IN-CORPUS | corollary of c1 + linearity |
| c5 | KILLED (implicit) | de Groote uniqueness (CILO Thm 4.2); Burichenko arXiv:1408.6273 |
| c6 | OPEN-BET (both novel) | none; BILR rank-23 over C, F₂ reduction unverified |
| c7 | OPEN-BET (both novel) | Wang arXiv:2603.07280: R_F2⟨3,3,3⟩ ≥ 20, silent on subtensors |
| c8 | SURVIVOR (both) | none; 200-sample evidence, full 211-orbit sweep not run |
| c9 | SURVIVOR (both) | none; exhaustive over all 21 orbits of ⟨2,2,2⟩/F₂ |
| c10a | LIKELY-KNOWN | mod-3 orbit counting; BILR orbit structures |
| c10b | SURVIVOR (both) | none; 2 data points, checkable vs known cyclic rank-23s |

Empirical pattern found en route: Strassen mod 2's unique
orbit-size-1 triad and Smirnov-1's C₃-fixed triad are both
the identity triad. Standing disposition (recommended,
awaiting USER): c8/c9 feed the orbit-reduced interference
search as feasibility pruning; c10b is a cheap Sage check;
c6/c7 are the search itself.

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
`Proofs/Xlib/STPPWreath.lean`; (b) corrected stale claim —
IsoclinismInvariants and CharDegrees are sorry-free, and
WreathNg.lean's docstring saying otherwise is stale;
(c) heuristic: pick the isoclinism representative before
wreath amplification.

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

## census-derived conjectures (2026-07-12)

C-numbers refer to the retired `orch-Cj-census-final.md`
(gnu/decomposability census of small-group orders).

C4/C5, order-256 desert/burst id-ranges — KILLED,
catalogue artifact. SmallGroups id order at 256 is
construction order (rank of G/Φ(G), then p-class,
Newman-O'Brien descendant traversal). O'Brien, "The groups
of order 256," J. Algebra 143 (1991). Surviving content:
decomposability rates by rank and p-class are unexamined.

C1/C14, p-group desert — FOLKLORE-DERIVABLE. "Almost all
p-groups are directly indecomposable" is a one-line
Higman-Sims corollary that no paper states. Caveat: at
n ≤ 9 the asymptotic regime has not set in; do not cite
Higman-Sims as proving our range. Methodological precedent:
Helleloid-Martin math/0602039.

C10/C11, 2^a·3 crossover at a=7 and C₃-peel growth —
APPARENTLY NOVEL. No literature studies decomposability
rates within the family 2^a·p. Nearest: Erdos-Palfy,
Discrete Math. 200 (1999); Eick-Moede 2018; OEIS A094448 /
A090751 hold raw counts, no rate analysis.

Pf3, rho_0(A×G) = rho_0(G) — ADJACENT; upper bound novel.
The ≥ direction is Murthy arXiv:0709.1223 Lem 4.8 plus
rho_0 = 1 for abelian. The ≤ direction is stated nowhere
across eight checked sources (0709.1223, 2602.15796,
2512.16730, 1107.5969, 1107.5973, math/0511460,
math/0307321, 2204.03826).

Pl4 rigidity lemma (no single-fiber commutative CC of rank
exactly n² realizes ⟨n,n,n⟩) — ADJACENT. Stated nowhere
but implicit in CU13 arXiv:1207.6528 (Conj 5.7 targets
n^(2+o(1)); Example 4.6 is the multi-fiber realization);
a 3-line counting argument from CU13's definitions. Cite
as "implicit in CU13, made explicit."

Pl4 rank ceiling r ≤ (N + [N_G(H):H])/2 — ADJACENT.
Both ingredients textbook folklore; the inequality is
stated nowhere found in ~15 sweeps (Cameron Math. Z. 124
bounds by deeper methods). Honest weight:
folklore-made-explicit, not a new theorem; the new content
is the cross-context link to BCGPU arXiv:2204.03826
Thm 3.6's normalizer parameter. Cite the link, not the
lemma. Follow-ons queued and never run: OEIS
cross-check/extension of A094448/A090751; rate-by-rank
reframing of C4/C5.

## per-result novelty sheets (July 2026)

One entry per retired sheet. "First recorded proof" claims
are all [A]-grade and were the exact claim class with a
falsification history — re-fetch before citing.

BooleanRankGeneric (`BooleanRankGeneric.lean`) —
NO-REFERENCE-FOUND; first recorded proof of the A354741
empirical comment (a.a.s. full Boolean row rank). Nearest:
Pourmoradnasseri-Theis arXiv:1611.08400 (Schein rank, a
different notion). Sheet's own framing: do not present as
novel; ingredients standard. Unchecked: Kim 1982 book,
Devadze 1968.

CapsetSliceRank (`CapsetSliceRank.lean`) — LIKELY-KNOWN,
first-recorded-complete-proof candidate for A236397(n) ≤
A090245(n) (Peebles 2013 poster Thm 4, stated there with
no proof). Peebles' HMC thesis likely has a proof but the
PDF 404s — unresolved retrieval, adjudicate before any
first-proof claim. Not subsumed by Naslund-Sawin
arXiv:1606.09575.

ComplexityPatterns (`ComplexityPatterns.lean`) — mixed:
C3 (a(n)=n iff n≤5 for A005520) NO-REFERENCE-FOUND; C1/C2
LIKELY-KNOWN (implicit in Iraids et al. arXiv:1203.6462);
C4/C5/C6 KNOWN-CLASSICAL (Guy UPINT F26; OEIS data). No
proof-assistant formalization of integer complexity found
in Lean, Coq, or Isabelle.

ErdosCovering (`Proofs/Proofs/ErdosCovering/*`) — the
sheet's surviving claims: STANDS — first machine-checked
proof of Erdos 1950 (odd non-2^k+p); first formalization
of the general covering-system fixed-divisor criterion;
first formalization of A089654. STANDS-NARROW — sorry-free
A039669 completeness to 10^9 (DeepMind's window is
sorry'd); Riesel 509203 first in Lean (ACL2 had it,
Cowles-Gamboa arXiv:1110.4671); 78557 without
native_decide. DEAD (retracted): first A039669 statement
(DeepMind `1142.lean`); first covering-system definition
(DeepMind `CoveringSystem.lean`); first proof-level
covering-system use (plby `Erdos275.lean`, sorry-free);
Nash's primitive-root sieve novelty (Nash 2000,
primepuzzles.net, states the identical reduction). The
sheet's §4 documents six falsified search claims; the
post-mortem lives with the triage-publishability shard.

FubiniMod (`FubiniMod.lean`) — KNOWN-CLASSICAL for k=2,4,16
(Poonen, Fibonacci Q. 26(1) 1988 gives exact periods mod
every s; Barsky). General Bala totient-period conjecture:
LIKELY-KNOWN, first recorded proof as a stated theorem;
sorry discharged same day (commit c37e31e). OEIS
"Conjecture" labels at A000670/A354242/A002050 still live.

GroupCountE2 — gnu(p²)=2 math KNOWN-CLASSICAL (Netto
1882); formalization of the classification-to-count step
claimed NEW. Group-deficient primes: trivial;
"group-perfect/deficient/abundant" vocabulary exists only
in OEIS A090052's name. A046057(1)=1, A046057(2)=4:
LIKELY-KNOWN as data (Conway-Dietrich-O'Brien 2008), no
located source proves minimality; formal proof claimed
first.

HamiltonBallinger (`HamiltonBallinger.lean`) — H1 (master
equality for the {1,+,^} norm, A348262) and H2 (power
subadditivity): NO-REFERENCE-FOUND — the norm is simply
unstudied; sheet flags this as unrecorded-because-
unstudied, of modest significance. H3 incomparability
witnesses LIKELY-KNOWN from OEIS values. H4 finiteness
sorry correctly attributed to the Hamilton-Ballinger 2022
A005245 comment (open).

MaxIrrepDegree (`Proofs/GroupTPP/MaxIrrepDegree.lean`) —
LIKELY-KNOWN; a(m)a(n) ≤ a(mn) for A060938 is a one-line
corollary of Irr(G×H) (Serre Thm 10, Isaacs Thm 4.21).
Earliest explicit statement: Eric M. Schmidt's 2012 OEIS
comment, no proof. Claimed first recorded proof.
Unchecked: Isaacs/Serre exercises, Berkovich-Zhmud, Gluck.

PalindromeRows (`PalindromeRows.lean`) — LIKELY-KNOWN,
first recorded proof of the odd case of A267632 row
palindromicity. Hadjicostas 2019 comments collapse it to
A047996, whose symmetry is folklore (Barnes 1959,
Ramanathan 1944 prove the counting formula, never
palindromicity). The 2^j case remains the file's open
sorry.

Practical (`Practical.lean`) — proved content
KNOWN-CLASSICAL (Srinivasan 1948, Stewart 1954, Sierpinski
1955). "First practical-number formalization in any proof
assistant" RETRACTED 2026-07-31: formal-conjectures has
`Nat.IsPractical` (2026-03-15) and a proved
`factorial_isPractical`. Surviving [A] first-claims:
Stewart criterion both directions, sigma-characterization,
weak Coleman, Coleman-conjecture archive (A007691 comment,
Jaycob Coleman 2013), and the apparently-unrecorded
OPN-hardness reduction (Coleman conjecture implies no odd
perfect number). Definitional delta vs upstream: their
`IsPractical 0` holds; agreement proved for 0 < n.

QuasilogChainGap (`Proofs/NumberComplexity/
QuasilogChainGap.lean`) — LIKELY-KNOWN; l(n) ≤ quasilog(n)
(A076142 nonnegative) is Scholz 1937 / Brauer 1939
subadditivity plus a trivial step; no source states the
comparison to A064097. Claimed first recorded proof of the
combined statement. Unchecked: Knuth TAOCP §4.6.3
exercises, Subbarao 1989, Thurber 1973.

Quasilog (`Quasilog.lean`) — LIKELY-KNOWN, first recorded
proof of R. G. Wilson v's 2013 "Conjecture" label on
A064097 (floor(log₂ n) ≤ a(n)); ten-line induction,
folklore-grade. The 2.5·log upper bound (Cloitre) remains
the open sorry.

SlizkovDoubling (`SlizkovDoubling.lean`) — no novelty
claim; everything KNOWN-CLASSICAL (Knuth TAOCP §4.6.3;
A003313 b-file; Thurber 1976). A230528 question remains
open; first k with l(2k)=l(k) is k=191.

StanleyDigits (`StanleyDigits.lean`) — greedy 3-AP-free =
base-3 digits KNOWN-CLASSICAL (Erdos-Turan 1936,
Odlyzko-Stanley 1978). Four cross-sequence identities
(A003278/A191107/A055246): LIKELY-KNOWN, stale OEIS
"Conjecture" labels, trivially implied by PARI closed
forms — de-facto-known, formally unproved.

StepWalk (`Proofs/NumberComplexity/StepWalk.lean`) —
NO-REFERENCE-FOUND; proof of Rebert's 2025 A014701
conjecture (keep-or-double walk characterization). Sheet
asserts the proof is not a one-line corollary — nontrivial
walk induction with a scalar potential invariant. Nearest
non-hit: Gruber-Holzer MFCS 2021 Lem 8. Strongest novelty
candidate of the seventeen sheets.

Submult — LIKELY-KNOWN; gnu(m)gnu(n) ≤ gnu(mn) for coprime
m,n is stated as "clear" without proof in Ren
arXiv:2405.04794 (2024, line 182). Folklore with no
standalone statement, attribution, or formal proof
located. The general (non-coprime) Lopes inequality is an
open conjecture (A000001 comment 2024-04-21). Unchecked:
Blackburn-Neumann-Venkataraman full text (paywalled).

ZumkellerTauSigma (`Proofs/Enumerative/
ZumkellerTauSigma.lean`) — NO-REFERENCE-FOUND, both for
the blocking lemma (L) (no odd perfect N with
(tau(N)/2)·N square) and for the A083207-to-OPN
connection; `not_isSquare_half_sigma_zero_mul_of_perfect`.
Sweep confirms the in-file hardness claim: known OPN
structure theory does not reach the cross-term. Second
strongest novelty candidate.

## erdos burndown ledgers

Four ledgers scored erdosproblems.com problems per the
0-5 rubric above: batch 1 = problems 2-440, batch 2 =
441-823, batch 3 = 825-1217 (116 entries each, solved
problems); special = 53 unsolved problems with status in
{falsifiable, decidable, verifiable, not disprovable, not
provable, independent}. 401 entries total. Recorded
distribution: score 0: 9, 1: 133, 2: 160, 3: 67, 4: 29,
5: 3 (recounted from the four sweep docs' ## header lines;
consistent with the 9-entry ZFC-independent list).

Score ≤ 2 entries are deliberately dropped here: their
content (who resolved what, with what machinery) is the
erdosproblems.com page itself, quoted by the sweep, and
is recoverable by re-fetching. What is not recoverable is
the scoring judgment, preserved below for scores ≥ 3.

Score 5: 152 (already formalized by DeepMind — no
contribution remains); 1058 (Luca 2001, Math. Comp., 4pp);
special 742 (Furedi 1992, large n, 18pp J. Graph Theory).

Score 4, batch 1: 175 (Granville-Ramare 1996; Velammal
1995; Kummer + Bertrand, Mathlib-ready), 245 (Mann 1960;
needs character theory), 384 (Ecklund 1969, 4pp; Bertrand
in Mathlib; top pick), 402 (Balasubramanian-Soundararajan
1996; Szegedy 1986, 5pp; Hall's theorem in Mathlib; top
pick), 440 (Tao comment proof, ~5 lines; ledger upgraded
it 3→4; top pick).

Score 4, batch 2: 542 (Schinzel-Szekeres 1959, ~8pp;
witness {2,3,5}; top pick), 603 (Erdos-Rado; external
formalization KitaKen1/erdos603-lean), 631 (Thomassen
1994, 2pp induction; needs planar infra; top pick), 632
(Dvorak-Hu-Sereni 2019; top pick if graph small), 702
(Frankl 1977; shifting; top pick), 715 (Tashkinov 1982;
Alon-Friedland-Kalai 1984, 1pp; GF(2) linear algebra; top
pick), 771 (Alon-Freiman 1988, ~10pp; top pick), 781
(Alon-Spencer 1989 "Ascending waves"; top pick).

Score 4, batch 3: 842 (Fleischner-Stiebitz 1992,
elementary), 880 (Hegyvari-Hennecart-Plagne 2007; k=2
trivial, k≥3 counterexample), 916 (Thomassen 1974, 6pp),
922 (Folkman 1970, elementary induction), 1025 (Spencer
1972), 1027 (proof is a KoishiChan comment-section post —
verify before use), 1050 (Borwein 1991, 7pp, Pade
approximants; top pick), 1140 (Epure-Gica 2010; finite
list {2,5,7,13,31,61,181,199}), 1213 (Hegyvari 1986;
pigeonhole; top pick), 1216 (Reid-Parker 1970;
native_decide feasible; top pick).

Score 4, special (unsolved, computational targets): 307,
364, 366 (consecutive powerful-number searches, OEIS
A060355; feasible in minutes to 10^12), 398
(Brocard-Ramanujan, A146968, verified to 10^9), 617
(Erdos-Gyarfas r=3 formalizable; top pick), 647 (GBP25
prize; only n=24 known; sieve to 10^9 feasible; top
pick), 835 (Ma-Tang; k=3 decidable).

Score 3, kept as number lists (prior art recoverable from
the problem pages; the score is the preserved judgment):
batch 1 — 35, 58, 73, 210, 216, 266, 362, 381, 438;
batch 2 — 471, 494, 504, 518, 534, 570, 577, 608, 630,
673, 703, 720, 735, 745, 758, 763, 767, 780, 795, 800,
806, 816; batch 3 — 884, 895, 899, 903, 915, 924, 948,
984, 994, 998, 1006, 1009, 1010, 1012, 1018, 1078, 1079,
1105, 1114, 1147, 1187, 1202; special — 19, 23, 106, 242,
287, 475, 488, 547, 551, 556, 699, 779, 993.

External formalizations already existing (do not re-do):
152 (DeepMind), 441 (AxiomProver/AxiomMath 2026), 603
(KitaKen1/erdos603-lean), 884 (github.com/honicky/
erdos884), 986 (Bradac 2026), 1187 part-2 counterexample
(KentaKitamura), 948 (Price — claimed, unverified).

Suspect entries needing human adjudication before any
routing: 63 (attribution hedged), 69 (conditional on prime
k-tuples only), 405 and 559 and 690 and 777 and 895
(resolution/status unclear from page), 480
(misformalization noted in formal-conjectures statement),
518 (attribution unclear), 960 and 987 and 1091
(resolution credited to "APSSV26b", an unpublished
internal OpenAI-model preprint), 1027 (comment-section
proof), 1077 (problem misstated), 1114 (proof in
Hungarian, Mat. Lapok), 1123 (rests on Erdos-Ulam "lost
proof"), 548 (Ajtai-Komlos-Simonovits-Szemeredi proof
unpublished, 200+ pp), 699 (statement subtle, sweep flags
re-read). ZFC-independent / score 0 (not formal targets):
474, 736, 739, 1119, 1127, 1154, 1169, 1174, 1176.

## file dispositions

- .tasks/f5exp/docs/orch-novelty-census.md — extracted: all six census verdicts, follow-on queue, and vocabulary preserved above.
- .tasks/f5exp/docs/sweep-glossary.md — extracted: pair definitions, verdict labels, P1-P3 tables, salvage notes, standing decisions preserved above.
- .tasks/f5exp/docs/sweep-novelty-P1-corpus.md — extracted: per-claim verdicts and citations merged into the P1 table; line-number search logs dropped as re-derivable.
- .tasks/f5exp/docs/sweep-novelty-P1-web.md — extracted: same merge; corpus-vs-web disagreements recorded above.
- .tasks/f5exp/docs/sweep-novelty-P2-corpus.md — extracted: merged into the P2 table.
- .tasks/f5exp/docs/sweep-novelty-P2-web.md — extracted: merged into the P2 table.
- .tasks/f5exp/docs/sweep-novelty-P3-corpus.md — extracted: merged into the P3 table; NOT-IN-CORPUS weakness noted.
- .tasks/f5exp/docs/sweep-novelty-P3-web.md — extracted: merged into the P3 table.
- .tasks/f5exp/docs/sweep-rubric.md — extracted: 0-5 score definitions and ground rules restated above.
- .tasks/f5exp/docs/sweep-solved-1.md — extracted: scores >= 3, flags, and distribution kept; score <= 2 dropped, recoverable from erdosproblems.com.
- .tasks/f5exp/docs/sweep-solved-2.md — extracted: same policy.
- .tasks/f5exp/docs/sweep-solved-3.md — extracted: same policy.
- .tasks/f5exp/docs/sweep-special.md — extracted: same policy plus status legend and ZFC-independent list.
- .tasks/main/docs/novelty-BooleanRankGeneric.md — extracted: verdict, nearest prior art, unchecked sources preserved.
- .tasks/main/docs/novelty-CapsetSliceRank.md — extracted: verdict and the unresolved Peebles-thesis retrieval preserved.
- .tasks/main/docs/novelty-ComplexityPatterns.md — extracted: per-claim C1-C6 verdicts preserved.
- .tasks/main/docs/novelty-ErdosCovering.md — extracted: STANDS/STANDS-NARROW/DEAD ledger preserved; falsification post-mortem deferred to the triage shard.
- .tasks/main/docs/novelty-FubiniMod.md — extracted: verdicts incl. same-day addendum preserved.
- .tasks/main/docs/novelty-GroupCountE2.md — extracted: three-part verdict preserved.
- .tasks/main/docs/novelty-HamiltonBallinger.md — extracted: H1-H4 verdicts preserved.
- .tasks/main/docs/novelty-MaxIrrepDegree.md — extracted: verdict, Schmidt-comment provenance, unchecked list preserved.
- .tasks/main/docs/novelty-PalindromeRows.md — extracted: verdict and open 2^j sorry noted.
- .tasks/main/docs/novelty-Practical.md — extracted: retraction and surviving first-claims preserved.
- .tasks/main/docs/novelty-QuasilogChainGap.md — extracted: verdict and unchecked Knuth sources preserved.
- .tasks/main/docs/novelty-Quasilog.md — extracted: verdict and open Cloitre sorry noted.
- .tasks/main/docs/novelty-SlizkovDoubling.md — extracted: no-novelty verdict preserved.
- .tasks/main/docs/novelty-StanleyDigits.md — extracted: stale-label verdicts preserved.
- .tasks/main/docs/novelty-StepWalk.md — extracted: strongest novelty verdict and search scope preserved.
- .tasks/main/docs/novelty-Submult.md — extracted: verdict and Ren line-182 pointer preserved.
- .tasks/main/docs/novelty-ZumkellerTauSigma.md — extracted: both NO-REFERENCE-FOUND verdicts and hardness confirmation preserved.
