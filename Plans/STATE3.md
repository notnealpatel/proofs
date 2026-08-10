# STATE3 — live queue and planning deltas

Distilled 2026-08-10 from `.tasks/f5exp/docs` planning docs
and the 25 non-done task cards, which this file supersedes.
Shard 3 of the doc-retirement campaign: live queue,
orientation, plans and critiques, retro. Facts verified
against the committed tree are tagged [M]; doc-asserted
facts [A]; opinions [O].

## context

The f5exp campaign is the matrix-multiplication / omega
program (Cohn–Umans TPP, slice rank, wreath products).
`Plans/PLAN.md` — the state of record for the OEIS/Erdős/
covering arcs — mentions this program exactly once, as
"Deliberately out of blog scope", and carries none of its
dispatch state. The entire queue below existed only in
`.tasks`. [M]

The Lean estate is safe: branch `f5exp` is fully merged
into `main` (merge `13cc0ab`, 0 ahead / 19 behind), and
the `Xlib` library was renamed `Proofs/GroupTPP`. [M]
All three campaign manuscripts survive committed under
`Documents/` (`abelian-factor-refutation.md`,
`exotic-groups-for-mm.md`, `four-way-chain.md`, re-homed
at `7e2a9e2`). [M]

Exactly three genuine sorries remain in the program: [M]

- `Proofs/GroupTPP/STPPWreath.lean:389` —
  `stpp_capacity_le` (general G; Fi1's target)
- `Proofs/GroupTPP/STPPWreath.lean:939` —
  `stpp_capacity_le_of_wreath` (multinomial; Mn1's target)
- `Proofs/BilinearComplexity/PeelingSupport.lean:496` —
  `cover_outmass_even` (double-counting parity; used at
  :642; Ad1/Pl28 territory)

## live cards

25 cards, status ready/active as of 2026-07-29. Deps in
parentheses are done cards. [M for status/deps frontmatter]

| card | agent | deps | goal |
|------|-------|------|------|
| Mn1 | postdoc | (Pl21) | close `stpp_capacity_le_of_wreath` :939, relax `[CommGroup G]` → `[Group G]`; conclusion frozen |
| Cv1 | consumer | (Pl21) | price FDRep↔charDegrees bridges; deliver `mathlib-clifford-coverage-v2`; feeds Hu18 Q2 |
| Ng1 | postdoc | (Pl22, Ad1) | WreathNg cleanup: unpin F3 suspect, irrep→charDegrees bridge, BCGPU barrier corollary |
| Tb1 | postdoc | (Pl22, Ad1) | new `BilinearComplexity/STPPBarrierStatements.lean`: TricoloredSumFree, K-TCSF kernel, statements only |
| Pd1 | postdoc | (Im14, Im15) | K8 untwistable-member bound: test-first against new data, then prove or record obstruction |
| Im6 | implementer | (Pf3, Im2) | encode the Pf3 refutation as MUST-NOT-REJECT sieve anchor (counterexample branch) |
| Im16 | implementer | (Im15) | materialize metered sweep programs for PSL(2,17)/S_7/A_8; pricing input for Hu11; do not run |
| Im17 | implementer | Im16 | PSL(2,27) p=3 hunt phase-1 screen; verdict HUNT-LIVE/DEAD/COLD for Hu12 |
| Hu9 | human | (Ma1) | sign off `abelian-factor-refutation` for circulation; terminal node, active |
| Hu11 | human | (Im15), Im16 | metered gate: approve wave-2 sweeps PSL(2,17)/S_7/A_8 |
| Hu12 | human | Im17 | metered gate: approve PSL(2,27) phase-2 exact beta_0 (~2.5–3 h export) |
| Hu15 | human | (Pl22) | gate Pl28 on: Tb1/B1 landed sorry-free AND J(q) priced and accepted; active |
| Hu16 | human | (Hu13) | revive-or-kill Pl23 remnant; recorded verdict 2026-07-29: KEEP PARKED |
| Hu17 | human | (Hu13) | Programs/ audit gate before Pl26; recorded verdict 2026-07-29: KEEP PARKED |
| Hu18 | human | Mn1, Cv1 | mid-campaign re-gate: confirm Clifford spend (~3–8k lines) + irrep-indexing choice (Q2) |
| Hu19 | human | Fi1 | shape-2 reporting gate: "CKSU theorem:asi in Lean for general finite groups" headline |
| Cl1 | prover | Hu18 | induced-rep dimension formula `dim Ind = [G:K]·dim V` in new `GroupTPP/InducedDimension.lean` |
| Cl2 | prover | Cl1 | irrep-indexing layer, `Irr(H^n) = Irr(H)^n`, S_n orbits; highest-risk card |
| Cl3 | prover | Cl2 | Young-subgroup extension + induced-degree formula; heaviest wave (1500–3500 lines) |
| Cl4 | prover | Cl3 | irreducibility + exhaustion via sum-of-squares; charDegrees multiset identity |
| Cl5 | postdoc | Cl4 | restore `[Group H]` on `wreath_charDegree_bound` (:510); abelian proof → `_of_comm` |
| Fi1 | postdoc | Cl5 | close :385/:389 by instantiation; trust sweep; GroupTPP sorry-free |
| Pl23 | planner | Hu16 | post-sweep triage remnant (frozen; salvage residue listed below) |
| Pl26 | planner | Hu17 | chow_sm3: pin exact small Chow ranks over F_2 for tr(X^3) and det(X) (frozen) |
| Pl28 | planner | Hu15 | plan BCCGNSU Theorem B (slice-rank barrier) formalization vs `SimultaneousTPP` |

DAG shape: dispatchable roots are Mn1, Cv1, Ng1, Tb1,
Pd1, Im6, Im16 plus human gates Hu9/Hu15 (active) and
Hu16/Hu17 (parked). Critical chain is Cv1+Mn1 → Hu18 →
Cl1→Cl2→Cl3→Cl4→Cl5 → Fi1 → Hu19 (nine nodes). Side
chains: Im16 → Hu11 and Im16 → Im17 → Hu12. Frozen
branches: Hu15→Pl28, Hu16→Pl23, Hu17→Pl26. Tb1 gates
Pl28 only through Hu15's conditions, not a DAG edge. [A]

Cheapest-first ordering per the critiques: Ng1 ("cheapest
positive-value item on the whole board"), then Mn1 + Cv1
in parallel, then the Hu18 decision. [A]

Doc-hygiene note: Pl23 was `ready` with body-level inputs
(`Im16.md`, `Im17.md`, `Pd1-untwistable-bound.md`) that
never existed — the critique called this the top dispatch
risk. With the card system retired the risk dies, but any
revival must restore deps [Pd1, Hu11, Hu12] first. [A]

## binding specs rescued from the critiques

Live cards cite the critique docs as binding specs; the
load-bearing conclusions are recorded here so the cards
stay executable after deletion.

Pl28 / Tb1 (critique-pl22 §S): the STPP notion MUST be
`GroupTPP.STPPWreath.SimultaneousTPP` (STPPWreath.lean:168)
via a minimal additive-image bridge — no fresh STPP
definition, or Theorem B gets proved about the wrong
object. Primary kernel is K-TCSF (BCCGNSU Theorem A
verbatim) with the explicit constant
`ε = (1/2)·log((2/3)·2^(2/3))` ≈ 0.02831; Theorem B
itself stays prose-only (no `∃ ε_ℓ` compactness form).
The `thm:main` reduction produces a BORDER tricolored
sum-free set; `lem:unborder` un-borders it. Slice rank is
not submultiplicative (arXiv:1705.09379); only
`sr(F⊗G) ≤ sr(F)·R(G)` and `sr(F⊗G) ≤ sr(F)·max dim` are
sound — reject any card stating the strong form. J(q) is
finite Chernoff analysis, not measure theory, repriced
800–1500 lines; realistic Track S total 4000–5500 lines.
Lucas is in Mathlib (`Mathlib.Data.Nat.Choose.Lucas`,
`lucas_theorem`); seam5's `Nat.lucas_prime_dvd` is a
phantom name, and seam5's claim that `SimultaneousTPP`
does not exist is false. Cite the paper by LaTeX label +
tex line from
`References/GroupTPP/arXiv-1605-06702/stpp-bound.tex`. [A]

Mn1 (critique-pl21): the CKSU "M-th roots, N → ∞"
handwave resolves through the landed engine
`le_of_pow_le_poly_mul_pow`
(`GroupTPP/GeomArithInequality.lean:71`) and
`sum_le_of_multinomial_prod_pow_le` (:123). This target
stumped one prior prover dispatch (the Ca1 blocker). [A]
Warning: Mn1's fuller math spec lived in
`Ca1-blocker-multinomial-assembly.md` and
`formalization-ledger.md:1842ff`, both outside this
shard — if no other shard rescued them, Mn1 starts from
the two lemma names above.

Aw1 dead-end record (from Pl19-burndown-pricing.md
lines 545–1218): `abelian_wreath_family_tendsto_two` for
general abelian H with FIXED H and n→∞ is NOT provable
via the CU wreath cocycle construction alone. The cocycle
u=(1,...,n) requires n distinct elements in H, forcing
|H| ≥ 2n, which fails for fixed H as n grows; for
H = Z/2Z the construction degenerates (H_2 = H_1). Five
alternative routes were tried: (a) generalized cocycle —
fails for |H| < 2n; (b) reduction to cyclic via
embedding — pseudo-exponent transfer unclear; (c) direct
computation with {(π,0)} subgroup — gives α→3, not 2;
(d) STPP capacity with fixed H — n is bounded by
|H|^{ω/(ω−1)}, cannot grow; (e) power-group H^k trick —
the theorem statement fixes H, not H^k. The capacity
route through `stpp_capacity_le` is the only viable
path. [A]

Clifford wave (critique-pl21): the original Mathlib
absence list was partly wrong — Frobenius reciprocity
(`indResHomEquiv`, `indResAdjunction`) and orthogonality
(`FDRep.char_orthonormal`) EXIST; the two absences that
hold are the induced-rep dimension formula and Clifford
theory proper. Exhaustion is free via sum-of-squares;
per-rep irreducibility is owed. The general n!-carrier
lemma is already supplied by Df1
(`stpp_to_tpp_wreath_card [Group H]`, STPPWreath.lean:892).
Anchor every new def on H = C_2, n = 2, G = D_4. Hu8-1c
ruled general-H back in as a target; Cl5 must not
re-hedge. [A]

Ng1 (critique-pl22 §N): the F3 answer-pinned suspect
`minNontrivIrrepDim_wreathS2_eq_two_of_ne_zero`
(WreathNg.lean:406–413, unused `¬IsPerfect` hypothesis)
must be replaced by the unconditional theorem; 13 prose
"sorry" mentions rot in a sorry-free file; `Sager/`
pointers at :21/:83 are dead. The corollary target is
`bcgpu_cor_3_4_kernel` (BCGPUBarrier.lean:260–276);
there is no decl named `bcgpu_cor_3_4`. Lower bound
(tuple-of-partitions degree formula) is wreath Clifford
theory — unpriceable now; upper-bound-only. [A]

Pl26 (critique-pl26): both headline windows were slack —
monomial counts give ChowRank(det3) ≤ 6 and
ChowRank(F3) ≤ 11, beating the Ryser-based edges;
corrected windows det3 ∈ [3,6], F3 ∈ [9−dmax(F3), 11].
The lower-bound floor direction was backwards: the
substitution bound is 9 − dmax, so floors need dmax
UPPER bounds, which nothing establishes (dmax(F3) ≤ 6 is
asserted with zero evidence). A cheap deterministic
dmax run (critique Appendix B, pure Python) settles both
gaps and was NEVER EXECUTED — the script is inside the
critique file and dies with it. SAT lower bounds require
DRAT/LRAT proofs + a verified checker (drat-trim /
cake_lpr), XOR-aware solver; HKS precedent is
SAT-direction, not UNSAT. det3 stabilizer ≥ 56448. Nine
inline EXACT claims re-verified (Appendix A); Waring rank
of F3 over F_2 is infinite. Novelty: no published
Chow/product rank of tr(X^k) in any characteristic.
Seed scripts survive at `Programs/CHILO/{verify_basics,
task1_dmax,task1_fast,task1_minimal}.sage`. [M paths, A
verdicts]

Pl23 salvage residue (critique-pl23): the remnant's
firing condition was vacuous (K5c killed, inputs never
existed). Worth keeping: PGL(2,9) is a FOURTH violating
group (176 configs); K12 attained exactly at e = 3/2
(the Murthy-3/2 echo); K7 killed — a novel refutation,
not a novel finding; Cj6 plateau law closes the
compounding question, but only C_2 × A_6 ran an exact
census (C_2 × M_10 / C_2 × S_6 rest on domination
checks — do not launder projection into exact claim).
Two standing doctrines: Hu4's parametric-witness-only
elevation rule, and shape-2-Hu-gate before treating
anything as reportable. [A]

## metered-run pricing and predictions

The Hu11/Hu12 gates need the Pl18 triage numbers.
Lattice+Cayley cost: PSL(2,13) ~99 s, PSL(2,17) ~8.3 m,
S_7 ~35 m, PSL(2,27) ~2.2 h, A_8 ~9.4 h (A_8 exports may
run days at exact semantics; 48,337 subgroups). [A]

Predictions on the line: PSL(2,17) violation predicted
(K11: Sylow_2 = D_16, dim_2 = 2); S_7 tests the
`2(n−1)²/15` closed form (predicts beta_0 = 24192); A_8
tests K5b (predicts 127008). PSL(2,27) is the sole odd-p
discriminator: candidate (Syl_3, Syl_3, Borel) at
σ = 85293; K5c extrapolation predicts beta_0 ≈ 68,796,
so the hunt is live iff the family law holds; a found
p = 3 violation is a shape-2 reportable. Backup targets
PSL(3,3) (5616), PSU(3,3) (6048). Verify the /p
normalization convention before trusting σ. [A]

## dropped-conjecture record (Pl18 fan audit)

The kernel ledger (K1–K16) silently dropped crisp,
falsifiable conjectures; this is the only record: [A]

- K1's formula omits the `max(beta_0, Σ_max)` envelope —
  wrong on slack groups as stated.
- Isomorphic-pair necessity (Cj3-C3, 240/240) and
  monotone trichotomy (Cj3-C4, 7/7): dropped.
- Cj6-C4 (odd primes sterile in padded groups), strictly
  stronger than K6: dropped. Cj7-C7 strong form
  (p = 3 blocked ⇒ tie): lost from K6.
- Blocked-saturation trichotomy (Cj7-C4, 12/12): dropped.
- K10 drops Cj2-C7's directional PGL(2,9) prediction —
  which Im15 then CONFIRMED.
- Im13 count: four confirmed instances, not three.

The scan contract (8 free-rider checks on every census
output) binds Im16/Im17 outputs. [A]

## judgments not otherwise recoverable

Pl15 numerics are recoverable: the committed
`Documents/abelian-factor-refutation.md` carries the
margin table (§4), all five verified kills with explicit
witness generators and verification commands (§5), the
lift law `beta_0(C_p×G) = p·max(beta_0, Σ_max^lift)`
(§5a), and reproducibility (§8). [M] Two analysis pieces
from `Pl15-aside-spec.md` exceed it: the composite-B /
C_4 analysis (composite kernels NOT dominated by the C_p
census; 6 surviving C_4 shapes in A_6 — open math, was
routed to Pl17) and the product-hunt subsumption
argument (the census subsumes product-group search for
the kill direction, eliminating product exports). [A]

Pl4 verdicts: the Gelfand-screen conjecture C2 was
PROMOTED TO THEOREM — N ≥ 4r/3 via a normalizer-quality
/ double-coset counting argument; C1 (N ≥ r + cap2)
remains a conjecture, verified 367/367. `partners_min = r`
recovery means constraint NC2' never binds. [A]

Historical but worth one line each: Sc1 proved the
original fixed-H `abelian_wreath_family_tendsto_two`
statement UNGROUNDED ("CU Prop 11" does not exist; the
(n!)^3 witness is impossible for fixed H) — the landed
sorry-free form [M] is the Hu8-2a restatement; the
Pl19 chain (Ca1/Le1/Lg1/Sq1/Aw1/Df1) and all 13 minpeak
cards are done [M], so the Pl19/Pl25 queue docs are
superseded. Minpeak guardrails that outlive the docs:
`cmd/minpeak` hardcodes a 9×9×9 spec gap, minpeak* of
<2,2,2> = 10 is EXACT, P(23) = 28 is CONJECTURE. [A]

PeelingSupport residue: the one sorry
(`cover_outmass_even`, :496) blocks on a Finset-indexed
double-sum swap; the rest of the L1–L5 ladder is
complete. [M sorry, A blocker]

Novelty-census verdicts (orientation digest): the Pf3
conjecture rho_0(A×G) = rho_0(G) is ADJACENT — the ≥
direction is Murthy thesis Lemma 4.8 + Thm 2.3, the ≤
direction stated nowhere; C10/C11 (2^a·3 crossover,
C_3-peel growth) graded APPARENTLY NOVEL; the order-256
desert/burst conjectures were killed as SmallGroups
catalogue artifacts. DihedralTPP is claimed as the first
written proof of Hedtke–Murthy Conj 7.5, treating the
unpublished private communication as OPEN per user
decision. [A]

## disagreements with PLAN.md

Erdős #1213: PLAN.md's P1 queue row recommends the
pigeonhole-on-interval-sums route as "Best
payoff-per-effort in the Erdős sweep". The f5exp retro (2026-07-11) records
the sweep's pigeonhole claim as REFUTED and the source
paper inaccessible, deferring the problem. [A both ways]
One of these is wrong; re-derive before dispatching #1213.

f5exp's Erdős kill list is absent from PLAN.md's
do-not-re-mine section: #1216 (the disproof quantifies
over ~2^91 tournaments — no feasible certificate), #742,
#835, #617 (native_decide search spaces infeasible on
audit), #1027 (martingale proof), #402 (already
formalized elsewhere). PLAN.md only lists #387/#937/#851
and the A005820/A075099 drops. [A] Worth merging into
PLAN.md's cross-cutting notes.

No other conflicts: the two documents cover disjoint
programs, and the f5exp round-2 deferred pool (771, 702,
922, 916, 842, 631, 781, 245) is consistent with
PLAN.md's open queue. [M]

## process residue (retro)

Most retro lessons are already doctrine (close-Pl-early,
computational-dispatch library survey, health-consumer
protocol). Unadopted residue at time of writing: the
quota-embargo rules were never promoted into standing
doctrine, the planner agent prompt reportedly still said
close-at-end, and the "state the known characterization
before brute-forcing" line was queued but unverified.
With the card system retired these are moot unless the
orchestration style returns. [A]

## adjudication items for the USER

1. The #1213 route contradiction above.
2. critique-pl26's Appendix B dmax script (cheap, pure
   Python, settles both Pl26 floors) was never run and is
   deleted with the critique. Re-derive from the C2
   description here if Pl26 revives.
3. Mn1's detailed math spec (`Ca1-blocker-*.md`,
   ledger :1842ff) is outside this shard; confirm another
   shard rescued it before dispatching Mn1.
4. Hu9 (manuscript circulation sign-off) is the only
   zero-cost open human action; the manuscript it gates
   is committed.

## File dispositions

- .tasks/f5exp/docs/critique-pl21.md — extracted: Clifford-wave corrections, Mathlib absence re-check, pricing captured above
- .tasks/f5exp/docs/critique-pl22.md — extracted: binding spec for Pl28/Tb1/Ng1 (§S/§N) captured above
- .tasks/f5exp/docs/critique-pl23.md — extracted: split-and-shelve verdict, salvage residue, doctrines captured above
- .tasks/f5exp/docs/critique-pl26.md — extracted: corrected windows, direction error, SAT/DRAT rules captured; Appendix B script lost (adjudication 2)
- .tasks/f5exp/docs/orient-erdos-nodes.md — drop: describes five landed sorry-free files recoverable from the committed tree
- .tasks/f5exp/docs/orient-frontier.md — drop: 2026-07-18 frontier fully superseded by the later cards (Wr1..Aw1 chain all done)
- .tasks/f5exp/docs/orient-impl-conjectures.md — extracted: novelty-census verdicts and Hu-gate map captured above
- .tasks/f5exp/docs/orient-program-and-planning.md — drop: campaign history table recoverable from git and done cards
- .tasks/f5exp/docs/orient-proof-track.md — extracted: Pf3 dead-end status, HM 7.5 first-proof claim, bilinear gaps captured
- .tasks/f5exp/docs/orient-references.md — drop: catalog of ./References which persists on disk; classification re-derivable
- .tasks/f5exp/docs/Pl14-fg1-cascade.md — drop: forge program design; source lives in Scratch/GroupSieve; step completed
- .tasks/f5exp/docs/Pl14-fg2-features.md — drop: forge program design; formulas live in program source
- .tasks/f5exp/docs/Pl14-fg3-rho0.md — drop: forge program design; calibration reproducible
- .tasks/f5exp/docs/Pl14-fg4-gelfand.md — drop: forge program design; verdict schema embedded in program
- .tasks/f5exp/docs/Pl14-fg5-lemma.md — drop: validation table reproducible via the program's --toy mode
- .tasks/f5exp/docs/Pl14-review.md — drop: code-review fixes all landed in source; no open items
- .tasks/f5exp/docs/Pl14-run-commands.md — drop: run manual derivable from program --help/--dry-run
- .tasks/f5exp/docs/Pl15-aside.md — drop: calibration + run commands, all executed; results in committed manuscript
- .tasks/f5exp/docs/Pl15-aside-spec.md — extracted: composite-B/C_4 analysis and product-hunt subsumption captured above
- .tasks/f5exp/docs/Pl15-bside.md — drop: space analysis, all targets executed; anchors in output JSONL + manuscript
- .tasks/f5exp/docs/Pl15-export.md — drop: export pricing; product exports proven unnecessary by the subsumption argument
- .tasks/f5exp/docs/Pl15-kill-witness.md — drop: witnesses, generators, and commands live in committed Documents/abelian-factor-refutation.md §5
- .tasks/f5exp/docs/Pl15-margin.md — drop: margin table and structural analysis live in committed Documents/abelian-factor-refutation.md §4–5a
- .tasks/f5exp/docs/Pl17-manuscript-gaps.md — drop: Ma1 executed; corrections present in the committed manuscript; Hu9 residue captured
- .tasks/f5exp/docs/Pl18-fan-audit.md — extracted: dropped-conjecture record and K1 envelope defect captured above
- .tasks/f5exp/docs/Pl18-triage.md — extracted: pricing table, predictions, scan contract captured above
- .tasks/f5exp/docs/pl19-anchor-distillation.md — drop: Hu8 ruled, chain landed; Sc1 ungrounded-statement finding captured above
- .tasks/f5exp/docs/Pl19-burndown-pricing.md — extracted (partial): Aw1 dead-end analysis rescued above; 5 of 6 targets landed sorry-free; Mn1 route captured above
- .tasks/f5exp/docs/Pl19-clifford-triage.md — drop: decision executed (Ab1/Ab2/Ab3 done); superseded by Hu8-1c reversal
- .tasks/f5exp/docs/Pl19-handoff.md — drop: 2026-07-18 board state fully superseded; plank signatures live in committed Lean
- .tasks/f5exp/docs/Pl21-plan.md — extracted: unexecuted Clifford campaign captured in the live-cards table and spec section
- .tasks/f5exp/docs/Pl22-plan.md — extracted: Ng1/Tb1 charters captured in the live-cards table and spec section
- .tasks/f5exp/docs/Pl24-peeling-support.md — extracted: live cover_outmass_even sorry and blocker captured above
- .tasks/f5exp/docs/Pl25-minpeak-farm.md — extracted: all 13 cards done; surviving guardrails captured above
- .tasks/f5exp/docs/pl2-verdicts.md — drop: burndown complete; 5 Vp2 doctrine sorries visible in committed source
- .tasks/f5exp/docs/Pl4-verdicts.md — extracted: C2 theorem promotion and NC2' redundancy captured above
- .tasks/f5exp/docs/retro-session1.md — extracted: Erdős kill reasons and process residue captured above
- .tasks/f5exp/docs/state-dag-raw.md — drop: 2026-07-17 DAG of done nodes; live DAG reconstructed above from card deps
- .tasks/f5exp/docs/state-survey.md — drop: 2026-07-17 snapshot; sorry counts and manuscript status superseded by tree
- .tasks/f5exp/cards/Cl1.md — extracted: goal, deps, anchor, and spec pointers captured above
- .tasks/f5exp/cards/Cl2.md — extracted: goal, risk grade, and Hu18-Q2 gate captured above
- .tasks/f5exp/cards/Cl3.md — extracted: goal, pricing, CKSU source pointer captured above
- .tasks/f5exp/cards/Cl4.md — extracted: irreducibility routes and free exhaustion captured above
- .tasks/f5exp/cards/Cl5.md — extracted: restore-general-H charter and no-re-hedge rule captured above
- .tasks/f5exp/cards/Cv1.md — extracted: bridge-pricing charter captured above
- .tasks/f5exp/cards/Fi1.md — extracted: instantiation + trust-sweep charter captured above
- .tasks/f5exp/cards/Hu9.md — extracted: sign-off gate captured above (adjudication 4)
- .tasks/f5exp/cards/Hu11.md — extracted: metered gate and per-target pricing captured above
- .tasks/f5exp/cards/Hu12.md — extracted: p=3 hunt gate and σ = 85293 candidate captured above
- .tasks/f5exp/cards/Hu15.md — extracted: Pl28 gate conditions (B1 + J(q) price) captured above
- .tasks/f5exp/cards/Hu16.md — extracted: KEEP PARKED verdict and salvage residue captured above
- .tasks/f5exp/cards/Hu17.md — extracted: KEEP PARKED verdict and Programs/-audit precondition captured above
- .tasks/f5exp/cards/Hu18.md — extracted: Clifford spend re-gate and Q1/Q2 captured above
- .tasks/f5exp/cards/Hu19.md — extracted: reporting-gate headline and novelty-check duty captured above
- .tasks/f5exp/cards/Im6.md — extracted: counterexample-anchor charter captured above
- .tasks/f5exp/cards/Im16.md — extracted: metered-program charter and predictions captured above
- .tasks/f5exp/cards/Im17.md — extracted: phase-1 screen steps, verdict vocabulary, backups captured above
- .tasks/f5exp/cards/Mn1.md — extracted: multinomial-closure charter and engine lemmas captured above (adjudication 3)
- .tasks/f5exp/cards/Ng1.md — extracted: WreathNg repair charter captured above
- .tasks/f5exp/cards/Pd1.md — extracted: K8 test-first charter and output contract captured above
- .tasks/f5exp/cards/Pl23.md — extracted: parked remnant and revival preconditions captured above
- .tasks/f5exp/cards/Pl26.md — extracted: verified facts, campaign lines, corrected windows captured above
- .tasks/f5exp/cards/Pl28.md — extracted: Theorem B charter, guards, and constants captured above
- .tasks/f5exp/cards/Tb1.md — extracted: statement-layer charter, bridge MUST, border caveat captured above
