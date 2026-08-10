# STATE4 — conjecture inventory

Distilled 2026-08-10 from 16 conjecture/probe docs under
`.tasks/f5exp/docs/` (July 2026 campaigns); this file
supersedes them. Tags: [M] = verified against the committed
tree during distillation; [A] = asserted by the source doc,
not re-verified; [O] = inference made here. Nothing below was
re-computed; kill-witnesses are transcribed losslessly because
losing one means redoing the computation.

## context

Everything in this shard belongs to the GroupTPP campaign
(Cohn-Umans group-theoretic matrix multiplication).
beta_0(G) = max |S||T||U| over subgroup triples satisfying the
triple product property; rho_0(G) = beta_0(G)/|G|. Notation
lineage (from the retired literature-grounding doc): Neumann
2011 `beta`, Hedtke 2011 / Hedtke-Murthy 2012 `beta_g`,
Murthy 2025-26 `beta_0`/`rho_0` (arXiv:2512.16730,
arXiv:2602.15796).

Durable anchors already committed, which this file cites
instead of duplicating:

- `Documents/abelian-factor-refutation.md` — the abelian-factor
  conjecture rho_0(A x G) = rho_0(G) and its five kill
  witnesses, plus the lift law (Theorem 1) and 14 exact
  product values. [M]
- `Proofs/GroupTPP/TPPLift.lean` — p=2 lift law, theorem
  `stppCapacity_prod_eq_two_mul_max` [M exists]; sorry-free
  claim is the manuscript's [A].
- `Programs/GroupTPP/survivors-census*.jsonl` — raw census,
  88185 records. [M]
- `Programs/GroupTPP/gelfand-keep-dedup.jsonl` — 307 Gelfand
  pair records. [M] (The source doc cited 367 records from a
  pre-reorg path; the committed file has 307 without the N=8
  rows — data loss or refilter unresolved.)
- `Programs/GroupTPP/forge/` — `aside_census.sage`,
  `verify_kill_any.sage`, `verify_all_combos.sage`,
  `out/pl15_results.jsonl`, six census logs. [M]

Glossary for the Hu2 entries (the defining docs die with this
distillation): a *configuration* is a triple of subgroups of G
with C_p-characters; *k* = number of nontrivially twisted
members; *blocked/eligible* as in the manuscript, sec. 1;
margin(G,p) = Sigma_max^lift(G,p) - beta_0(G); d_p(H) =
dimension of Hom(H, C_p); "violation" = margin > 0, "tie" =
margin 0, "slack" = empty blocked census.

## formalized

- Lift law at p=2: beta_0(C_2 x G) =
  2*max(beta_0(G), Sigma_max^lift(G,2)), with the whole
  sign-liftable framework (charLift, SignKilled, SigmaMaxLift,
  Goursat trichotomy). `Proofs/GroupTPP/TPPLift.lean` [M].
  General p is proved on paper (manuscript Theorem 1) but not
  formalized [A]. No other conjecture in this shard was ever
  formalized — the Hu2/Cj docs claim no Lean artifacts [M,
  grepped by extraction agents].

## settled after drafting (superseded by the lift law)

These Hu2 entries were open when written; the committed
manuscript now proves or decides them. Statuses below are [O]
inferences from `Documents/abelian-factor-refutation.md`.

- Cj2-C1 (two-twist threshold: strict violation forces k>=2):
  proved, manuscript Lemma L / "two-twist threshold".
- Cj2-C2 (eligibility implies realizability): proved;
  "the 8/8 empirical record was not luck; it is a theorem."
- Cj2-C8, Cj5-C1, Cj6-C1 (lift capacity formula / padding
  tightness): proved as Theorem 1 + Corollary 3; exact values
  for all 14 C_2/C_3 products, incl. beta_0(C_2 x A_7) =
  31104.
- Cj6-C3 (padding equality iff margin <= 0): direct corollary
  of the law.
- Cj6-C8 (padding not rho_0-monotone): now unconditional —
  exact beta_0(C_2 x S_6) = 5184 < 6144 = beta_0(C_2 x M_10)
  while rho_0(S_6) > rho_0(M_10).
- Cj7-C6 (ties stable under one pad): equality direction
  follows from the law; beta_0(C_p x G) = p*beta_0(G) on the
  tie locus.
- Odd-prime sterility for p coprime to |G|: proved (coprime
  padding identity). The surviving open part is p dividing
  |G|, below.

## killed

Each entry preserves the counterexample; witnesses marked [M]
live in the committed tree.

- rho_0(A x G) = rho_0(G) (the campaign's central conjecture):
  killed five ways at A = C_2 (S_6, M_10, A_7). Durable in
  `Documents/abelian-factor-refutation.md` sec. 5 with
  generator-level witnesses and verifier commands [M]. Not
  repeated here.
- "Every strict violation is k=3" (Cj2 premise; also the
  operative content of Cj6-C5): killed by the sigma=2560
  families — (C2xD8, C2xD8, C5:C4) in S_6 and
  (QD16, QD16, C5:C4) in M_10 lift ONLY at k=2 (third member
  untwisted) to TPP triples of size 5120 > 2*beta_0. These are
  manuscript kills #4/#5, verified by
  `verify_all_combos.sage` [M]. The literal Cj6-C5 clause
  "all three members 2-twistable" may survive (C5:C4 has
  d_2 >= 1) but its evidence claim "k=2 stratum stops at
  beta_0" is false [O].
- Cj7-C4 initial biconditional "E=B>0 iff margin=0": killed by
  A_7 at p=2 — E=B=24 fully-blocked-eligible yet margin
  +4968. Weakened trichotomy survives (open, below).
- "margin(G,2)>0 iff |Syl_2(G)| >= 16": killed by A_7,
  |Syl_2(A_7)| = 8 (Sage-checked [A]) with margin +4968.
- Cj3-R1 (total twist supply threshold explains violations):
  rejected — S_5 has triples of total supply >= 9 and zero
  blocked configs; M_10 tie configs match S_6's violating
  supply.
- Cj3-R2 (dimension-count solvability of the eligibility
  system): rejected — M_10 has ncolls 7 > D=5, A_7 ncolls
  9 > D=4; systems are rank-deficient yet solvable.
- Cj3-R3 (order or |Sigma| thresholds alone predict): rejected
  — S_6 has 2489 shapes above beta_0 with eligible = blocked
  = 0 on almost all.
- Census C3 (2^a*p bifurcation: p=3 rate >= 0.30, p>=5 <=
  0.25): killed by order 384 = 2^7*3, rate 3766/20154 =
  0.1869. True picture is decay for p=3 (0.500, 0.468, 0.411,
  0.309, 0.187 for a=3..7) vs stable p>=5, with crossover
  between a=6 and 7. Replaced by C10 (open, below).
- Census C2 strict band separation by omega(n): killed by
  order 405 = 3^4*5 at rate 10/11 = 0.909 (omega=2 band cap
  0.60) and orders 280 (0.357), 440 (0.400), 480 (0.458)
  under the omega=3 floor 0.55. Aggregate monotonicity
  survives (open, below).
- "Lamplighter Z_2 wr Z_n has n(G) = 2" (quasirandomness
  probe): killed — n(Z_2 wr Z_n) = smallest prime factor of
  n; e.g. n=3 has character degrees [(1,6),(3,2)] so n(G)=3.
  Checked computationally for n=2..20 [A].
- "Extraspecial p-groups are killed by Tier 2b" (probe claim):
  corrected in the verdict doc — Tier 2b bounds, it does not
  reject individual groups; SmallGroup(32,49) (extraspecial,
  rho_0 = 2) is the campaign's validation anchor.
- beta_0 sequence in OEIS: no match. Tested 108, 256, 972,
  1980, 2304, 2400, 10584 and 30*rho_0 = 54, 64, 81, 90, 96,
  100, 126. Near-matches ruled out: A129003, A204303,
  A109624, A033430, A001597 (2-term or positional
  coincidences). Zero OEIS footprint for TPP / matrix
  multiplication capacity keywords [A]. Worth knowing before
  anyone re-searches.

Also a scale caveat, not a kill: Nikolov-Pyber's index bound
(subgroup of index <= c_0 * n(G)^2) has c_0 ~ 10^10, vacuous
for every group of order <= 512; descriptive lens only at
sieve scale [A].

## open — lift and padding structure (Hu2-Cj2..Cj7)

All computationally supported unless noted; corpus is the
seven pl15 targets (A_5, S_5, A_6, PSL(2,11), M_10, S_6, A_7)
at p in {2,3}, records in
`Programs/GroupTPP/forge/out/pl15_results.jsonl` and the six
census logs [M].

### odd-prime sterility (p dividing |G|)

One family: Cj2-C6, Cj3-C1, Cj4-C1, Cj5-C2, Cj6-C4, Cj7-C7.
Claim: for odd p, Sigma_max^lift(G,p) <= beta_0(G); stronger
(Cj7-C7): a nonempty blocked p=3 census forces margin exactly
0. Evidence: all p=3 census rows have margin <= 0; the two
nonempty ones (A_6, A_7) are exact ties. No p >= 5 data
anywhere; confidence low outside {2,3}.

Related cross-prime claims: Cj4-C8 (the blocked-eligible max
is attained at kernel prime 2), Cj7-C8 (margin(G,3)=0 implies
margin(G,2) >= 0; only 2 data points).

The named threat (Cj4-C7): a p=3 violation needs a
3-twistable X with |X| >= 27 and dim_3(X) >= 2; smallest
plausible target PSL(2,27) with config (C3^3, C3^3, C3^3:C13)
at sigma = 85293. Structural skeleton Sage-checked in a
session scratchpad that was NOT committed [A];
eligibility/blockedness and beta_0(PSL(2,27)) never computed.
This is the single computation most likely to decide the
family.

### anatomy of violations and ties

- Cj2-C3: a member with p not dividing |H/[H,H]| caps the
  config at |Sigma| <= beta_0(G).
- Cj2-C4 (no-gap): nonempty eligible census implies
  Sigma_max >= beta_0. 8/8 rows; S_4 check outstanding.
- Cj2-C5: tie shapes are one-entry p-inflations of honest
  witness shapes; 4/5 clean. Unresolved exception: the A_6
  p=2 tie (6,36,9) does not inflate the recorded witness
  (12,9,9); would need an unrecorded honest witness of orders
  (3,36,9) or (6,18,9).
- Cj2-C7: at p=2, violation iff G contains a proper A_6
  subgroup. 3 positive cases only; low confidence.
- Cj3-C2: every violating config has a twisted member with
  d_2 >= 2; no all-poor config exceeds beta_0 (~1000 blocked
  configs checked).
- Cj3-C3 / Cj4-C3: every violating config has two isomorphic
  members (240/240); the max-sigma one is fully twisted with
  shape (X,X,Y).
- Cj3-C6 (rigidity): passing kernel combos number 1-2 per
  witness (2/27 S_6, 2/9 M_10, 1/3 A_7).
- Cj4-C2: 240/240 violating configs have a twisted member
  with >= 3 index-2 kernels. High confidence.
- Cj4-C6 (onset): violation iff exists H <= G with
  dim_2(H) >= 2 and |H| >= 16. Predicts PSL(2,13) no
  violation, PSL(2,17) violation — a cheap decisive test.
- Cj4-C5: at p=2 the eligible census always reaches beta_0;
  at p=3 it is generically empty (4/7 targets). The p=2/odd
  asymmetry is supply, not blocking.
- Cj7-C1 (p-isogeny law): ties admit a member bijection to an
  honest witness with p-power ratios summing to exponent +1
  (observed vectors (+1,0,0), (-1,+2,0)); violations admit
  none. 7/7 nonempty censuses.
- Cj7-C2 (coupling): tie configs share members with an honest
  witness iff some witness member has nontrivial
  p-abelianization (4/4).
- Cj7-C3 (k=2 boundary): all 504 tie configs across four tie
  families have k=2 with the untwisted member of trivial
  p-abelianization; violations always include k=3 optima.
- Cj7-C4 (final form): margin=0 implies every eligible config
  is fully blocked (E=B>0); margin<0 iff B=0. 12/12 census
  points.
- Cj7-C5: every tie config contains a Sylow normalizer (or
  the Sylow itself) for the same prime anchoring the honest
  witness (4/4; the A_6 p=2 S_3 member is a strained fit).

### growth laws and numeric predictions

- Cj3-C4: slack/tie/violation is monotone in rho_0 with
  fitted thresholds 27/10 and 3 (7/7).
- Cj3-C5: |G| >= 360 implies margin >= 0; |G| >= 720 implies
  margin > 0. Crude, 7 points.
- Cj3-C7: relative margin margin_2/beta_0 nondecreasing in
  |G|: 0.080, 0.333, 0.469; sup > 1/2 conjectured.
- Cj5-C3: rho_0(S_n) = 2(n-1)^2/15 for n >= 5 (fits n=5,6).
  Prediction: beta_0(S_7) = 24192.
- Cj5-C4: for p >= 7 dividing |G|, v_p(beta_0) >= v_p(|G|);
  30*rho_0(G) integral in all 7 rows.
- Cj5-C5: isosceles witnesses — some optimal triple has two
  members of equal order (7/7; PSL(2,11)'s two order-6
  members are non-conjugate).
- Cj5-C6 / Cj6-C6: excess ratio e(G) <= 3/2; observed 27/25,
  4/3, 72/49 (= 1.469, uncomfortably close to 3/2).
- Cj5-C7: the maximal excess M(G) is always 2^a*3^b (2592,
  3072, 15552); note the non-maximal 2560 = 2^9*5 is not.
- Cj5-C8: strong: rho_0(A_n) = 3(n^2-8n+21)/10, predicting
  beta_0(A_8) = 127008 with witness orders (288,21,21); weak:
  successive ratio >= 3/2. Strong is 3-point extrapolation.
- Cj5-C9: rho_0(PSL(2,q)) = (q+1)/4 for prime q >= 11
  (Borel-torus witness (q(q-1)/2, (q+1)/2, (q+1)/2)); one
  data point. Prediction: beta_0(PSL(2,13)) = 3822.
- Cj5-C10: excess E(A_n) > 0 for n >= 7 with E/beta_0 bounded
  below (~23/49 fit); single positive point, low confidence.
- Cj6-C2 (saturation): rho_0(C_2^k x G) = rho_0(C_2 x G) for
  k >= 1; k=2 never computed. Three structural arguments, no
  data.
- Cj6-C7: capacity-ratio records are held by decomposable
  groups for all N >= 1440; heavy extrapolation from
  rho_0(C_2 x A_7) = 216/35.

## open — decomposition census (C1-C16)

Census question: which sieve survivors admit a nontrivial
abelian direct factor, and where does the complement sit.
Corpus: 88185 records, orders 2..511 (84681 SURVIVE + 3504
CAP), 10256 decomposable (11.63%). Raw data committed at
`Programs/GroupTPP/survivors-census*.jsonl` [M]; every rate
below is recomputable from it, so only headline numbers and
kill conditions are preserved. All verdicts [A] full-data,
2026-07.

- C1 (p-group desert) supported: prime-power decomposition
  rate 2183/57000 = 0.0383, monotone decreasing in k for 2^k
  (0.071 at 2^7 to 0.037 at 2^8); no prime-power order
  exceeds 0.08.
- C2 (refined) supported: aggregate rate strictly monotone in
  omega(n): 0.038 / 0.227 / 0.540 / 0.723 for omega=1..4.
  Strict per-order bands are dead (see killed).
- C4 supported: order-256 desert IDs 17000-25999 exact zero
  over 8997 records; 37 of 57 thousand-ID bins are desert.
- C5 supported: order-256 burst IDs 27000-27999 rate 0.3916
  with C_2 factor 91.7%; second burst 53000-53999 rate
  0.3639 with more C_2xC_2.
- C6 supported (threshold adjusted): C_2 fraction among
  decomposable 2-power survivors 1904/2183 = 0.872.
- C7 supported: shard uniformity, chi-sq(3) = 0.073.
- C10 (replaces killed C3): r(2^a*3) strictly decreasing,
  ~K/2^{a/3}; r(2^a*p) for p>=5 weakly increasing into
  [0.16, 0.22]; crossover a_0 between 6 and 7.
  Kill condition: order 768 = 2^8*3 rate > 0.187, or
  640 = 2^7*5 rate < 0.16.
- C11: C_3-factor fraction among decomposable 2^a*3 groups
  increases to 1: f(3..7) = 0.33, 0.32, 0.36, 0.43, 0.53.
  Kill: f(8) < 0.53 at order 768.
- C12: CAP records decompose at 8.5x the SURVIVE rate (0.766
  vs 0.090), universally per order. Kill: any order with
  SURVIVE rate above CAP rate.
- C13: recursion closure — 97.6% of SURVIVE-decomposable
  complements are themselves in the census (7414/7599); the
  gap is exactly small orders (8,16,32) rejected at earlier
  tiers. Kill: a structurally missing complement of order
  <= 511.
- C14: desert fraction of ID space grows with k: 0.500 at
  2^7, 0.735 at 2^8 (500-ID bins). Kill: order 512
  decomposability spread uniformly.
- C15: T3b decomposition rate in the cap prime: 0.763 (p=2),
  0.801 (p=3), 0.744 (p=5), 0.619 (p=7), 0.500 (p=11), 0.000
  (p=13, n=1); conjectured <= p^2/(p^2+p) and decreasing for
  p >= 5. Note p=3 > p=2 already breaks strict monotonicity;
  low-medium confidence.
- C16 (replaces early C8): injection rate Inj(n,2n) — the
  fraction of order-n survivors appearing as C_2 x H
  complements at 2n — is ~0.92 for 2-groups (0.922 at
  64->128, 0.921 at 128->256) vs 0.653 at 192->384.
  Kill: Inj(256,512) < 0.85.

Early-census C8 (0.58 at ~60% coverage) and C9 (asymptotic
density extrapolation) are subsumed by C16 and the full-data
tables; nothing else in the early doc survives scrutiny [O].

## open — gelfand pairs (Cj1)

Corpus: 307 deduped Gelfand pairs (G,H), G nonabelian of
order 2..127, H proper non-normal, commutative single-fiber
scheme on N = [G:H] points, rank r. Data committed at
`Programs/GroupTPP/gelfand-keep-dedup.jsonl` [M]. (The source
doc recorded 367 records incl. N=8 rows from a pre-reorg
path; the committed file has 307 without them — data loss or
refilter unresolved.)

- Cj1-C1: N >= r + cap2. 307/307, zero violations. [A,
  source doc only — the "exactly two records at N = r + cap2
  = 8, both |H| = 2 in SmallGroup(16,3) and (16,11)" claim
  is absent from the committed jsonl (0 records with |G|=16
  or N=8); re-tag as unverifiable against committed data.]
- Cj1-C2: N >= 4r/3 (strictly stronger for r > 3*cap2).
  307/307. Fifteen equality records, all H = C_2, N in
  {12,...,60} with r = 3N/4; largest [120,32] with N=60,
  r=45. [M]

## probe verdicts

- Coherent configurations: the group sieve is a genuine
  special case of a CC sieve, and commutative CCs can embed
  matrix multiplication where abelian groups cannot (CU 2013
  Thm 5.4) — so Tier 0 would invert. But CC enumeration is
  intractable beyond order ~34 (Hanaki-Miyamoto) and the
  probe's verdict was: real, not actionable at PoC scale.
  Salvageable lead: Gelfand pairs as commutative Schurian CCs
  (this is what Cj1 above pursued).
- Quasirandomness: Tier 2b's n(G) is exactly Gowers'
  quasirandomness parameter; BCGPU Thm 3.2 is Gowers mixing
  applied to TPP. Accepted fold-ins from the verdict doc:
  qr(G) = log n(G)/log|G| as secondary sort key; min
  proper-subgroup index m(G) as descriptive column; follow-on
  card Qr1 = exact beta_0/rho_0 for Z_2 wr Z_n, n=3..6
  (orders 24, 64, 160, 384) with the corrected n(G). Declined:
  Lie-type Tier 2b tightening, recursive Nikolov-Pyber
  decomposition. Unknown whether Qr1 ever ran [O].

## oeis formalization triage

The triage doc scored 46 briefs. Verdict counts: 1
already-proved core (A319510), 1 trivial-go (A060938), 13
maybe, 31 out-of-reach/ill-posed. All cited Lean paths exist
in the tree but most are stale pre-reorg names (`Proofs/Xlib/`
is now `Proofs/GroupTPP/`, root-level files moved under
`Proofs/Enumerative/`, `Proofs/Erdos175/` under
`Proofs/Erdos/`) [M].

Actionable targets absent from `Plans/PLAN.md` — the real
at-risk state:

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

## loose ends for adjudication

- `Documents/abelian-factor-refutation.md` cites paths that
  the `.tasks` deletion will orphan: `Pf13-lift-law.md`
  (Lemma J and Lemma L proofs backing Theorem 1),
  `Pl15-*.md`, `Pf3-abelian-factor.md`. None are in this
  shard's manifest; confirm another shard rescued Pf13 before
  deleting, since it carries the only written proofs of the
  two lemmas the formalization did not cover at general p.
- The same manuscript cites `Proofs/Xlib/TPPLift.lean` and
  `Scratch/GroupSieve/forge/out/`; the tree now has
  `Proofs/GroupTPP/TPPLift.lean` and
  `Programs/GroupTPP/forge/out/` [M]. Stale-path cleanup is a
  five-minute edit.
- Cheapest decisive computations if the Hu2 program resumes:
  beta_0(PSL(2,13)) (tests Cj4-C6 and Cj5-C9 at once),
  the PSL(2,27) p=3 census (tests odd-prime sterility), and
  order-768 decomposition rates (tests C10 and C11).

## file dispositions

- `.tasks/f5exp/docs/beta0-literature-grounding.md` —
  extracted: notation lineage kept here; values and kills are
  durable in `Documents/abelian-factor-refutation.md`; its
  C_2xA_7 >= 21168 line is a stale pre-law snapshot.
- `.tasks/f5exp/docs/beta0-oeis-check.md` — extracted:
  negative OEIS result and ruled-out near-matches kept here.
- `.tasks/f5exp/docs/Cj1-gelfand-conjectures.md` — extracted:
  both conjectures and equality witnesses kept; data
  committed [M].
- `.tasks/f5exp/docs/formalize-oeis-triage.md` — extracted:
  verdicts, untracked targets, and stale-path map kept here.
- `.tasks/f5exp/docs/Hu2-Cj2-conjectures.md` — extracted:
  C1-C8 inventoried here (C1/C2/C8 settled by lift law).
- `.tasks/f5exp/docs/Hu2-Cj3-conjectures.md` — extracted:
  C1-C7 plus rejected R1-R3 with witnesses kept here.
- `.tasks/f5exp/docs/Hu2-Cj4-conjectures.md` — extracted:
  C1-C8 kept, incl. the uncommitted PSL(2,27) target [A].
- `.tasks/f5exp/docs/Hu2-Cj5-conjectures.md` — extracted:
  C1-C10 kept with all numeric predictions.
- `.tasks/f5exp/docs/Hu2-Cj6-conjectures.md` — extracted:
  C1-C8 kept (C1/C3/C8 settled, C5 killed).
- `.tasks/f5exp/docs/Hu2-Cj7-conjectures.md` — extracted:
  C1-C8 kept, incl. the C4-biconditional and Syl_2 kills.
- `.tasks/f5exp/docs/orch-Cj-census-early.md` — drop:
  superseded by the final census; early C8/C9 subsumed by C16
  and full-data tables.
- `.tasks/f5exp/docs/orch-Cj-census-final.md` — extracted:
  C1-C7 verdicts and C10-C16 with kill conditions kept; full
  tables recomputable from committed census jsonl [M].
- `.tasks/f5exp/docs/pf3-probes/beta0-exact.sage` — move to
  `Programs/GroupTPP/forge/`: independent exhaustive Sage
  route to beta_0(A_6) = 972; cheap calibration asset
  complementing the Go engine.
- `.tasks/f5exp/docs/probe-coherent-configs.md` — extracted:
  verdict and abelian-inversion insight kept here.
- `.tasks/f5exp/docs/probe-quasirandomness.md` — drop: its
  surviving claims and corrections are captured via the
  verdict entry here.
- `.tasks/f5exp/docs/probe-quasirandomness-verdict.md` —
  extracted: lamplighter kill, Nikolov-Pyber scale caveat,
  extraspecial correction, and fold-in decisions kept here.
