# matmul-search — the omega/matmul computational search program

Computational discovery of faster matrix multiplication via
group/structure-guided search.  GroupTPP campaign: enumerate,
sieve, census, and predict beta_0/rho_0 across finite groups
and their products; search proposes, Lean certifies.

Sources: `git show 4901d3b:Plans/STATE4.md` sections context
through loose ends, `git show 4901d3b:Plans/STATE8.md` sections
sieve-summary through code-relocations and Pf3/Bw1/Bf1/Bf2/Qr1
rescues, `git show 4901d3b:Plans/STATE1.md` sections P2 rank
calculus and census-derived conjectures (C10/C11 only),
`git show 4901d3b:Plans/STATE2.md` section native_decide surface
(certificate facts only), `git show 4901d3b:Plans/STATE6.md`
section fetch-gaps (Kauers-Moosbauer-Wood); reorganized
2026-08-10.

## demotion caveat

ALL Sage-derived numerics in this file — the decomposition
census (C1-C16), sieve tier counts, beta_0 predictions
(S_7=24192, A_8=127008, PSL(2,13)=3822), the A_6=972
calibration anchor, Gelfand pair data, kill witnesses, and
boundary/conspiracy witnesses — are unreviewed and hold
[A]-computational status.  They are leads, not results.  Per
Plans/PROTOCOL.md, decisions require Lean certificates or two
independent implementations.

Named priority: recompute beta_0(A_6)=972 first (calibration
anchor for the entire census); regenerate the Gelfand jsonl
from scratch rather than reconciling the 367-vs-307 discrepancy
forensically.

## context

Everything in this file belongs to the GroupTPP campaign
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

## certificate interface status

Kernel `decide` proven at `strassen_isDecomp_F2` (2x2x2) and
`schoolbookDecomp333`; `PeelingCert222` minpeak=10 /
`PeelingCert333` peak=26 machine-checked; untested at 4x4x4
scale.  `native_decide` residue: `strassen_minpeak_F2`
(PeelingCert222.lean:49, 5040 permutations) and
`schoolbookDecomp333_isDecomp`/`_peak` (PeelingCert333.lean:62,67,
729 cells x 27 triads); kernel reduction judged infeasible,
values cross-checked externally [A].

SOTA gap: Kauers-Moosbauer-Wood arXiv:2602.11041 cited but
never fetched (Plans/grounding.md fetch-gap list) [M missing].
Current records must be grounded there before setting targets.

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

## group sieve final state

Campaign conclusion of `groupsieve.sage` (2026-07-12),
cited by its header and `census.sage`; the aggregate was
recorded nowhere committed [M].

Stratum A: 100% coverage, 91774 nonabelian of 92803
groups through order 511. Per-tier: T0 abelian 1029;
T1a 27; T1b 947; T1c 91 (CAP); T2b 84681 (SURVIVE);
T3a 796; T3b 5232; 0 errors. Actions: REJECT 3589,
CAP 3504, SURVIVE 84681. Top survivors are all order
504/500 with ceiling ~16.87, n(G)=2, e.g. [504,55].
Known cascade gap: [24,10] (C3xD8) and [24,11] (C3xQ8)
have known rho_0 = 1 but the cascade only certifies
CAP(4/3). T2a is absent by design — provably shadowed by
T1b (Isaacs Cor 2.30).

Spec-grounding corrections found while writing the sieve
(recorded only in sieve-spec.md): Murthy Prop 1.19 is
actually Prop 2.14; T1b needs the class-2 hypothesis of
Thm 6.1; cyclic G' must CAP not drop (extraspecial
counterexample); BCGPU renumbering Thm 3.3->3.2,
Cor 1.6->3.3, Cor 3.6->3.8, Thm 3.4->3.6; n(G) is the
smallest irrep dim > 1, not second-smallest distinct
dimension.

## mc(inv8) campaign verdicts

MCLOWER (cited by
`Proofs/Scratch/mclower_inv8_slices.lean:30`, S1.2).
Final verdict: `13 <= MC(inv_8) <= 32` stands. S1.2
content: witnessed phi_k ranks over the AES modulus are
`rank phi_k = 8` for all k in 1..7, `rank phi_0 = 0`;
correction budget at level k is <= 7-k; at no level does
the required rank of psi_k exceed 8 = dim of its domain.
The correction ladder is dimensionally graceful
everywhere, so W1 — linear slice counting — provably
cannot force MC >= 14 at any level or across the ladder.
W2 (solver) sized at ~2^80-2^100 after the (star-star)
reduction, beyond reach. Primary deliverable: the
(star-star) reformulation — a 13-AND circuit exists iff
inversion's 8-dim component space can be presented as 8
AND gates over a shared 5-AND base algebra. Posterior on
MC >= 14: ~0 via slices, ~0.3-0.4 via a new argument.

MCUPPER (2026-07-23; verdict recorded nowhere committed
[M]): priced negative, the 32-AND record for inv_8 is NOT
beaten. Route 1, cheap don't-care partial multipliers:
provably dead (vanishing space empty through degree 3
single / degree 2 joint). Route 2, bilinear cross-output
sharing: closed — the 256x32 matrix of
`{x_i * Delta'_j(x)}` on all realizable inputs has full
rank 32; joint GF(2^2) rank exactly 6 = 2*mu_2; bilinear
don't-care freedom is 0 for all n in {2,4,6,8} (the n=4
saving is non-bilinear). Route 3, general-MC degree >= 3
side-mixing: open, tied to Mirwald-Schnorr optimality for
m >= 3 outputs. Route 4, m8 < 9: open frontier
(mu_2(GF(2^4)) = 9 holds only in the bilinear model;
general-MC SAT gave k=3 UNSAT, k=4 timeout). Composite
residual for beating 32: ~0.08-0.10. Side facts: the BP
5-AND inverter's 60 valid input maps form one
GammaL(1,16) orbit; the self-equivalence group of inv_8
is GammaL(1,2^8), order 2040, nonabelian
`C3:(C5:(C17:C8))` — an earlier "Z/255 x Z/8" claim was
wrong.

SAT frontier survey for MC-optimality certification:

| who | year | n | m | k | method | runtime |
|---|---|---|---|---|---|---|
| Zajac-Jokay | 2014 | 4 | 4 | 5 | exhaustive (*) | modest |
| CTP | 2018 | 6 | 1 | 6 | enum+equiv | 38422 core-h |
| Soeken | 2020 | 5 | 1 | 4 | SAT (Z3) | 530 s |
| Soeken | 2020 | 6 | 1 | 6 | SAT (Z3) | 5882 s |
| Stoffelen | 2016 | 4 | 4 | 5 | SAT | seconds |
| Stoffelen | 2016 | 5 | 5 | ~7 | SAT | minutes |
| Zhang-Huang | 2023 | 4 | 4 | 5 | SAT (improved) | 2-100x faster |

(*) Constructive enumeration of 302 affine equivalence
classes, not SAT/UNSAT.

## route c gauge structure

Referent for `Programs/RouteC/routec_gauge_invariants.sage`
and `routec_gauge_symmetries.sage` headers. Verdict: as a
performance route, likely no (1-3% throughput); but the
gauge objective is structurally sensitive (posterior
dead-by-flatness 0.35 -> 0.10, structurally sensitive
0.20 -> 0.50).

- Normal form (the "telescoping" section):
  `Lambda(a,a') = mult_{a'} . MC . Aff . mult_a` over
  32x32 / GF(2).
- W1: all 2040 self-equivalence pairs check, zero
  failures; the group is GammaL(1,2^8) (see mcupper note
  above for the structure correction).
- W2: Paar-1 over 145 seeded gauges spans 159-230
  (identity 226); the invariants sage header quotes
  145-228.
- P1: exact stabilizer of Aff under the two-sided mult
  action is trivial (exhaustive, 65025 pairs); proof-grade
  via committed `Proofs/Scratch/RouteCGaugeStab.lean` [M].
- P4 sub-BP contrast: identity 216, low tail 134-149,
  equal-weight contrast gap 45 -> 36 XOR after
  cancellation; equal-weight band retains spread 46 —
  flatness rejected.
- P5 mu_5 norm-harmonic: cosets mod 5 carry F-statistics
  15.7 (input) / 7.3 (output) in both weight and savings;
  invariant `chi(a) = a^51 = N(a)^3` in mu_5. Flagged as
  first sighting of closed-form subgroup-aligned structure
  in an SLP-cost landscape (novelty unswept).

## peeling bottleneck notes (Bf1, Bf2, Bw1)

Bf1 duality (referent of committed
`Programs/BilinearComplexity/b1_levelcut_222.sage`):
`minpeak(D) = max over blocking families B of
min_{S in B} f(S)` on the Boolean lattice — elementary
two-direction proof; the antichain-restricted variant is
false (explicit 2^[3] counterexamples in the source doc).

Bf2 verdicts on Strassen <2,2,2>/F_2: Q1 TRUE —
`LB_level = minpeak = 10` at levels m = 1,2,3; Q2 false
only as a greedy scan-order artifact (level cuts exist at
every threshold). Peak distribution over all 5040
orderings: {10: 720, 12: 4032, 14: 288}; per-level minima
10,10,10,8,6,4,0. Killed: "every peak-10 ordering peels
M1 last". Open pre-registered conjectures C2 (level-bound
tightness), C3 (first-step tightness), C4
(distance-profile shape) — active hypotheses for the
Pl25 minpeak campaign, recorded nowhere else.

Bw1 boundary witnesses (compression needs rank-1
structure; negative examples for the frame-F2 exchange
lemma): W4 in F_2^4: `x1=(1,1,1,0), x2=(1,1,0,1),
x3=(1,0,1,1)` — all proper subset sums weight >= 2, total
weight 1. W6 in F_2^6: `x1=(1,1,1,1,1,0),
x2=(1,1,1,0,0,1), x3=x1+x2` — all proper sums weight
>= 3, total weight 0. Generalize via complement-of-basis
(odd k) and linear-code reductions (any k).

## quantum-ec feasibility (qABCD, qC, Qr1)

qABCD/qC verdicts (secp256k1 reversible arithmetic; not
recorded in `Proofs/ShearEC/` [M]):

- Load-bearing correction: Kaliski binary-GCD inversion
  has ZERO full multiplications — GCD dominates Fermat,
  so there is no multiplication target for a group
  substrate in the inversion loop (grounding: Roetteler
  arXiv:1706.06752; Taguchi IACR 2024/228).
- Fermat route best known: NAF add-sub chain 262
  (256 sq + 6 add/sub); Dettman 269 add-only; lower bound
  >= 257, Schonhage ~260 add-only.
- TPP for 4x4 polynomial mult with {0,+-1} reps: NO for
  |G| <= 9, on three independent grounds — Hedtke bound
  needs |G| >= 13; embedding exists iff G has an element
  of order >= 7 (structure theorem, only in these docs);
  and the C2^3 Walsh-Hadamard loophole fails
  (exponent-2 obstruction: phi_3 takes <= 2 values).
  Embedding counts: C7: 6, C8: 4, C9: 6.
- {0,+-1} realizability: S3 std YES (integral
  non-monomial), D4 YES (monomial), Q8 NO (quaternionic,
  FS = -1). Sub-mult costs via R<2,2,2> = 7: S3 = 9,
  D4 = 11, Q8 = 11, S3xC2 = 18.
- Toom-k inverse interpolation entry growth (exact):
  k=4 -> 15, k=5 -> 196, k=6 -> 4100, k=7 -> 126456.

Qr1 lamplighter sieve parameters (lookup table only in
this doc): C2 wr C3 = [24,13], n(G)=3, T3b CAP(1.5);
C2 wr C4 = [64,32], n(G)=2, T2b SURVIVE ceiling 5.66;
C2 wr C5 = [160,235], n(G)=5, T3b CAP(2.5);
C2 wr C6 = [384,5790], n(G)=2, T2b SURVIVE ceiling
13.86. Character degree multisets: C2wrC4 [1,2,4],
C2wrC6 [1,2,3,6]. Even-n lamplighters survive the sieve
(n(G)=2, maximally non-quasirandom).

## candidate-ledger kill/defer rationales

From the Erdos problem sweep (401 problems); landed
problems are in `Proofs/Erdos/` and
`Formalize/ERDOS_CANDIDATES.md`.

- #1216 killed (2^91 tournament enumeration infeasible).
- #742 killed (enumeration scale).
- #835/#617 killed (SAT scale).
- #1213 deferred (proof paper inaccessible).
- #384 deferred (Chebyshev-type gap; Mathlib has
  `Nat.exists_prime_lt_and_le_two_mul`,
  `Nat.factorization_choose`,
  `Chebyshev.theta_le_log4_mul_x` but not the needed
  strengthening).
- #402 was already formalized despite a
  `formalized=no` sweep tag.

## F_2 rank-calculus survivor cluster

From calibration sweep P2 (STATE1); the surviving
conjectures only — their novelty grading stays in
Plans/standing.md.

- c8: SURVIVOR (both sweeps). 200-sample evidence that
  Strassen mod 2's unique orbit-size-1 triad and Smirnov-1's
  C_3-fixed triad are both the identity triad; full 211-orbit
  sweep not run.
- c9: SURVIVOR (both sweeps). Exhaustive over all 21 orbits
  of <2,2,2>/F_2.
- c10b: SURVIVOR (both sweeps). 2 data points, checkable vs
  known cyclic rank-23s.
- c5+c6+c10 rigidity package: every abstract monomial
  realization is, up to gauge, a Cohn-Umans TPP
  realization. Both sweeps judged derivable-but-never-stated.
- c8/c9 stabilizer-peel: feeds the orbit-reduced interference
  search as feasibility pruning.
- c6/c7 are the search itself (OPEN-BET).

## 2^a*3 decomposability crossover

From the census-derived conjectures (STATE1 and STATE4 C10/C11);
surviving-conjecture entries only — novelty grading stays in
Plans/standing.md.

C10/C11 (2^a*3 crossover at a=7 and C_3-peel growth) graded
APPARENTLY NOVEL. No literature studies decomposability rates
within the family 2^a*p. Nearest: Erdos-Palfy, Discrete
Math. 200 (1999); Eick-Moede 2018; OEIS A094448/A090751 hold
raw counts, no rate analysis.

## census-derived conjectures — additional entries (2026-07-12)

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

Pl4 verdicts: the Gelfand-screen conjecture C2 was
PROMOTED TO THEOREM — N ≥ 4r/3 via a normalizer-quality
/ double-coset counting argument; C1 (N ≥ r + cap2)
remains a conjecture, verified 367/367. `partners_min = r`
recovery means constraint NC2' never binds. [A]

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

## code relocations

- `kernel-graph.mmd` — move to `Programs/GroupTPP/`.
  Mermaid map of the TPP kernel DAG; several nodes stale
  (K5c/K7/K14-surface killed by Im15) — refresh on move.
- `route-d-aes-diffusion-witness.py` — move to
  `Programs/Unsorted/` (no RouteD dir; unrelated to
  RouteC). Witness script for per-round batch-constant
  SubBytes inputs in AES-CTR.
- `pf3-probes/`: `lemmaM2.sage` and `lemmaD.sage` are
  verbatim-refactored into committed
  `Programs/GroupTPP/lemma_sweep.sage` [M] — drop. The
  other six probes are not subsumed and are the
  regeneration path for the A_6 witnesses above — move to
  `Programs/GroupTPP/pf3-probes/`. Note: the directory
  also contains `beta0-exact.sage` (off-manifest); move
  it with the rest.

OEIS conjecture-discovery targets: see Plans/conjecture-hunts.md.

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
