# STATE8 — residuals

Distilled 2026-08-10 from the residual (unthemed) working
docs under `.tasks/f5exp/docs/`, superseding them. This
shard covers 91 files: done-card notes, campaign ledgers,
handoffs, and code artifacts. Default verdict is drop —
outcomes recoverable from the committed tree or history.
The exceptions are rescued below.

Provenance: six consumer audits over the source docs, plus
direct reads of `Pf13-lift-law.md` and
`Ca1-blocker-multinomial-assembly.md`. Tree checks tagged
[M] were grep/read-verified against the committed tree.
Witness data is quoted from the source docs, which carry
their own verification tags; nothing below is new math.

## rescued: the lift law (Pf13-lift-law.md)

Cited by `Documents/abelian-factor-refutation.md` (363,
580) and `Proofs/GroupTPP/TPPLift.lean:37` as the only
written proofs of Lemmas J and L. The Lean file formalizes
the p=2 law; the informal all-p proof lived only here.

Setup. A configuration in G at prime p is
`(S',T',U', f_S,f_T,f_U)` with `S',T',U' <= G` and homs
`f_X : X' -> C_p`. Let `Pi = S' x T' x U'`,
`psi(x,y,z) = f_S(x)+f_T(y)+f_U(z)`, twist count
`k = #{X : f_X != 0}`, `Sigma = psi^{-1}(0)`; if k >= 1
then `|Sigma| = |Pi|/p`. Nontrivial collisions
`N(S',T',U') = {(x,y,z) : xyz=1} \ {(1,1,1)}`; TPP iff
N empty. Sign-liftable: k >= 1 and `psi(c) != 0` for all
c in N. `Sigma_max^lift(G,p) = max |Sigma|` over
sign-liftable configurations (0 if none exists).

Theorem 1 (lift law). For every finite G and prime p:
`beta_0(C_p x G) = p * max(beta_0(G), Sigma_max^lift(G,p))`.
Proof shape: Goursat trichotomy puts every member of a TPP
triple of `C_p x G` as a graph or full product, at most one
full product. Case B (one full-product member): the free
central coordinate absorbs any character, TPP iff the
G-projection is TPP; attains `p*beta_0(G)`. Case A (three
graphs): TPP iff sign-liftable when k >= 1 (size
`p|Sigma|`) or honest G-TPP when k = 0. No composite-B
caveat: with a C_p pad the sign kernel is forced.

Lemma J (junction concentration). Sign-liftable with some
pairwise member intersection nontrivial implies
`|Sigma| <= beta_0(G)`. Proof: junction collisions
`(v,v^{-1},1)` etc. force each delta
(`delta_ST = f_S - f_T` on `S' cap T'`, ...) to be an
injective hom into C_p, so each nontrivial junction is
C_p and its delta onto. Step 1: two nontrivial junctions
give an explicit nontrivial psi=0 collision, e.g. for
junctions (S'∩T', T'∩U') pick w with
`delta_TU(w) = -delta_ST(v)`, then
`c = (v, v^{-1}w, w^{-1})` is in N with psi(c)=0 —
contradiction; the other two pairs are symmetric. Step 2:
with the single junction W = T'∩U', any collision with
x != 1 admits an interleave shift
`c_w = (x, yw, w^{-1}z)` with
`psi(c_w) = psi(c) + delta_TU(w)`, tunable to 0 —
contradiction; so `N = {(1,w,w^{-1}) : w in W \ 1}`.
Step 3: one of `f_T|_W, f_U|_W` is nonzero, say f_T; then
`(S', ker f_T, U')` is an honest TPP triple of size
`|Pi|/p = |Sigma|`. QED.

Lemma L (lambda-shrink / k<=1 absorption). For a
sign-liftable configuration: (a) N empty gives
`|Sigma| <= beta_0(G)/p`; (b) any unblocked member X
(some `lambda : X' -> C_p` nonzero on all X-components of
collisions) gives `|Sigma| <= beta_0(G)` via
`(ker lambda, T', U')`; (c) k = 1 makes the twisted
member unblocked by its own character, so
`|Sigma| <= beta_0(G)`. Hence k >= 2 is necessary for any
strict violation `beta_0(C_p x G) > p*beta_0(G)` — the
former conjecture J1 is a theorem.

Coprime corollary. If p does not divide |G| then
`beta_0(C_p x G) = p * beta_0(G)` (no index-p subgroups,
so no sign-liftable configuration).

Theorem-backed exact values (8.5):

| product | evaluation | value | status |
|---|---|---|---|
| C_2 x A_5 | 2*max(108, 108) | 216 | computed (Im12) |
| C_2 x S_5 | 2*max(256, <=232) | 512 | new exact |
| C_2 x A_6 | 2*max(972, 972) | 1944 | computed (Im13) |
| C_2 x PSL(2,11) | 2*max(1980, 1980) | 3960 | new exact |
| C_2 x M_10 | 2*max(2304, 3072) | 6144 | computed (Im12) |
| C_2 x S_6 | 2*max(2400, 2592) | 5184 | computed (Im12) |
| C_2 x A_7 | 2*max(10584, 15552) | 31104 | new; rho_0 = 216/35 |
| C_3 x A_5 | 3*max(108, 0) | 324 | new exact |
| C_3 x S_5 | 3*max(256, 0) | 768 | new exact |
| C_3 x A_6 | 3*max(972, 972) | 2916 | new exact |
| C_3 x PSL(2,11) | 3*max(1980, 0) | 5940 | new exact |
| C_3 x M_10 | 3*max(2304, 0) | 6912 | new exact |
| C_3 x S_6 | 3*max(2400, 0) | 7200 | new exact |
| C_3 x A_7 | 3*max(10584, 10584) | 31752 | new exact |

Witness decode (8.6): the two strict-violation witnesses
are provably graph-type (Case A) — C_2 x M_10 orders
(16,24,16) force Case A since a Case-B reading needs an
honest G-triple of size 3072 > 2304 = beta_0(M_10);
likewise C_2 x S_6 (12,36,12), 2592 > 2400. The witnesses
are graph lifts of the census top families
(QD16, S4, QD16) at |Sigma|=3072 and (D12, S3xS3, D12) at
|Sigma|=2592.

Statement hygiene (8.7): `Sigma_max^lift(A_5,2) = 108`,
not 0 — A_5 has six eligible unblocked configurations at
108 that genuinely lift to 216-triples. The empty-set
convention engages only when no sign-liftable
configuration exists at all. "Slack" describes the blocked
census class being empty (`A_2(A_5,2) = 0`).

## rescued: abelian-factor background (Pf3-abelian-factor.md)

Cited as "mathematical background" by
`Documents/abelian-factor-refutation.md:581`,
`Programs/GroupTPP/lemma_sweep.sage:28`,
`cmd/sieve/lemmasweep/main.go:21`, `groupsieve.sage`.
The conjecture `rho_0(A x G) = rho_0(G)` remains OPEN in
general; the refutation manuscript covers the kills, this
doc held the theory and A_6 witnesses.

- `beta_0(A_6) = 972`, `rho_0(A_6) = 27/10` (largest
  exactly known rho_0 per the doc), witness
  `(<(3,6,4),(3,4)(5,6)> = A_4, <(1,3,4),(2,5,6)> = P,
  <(1,5,6),(2,3,4)> = P')`, type (12,9,9).
- First Lemma-D refutation instance in A_6:
  `(S' = A_4, T' = S_3, U' = S_3)` with `|Sigma| = 216`;
  no inside witness exists.
- Tight blocked configuration:
  `(C_3^2, C_3^2:C_4, S_3)` with
  `|Sigma| = 972 = beta_0(A_6)` exactly; all 72 eligible
  configs of that shape blocked; complete census kills
  every shape with `|Sigma| > 972`.
- "Blocked => |Sigma| <= |G|" is refuted: 972 > 360.
- Small-group beta_0 table: S_3 = 8, D8 = Q8 = 8,
  D10 = 10, Dic3 = 12, D12 = 16, A_4 = 18, C3xS3 = 24,
  S_4 = 36.

## rescued: group sieve final state (sieve-summary, sieve-spec)

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
smallest irrep dim > 1, not second-smallest.

## rescued: mc(inv8) campaign verdicts (mclower, mcupper)

MCLOWER (cited by
`Proofs/Scratch/mclower_inv8_slices.lean:30`, §S1.2).
Final verdict: `13 <= MC(inv_8) <= 32` stands. §S1.2
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

SAT frontier survey for MC-optimality certification
(from mc-exact-sat-wedge.md, not recorded elsewhere):

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

## rescued: wreath gamma counterexample (Lg1-counterexample.md)

Cited by `Proofs/GroupTPP/STPPWreath.lean:1278`. The
original `pseudoExponent_wreath_le_gamma` was unprovable:
`wreathGamma n` (two-term truncation
`2 + (1+log 2)/log n`) is strictly below
`gamma_exact(n) = log((2n)^n n!)/log(n!)` for all n >= 2,
because the dropped `O(1/(log n)^2)` remainder is
positive. n=2: exact 5 vs 4.443; n=3: exact 4 vs 3.541.
Repair option A (restate with exact gamma) was applied in
the committed file [M]. Status ladder at the time: n=2..5
true via the trivial route, n >= 6 open.

## rescued: multinomial assembly blocker (Ca1)

Live card Mn1: the remaining sorry in
`stpp_capacity_le_of_wreath` (`stpp_capacity_le_comm`
derives from it). Full spec preserved here.

CKSU's proof of theorem:asi (FOCS05-10page.tex:1606-1629)
has six steps; 1-5 are plank compositions (power,
selection, STPP2TPP, CU 4.1, wreath bound); step 6 closes
via `sum_le_of_multinomial_prod_pow_le`, whose hypothesis
is: for all N and compositions mu with sum(mu) = N,

```
multinomial(N, mu) * prod_i s_i^{mu_i} <= C^N
```

with `s_i = (|A_i||B_i||C_i|)^{omega/3}` and
`C = D_omega(G)`. Abbreviate `M = multinomial(N, mu)`,
`x = prod s_i^{mu_i}`, `y = D^N`. Steps 1-5 applied to
the multinomial-selected triples of type mu yield only

```
M! * x^M <= y^M        (*)
```

and the hypothesis needed is `M * x <= y`. (*) gives
`x <= y` by M-th roots but NOT `M * x <= y`:
counterexample M=2, x=1, y=sqrt(2). CKSU's "taking M-th
roots and letting N -> infinity" (tex:1621) hides a
nontrivial real-analysis argument. Sage-verified that
`M * x <= y` DOES hold for valid STPP triples — the
target inequality is true; the gap is purely in
extracting it from the capacity chain.

Resolution options: (1) dedicated extraction lemma using
the scaled family `ell * mu`; the iterated chain gives
`M(ell)! * x^{ell M(ell)} <= y^{ell M(ell)}`, close with
`le_of_pow_le_poly_mul_pow`. (2) direct combinatorial
proof of `M * x <= y` from STPP structure, bypassing the
chain. (3) entropy-based geom-arith step with no
multinomial prefactor. Recommended: option 1. The naive
lemma `M! * x^M <= y^M -> M * x <= y` is false (above);
it becomes true only using the full mu-family of
inequalities together, not one at a time.

## rescued: route c gauge structure (route-c-gauge-dual-ciphers.md)

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

## rescued: tpp convention bridge (tpp-inversion-bridge-analysis.md)

Cited as "Document 1" by `Prompts/User/f5high-3rev.md`.
Thesis: left-quotient and right-quotient TPP are
non-equivalent predicates on the same ordered triple; the
bridge is `Q_l(X) = Q_r(X^{-1})`, making `tppCapacity`
convention-independent. The left form in the repo's
TPP.lean was a transcription mutation — every published
source uses right quotients. The bridge theorem and S_3
counterexample are committed in
`Proofs/GroupTPP/...TPP.lean` [M]; not committed are:
S_3 exhaustive count (1746 left-only and 1746 right-only
of 250047 triples); an erratum-grade slip in Blasiak-Cohn
ITCS 2023 (90 pairs (S,T) with (S,T,{e}) right-TPP and
S x T -> G non-injective, e.g. `S = {(132),(23)},
T = {e,(13)}`); Hedtke-Murthy D_10 witness is right-TPP
but not left-TPP; `tppCapacity (DihedralGroup 6) = 16`
matches their Table 1 row [12,4].

## rescued: cc/gelfand sieve spec (Cc2-ccsieve-spec.md, Pf5-anchor-validation.md)

Cc2 rev2 is the normative spec named by
`Programs/GroupTPP/gelfand.sage` and `forge/gelfand.sage`
headers. Load-bearing content not in the sage source:
the NC2 correction (rev2 uses the image-counting form,
not min-over-all-classes), the capacity derivation
`capacity = floor(sqrt(r))` from CU13 Prop 3.5, and three
validation anchors — J(5,2): rank 3, REJECT; H(3,2):
rank 4, cap_eff 2, exhaustive search (13824 combos)
confirms no <2,2,2> realization, so the capacity bound is
strictly loose; (C3 x D8, SmallGroup(24,10)): rank 9,
non-thin, cap_eff 3, dual vector `[0,1,5,3,7,2,8,4,6]`.

Pf5 upgraded anchor 2/3 verdicts to proof grade with the
rank-n^2 rigidity lemma: no association scheme of rank
exactly n^2 realizes <n,n,n> for n >= 2 (the triangle
condition forces a coherent-algebra dimension count that
fails at rank n^2). It also logged six defects D1-D6 in
the Cc2 rev1 spec, all fixed in rev2; and cross-checked
CU13 numbering (the memo's "Thm 5.4/Conj 5.1/Sec 5.1"
are 5.6/5.7/6.1).

## rescued: peeling bottleneck notes (Bf1, Bf2, Bw1)

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

## rescued: quantum-ec feasibility (qABCD, qC, Qr1)

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

## rescued: novelty and erratum notes

bilinear-complexity-analysis.md ("Document 2" of
`Prompts/User/f5high-3rev.md`): honest framing is "first
ITP formalization of the bilinear complexity of matrix
multiplication" (~95% confidence after adversarial
search). The broader "first tensor rank in any ITP" is
FALSE — Mathlib has `Holor.cprank` (Bentkamp 2018). New
over prior work: rank of the matmul tensor specifically,
certified R<2,2,2> <= 7 by kernel decide, the flattening
lower bound, and CommSemiring-generic rank calculus.

character-degree-analysis.md: `charDegreeSum_two` and
`card_charDegrees` are second-ever ITP formalizations
(MathComp `character.v` has `NirrE`, `irr_sum_square`
~14 years earlier); Artin-Wedderburn uniqueness plausibly
first in any system; CommSemiring class-sum basis first.
Gap: `charDegrees` is ring-theoretic, not bridged to
`FDRep` characters. Suggested upstream order: Wedderburn
uniqueness, then class-sum basis, then charDegrees.

mentalmap-factcheck.md: corrections for
`Prompts/Ref/MENTALMAP` are STILL UNAPPLIED [M]:
(1) Pratt numbering Conj 1.1 -> 1.2, Thm 1.1 -> 1.3,
Thm 1.2 -> 1.4; (2) line 99 "abelian: alpha = gamma" is
wrong — abelian gives alpha = 3, gamma = infinity;
(3) the gamma table values (2.207, 1.844, 1.848, 1.958)
do not match the CU03 definition
`gamma = log|G|/log(max_d)`, source unknown; (4) "alpha
from STPP triples" should read TPP.

candidate-ledger.md (named by `Prompts/User/erdosmining`
as the raw triage of 401 swept Erdos problems). Landed
problems are in `Proofs/Erdos/` and the newer
`Formalize/ERDOS_CANDIDATES.md`; not replicated there
are the kill/defer rationales: #1216 killed (2^91
tournament enumeration infeasible), #742 killed
(enumeration scale), #835/#617 killed (SAT scale);
#1213 deferred (proof paper inaccessible), #384 deferred
(Chebyshev-type gap; Mathlib has
`Nat.exists_prime_lt_and_le_two_mul`,
`Nat.factorization_choose`,
`Chebyshev.theta_le_log4_mul_x` but not the needed
strengthening). #402 was already formalized despite a
`formalized=no` sweep tag.

## dangling pointers

Committed files that name deleted `.tasks` paths. Rescued
referents live in this file; pointers should eventually be
rewritten to `Plans/STATE8.md` or made self-contained.

- `Proofs/GroupTPP/TPPLift.lean:37`,
  `Documents/abelian-factor-refutation.md:363,580` ->
  `Pf13-lift-law.md` (rescued above).
- `Documents/abelian-factor-refutation.md:581`,
  `Programs/GroupTPP/lemma_sweep.sage:28`,
  `cmd/sieve/lemmasweep/main.go:21`,
  `Programs/GroupTPP/groupsieve.sage:122,342` ->
  `Pf3-abelian-factor.md` (rescued above).
- `Proofs/GroupTPP/STPPWreath.lean:1278` ->
  `Lg1-counterexample.md` (rescued above).
- `Proofs/Scratch/mclower_inv8_slices.lean:30` ->
  `mclower-campaign.md` §S1.2 (rescued above).
- `Proofs/Erdos/Erdos542/SchinzelSzekeres.lean:67,76` ->
  `erdos542-weights.md`; harmless — all 13 LP-dual weights
  are embedded and compiled in the Lean file [M]; the
  greedy reconstruction algorithm and margin analysis are
  re-derivable from the paper; pointer is provenance-only.
- `Programs/GroupTPP/gelfand.sage`, `forge/gelfand.sage`
  -> `Cc2-ccsieve-spec.md` rev2 (rescued above).
- `Programs/GroupTPP/groupsieve.sage:76-77`,
  `census.sage`, `stratum-b-full.log` ->
  `sieve-{spec,summary}.md` (rescued above).
- `Programs/RouteC/routec_gauge_{invariants,symmetries}.sage`
  -> `route-c-gauge-dual-ciphers.md` (rescued above).
- `Programs/BilinearComplexity/b1_levelcut_222.sage` ->
  `Bf1-bottleneck.md` (rescued above).
- `Prompts/User/erdosmining` -> `candidate-ledger.md`;
  `Prompts/User/f5high-3rev.md` -> both analysis docs
  (rescued above). Prompt files are historical records;
  many also cite other-shard `.tasks` docs.
- Code that emits or writes `.tasks` paths at runtime:
  `Programs/GroupTPP/groupsieve.sage:853` and
  `forge/cascade.sage:979` print `Im3-ranking.md` in
  their summaries; `groupsieve.sage:857` and
  `cascade.sage:983` print `orch-Cj-census-early.md`;
  `Programs/GroupTPP/cmd/gelfandrank/main.go:71`
  hardcodes `Im8-gelfand-ranking.md` as its OUTPUT path
  and will break after deletion — needs an `-o` flag or
  a committed output location. (`Im8` was a generated
  artifact, not authored prose.)
- `Programs/GroupTPP/forge/verify_all_combos.sage:9`
  cites `Im12.md` (comment-level provenance, not runtime).
- `Prompts/User/o46max-3.md:14,16` and
  `Prompts/Ref/CONTEXT:130` cite `Im4-verification.md` /
  `Im3-ranking.md` (low severity, historical prompts).

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

## file dispositions

- .tasks/f5exp/docs/alphatensor-decomp-analysis.md — drop: internal 2-orbit/exact-cover hypotheses falsified; no downstream consumer.
- .tasks/f5exp/docs/Bf1-bottleneck.md — extracted: blocking-family duality + antichain failure (rescued); cited by committed b1_levelcut sage.
- .tasks/f5exp/docs/Bf2-levelcut-verdict.md — extracted: Q1 verdict, peak distribution, open conjectures C2-C4 (rescued).
- .tasks/f5exp/docs/bilinear-complexity-analysis.md — extracted: novelty framing + Holor.cprank correction (rescued); cited by f5high-3rev prompt.
- .tasks/f5exp/docs/Bw1-boundary-witness.md — extracted: W4/W6 witness vectors + construction families (rescued).
- .tasks/f5exp/docs/Ca1-blocker-multinomial-assembly.md — extracted: full Mn1 blocker spec, counterexample, resolution options (rescued).
- .tasks/f5exp/docs/candidate-ledger.md — extracted: kill/defer rationales + Mathlib inventories (rescued); named by erdosmining prompt.
- .tasks/f5exp/docs/Cc1-cu13-verification.md — drop: numbering corrections absorbed into Cc2 rev2 and noted in Pf5 rescue.
- .tasks/f5exp/docs/Cc2-ccsieve-spec.md — extracted: NC2 correction, capacity derivation, validation anchors (rescued); normative spec of gelfand.sage.
- .tasks/f5exp/docs/character-degree-analysis.md — extracted: ITP novelty survey + FDRep gap + upstream order (rescued).
- .tasks/f5exp/docs/Cn1-conspiracy-engine.md — drop: lemmas and counterexample committed in Conspiracy.lean + Scratch/Cn1Counterexample.lean [M].
- .tasks/f5exp/docs/Cn2-pair-classification.md — drop: sharpness witnesses decide-certified in committed Scratch/Cn2Sharpness.lean [M].
- .tasks/f5exp/docs/Cn3-ladder.md — drop: section 8 lemmas committed; sage cross-check supplementary.
- .tasks/f5exp/docs/cu41-preflight.md — drop: API/sorry audit re-derivable from committed Lean sources; convention bridge covered by tpp rescue.
- .tasks/f5exp/docs/ec-point-addition-toffoli-breakdown.md — drop: transcriptions of published RNSL/HJNRS tables; ShearEC does not depend on it.
- .tasks/f5exp/docs/Ep542-notes.md — drop: proof committed sorry-free; tail constants embedded in SchinzelSzekeres.lean [M].
- .tasks/f5exp/docs/erdos542-weights.md — drop: all 13 exact weights embedded in SchinzelSzekeres.lean [M]; pointer is provenance-only.
- .tasks/f5exp/docs/groupsieve-consolidation.md — drop: 9 bugs fixed in committed groupsieve.sage; ledger is git-history material.
- .tasks/f5exp/docs/hu3-pl17-kernels.md — drop: digest of Im12/Im15 data, partially stale (PSL(2,13) prediction superseded).
- .tasks/f5exp/docs/hu4-hu7-pl18-kernels.md — drop: conjecture state superseded by Im15 results.
- .tasks/f5exp/docs/Im12.md — drop: beta_0 values and kill census in committed jsonl outputs [M].
- .tasks/f5exp/docs/Im13.md — drop: beta_0(C_2 x A_6) = 1944 in committed outputs and lift-law table above.
- .tasks/f5exp/docs/Im14.md — drop: saturation values derivable from committed theorem + census.
- .tasks/f5exp/docs/Im15.md — drop: PGL(2,9)/PSL(2,13) results in committed jsonl outputs [M].
- .tasks/f5exp/docs/Im2-stratum-b.md — drop: run design embedded in committed groupsieve.sage.
- .tasks/f5exp/docs/Im3-ranking.md — drop: regenerable via cmd/tier4rank; reword stale path strings in groupsieve.sage:853, cascade.sage:979.
- .tasks/f5exp/docs/Im4-verification.md — drop: one-time checkpoint verification of committed data.
- .tasks/f5exp/docs/Im5-rho0-manifest.md — drop: planning manifest; targets from published tables.
- .tasks/f5exp/docs/Im6-notes.md — drop: T3c toggle semantics documented in committed code.
- .tasks/f5exp/docs/Im7-gelfand-run.md — drop: run docs for committed gelfand.sage.
- .tasks/f5exp/docs/Im8-gelfand-ranking.md — drop: generated output of cmd/gelfandrank; fix its hardcoded output path (main.go:71).
- .tasks/f5exp/docs/kernel-graph.mmd — move to Programs/GroupTPP/: kernel DAG diagram; refresh stale nodes.
- .tasks/f5exp/docs/kernel-synthesis-vs-pl19.md — drop: triage artifact; conclusions landed in TPPLift.lean and the manuscript.
- .tasks/f5exp/docs/Lf1-lift-api.md — drop: charLift API landed sorry-free in TPPLift.lean [M].
- .tasks/f5exp/docs/Lg1-counterexample.md — extracted: wreathGamma < gamma_exact counterexample (rescued); cited by STPPWreath.lean:1278.
- .tasks/f5exp/docs/Ma1-changelog.md — drop: all edits applied to committed abelian-factor-refutation.md [M].
- .tasks/f5exp/docs/mc-exact-sat-wedge.md — extracted: SAT frontier survey table rescued above; SAT infeasibility (~10^79 gap) verdict recorded in mclower rescue.
- .tasks/f5exp/docs/mc-inv8-boyarfind-theorem4.md — drop: computational spine machine-checked in mclower_inv8_slices.lean; reconstruction of published theorem.
- .tasks/f5exp/docs/mc-inv8-q1-continuation.md — drop: advisor synthesis; verdicts captured in campaign rescues.
- .tasks/f5exp/docs/mclower-campaign.md — extracted: §S1.2 ladder + final verdict + (star-star) reformulation (rescued); cited by Scratch lean.
- .tasks/f5exp/docs/mc-tower-restricted-class.md — drop: tower-class framework for a concluded campaign; key results in mcupper rescue.
- .tasks/f5exp/docs/mcupper-campaign.md — extracted: four-route priced-negative verdict + witnesses (rescued); recorded nowhere committed.
- .tasks/f5exp/docs/md1-notes.md — drop: all three sorries closed in committed CharDegreesMul.lean [M].
- .tasks/f5exp/docs/mentalmap-factcheck.md — extracted: four MENTALMAP corrections, still unapplied (rescued).
- .tasks/f5exp/docs/Nc1-strassen222.md — drop: minpeak = 10 machine-checked in PeelingCert222.lean [M].
- .tasks/f5exp/docs/Nc2-schoolbook.md — drop: peak = 26 machine-checked in PeelingCert333.lean [M].
- .tasks/f5exp/docs/Nc3-crosscheck.md — drop: Lean/Go cross-check passed; convention note re-derivable.
- .tasks/f5exp/docs/Pf10-bilinear-strassen.md — drop: R<2,2,2> <= 7 committed in Strassen.lean; Q-decide recipe is generic lore.
- .tasks/f5exp/docs/Pf13-lift-law.md — extracted: Lemma J/L proofs, exact-values table, witness decode, Ma1 correction (rescued in full).
- .tasks/f5exp/docs/pf1-borderrank.md — drop: session log; BorderRank.lean committed.
- .tasks/f5exp/docs/pf2-circuit.md — drop: session log; Circuit.lean committed with IsVP annotation rationale.
- .tasks/f5exp/docs/Pf3-abelian-factor.md — extracted: A_6 witnesses, beta_0 table, tight blocked config, refutations (rescued); cited by 5+ committed files.
- .tasks/f5exp/docs/Pf3-notes.md — drop: explicitly superseded by Pf3-abelian-factor.md.
- .tasks/f5exp/docs/pf3-probes/a6-blocked-finder.sage — move to Programs/GroupTPP/pf3-probes/: A_6 Lemma-D refutation finder; not subsumed by lemma_sweep.
- .tasks/f5exp/docs/pf3-probes/a6-shape-scan.sage — move to Programs/GroupTPP/pf3-probes/: A_6 M-violation shape census; not subsumed.
- .tasks/f5exp/docs/pf3-probes/a6-tight-verify.sage — move to Programs/GroupTPP/pf3-probes/: end-to-end tight-config + 1944-triple verifier; not subsumed.
- .tasks/f5exp/docs/pf3-probes/blockedscan.sage — move to Programs/GroupTPP/pf3-probes/: blocked-config scanner; no committed equivalent.
- .tasks/f5exp/docs/pf3-probes/conc.sage — move to Programs/GroupTPP/pf3-probes/: concentration probe; superseded analytically but regenerates witnesses.
- .tasks/f5exp/docs/pf3-probes/lemmaD.sage — drop: refactored verbatim into committed lemma_sweep.sage probe_lemma_d [M].
- .tasks/f5exp/docs/pf3-probes/lemmaM2.sage — drop: refactored verbatim into committed lemma_sweep.sage probe_lemma_m [M].
- .tasks/f5exp/docs/pf3-probes/lemmaWC.sage — move to Programs/GroupTPP/pf3-probes/: Lemma C/W probe; conjectures refuted but script unsubsumed.
- .tasks/f5exp/docs/Pf4-dihedral-subsets.md — drop: rho(D_2n) <= 4/3 formalized sorry-free in DihedralTPP/{Basic,Sharpness}.lean [M].
- .tasks/f5exp/docs/Pf4-notes.md — drop: superseded by Pf4-dihedral-subsets.md + Lean.
- .tasks/f5exp/docs/Pf5-anchor-validation.md — extracted: rank-n^2 rigidity lemma + anchor verdicts (rescued).
- .tasks/f5exp/docs/Pf7-bilinear-basic.md — drop: API committed in BilinearComplexity/Basic.lean [M].
- .tasks/f5exp/docs/Pf8-bilinear-calculus.md — drop: RankCalculus.lean committed [M].
- .tasks/f5exp/docs/Pf9-bilinear-flattening.md — drop: Flattening.lean committed [M].
- .tasks/f5exp/docs/qABCD_epistemic_handoff.md — extracted: quantum-EC verdicts, GCD correction, Toom-k table (rescued).
- .tasks/f5exp/docs/qA_reptheory_verification.md — drop: subsidiary worksheet; unique data duplicated in qABCD (rescued).
- .tasks/f5exp/docs/qB_addsub_chain.md — drop: NAF 262 and bounds captured in qABCD rescue; trace re-derivable.
- .tasks/f5exp/docs/qC_tpp_pm_feasibility.md — extracted: order->=7 structure theorem + C2^3 obstruction + embedding counts (rescued).
- .tasks/f5exp/docs/Qr1-lamplighter.md — extracted: lamplighter SmallGroup ID / tier / ceiling table (rescued).
- .tasks/f5exp/docs/reconcile-thread-map.md — drop: coordination metadata; DAG is canonical; residual gaps low priority.
- .tasks/f5exp/docs/reorg-proofs-classification.md — drop: reorganization executed [M]; current tree is canonical.
- .tasks/f5exp/docs/reorg-references-mapping.md — drop: citation map mechanically reproducible by grep; snapshot stale.
- .tasks/f5exp/docs/reorg-scratch-classification.md — drop: Programs/ reorganization executed [M].
- .tasks/f5exp/docs/Rf1.md — drop: Matrix.piAlgEquiv migration committed [M].
- .tasks/f5exp/docs/Rf2.md — drop: FourierBarrier.lean docstring/deletion changes committed [M].
- .tasks/f5exp/docs/Rf3.md — drop: de-privatized CUCapacity declarations committed [M].
- .tasks/f5exp/docs/Rf4.md — drop: higherCommProb_two landed in HigherCommProb.lean [M].
- .tasks/f5exp/docs/Rf5.md — drop: abbrev + simp changes landed; two described re-export deletions never applied (harmless hygiene) [M].
- .tasks/f5exp/docs/route-c-gauge-dual-ciphers.md — extracted: normal form, stabilizer, P4/P5 findings, posteriors (rescued); referent of RouteC sage headers.
- .tasks/f5exp/docs/route-d-aes-diffusion-witness.py — move to Programs/Unsorted/: AES-CTR SubBytes batch-constancy witness script.
- .tasks/f5exp/docs/route-d-amortized-nonlinearity.md — drop: dead-end verdict (ceiling 27/16R proved, known art); counts re-derivable.
- .tasks/f5exp/docs/sieve-spec.md — extracted: manuscript-vs-literature corrections (rescued); named as normative spec by groupsieve.sage.
- .tasks/f5exp/docs/sieve-summary.md — extracted: campaign per-tier counts, survivors, cascade gaps (rescued); generated but unregenerated-since aggregate.
- .tasks/f5exp/docs/Sm1-peel-model.md — drop: API committed; j>=1 vs j>=0 convention re-derivable from peak definition.
- .tasks/f5exp/docs/Ss1-splitting.md — drop: PeelingSplit.lean committed; ordering obstruction inherent in the lemma statement.
- .tasks/f5exp/docs/toom-cook-operation-counts.md — drop: published numbers (Bodrato-Zanoni, Oku-Kudo, Nissim et al.), re-findable.
- .tasks/f5exp/docs/tpp-inversion-bridge-analysis.md — extracted: convention thesis, Blasiak-Cohn slip, D_10 cross-check (rescued).
- .tasks/f5exp/docs/vp2-apolarity-impl.md — drop: Apolarity.lean landed sorry-free and committed [M]; session checkpoint only.
