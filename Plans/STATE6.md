# STATE6 — literature grounding

Distilled 2026-08-10 from the 23 literature-grounding
working docs under `.tasks/f5exp/docs/` (shard 6 of the
doc-retirement campaign). This file supersedes those docs.
It records claim-to-source anchors, misquote discoveries,
and found/not-found verdicts — not paper content, which is
re-fetchable into `References/`. Tags: [M] = verified in
the current tree by this distillation, [A] = agent
assertion carried from the source docs (never upgraded),
[O] = observation. Path note: the seam docs cite
`Proofs/Xlib/*`; those files now live under
`Proofs/GroupTPP/*` [M].

## murthy 2026 digest (gr1)

Source: Murthy, arXiv:2602.15796, at
`References/GroupTPP/arXiv-2602-15796/` [M] (the docs
cite it without the `GroupTPP/` prefix — stale path).

Confirmed anchors: Thm 3.1 (class-2 ceiling
`rho_0 < sqrt(|G:Z(G)|)`), Thm 4.1 (cyclic `G'` of order
p gives `rho_0 <= p`), Thm 5.1 (class 2 with
`p^2 <= |G:Z| <= p^3` gives `rho_0 = 1`), Thm 6.1
(`cd(G) = {1,p}` gives `rho_0 = 1`).

Erratum: the task card cited "Prop 1.19" for the
p-group `order <= p^4 => rho_0 = 1` fact; the paper
numbers it Prop 2.14. Statement itself matches.

Sharpness anchors from the paper's tables: [32,49]
(extraspecial ExSp(2,5)) is the unique cyclic-`G'`
group with `rho_0 = 2 = p`; [32,50] has `rho_0 = 1`,
so the Thm 4.1 cap is sharp for only one central-product
type. [64,226] has `cd = {1,2,4}`, so Thm 6.1 does not
apply and only Thm 3.1 bounds it.

## murthy 2025 digest (gr2, murthy-2025-read)

Source: Murthy, arXiv:2512.16730, at
`References/GroupTPP/arXiv-2512-16730/` [M].

Confirmed anchors: Thm 4.1 (abelian normal subgroup of
prime index p gives `rho_0 <= p^2/(2p-1)`); Cor 4.3(2)
(p-group with abelian subgroup of index p gives
`rho_0 = 1`); Cor 4.3(1) (`(2p-1)` not dividing `|G|`
tightens to `rho_0 <= p/2`).

Hypothesis subtlety worth keeping: Cor 4.3(2) does NOT
assume normality — it is derived for p-groups
(prime-index subgroups of p-groups are normal). But
normality is load-bearing in Thm 4.1's proof, so a
sieve checking "abelian subgroup of prime index" without
normality is safe only in the p-group case [A].

Counterexample anchors: GAP [32,11] and [32,27] achieve
general `rho = 3/2 > 4/3` via a non-subgroup triple of
type (6,4,2), yet have `rho_0 = 1` by Cor 4.3(2). They
kill the abelian-non-cyclic extension of Conjecture 5.1
but do not touch Thm 4.1.

Negative results (all verified against the full paper):
the paper computes NO new `beta_0` values — every
numerical value back-references Hedtke–Murthy 2012
Tables 1–4 [A]; it never treats direct products, never
mentions omega or STPP, and never uses Goursat. So the
repo's `beta_0` values for S_5, S_6, M_10, A_7 and its
entire `C_p x G` program have no precedent there [A].

## murthy conjecture 5.1 vs the lift law (c51 check)

Primary verdict: INDEPENDENT-BUT-ADJACENT. Murthy's
Conjecture 5.1 (arXiv:2512.16730, `rho <= p^2/(2p-1)`
for cyclic normal prime index p) neither implies nor is
implied by the project's lift law K1 or excess-ratio
bound K12 [A]. Four axes: invariant mismatch (rho vs
rho_0), group-class mismatch (the project test groups
A_5, S_5, A_6, PSL(2,11), M_10, S_6, A_7 have no cyclic
normal subgroup of prime index), direction mismatch
(ceiling vs exact product identity), and no logical
path either way. No bridge computation looked
productive [A].

The rho_0 shadow of Conj 5.1 is already a theorem
(Thm 4.1, for the broader abelian-normal class); the
open content is purely the rho_0-to-rho lift in the
cyclic case. Chaining proved Thm 4.1 with conjectural
K12 would give `rho_0(C_2 x G) <= (3/2) p^2/(2p-1)` [A].

## bcgpu digest (gr3)

Source: BCGPU, arXiv:2204.03826, at
`References/GroupTPP/arXiv-2204-03826/` and a top-level
copy `References/arXiv-2204-03826/` [M]. The task card
was written from a differently numbered version; the
concordance against the arXiv source:

| Card | arXiv | LaTeX label |
|------|-------|-------------|
| Thm 3.3 | Thm 3.2 | `thm:gowerstrick` |
| Cor 1.6 | Cor 3.3 | `cor:bigreps` |
| Cor 3.6 | Cor 3.8 | `cor:centerbarrier` |
| Thm 3.4 | Thm 3.6 | `thm:normbarrier` |

All four statements match; only numbering drifted.
`Proofs/GroupTPP/BCGPUBarrier.lean` anchors to Thm 3.2
and its corollary [M exists].

Scope verdicts that constrain sieve design: the center
barrier (Cor 3.8) applies only to subgroup triples, not
arbitrary subsets (Remark 3.7 has the subset form);
`n(G) > 1` or `|Z(G)| > 1` are pointwise contribution
ceilings, never family-level hard rejects; and the paper
itself exhibits NO finite group or family meeting its
packing bound — it says so for Lie type in Sec 1.1.
Definition check: `n(G)` is the min dimension over
irreps of dim >= 2, not "second-smallest distinct
dimension."

## cu / cksu / hedtke anchors (gr4)

CU 2003 (`References/GroupTPP/arXiv-math-0307321/CU.tex`
[M]) Lemma 3.1 grounds abelian triviality
(`alpha(G) = 3` for abelian G); the translation to
`rho_0 = 1` is valid under either normalization.
Normalization caveat worth preserving: no paper defines
a quantity named `rho_0` — CU uses alpha, CKSU uses
strong-USP capacity. Conversions: `rho_0 = 3/alpha` or
the product ratio `nmp/|G|`. Any repo statement must say
which it uses.

CKSU 2005
(`References/GroupTPP/arXiv-math-0511460/FOCS05-10page.tex`
[M]) anchors: strong USP capacity `>= 2^{2/3}`
(Prop 4.4), `omega < 2.48` via strong USP (Cor 4.3),
`omega < 2.41` via wreath (Thm 5.5). Hedtke 2011
contributes structural WLOG facts only, no new capacity
values. Validation anchors from CU: `alpha(S_3) =
log_2 6` via (2,2,2); extraspecial `q^5` gives 2.5;
[80,3] gives 2.4811 via (5,5,8).

## hu8-q2: the fixed-base wreath claim

The strongest misquote discovery in the shard. The old
theorem `abelian_wreath_family_tendsto_two` for FIXED
abelian H cited "CU Prop 11"; no such proposition exists
in any version of CU (math/0307321) or CKSU
(math/0511460). CU's wreath theorem (Sec 7.4) uses the
GROWING base `C_{2n}`; its cocycle witness needs 2n
distinct base elements, which fails for fixed H once 2n
exceeds the exponent (for `H = C_2`, past n = 2).
Literature verdict (d): no paper proves, refutes, or
poses the fixed-H claim; its truth is UNKNOWN and
"likely false" is a route-failure inference, not a
refutation [A].

Barrier cross-checks in the doc: BCCGNSU 1605.06702
Thm B exempts large-cyclic-factor abelian groups;
BCGPU is Lie-type only; Sawin 1702.00905 defers the
abelian case; BCCGU 1712.02302 is bounded-exponent
nilpotent only. None applies.

This verdict is already fully absorbed into the
restated growing-base theorem and its provenance
docstring at `Proofs/GroupTPP/STPPWreath.lean` (Hu8-2a
block near line 1735) [M]. That docstring still points
at `.tasks/f5exp/docs/hu8-q2-literature-check.md`
(line 1744) — repoint it to this file when next
touching STPPWreath [M].

## hu9: novelty crosscheck of the manuscript

Audit target now lives at
`Documents/abelian-factor-refutation.md` [M] (the doc
cites a `Manuscripts/Drafts/` path that no longer
exists). Verdicts, all doc-author assessments [A]:

- `rho_0(A x G) = rho_0(G)` product conjecture: NOVEL.
  Thesis arXiv:0709.1223 Lemma 4.8 gives only the `>=`
  direction; neither Murthy paper states a product
  identity. Independently re-proposed by the
  reading-papers doc from Murthy26 Table 1 consistency.
- Lift law
  `beta_0(C_p x G) = p * max(beta_0(G), Sigma_max^lift)`:
  NOVEL; CU03 Lemma 2.2 gives `>=` only, Neumann
  Obs 4.1 an upper bound but no formula.
- Goursat classification applied to TPP triples in
  `C_p x G`: standard 1889 technique, novel application.
- Exact `beta_0` values: MIXED. A_5 = 108, A_6 = 972,
  PSL(2,11) = 1980 are in Hedtke–Murthy 2012 Tables
  3–4 (known); S_5 = 256, M_10 = 2304, S_6 = 2400,
  A_7 = 10584 found nowhere (possibly novel).
- "Sign configuration" / "sign-liftable" / "twist
  count" terminology: no precursor in the cited corpus.

Citation errata found by the audit — "Murthy
2602.15796 Thm 2.3" and "Prop 2.19(2)" do not exist in
that paper (the real sources are Hedtke–Murthy 2012
Thm 3.5/Obs 3.6), and "CU03 Lemma 3.1" should be
"Lemma 2.2 + 3.1" — are already FIXED in the committed
manuscript; its own correction note records this [M]
(`Documents/abelian-factor-refutation.md`, end matter).

## hu9: barrier and sdpp verdicts

Barrier map, anchored: BCCGNSU (arXiv:1605.06702)
Thm A/B kill bounded-exponent abelian STPP routes and
the strong-USP conjecture (CKSU Conj 3.4); Alman 2019
(arXiv:1812.08731, `References/BilinearComplexity/`
[M]) Thm 1.1 pins `omega_u(CW_q) >= 2.16805`. Surviving
regimes with NO known barrier: non-abelian groups,
abelian groups of unbounded exponent, association
schemes [A]. CKSU Conjecture 4.7 (SDPP) is anchored to
math/0511460 Sec 4 and remains open; Pratt 2023
(arXiv:2309.03878, `References/GroupTPP/` [M]) Thm 1.4
ties it to skew-corner-free set bounds.

Repo-state verdict, still true today: the project has
ZERO DPP/SDPP formalization or computation — no Lean
definition, no reduction, no search code [M: `grep
SDPP` over `Proofs/` is empty]. Product-relevance
stance [A]: wreath products remain the live mechanism;
direct products are the weakest product construction
for the omega program, and the lift law, however good
as group theory, does not reopen an omega = 2 route.

## seam1: wreath family vs the bcgpu barrier

`n_2(G wr S_b) = b - 1` for `b >= 5` is classical
(Rasala 1977; James–Kerber 1981 Ch. 4) — not novel.
The COMPOSED statement — the CU wreath family evades
the BCGPU barrier because `n(G_b)` grows polynomially
while `|G_b|` grows super-exponentially — appears in no
paper [A]; BCGPU's own evasion remark (Sec 1.1) covers
direct products only, and CU predates the barrier.

Errata against the seam premise: "non-perfect G" is
needed only at b = 2 (for `b >= 5` the formula is
unconditional); the barrier is structurally orthogonal
(STPP aggregation bypasses the per-triple bound), not
"silent"; and the operative fact is relative growth,
not the absolute polynomial rate. Lean state:
`BCGPUBarrier.lean` sorry-free, `STPPWreath.lean` and
`WreathNg.lean` carry the wreath side; full
`n_2 = b - 1` needs Clifford theory absent from
Mathlib [A].

## seam2: rho_0 spectrum

Anchors: Eberhard arXiv:1411.0848
(`References/GroupTPP/` [M]) proves rationality of
limit points and reverse well-ordering for the
commuting-probability spectrum; Browning
arXiv:2201.09402 (closedness) is NOT in `References/`
[M missing]. Negative verdicts [A]: the Eberhard
mechanism does not transfer to the `rho_0` spectrum —
its three pillars (Neumann commutator structure,
Egyptian-fraction character decomposition, bounded
denominators) have no TPP analogues, and Murthy's
`p^2/(2p-1)` growth kills the bounded-denominator
route outright. No paper studies well-ordering or
accumulation of `{rho_0(G)}`, and none relates
`Pr(G)` to `beta(G)` — a genuinely unstudied question.

Errata: the spectrum is unbounded (PSL(2,q) grows
~sqrt(q)), so any well-ordering question needs a
domain cut; and `HigherCommProb.lean` formalizes
Levit–Shwartz higher commuting probability, not
Eberhard's spectrum results. The ~20-group corpus is
too sparse to support any spectrum conjecture [A].

## seam3: isoclinism and the lift law

Anchors: Hall 1940 (isoclinism), Lescot 1995
(commuting probability is an isoclinism invariant),
Erfanian–Russo (higher `P_r` invariant).
`Proofs/GroupTPP/IsoclinismInvariants.lean` [M exists]
carries the formalized side.

The load-bearing negative: `rho_0` is NOT an
isoclinism invariant, proved by the Pl15 witnesses
`rho_0(C_2 x M_10) = 64/15 > 16/5`,
`rho_0(C_2 x S_6) = 18/5 > 10/3`,
`rho_0(C_2 x A_7) = 216/35 > 21/5`, combined with
Hall's `G ~ G x A`. All five violations were
brute-verified [A]. No literature connects isoclinism
to TPP or the Cohn–Umans program at all — zero hits on
every crossed search [A]. The commProb/rho_0 dichotomy
is structural: isoclinism preserves commutator
geometry, not the subgroup lattice.

## seam4: twisted fourier bounds

`Proofs/GroupTPP/FourierBarrier.lean` [M exists]
formalizes BCGPU Thm 3.2's proof (`master_bound`).
The seam's question was whether a character-twisted
variant could bound `Sigma_max^lift` against
`beta_0(G)`. Verdicts [A]: no paper bounds
character-twisted convolution counts (Gowers
0710.3877, BCGPU, Eberhard 1512.03517, EKLM
2401.15456, Peluse 2109.12627 all surveyed, none has
twists); the twisted count in G IS the untwisted count
in `C_2 x G`, so the route is circular with a
`2*sqrt(2)` loss, on top of a ~3x slack already
visible at A_5 (BCGPU gives ~328 vs
`beta_0(A_5) = 108`). Stance carried forward: do not
formalize a twisted FourierBarrier — it is provably
weaker than what already exists. The premise's
conflation of "bound |S||T||U|" with "compare
`Sigma_max^lift` to `beta_0`" was the root error.

## seam5: slice rank and the bccgnsu barrier

Formalization-novelty verdict [A]: as of 2026-07 no
ITP has slice rank, tricolored sum-free sets, or the
BCCGNSU barrier; the only neighbor is
Dahmen–Holzl–Lewis's Lean 3 cap-set proof
(arXiv:1907.01449, `References/BilinearComplexity/`
[M]), frozen and without the STPP bridge. The repo's
`Proofs/BilinearComplexity/SliceRank.lean` and
`GroupTensor.lean` are sorry-free [M exist];
Theorems A/B remain unformalized.

Mathematical hazard worth keeping: slice rank is NOT
sub-multiplicative under Kronecker products; BCCGNSU
works around it with the two weaker Prop 3.1 bounds
(`sr * tensor-rank` and `sr * max-side`). And the
open direction is the UPPER bound on diagonal slice
rank (polynomial method side) — `sliceRank_diag`
(lower bound) is done. Cost estimate carried: ~2850
lines [A].

## seam6: verified certificates

Novelty verdict [A]: no prior work verifies
GAP/Sage-imported Cayley tables in a proof assistant;
"first verified group-theoretic computational
certificate" would be genuine if built. Precedent
anchors: Gonthier four-color (Coq 2005), Flyspeck
tame graphs (Isabelle), Schur S(5) via cake_lpr
(2017), LRAT-Catcher (Szeider arXiv:2607.00815),
`K_8(4,2) = 23` (Florath arXiv:2606.16688), covering
codes (Florath arXiv:2606.09600) — all three 2026
papers under `References/Unsorted/` [M].

Feasibility verdicts [A]: single-witness TPP
certification and Cayley-axiom checks are
`native_decide`-feasible to order ~720; exhaustiveness
needs the hybrid verified-pruning architecture reusing
`MurthySmallPGroups.lean` / `HedtkeMurthyNormal.lean`
lemmas; kernel-only trust dies above order ~100, and
`native_decide` trust is honestly close to "trust the
Go engine" — the gap is real but modest [A].

## exact cover (F_2 rank claims)

Verdicts on "exact-cover rank of <n,n,n> over F_2
equals n^3" [A throughout]: the equivalence
exact-cover = composition-method is Lacelle 2026
(arXiv:2606.13408, `References/BilinearComplexity/`
[M], Thm 1 / non-overlap theorem); the schoolbook
count for composition methods is folklore. The LOWER
bound (no exact cover beats n^3) is NOT in Lacelle and
appears new; the explicit conjecture is found nowhere.
Witness anchors: n = 2 has exact-cover rank 8 vs true
rank 7 (Strassen 1969, tight by Hopcroft–Kerr 1971 and
Winograd 1971) vs support rank 7 (Blaser–Christandl–
Zuiddam arXiv:1705.09652 [M]); over F_2 at n = 4,
Strassen-recursive rank 49 is an exact cover while
AlphaTensor's 47 breaks it. One cited source is NOT
fetched: Kauers–Moosbauer–Wood arXiv:2602.11041
[M missing].

## winograd R(2,2,2) >= 7

The campaign landed: `seven_le_rank_matMulTensor_zmod`
and the lift to ℤ are sorry-free in
`Proofs/BilinearComplexity/Winograd.lean` [M]. Surviving
grounding: the correct route is Hopcroft–Kerr 1971 over
F_2, NOT Winograd's original (needs infinite field and
division) [A]; the primary skeleton is Wang et al.,
`References/BilinearComplexity/arXiv-2603-07280/main.tex`
[M] — Sec 2 sketch, Sec 6 forced-product and
substitution lemmas, Appendix D ten-orbit proof.
Novelty claim [A]: first machine-checked matmul rank
lower bound in any ITP; Coq prior art is Strassen
correctness only, and Blaser's survey states the result
without proof. Soundness note: only the pushforward
direction (F_2 lower bound lifts to ℤ) is used.

## goursat classification

The L2 three-case classification of subgroups of
`C_2 x G` is exactly Goursat's lemma specialized to
`A = C_2` — verdict "exactly correct" [A], Sage-checked
on five small groups. Mathlib has
`Subgroup.normal_of_index_eq_two` (needed for the graph
case) but no Goursat's lemma; the recommended
formalization is a direct case split on
`MonoidHom.fst`, not full Goursat [A].

## process and infra residue

The bruteforce audit's sole surviving artifact: Pl1
(group sieve) DID compute before grounding (53% crash
rate from unread GAP API docs), Pl2/Pl3 did not; the
recommendation is a mandatory "library survey"
directive in implementer dispatch prompts [A].

Orientation-doc errata not covered above: `tier4.sage`
had the wrong p = 2 extraspecial involution formula
(`census.sage`'s `2^{2n}+2^n-1` is correct; fixed in
Fg2) [A]; the campaign brief's Cohn–Umans embedding
bound "R <= |G|" was corrected to "R <= R(m_KG)"
(Murthy Thm 4.13 / CU) [A]. The reading-notes doc adds:
every tier citation in the sieve spec checks out
against primary sources [A]; the [24,10]/[24,11]
`rho_0 = 1` facts are known only computationally (HM
2012 tables, reproduced Murthy26 Table 1); Gowers's
Thm 3.3 min-dim includes 1-dim reps and is the wrong
sieve parameter — BCGPU's `n(G)` is correct; the FSV
1701.05328 fetch gap is now CLOSED
(`References/AlgComplexity/arXiv-1701-05328/main.tex`
exists [M]).

## fetch gaps and stale paths

Cited but absent from `References/` [M]: Browning
arXiv:2201.09402, Eberhard arXiv:1512.03517, EKLM
arXiv:2401.15456, Peluse arXiv:2109.12627, Erfanian–
Russo arXiv:2605.17171, Kauers–Moosbauer–Wood
arXiv:2602.11041. Docs cite Murthy papers at
`References/arXiv-2602-15796` and
`References/arXiv-2512-16730`; both actually live under
`References/GroupTPP/` [M]. One committed pointer to
repoint: `Proofs/GroupTPP/STPPWreath.lean:1744` cites
the deleted hu8-q2 doc — its substance is in the hu8
section above [M].

## File dispositions

- .tasks/f5exp/docs/audit-bruteforce-grounding.md — extracted: process verdicts and library-survey protocol kept above; no literature anchors.
- .tasks/f5exp/docs/exact-cover-literature.md — extracted: Lacelle anchor and lower-bound-novelty verdicts kept.
- .tasks/f5exp/docs/goursat-grounding.md — extracted: classification verdict and Mathlib gap kept.
- .tasks/f5exp/docs/gr1-murthy26-digest.md — extracted: theorem anchors, Prop 1.19/2.14 erratum, sharpness witnesses kept.
- .tasks/f5exp/docs/gr2-murthy25-digest.md — extracted: theorem anchors, normality subtlety, [32,11]/[32,27] counterexamples kept.
- .tasks/f5exp/docs/gr3-bcgpu-digest.md — extracted: numbering concordance and scope verdicts kept.
- .tasks/f5exp/docs/gr4-tpp-anchors.md — extracted: CU/CKSU anchors and rho_0 normalization caveat kept.
- .tasks/f5exp/docs/hu8-q2-literature-check.md — extracted: verdict already absorbed into STPPWreath.lean docstring; the line-1744 pointer must be repointed here.
- .tasks/f5exp/docs/Hu9-barrier-analysis.md — extracted: barrier map and surviving-regime verdicts kept.
- .tasks/f5exp/docs/Hu9-literature-crosscheck.md — extracted: novelty verdicts kept; its citation errata are already fixed in Documents/abelian-factor-refutation.md.
- .tasks/f5exp/docs/Hu9-product-relevance.md — extracted: product-construction stance kept; per-paper irrelevance notes dropped as re-derivable.
- .tasks/f5exp/docs/Hu9-sdpp-audit.md — extracted: CKSU 4.7/Pratt anchors and the still-true zero-SDPP verdict kept.
- .tasks/f5exp/docs/murthy-2025-read.md — extracted: no-precedent negatives and Conjecture 5.1 collision analysis kept.
- .tasks/f5exp/docs/murthy-c51-lift-law-check.md — extracted: INDEPENDENT-BUT-ADJACENT verdict and derived chained bound kept.
- .tasks/f5exp/docs/orient-grounding-infra.md — drop: index over the gr digests; its two unique errata (tier4.sage formula, R <= R(m_KG)) kept above.
- .tasks/f5exp/docs/reading-papers-1to4.md — extracted: tier-citation verdict, sieve-parameter note, closed FSV fetch gap kept.
- .tasks/f5exp/docs/seam1-wreath-bcgpu-grounding.md — extracted: classical-vs-composed verdict and three premise errata kept.
- .tasks/f5exp/docs/seam2-rho0-spectrum-grounding.md — extracted: non-transfer verdict, unstudied-question finding, errata kept.
- .tasks/f5exp/docs/seam3-isoclinism-liftlaw-grounding.md — extracted: non-invariance proof sketch and literature-gap verdict kept.
- .tasks/f5exp/docs/seam4-fourier-twisted-grounding.md — extracted: circularity verdict and do-not-formalize stance kept.
- .tasks/f5exp/docs/seam5-slicerank-barrier-grounding.md — extracted: ITP-novelty verdict and sub-multiplicativity hazard kept; component inventory dropped (recover from tree).
- .tasks/f5exp/docs/seam6-verified-certificates-grounding.md — extracted: precedent anchors and feasibility/trust verdicts kept.
- .tasks/f5exp/docs/winograd-grounding.md — extracted: route/novelty verdicts and the arXiv-2603-07280 skeleton anchor kept; campaign itself landed in Winograd.lean.
