# Grounding — claim-to-source anchor layer

What grounds what, in which primary source.
Misquote records, errata, Mathlib coverage verdicts,
fetch gaps, and the prior-art enumeration.

Sources: `git show 4901d3b:Plans/STATE6.md` wholesale; `git
show 4901d3b:Plans/STATE5.md` sections "mathlib coverage
verdicts" (with pre-bump caveat), "unattempted and rejected
targets", "ledger-vs-tree deltas", "known-hard, shelved, and
honestly partial" (excluding stpp resolution options),
"File dispositions"; `git show 4901d3b:Plans/PLAN.md` section
"PRIOR ART, as enumerated"; reorganized 2026-08-10.


## mathlib coverage verdicts

All Mathlib verdicts below were audited against the
v4.30.0-rc2 toolchain on 2026-07-17/18. The tree is now on
v4.33.0-rc1 (bumped in commit 68ff035, 2026-07-29), so every
Mathlib-absence claim in this section predates the bump and
needs re-verification before use. Absence claims originally
tagged [M] should be read as [A, pre-bump] until re-checked.

### group algebra center (`GroupAlgebraCenter.lean`)

Exists: `ConjClasses` API, `MonoidAlgebra.basis`,
`Matrix.subalgebraCenter_eq_scalarAlgHom_map`,
`AlgEquiv.subalgebraMap`, `Set.center_pi`, and
`centerCongr` at `Subgroup`/`Subring`/`Subsemiring`. [M]
Missing: `Subalgebra.centerCongr` (the one layer without
it), class sums and the class-sum basis of Z(k[G]),
`finrank_center = Nat.card (ConjClasses G)`, `center_pi`
at `Subalgebra` level, `map_center`. [M] Everything in the
project's center layer is original for this reason.

### commuting probability / isoclinism

Mathlib's `commProb` API is rich (`commProb_def'`,
`inv_card_commutator_le_commProb`, prod/pi/quotient
lemmas, `DihedralGroup.commProb_reciprocal`, class
equation). [M] Missing entirely: the 5/8 bound, any
isoclinism notion, r-th commuting probability, Hall's
Lemma A, the Nath–Das strengthened lower bound, explicit
nilpotency-class-2 structure. [M] Flagged upstreamable
independent of the campaign: `conjClassesProdEquiv`
(`ConjClasses (G x H) ~= ConjClasses G x ConjClasses H`).

### erdos support lemmas

Missing: restricted sumsets `{a+b : a != b}` (Cauchy–
Davenport in Mathlib is unrestricted only), a 1D
gap-separated counting primitive
(`Besicovitch.card_le_of_separated` is metric, not it),
and any degree/regularity/handshake API on the new
`Graph alpha beta` multigraph type. [M] Design verdict:
the project's `Multiset (Sym2 V)` multigraph carrier is
architecturally incompatible with Mathlib's `Graph`
(separate edge type + incidence); no migration until
`Graph.degree` lands upstream.

### nonabelian fourier / BCGPU

Mathlib has the primitives (trace lemmas, Frobenius norm,
`posSemidef_conjTranspose_mul_self`, C*-algebra
positivity) but zero nonabelian Fourier theory: no
Wedderburn-block Fourier inversion, no Plancherel/Parseval
for group algebras, no Hilbert–Schmidt Cauchy–Schwarz
`|Tr(MN)| <= ||M||_F ||N||_F`, no unitarian trick. [M]
The 1183-line `FourierBarrier.lean` support layer is
built from scratch; the audit found 0 of its 6 conceptual
sections eliminable.

### analytic helpers / omega / slice rank

Missing: Archimedean constant absorption
(`x^l <= K*y^l for all l -> x <= y`; Mathlib only has the
constant-free case), root convergence along `1/l`, and —
with zero Mathlib hits — slice rank, tensor rank as
sum-of-rank-1, diagonal tensors, and any matrix
multiplication exponent. [M]

### monoid algebra equivalences

`MonoidAlgebra.tensorEquiv` exists but requires
`CommSemiring` on both algebras and `CommMonoid` on the
monoid — doubly blocked for `Matrix m m C` over a
noncommutative group, which is why
`matrixMonoidAlgEquiv` goes through `liftNCAlgHom`
directly. [M] Missing: `AlgEquiv.piCurry` (the `Equiv`
and `LinearEquiv` versions exist), MonoidAlgebra-over-Pi
distribution. `Matrix.piAlgEquiv` exists and subsumed
the project's local copy (adoption verified in tree). [M]

### 3-tensor rank calculus

Mathlib has no concrete coordinate 3-tensor type
(`PiTensorProduct` is module-level), no tensor rank, no
structure tensor, no 3-tensor Kronecker/direct
sum/cyclic-rotation/contraction, no GL-invariance of
rank. [M] Deliberate design stance: concrete
`Fin`-indexed coordinate model over
`PiTensorProduct`/`SymmetricPower` (abstraction tax;
`SymmetricPower` API too green). Refactoring to
product-type indices to reuse `Matrix.kroneckerMap` was
rejected — it would propagate type changes across the
whole campaign.

### TPP layer

`TripleProductProperty` absent from Mathlib (trivariate;
`UniqueMul` is bivariate). No finset `leftQuot`, no
`Finset.inv_inv` / `InvolutiveInv (Finset G)` instance —
the project's `finset_inv_inv` at
`Proofs/GroupTPP/TPP.lean:527` is still local and remains
an upstream candidate. [M] The audit's
`DihedralTPP.IsTPP` duplication finding is resolved: it
is now an `abbrev` for `TripleProductPropertyR`
(verified in tree 2026-08-10). [M]

### wedderburn uniqueness

Mathlib's `Isotypic.lean`/`WedderburnArtin.lean` layer is
strong, but Artin–Wedderburn *uniqueness* is an open TODO
at `Mathlib/RingTheory/SimpleModule/Basic.lean:48-49`;
the project's `isotypicLengthMultiset_eq_of_algEquiv` is
the only formalization the audit knew of. [A]
`length_eq_of_semilinear` is strictly more general than
Mathlib's `LinearEquiv.length_eq`. The audit judged this
whole layer clean upstream material. `charDegrees` was
deliberately defined via Wedderburn rather than `FDRep`
because `FDRep` lacks an enumeration of irreducibles.

### clifford theory (general-base wreath blocker)

Mathlib has `Representation.ind`, `Rep.resFunctor`,
`DoubleCoset`, characters, Schur, and group extensions,
but none of Clifford theory: no `dim Ind = [G:H] dim V`,
no Frobenius reciprocity, no induced character formula,
no conjugation action on `Irr(N)`, no inertia subgroups,
no Mackey decomposition, no projective representations /
Schur multiplier bridge. [M] Estimate: general-base
`wreath_charDegree_bound` needs ~4000-8000 new lines with
no shortcut. One audit claimed the Maschke semisimplicity
instance was also missing; the roadmap said it exists.
Resolved: `Mathlib/RepresentationTheory/Maschke.lean`
provides `IsSemisimpleRing k[G]` — the clifford audit
searched wrong. [M]

Cross-audit upstream shortlist: `conjClassesProdEquiv`,
`Finset.inv_inv`, `Subalgebra.centerCongr`,
`norm_trace_mul_le`, Artin–Wedderburn uniqueness.


## unattempted and rejected targets

### coverage-batch triage (2026-07-22, 53 arXiv targets)

Verdict split 9 COVERED / 18 PARTIAL / 26 ABSENT.
[A] All confidence tags were "high" except arXiv-2411.18534
(medium-high, vague brief). The committed
`Formalize/arXiv-*.md` cards do NOT carry these verdicts
(spot-checked), so this list is the only surviving record.
[M]

ABSENT — triaged, never attempted, with the blocking gap:

- 1011.2083 Yadav |G/Z| vs conjugacy sizes: needs
  IsCentralProduct/IsHomocyclic; Mathlib's Wiegold bound
  is a different result.
- 1107.5973 Hedtke STPP upgrading: no growth analysis for
  extending a subgroup by one element.
- 1204.4641 Kurdachenko–Shumyatsky ranks: needs Fitting
  subgroup + Schreier assembly.
- 1401.7714 Le Gall omega < 2.3728639: laser method, CW
  tensors, convex optimization all missing.
- 1406.5145 secant-variety lower bounds: no secant
  variety, Waring rank, or catalecticant.
- 1411.0848 Eberhard limit points of Pr(G):
  classification/model-theoretic machinery out of reach.
- 1612.01527 Grochow–Moore orbit constructions: no
  group-orbit tensor decomposition framework.
- 1702.00905 Sawin multiplicative matchings: no
  definition, closest tangent is TPP.
- 1802.02194 length/depth of finite groups: neither
  invariant exists (`RelSeries.length` is raw chains).
- 1810.08671 Alman–VW galactic barriers: no CW_q family,
  laser or galactic method, asymptotic rank.
- 1812.06952 CVZ irreversibility: no degeneration
  preorder, irr(t), or relative exponent.
- 2002.09472 geometric rank: no geometric rank, subrank,
  or border subrank.
- 2010.05846 Alman–VW omega < 2.3728596: laser machinery.
- 2112.08681 Pr_p commuting probability: no p-core O_p(G)
  or concrete PSL_2(p).
- 2210.10173 DWZ omega < 2.371866: asymmetric hashing +
  laser.
- 2307.07970 VWXXZ omega <= 2.371552: same, plus dual
  exponent alpha.
- 2309.03878 corners-to-STPP barriers: only basic
  `IsCornerFree` exists, no bridge.
- 2311.06666 modular isomorphism problem: statement never
  formalized though blocks exist.
- 2404.06427 Strassen asymptotic-rank universal sequence:
  asymptotic rank not even defined.
- 2410.14905 Lie-group separating functions: framework
  absent.
- 2410.23034 conjugacy ratio: no word-metric balls or
  abelian-by-cyclic classification.
- 2411.15789 asymptotic rank Zariski-closed: absent at
  the definitional level.
- 2504.12263 Clifford commutant: quantum Clifford group
  (not `CliffordAlgebra`), Pauli group, Schur–Weyl all
  absent.
- 2511.19494 nilpotent generation bounds: len >= rank
  inequality absent.
- 2602.11309 cactus barriers: Hilbert schemes /
  smoothability / cactus varieties are an acknowledged
  project-level open gap.
- math/0606605 Avino-Diaz Delta(G) algorithm: max normal
  p-subgroup of Aut(G) machinery missing.

Recurring gaps, in order of leverage: (1) laser method /
CW tensor family — blocks six omega-record targets; (2)
scheme-theoretic algebraic geometry (Hilbert schemes,
secant/cactus varieties) — blocks three border-rank
targets. [A]

Pitfalls recorded on PARTIAL/COVERED targets worth
keeping: `LittleWedderburn` is the wrong Wedderburn
(finite division rings, not semisimple decomposition);
Mathlib's `inv_card_commutator_le_commProb` is the weak
1/|G'| bound, not Nath–Das; Mathlib's
`RegularWreathProduct` is NOT the imprimitive wreath
`D^n x| S_n` Cohn–Umans needs (checked, does not
subsume); `BCGPUBarrier.lean` formalizes arXiv 2204.03826
— citations of it for 1605.06702 or 1712.02302 theorems
are wrong; project flattening bounds RANK, not border
rank (Young flattenings absent); exhaustive TPP tables
(1104.5097) are computational artifacts, not theorems.

### ledger: rejected routes (why, not just what)

- `matrixMonoidAlgEquiv` via `MonoidAlgebra.tensorEquiv`:
  doubly blocked by `CommSemiring`+`CommMonoid`
  constraints; rebuilt directly on `liftNCAlgHom`. [M]
- Commutativity transport via `Pi.evalAlgHom.surjective`:
  no `RingHomSurjective` instance; replaced by explicit
  `Pi.single` preimage. [M]
- Geom-arith inequality via entropy+Stirling: never
  attempted; the multinomial route won because Mathlib
  has `Finset.sum_pow_eq_sum_piAntidiag`. [M]
- `pseudoExponent_wreath_le_gamma` as first stated:
  RHS dropped CU's positive O(1/log^2 n) term; provable
  only for n=2..5, OPEN for n>=6 (Sage sweep to 10^9
  confirms). Repaired by restating with CU's exact
  gamma. [M]
- Hom-form/invertible-contraction proof of
  `rank_mulTensor_le_sum_charDegrees`: the entire
  RankCalculus machinery was unnecessary; a trace-form
  argument is strictly shorter. [M]
- Fixed-base H=C2 wreath family: "CU Prop 11" matches
  nothing in CU and the cocycle witness is impossible
  past n=2; restated as growing-base family. [M]

### roadmap: routes ruled out and still-open targets

Ruled out with reasons (2026-07-12): BB border-apolarity
Thm 4.18 (needs multigraded Hilbert scheme);
Ellenberg–Gijswijt cap-set barriers (no slice-rank
consumer); laser-method omega records (near-zero reuse);
coherent-configuration library for one rigidity lemma
(fails worth-formalizing test); `charDegrees` via `FDRep`
(no irreducible enumeration); building on
`PiTensorProduct`/`SymmetricPower` (abstraction tax).

Most roadmap priorities (charDegrees foundation, rank
calculus, omega, slice rank, TPP unification) have since
landed — see tree. Still open as of today:

- Waring rank + catalecticant layer (roadmap P6):
  `WaringRank`, catalecticant flattening,
  `WaringRank(sM3) <= 18` from the CHILO identity. No
  trace in tree (grepped 2026-08-10). [M]
- Schoenhage tau theorem: deliberately deferred as a
  named hypothesis; hard.
- Murthy Thm 4.13 (TPP induces degeneration): landed.
  `Proofs/BilinearComplexity/GroupTensor.lean` header names
  Murthy 4.13; `rank_matMulTensor_le_of_isTPP` (line ~124)
  proved sorry-free. [M]

### known-hard, shelved, and honestly partial

- Gh1, general-H `wreath_charDegree_bound` (Huppert
  25.6): shelved; needs full Clifford theory, >= 5
  cards; abelian branch covers all current consumers. [A]
- `stpp_capacity_le` / `stpp_capacity_le_of_wreath`
  (CKSU asi): still sorry in
  `Proofs/GroupTPP/STPPWreath.lean` today. [M]
- Erdos 175 analytic tail: the powers-of-2 case is
  proved only for k <= 30; the k > 30 tail needs
  Granville–Ramare 1996 analytic methods, documented
  permanently out of scope. The formalization is
  honestly partial. [A]
- Goursat route (beta0(C_2 x G)): entirely informal —
  no Lean artifact exists at all. The two actual open
  lemmas (not the earlier misidentified pair): (i)
  intersection-separated configurations never exceed the
  census maximum, (ii) "sign-liftable" matches census
  eligibility semantics. [A]


## Ax1 axiom-audit voiding record

The Ax1 axiom re-audit is VOID: `lakefile.toml`'s
default target skipped Xlib, so its `lake build` was a
no-op and the axiom probe read stale Jul-12 oleans; the
"noncomputable defs in #print axioms" anomaly was a
stale-artifact effect. Cu2 compiled and re-audited.
Distrust any axiom claims sourced to Ax1. [M]


## ledger-vs-tree deltas

The ledger snapshot is 2026-07-18 and PREDATES two
renames: its `Proofs/Xlib/*.lean` paths are now
`Proofs/GroupTPP/*.lean`, and its `Proofs/Proofs/ErdosNNN`
paths are now `Proofs/Erdos/ErdosNNN`. [M] Any historical
commit-message or doc reference to `Xlib` means today's
`GroupTPP`.

Provenance hazards the ledger records that git cannot
show:

- The roadmap's famous "131 sorries" figure was
  grep-inflated and pre-Pl10; the real debt after Pl10
  was 4, all in `STPPWreath.lean`. Two remain today. [M]
- `stpp_capacity_le_comm` is sorry-free itself but
  depends on the sorry'd skeleton — do not cite it as an
  unconditional result. [A]
- Audit-era cleanups since resolved in tree (verified
  2026-08-10): `matrixPiAlgEquiv` replaced by
  `Matrix.piAlgEquiv`; `DihedralTPP.IsTPP` unified as an
  abbrev of `TripleProductPropertyR`; the Maschke
  instance question settled (exists in Mathlib). [M]
- Still open from the audits: `finset_inv_inv` remains
  local (upstream candidate). [M] The `higherCommProb G 2 =
  commProb G` bridging lemma is proved:
  `Proofs/GroupTPP/HigherCommProb.lean:372`,
  `@[simp] theorem higherCommProb_two`. [M]

For `Formalize/INDEX` staleness itself, `Plans/debt.md`
chore X2 is the state of record; this shard's docs add no
INDEX deltas beyond it.


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

matmul-endgame.md cross-references this "CU Prop 11"
phantom record.

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
and the lift to Z are sorry-free in
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
direction (F_2 lower bound lifts to Z) is used.

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


## prior art, as enumerated

(From PLAN.md. Standing verdicts that consume these
findings are in standing.md.)

Recorded here because the canonical grading document
(`.tasks/main/docs/novelty-ErdosCovering.md`) is outside version control.
Each absence names the enumeration it was checked against.

  alpha(p) / Pisano   Absent from Mathlib rev 3edb3c0 (`grep -ric
                      apparition|pisano` over Mathlib/ = zero files).
                      Absent from AFP (63 NT entries enumerated) and
                      from Coq/Rocq sources checked. agda-unimath DOES
                      have `elementary-number-theory.pisano-periods` —
                      closest prior art anywhere; it defines the period
                      but not the entry point, and does not prove the
                      zero-set theorem. The mathematics is routine
                      (Vajda 1989 p. 73); first-formalization at most,
                      never new mathematics.
  Naslund-Sawin       No prior formalization found. formal-conjectures
                      `ErdosProblems/857.lean` exists but is a stub —
                      `answer(sorry)`, body `sorry`, 0 lines proved.
                      Mathlib has zero sunflower/slice-rank content. AFP
                      `Sunflowers` is Erdos-Rado, i.e. #20, a different
                      problem. Lean 3 `lean-forward/cap_set_problem` is
                      Ellenberg-Gijswijt, method-adjacent but not this.
                      `SproutSeeds/sunflower-lean` is structural, not
                      the tensor bound.
  Covering in Lean    NOT clear ground. erdosproblems.com links
                      per-problem Lean artifacts in personal repos: #16
                      is "disproved (Lean)" via D. Chin 2026-02-25,
                      building two covered APs from the SAME
                      {3,5,7,13,17,241}/period-24 system as
                      NotTwoPowerPlusPrime. Sweep each entry's comment
                      thread before any novelty claim, not just the
                      formal-conjectures tree.

  Sunflower lemma     Sweep 2026-08-07 (absorbed 2026-08-10 from the
                      retired results ledger): "sunflower" absent
                      from every Mathlib file; LeanCamCombi
                      explicitly checked, absent; formal-conjectures
                      has only a statement-request issue (#2284); no
                      Lean repos or Zulip threads; AFP entry
                      confirmed — Thiemann, Feb 2021, CLASSICAL
                      Erdos-Rado bound only. Nobody in any prover
                      has the ALWZ improved bound (the L-effort
                      target in NEW TARGETS above). Bloom's comment
                      on #535 acknowledges the gcd-sunflower
                      connection exists; no prior formalization of
                      it found. Confirms P5's first-in-Lean claim.
  Integer complexity  Sweep 2026-08-07 (absorbed 2026-08-10 from the
                      retired results ledger): no formalization of
                      integer complexity (A005245 / Mahler-Popken)
                      or ANY theorem about it in Mathlib, AFP,
                      Coq/Rocq, Mizar, Metamath, or HOL Light; the
                      Latvia group / Altman / Zelinsky literature is
                      computation only — first-formalization claim
                      for ||3^b|| = 3b (d657720). Attribution audit:
                      the cube-bound route is Iraids et al.
                      `cbounds2` (arXiv:1203.6462); the earlier
                      Iraids->Altman fix concerned the separate
                      window theorems only. Supports the Mathlib PR
                      (`Documents/mathlib-integer-complexity/
                      PROPOSAL.md`) and a future ||2^n|| = 2n post.

  LIMIT on all of these: GitHub code search does not index every repo
  and was unauthenticated for the alpha sweep; the Rocq opam index (584
  packages) and the Mizar MML (~1300 articles) were not enumerated
  exhaustively. "None found in the corpora named" is the claim; "does
  not exist" is not.
