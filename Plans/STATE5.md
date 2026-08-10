# STATE5 — formalization state deltas

Distilled 2026-08-10 from the `.tasks/{f5exp,main}/docs`
formalization shard (ledger, roadmap, 11 coverage batches,
9 leandoc audits, clifford coverage, reconcile), superseding
those files. The committed tree (`Proofs/**`,
`Formalize/INDEX`, git log) remains the record of what
landed; this file keeps only what the tree cannot say:
Mathlib coverage verdicts that shaped statement design,
triage of never-attempted targets, rejected routes, and
ledger-vs-tree discrepancies. Tags: [M] machine-verified
(by the source doc or by this distillation), [A] asserted
in a source doc without independent check.

All Mathlib verdicts below were audited against the
v4.30.0-rc2 toolchain on 2026-07-17/18. The tree is now on
v4.33.0-rc1 (bumped in commit 68ff035, 2026-07-29), so every
Mathlib-absence claim in this section predates the bump and
needs re-verification before use. Absence claims originally
tagged [M] should be read as [A, pre-bump] until re-checked.

## mathlib coverage verdicts

These are the audits' research conclusions. "Missing" means
the auditor searched leandoc/grep over vendored Mathlib and
found nothing; it is corpus-relative, not a nonexistence
proof.

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
  `Proofs/GroupTPP/STPPWreath.lean` today. [M] The
  blocker is extracting the multinomial prefactor from
  the M-th root limit (CKSU tex:1606-1629). Three
  recorded resolution options: (a) dedicated
  `factorial_root_mul_le_of_factorial_pow_le`, (b) route
  through `sum_le_of_multinomial_prod_pow_le`, (c) a
  shorter CommGroup-only proof avoiding multinomial
  selection. [A]
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

## ledger-vs-tree deltas

The ledger snapshot is 2026-07-18 and PREDATES two
renames: its `Proofs/Xlib/*.lean` paths are now
`Proofs/GroupTPP/*.lean`, and its `Proofs/Proofs/ErdosNNN`
paths are now `Proofs/Erdos/ErdosNNN`. [M] Any historical
commit-message or doc reference to `Xlib` means today's
`GroupTPP`.

Provenance hazards the ledger records that git cannot
show:

- The Ax1 axiom re-audit is VOID: `lakefile.toml`'s
  default target skipped Xlib, so its `lake build` was a
  no-op and the axiom probe read stale Jul-12 oleans; the
  "noncomputable defs in #print axioms" anomaly was a
  stale-artifact effect. Cu2 compiled and re-audited.
  Distrust any axiom claims sourced to Ax1. [M]
- The roadmap's famous "131 sorries" figure was
  grep-inflated and pre-Pl10; the real debt after Pl10
  was 4, all in `STPPWreath.lean`. Two remain today. [M]
- `abelian_wreath_family_tendsto_two` kept its NAME but
  changed statement (fixed-base -> growing-base family)
  after the original was found ungrounded — the (n!)^3
  witness violates pairwise bounds for fixed H at large
  n. Same-name-different-theorem across history. [M]
- `wreath_charDegree_bound` was weakened in place from
  `[Group H]` to `[CommGroup H]` (general case = shelved
  Gh1). [M]
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

For `Formalize/INDEX` staleness itself, `Plans/PLAN.md`
chore X2 is the state of record; this shard's docs add no
INDEX deltas beyond it.

## File dispositions

- .tasks/f5exp/docs/formalization-ledger.md — extracted: planned/rejected/hard items, Ax1 voiding, and name-stability hazards captured above; landed-work claims recoverable from tree.
- .tasks/f5exp/docs/formalization-roadmap.md — extracted: ruled-out routes, hardness grades, and still-open P6/Schoenhage targets captured; landed claims recoverable from tree.
- .tasks/f5exp/docs/formalize-coverage-batch-01.md — extracted: Yadav ABSENT verdict + LittleWedderburn/Nath-Das pitfalls.
- .tasks/f5exp/docs/formalize-coverage-batch-02.md — extracted: Hedtke-upgrade and Kurdachenko–Shumyatsky ABSENT verdicts + TPP-table caveat.
- .tasks/f5exp/docs/formalize-coverage-batch-03.md — extracted: Le Gall/secant/Eberhard ABSENT verdicts + RegularWreathProduct pitfall.
- .tasks/f5exp/docs/formalize-coverage-batch-04.md — extracted: orbit-method and Sawin ABSENT verdicts + BCGPU citation pitfall.
- .tasks/f5exp/docs/formalize-coverage-batch-05.md — extracted: length/depth, galactic, irreversibility ABSENT verdicts + 1712.02302 attribution pitfall.
- .tasks/f5exp/docs/formalize-coverage-batch-06.md — extracted: geometric-rank, AVW-laser, Pr_p ABSENT verdicts.
- .tasks/f5exp/docs/formalize-coverage-batch-07.md — extracted: five ABSENT verdicts incl. corners-STPP and asymptotic rank.
- .tasks/f5exp/docs/formalize-coverage-batch-08.md — extracted: three ABSENT verdicts + the one medium-high-confidence caveat (2411.18534).
- .tasks/f5exp/docs/formalize-coverage-batch-09.md — extracted: quantum-Clifford, nilpotent-generation, cactus ABSENT verdicts.
- .tasks/f5exp/docs/formalize-coverage-batch-10.md — extracted: C-to-Q transfer gap and CU/CKSU partial verdicts; no unique ABSENT targets.
- .tasks/f5exp/docs/formalize-coverage-batch-11.md — extracted: Avino-Diaz ABSENT verdict + sl_n structure-tensor gap.
- .tasks/f5exp/docs/mathlib-clifford-coverage.md — extracted: Clifford-theory gap inventory and 4000-8000-line estimate; Maschke claim corrected here.
- .tasks/f5exp/docs/orch-leandoc-audit-center.md — extracted: center-layer missing-declaration verdicts.
- .tasks/f5exp/docs/orch-leandoc-audit-commprob.md — extracted: commProb/isoclinism verdicts + conjClassesProdEquiv upstream flag.
- .tasks/f5exp/docs/orch-leandoc-audit-erdos.md — extracted: restricted-sumset/gap-counting/multigraph verdicts.
- .tasks/f5exp/docs/orch-leandoc-audit-fourier.md — extracted: nonabelian-Fourier gap inventory.
- .tasks/f5exp/docs/orch-leandoc-audit-limits.md — extracted: Archimedean-helper and slice-rank/omega absence verdicts.
- .tasks/f5exp/docs/orch-leandoc-audit-monoidalgebra.md — extracted: tensorEquiv commutativity block + piAlgEquiv subsumption (now applied).
- .tasks/f5exp/docs/orch-leandoc-audit-rank-calculus.md — extracted: 3-tensor gap inventory + Fin-indexed design rationale.
- .tasks/f5exp/docs/orch-leandoc-audit-tpp.md — extracted: TPP-absence verdicts + Finset.inv_inv upstream flag; IsTPP unification since landed.
- .tasks/f5exp/docs/orch-leandoc-audit-wedderburn.md — extracted: Artin–Wedderburn uniqueness gap + upstream-quality assessment.
- .tasks/f5exp/docs/reconcile-lean-audit.md — extracted: sorry-count correction, Goursat two-open-lemmas correction, Maschke discrepancy (resolved), Aw1 ungrounded flag.
