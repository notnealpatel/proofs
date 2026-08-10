# STATE2 — audit debt

Distilled 2026-08-10 from the 33 audit-debt working docs
under `.tasks/f5exp/docs/` and `.tasks/main/docs/`
(shard 2 of the doc-retirement campaign). This file
supersedes those docs. Every item below was cross-checked
against the tree at commit `7b0e828` before recording.
Tags: [M] = verified in the current tree by this
distillation, [A] = agent/auditor assertion carried from
the source docs, [O] = observation.

## ad1 burndown: verified, with residue

Card `Ad1` (status done) claimed to retire every
2026-07-29 f5exp vacuity finding. Per-item verification
against the tree confirms all six items landed as commit
`2cb92cc` [M]: the Fubini `native_decide` chain is gone,
`strassen_isDecomp_F2` / `schoolbookDecomp333_length` are
kernel `decide`, `two_le_shearCount_of_quad` is restated
embedding-generic with the n = 5 witness at
`Proofs/ShearEC/ShearQuadraticRank.lean:791`,
`lakefile.toml` sets `autoImplicit = false`,
`extraspecialD4` exists at
`Proofs/GroupTPP/ExtraspecialLattice.lean:314`, and the
stale-text fixes are in place. A follow-up vacuity
recheck independently re-derived the item-3 and item-5
repairs and returned SOUND [A]. The card is trustworthy;
what survives is the declared residue below.

The burndown's own residual list, current status [M]:

- Q8 companion witness
  (`ExtraspecialData (QuaternionGroup 2)`): not built.
  Without it `subgroupCount_eq_of_same_rank` is only ever
  instantiated at (D4, D4), where it is reflexive. GAP
  evidence says the cross-type instance is true and
  non-trivial (D4 and Q8 upper lattices agree 3/1) [A].
- Commutator-form `B`: the D4 witness supplies the
  coordinate symplectic form, not the literal commutator
  pairing; equivalence argued in prose (uniqueness of
  the nondegenerate alternating form on a 2-dim F2
  space), not in Lean [A].
- `fubini_eq_sum_range` private duplicate still at
  `Proofs/Enumerative/A051293/Analytic.lean:540`,
  redundant with public `fubini_succ_eq_sum_range`.
- `Proofs/Scratch/ShearReviewAudit.lean` still opens
  with `import Xlib`, a lib that no longer exists;
  invisible only because `Scratch` is not a default
  target.
- Methodology note worth keeping: phantom-binder audits
  must re-elaborate whole files under
  `autoImplicit = false`; `#check @` sampling missed 14
  live phantoms in `PeelingSupport.lean` [A].

## dangling in-tree pointers

Three committed Lean files cite docs this retirement
deletes [M]. My stance: repoint them at this file, since
the substance now lives here.

- `Proofs/CHILO/ConnerWaring.lean:26,42` cite
  `vacuity-chilo.md` as the erratum verification record.
- `Proofs/GroupTPP/ExtraspecialLattice.lean:121` cites
  `vacuity-ad1-recheck.md` for the D1 scope note.
- `Proofs/ShearEC/ShearQuadraticRank.lean:45,736` cite
  `vacuity-shearec.md` for the n = 4 emptiness argument.

## conner–waring erratum record

Content of the cited verification record, preserved [A]:
arXiv:1711.05796 (Conner, Exp. Math. 30(3)) prints
`a = -2^{-1/3}`. Forcing the trace identity at `A = I`:
traces of `m_1..m_9` are 2 each, `m_10` is `3a`,
`m_11..m_18` are 0, so `72 + 27a^3 = 6*tr(I^3) = 18`,
giving `a^3 = -2`, i.e. `a = -2^{1/3}` — an exponent
sign typo. Sage symbolic check: the identity fails mod
`(w^2+w+1, a^3+1/2)` and holds mod `(w^2+w+1, a^3+2)`;
200-bit numeric check `|(-2^{1/3})^3 + 2| ~ 2.5e-60`.
No published erratum was found; the corrected constant
is unique. The Go oracle `cmd/probe-waring` now exists
in-tree [M], so the numerical side is re-runnable.

## shearec n = 4 scope note

The pre-repair `two_le_shearCount_of_quad` was stated
over `Circuit 4`, where register count = variable count
leaves no workspace register; the hypothesis class is
believed empty by a structural argument, not
kernel-refuted [A]. The restated theorem forces only
`4 <= n` (via the injective embedding); at `n = 4` no
witness is known, content is carried at `n = 5` by
`quadWitness`. Docstrings at :44 and :733 disclose this
[M]. Optional hardening endorsed by the recheck: restate
`two_le_shearCount_of_quad_tight` as an existential
(`∃ Ci, polys Ci 4 = ... ∧ shearCount Ci = 2`) so the
exhibit is carried by the statement, not the proof
route; the current conjunction form survives a silent
reproof by `decide` [A]. Not done [M].

## extraspecialdata drift (d1)

The recheck's one finding, low severity, still live.
`ExtraspecialData` fields do not force `Z = center G`,
`V = G/Z`, or `B` = commutator form; the class provably
contains non-extraspecial groups — the probe built
`ExtraspecialData C2` at `n = 0`, `Z = ⊤`, `V = PUnit`,
`B = 0`, axiom-clean, and abelian models exist at
`n >= 1` too (e.g. C4 x C2) [A]. Consequence: do not
cite `subgroupCount_eq_of_same_rank` as a formalized
theorem about extraspecial groups per se; the binding is
witnessed only at D4. The module header now carries an
honest scope note [M], but the field docstrings still
assert the textbook bindings ("The center
`Z(G) = G' = Φ(G)`", "commutator symplectic form") [M].
Repair options: retitle field docstrings as intended
readings, or add tying fields in a strengthened variant.
The Q8 + commutator follow-ups would close most of this.

## sorry inventory

Audit-relevant sorries, all still open [M]:

- `Proofs/BilinearComplexity/PeelingSupport.lean:498`
  `cover_outmass_even` (intended, L3b); taints its one
  consumer `outmass_ge_two` [A].
- `Proofs/GroupTPP/STPPWreath.lean:389`
  `stpp_capacity_le` — blocked on Clifford theory for
  wreath character degrees; triage estimated ~4-8k lines
  [A]; the Pl21 Clifford campaign never materialized
  (no Clifford files under `Proofs/`) [M].
- `Proofs/GroupTPP/STPPWreath.lean:939`
  `stpp_capacity_le_of_wreath` — the factored skeleton;
  its gap is the multinomial assembly [A].

Everything else the f5exp triage tracked was discharged:
CUCapacity (2), BCGPUBarrier (4), and the wreath chain
`wreath_charDegree_bound` through
`abelian_wreath_family_tendsto_two` are sorry-free [M].
The ~40 other sorries under `Proofs/` are intended
open-conjecture archives (per-file "intended sorry"
convention), self-documenting in-tree; they are not
audit debt. Note `stpp_capacity_le` has zero term-level
consumers [M] — the capacity chain routes around it.

## native_decide surface

Deliberate, audited-acceptable residue [M]:
`strassen_minpeak_F2`
(`PeelingCert222.lean:49`, 5040 permutations) and
`schoolbookDecomp333_isDecomp` / `_peak`
(`PeelingCert333.lean:62,67`, 729 cells x 27 triads);
kernel reduction judged infeasible, values
cross-checked externally [A].

One stray: an anonymous `example` at
`Proofs/GroupCount/Structures.lean:249` keeps
`native_decide` in the import closure of the GroupCount
lane [M]. Logically inert (no named constant), but it
falsifies any lane-level "zero native_decide in closure"
claim; single root cause behind two review findings
(Gnu STYLE-8, DennisSurjectivity TRUST-2).

## grouptpp findings still open

From the f5exp GroupTPP audit, unrepaired [A], spot
confirmations [M] where noted:

- F2: `WreathNg.lean:72-74,399-405` still claim
  `minNontrivIrrepDim` rests on a foundational
  CharDegrees sorry that is long discharged; a reader
  auditing trust from these docstrings would wrongly
  downgrade the results.
- F3: `WreathNg.lean:406-413`
  `minNontrivIrrepDim_wreathS2_eq_two_of_ne_zero`
  carries an unused non-perfectness hypothesis and its
  conclusion is pinned by arithmetic bookkeeping; it
  asserts nothing about wreath products.
- F4: `DihedralTPP/Basic.lean:16` claims sharpness "for
  `3 | n`"; only n = 6 is formalized (decide-verified).
- F6: `HigherCommProb.lean:104,372` admit infinite `G`
  where `higherCommProb` junk-evaluates to 0, making
  those two statements hold at 0 = 0*0.
- F8: `MurthyClass2.lean:759` unused `_h : IsClass2 G`
  (consumed at call sites, so decorative not harmful).
- F9/F10: cosmetic `d > 1` in a def body; monolithic
  `import Mathlib`. Recorded, no action needed.

## docstring and style debt

Counts from the audits, unrepaired, spot-verified [M]:

- AlgComplexity: 37 public theorems without docstrings
  (23 Circuit, 1 BorderRank, 13 Apolarity).
- BilinearComplexity: 25 public declarations.
- Enumerative: ~6 (`zumkeller_identity`, `b_comb_eq_b`,
  `a_comb_eq_sum`, `S_expansion`, `polylog_summable`,
  `polylog_shift_tsum`).
- GroupTPP: 6 in `FDRepBridge.lean` plus
  `piMonoidAlgFwd`, `matrixColEquiv`.
- Erdos20: `Sunflower.lean` has zero docstrings on its
  8+ core defs, and its defs sit in the root namespace.
- CHILO: `omegaC_rel`, `cbrt2_cube`
  (`ConnerWaring.lean:148,158`).

Nonterminal `simp` (5 sites) [M]:
`PeelingSupport.lean:79`, `Fubini.lean:90`,
`Counting.lean:179`, `Analytic.lean:298,446`.

Private-lemma docstring drift (low severity) [M]:
`Analytic.lean:89-90` — `tail_sum_bound` docstring
describes behaviour of the public `a(n)` sequence but
is itself `private`.

Decorative hypotheses in Enumerative [M]: `S_reindex`
(`Analytic.lean:247`), `laplace_tail_bound`
(`Analytic.lean:268`), `a_comb_eq_a`
(`Counting.lean:346`).

Stale prose [M]: `BorderRank.lean:5,66` and
`Apolarity.lean:6` reference pre-reorg module path
`Proofs.Vp2.Vp2`; `Zumkeller.lean:45` cites
`cmd/51293/perk.go` (actual: `cmd/A051293/perk.go`);
`open scoped Classical` lingers at `Vp2.lean:219`.

## sage–lean faithfulness caveat

Permanent scope caveat for BilinearComplexity, not
repairable debt. The GL-invariance and contraction layer
is formalized (contraction additivity `contract{1,2,3}_sub`
landed at `RankCalculus.lean:348-364` [M]), but the
orbit counts 7/14/17 rest on unformalized
automorphism-group structure: no `Aut(<n,n,n>)`
stabilizer, change-of-basis embedding, transpose
involution, or Burnside counting exists in Lean [M].
Treat the orbit counts as well-motivated computational
claims, not verified theorems [A].

## main-branch review residuals

Everything semantic from the July-Aug main-campaign
vacuity reviews was repaired or acquitted; the style
reviews carry zero MUST debt [M]. Surviving small items:

- `BilinearComplexity/BooleanRankGeneric.lean:618` audit
  block says "every named declaration" while instances
  are omitted (independent sweep was 48/48 clean, so
  cosmetic) [M]. Card
  `A354741-boolean-rank-generic.md:29` CLAIM line still
  says "FULL Boolean rank n" unqualified; the correction
  block exists but the line stands [A].
- `GroupCount/CdoIteration.lean`: latent maintenance
  trap — `norm_num` unfolding `gnu^[k]` at literal `k`
  near the ground-truth section has no caution comment
  [M]; OEIS blockquote at :10-13 not byte-exact [A].
- `GroupCount/DennisSurjectivity.lean` closure carries
  the `Structures.lean:249` native_decide (above); card
  `A046057-dennis-surjectivity.md:36` still says "508
  realized values" (meaning inverted; correction note
  adjacent) [A].
- `Erdos/ErdosLovasz.lean:906`
  `thirteen_le_erdosLovaszNum_six_of_erdos_lovasz` is an
  arithmetic identity (8/3*6 - 3 = 13); disclosed in its
  docstring, but the name reads as a derived bound [M].
- `NumberComplexity/SlizkovDoubling.lean:256`
  `slizkov_witness_iff` is a Nat-order tautology used as
  a "bridge"; a NOTE now concedes it does not certify
  archive fidelity, but the structural hazard (a drifted
  archive compiles identically) stands [M].
- `NumberComplexity/StepWalk.lean:302` `lt_or_ge` in a
  proof body; :479-484 diagnostic `#check` commands left
  in a library file [M]. Both advisory.
- `GroupCount/Submult.lean:117-118` lacks `[Finite H']`,
  leaving a j = 0 junk region reachable (true theorem,
  low severity) [M].
- `Enumerative/ZumkellerTauSigma.lean:753`
  `sum_divisors_mod_two_of_isSquare` over-assumes
  oddness; the odd-perfect trio (:820,842,872) and the
  intended sorry (:446) are documented deviations, not
  repair targets [A].

One review evidence item is genuinely lost with the
docs: the BooleanRankGeneric three-way cross-check
(Lean eval/decide vs Python vs Mathematica semantics)
matching A354741 rows 0-4 and discriminating A286331 and
A355333 (`156 != 168` at n = 3) ran from a deleted
scratch script; the discrimination facts are re-derivable
from OEIS but the script is not preserved [A].

## File dispositions

- .tasks/f5exp/docs/Ad1-burndown.md — extracted: repairs verified in tree; residual-debt list preserved above.
- .tasks/f5exp/docs/Pl20-repair-audit.md — extracted: two STPPWreath sorries and Pl21/Df1 forward state preserved; landed chain verified.
- .tasks/f5exp/docs/sage-lean-faithfulness.md — extracted: orbit-count caveat preserved; contraction gap verified closed.
- .tasks/f5exp/docs/vacuity-ad1-recheck.md — extracted: D1 drift and _tight hardening note preserved; in-tree pointer at ExtraspecialLattice.lean:121 needs repointing.
- .tasks/f5exp/docs/vacuity-algcomplexity.md — extracted: 37 docstrings, stale module paths, Classical scope survive; core findings retired.
- .tasks/f5exp/docs/vacuity-bilinearcomplexity.md — extracted: native_decide surface, 25 docstrings, bare simp, PeelingSupport sorry survive.
- .tasks/f5exp/docs/vacuity-chilo.md — extracted: erratum record inlined above; ConnerWaring.lean:26,42 pointers need repointing.
- .tasks/f5exp/docs/vacuity-enumerative.md — extracted: S2-S6 residuals survive; T1/S1 verified retired.
- .tasks/f5exp/docs/vacuity-erdos.md — extracted: Sunflower docstring/namespace debt survives; Spread stale text verified fixed.
- .tasks/f5exp/docs/vacuity-grouptpp.md — extracted: F2-F4, F6-F10 survive; F1/F5 verified retired.
- .tasks/f5exp/docs/vacuity-shearec.md — extracted: n=4 scope argument inlined above; ShearQuadraticRank.lean:45,736 pointers need repointing.
- .tasks/f5exp/docs/xlib-sorry-triage.md — extracted: two open STPPWreath sorries and Clifford estimate preserved; 10 of 12 triaged sorries verified discharged.
- .tasks/main/docs/review-style-CdoIteration.md — drop: zero MUST debt; two documented SHOULDs, accepted at review.
- .tasks/main/docs/review-style-DennisSurjectivity.md — drop: all items PASS, spot-checked clean.
- .tasks/main/docs/review-style-GroupPerfect.md — drop: all items PASS, spot-checked clean.
- .tasks/main/docs/review-style-MaxIrrepDegree.md — drop: advisories explicitly accepted; no violations.
- .tasks/main/docs/review-style-StepWalk.md — drop: namespace advisory fixed since review; rest informational.
- .tasks/main/docs/review-style-Submult.md — drop: Ren attribution landed; no violations.
- .tasks/main/docs/review-style-ZumkellerTauSigma.md — drop: unnamed have fixed; axioms-block absence is sub-family convention.
- .tasks/main/docs/review-vacuity-BooleanRankGeneric.md — extracted: audit-block overclaim and card CLAIM line survive; cross-check note above.
- .tasks/main/docs/review-vacuity-CdoIteration.md — extracted: norm_num maintenance trap and blockquote fidelity survive.
- .tasks/main/docs/review-vacuity-ComplexityPatterns.md — drop: all actionable findings verified repaired in-file.
- .tasks/main/docs/review-vacuity-DennisSurjectivity.md — extracted: closure native_decide and card EVIDENCE inversion survive.
- .tasks/main/docs/review-vacuity-ErdosLovasz.md — extracted: identity-theorem naming hazard survives; renames verified landed.
- .tasks/main/docs/review-vacuity-Gnu.md — drop: all eight findings verified repaired; shared native_decide item recorded above.
- .tasks/main/docs/review-vacuity-GroupPerfect.md — drop: verdict SOUND; all notes informational or repaired.
- .tasks/main/docs/review-vacuity-HamiltonBallinger.md — drop: all three findings verified repaired.
- .tasks/main/docs/review-vacuity-MaxIrrepDegree.md — drop: clean verdict, no findings.
- .tasks/main/docs/review-vacuity-QuasilogChainGap.md — drop: both findings verified repaired.
- .tasks/main/docs/review-vacuity-SlizkovDoubling.md — extracted: tautology-bridge hazard survives; DRIFT-2 verified closed by l_eq_lAsc.
- .tasks/main/docs/review-vacuity-StepWalk.md — extracted: lt_or_ge and diagnostic-command advisories survive.
- .tasks/main/docs/review-vacuity-Submult.md — extracted: missing [Finite H'] junk region survives.
- .tasks/main/docs/review-vacuity-ZumkellerTauSigma.md — extracted: over-assumed oddness at :753 survives; S1-S3 are documented deviations.
