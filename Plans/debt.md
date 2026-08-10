# debt — burndown ledger

Everything mechanical that must be repaired or completed.
This file shrinks to empty. Items are open unless marked
done. File-dispositions sections of STATE1–8 are NOT
carried forward — they were single-use for the .tasks
deletion and live at `git show 4901d3b:Plans/STATE<N>.md`.

Sources: `git show 4901d3b:Plans/STATE2.md` in full; `git
show 4901d3b:Plans/STATE0.md` pre-deletion checklist items
2–7; `git show 4901d3b:Plans/PLAN.md` sections "CHORES" and
"AXIOM HYGIENE"; `git show 4901d3b:Plans/STATE8.md`
dangling-pointer ledger; reorganized 2026-08-10.


## chores (from PLAN.md)

  X1  Adopt `leanprover-community/axiom-audit` (allowlist-subset check,
      runs over `.olean`, catches transitive deps, community-maintained)
      and retire the five stale hand-rolled sweeps under
      `Proofs/Scratch/` (Ad1AxiomSweep, Aw1AxiomAudit, Le1AxiomAudit,
      Secp256k1AxiomAudit, ShearReviewAudit) with `goof rm` — only
      after parity is demonstrated by planting both a native_decide
      proof and a `sorry` and watching the new tool fire. Measured facts
      behind this are under AXIOM HYGIENE below.
  X2  Refresh `Formalize/INDEX`: record the landed-but-unrecorded files
      — FixedDivisor/Sierpinski/Riesel/Erdos1950Instance (9d873d7,
      5157ca8), RankOfApparition (3c7d4ef), ZumkellerSigmaHalf +
      MultiperfectZumkeller + nine A083207 instances (3e593ab), the
      NederGap stub state, and the ShearEC arc — CORRECTED 2026-08-05:
      T1–T4 are fully covered and sorry-free (T1 =
      TotalDegreeAeval + ShearCircuit, T2 = ShearInversionLB +
      Secp256k1Prime, T3 = ShearQuadraticRank + ShearAddition, T4 =
      ShearAdditionEC + ShortCurveScaling + VariableChangePointEquiv),
      but `ShearAdditionChains.lean` (T5) is a THREE-LINE EMPTY STUB —
      the min-shears-for-x^n = l(n) bridge does not exist; it joins the
      A003313 lane as the natural sibling. Strike the STATEMENTS
      rows that landed; mark queue items 2–5 follow-ons accurately
      (Sierpinski/Riesel follow-on is DONE). Two spec files INDEX
      cites do not exist anywhere (review-vacuity-SlizkovDoubling.md,
      review-vacuity-ErdosLovasz.md) — note the citations as dead.
      X2 should additionally record the wave 2–3 landings
      (commits of 2026-08-05..09; enumerate via git log).


## axiom hygiene — measured facts (keep until X1 lands)

The five hand-listed sweeps under `Proofs/Scratch` state their criterion
as "no `Lean.ofReduceBool`". That name is never emitted on this
toolchain, so those five detect nothing. Measured on v4.33.0-rc1: a
native_decide proof yields `<decl>._native.native_decide.ax_1_1`.

This is documented upstream behaviour, not a discovery — RFC #12216 /
PR #12217, shipped in Lean v4.29.0 (2026-03-27), moved native
computation to one axiom per computation; `ofReduceBool` was deprecated
2026-02-01. Only an allowlist-SUBSET test works. `RankOfApparition`
section 10 does it that way and `throwError`s, verified to fire by
planting both a native_decide proof and a `sorry`. It cannot close two
limits from inside: `example`s contribute no constant and escape any
such sweep, and the sweep is positional. Mathlib solves the same problem
with a syntactic linter plus periodic lean4checker, and explicitly notes
name-checking is "not airtight".


## pre-deletion residuals (from STATE0.md items 2–7)

  2  Moves per dispositions: seven `pf3-probes/*.sage` →
     `Programs/GroupTPP/` (`beta0-exact.sage` → its `forge/`;
     lemmaD/lemmaM2 dropped, verbatim in committed `lemma_sweep.sage`);
     `kernel-graph.mmd` → `Programs/GroupTPP/`;
     `route-d-aes-diffusion-witness.py` → `Programs/Unsorted/`.
  3  Code fixes: `Programs/GroupTPP/cmd/gelfandrank/main.go:71` writes
     to a `.tasks` path (breaks at runtime after deletion);
     `groupsieve.sage:853,857` and `cascade.sage:979,983` print
     `.tasks` paths.
  4  Repoint Lean headers citing `.tasks` docs to STATE files:
     `ConnerWaring.lean:26,42`, `ExtraspecialLattice.lean:121`,
     `ShearQuadraticRank.lean:45,736`, `STPPWreath.lean:1744`,
     `SchinzelSzekeres.lean:67,76`; low-severity comment refs in
     `verify_all_combos.sage:9` and historical `Prompts/` files are
     listed in STATE8.
  5  Standing errors surfaced by the audit, not yet fixed:
     `Formalize/A007691-coleman-practical.md` and
     `Formalize/INDEX:84-86` still carry the retracted
     first-formalization claim; PLAN.md's Erdős #1213 pigeonhole
     route is refuted (STATE3); Gelfand 367-vs-307 jsonl discrepancy
     unresolved (STATE4); `Prompts/Ref/MENTALMAP` factcheck errors
     unapplied (STATE8).
  6  Known losses, accepted: the BooleanRankGeneric three-way
     cross-check script (STATE2) and the Cj4-C7 PSL(2,27) Sage
     skeleton (STATE4) existed only in uncommitted scratch.
  7  Delete `.tasks/**` (done cards' outcomes are in git history).


## ad1 burndown residual

Card `Ad1` (status done) repairs verified in tree [M].
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


## dangling in-tree pointers (from STATE2)

Three committed Lean files cite docs this retirement
deletes [M]. Repoint them at `Plans/debt.md` (the STATE2
rescues live in this file; STATE8 originals at
`git show 4901d3b:Plans/STATE8.md`).

- `Proofs/CHILO/ConnerWaring.lean:26,42` cite
  `vacuity-chilo.md` as the erratum verification record.
- `Proofs/GroupTPP/ExtraspecialLattice.lean:121` cites
  `vacuity-ad1-recheck.md` for the D1 scope note.
- `Proofs/ShearEC/ShearQuadraticRank.lean:45,736` cite
  `vacuity-shearec.md` for the n = 4 emptiness argument.


## conner–waring erratum record

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


## stale paths inherited from the reorganization

RESOLVED 2026-08-10: two stale source-inherited paths were corrected
during the reorganization fix pass — `Proofs/Xlib/STPPWreath.lean` →
`Proofs/GroupTPP/STPPWreath.lean` (conjecture-hunts.md) and
`Proofs/Proofs/ErdosCovering/*` → `Proofs/Erdos/Covering/*`
(standing.md); both targets verified on disk [M].

## dangling pointers (from STATE8)

Committed files that name deleted `.tasks` paths. Rescued
referents were distributed into the idea files (largely
`Plans/matmul-search.md` and `Plans/matmul-endgame.md`;
originals at `git show 4901d3b:Plans/STATE8.md`); pointers
should eventually be rewritten to those homes or made
self-contained.

- `Proofs/GroupTPP/TPPLift.lean:37`,
  `Documents/abelian-factor-refutation.md:363,580` ->
  `Pf13-lift-law.md` (rescued in STATE8).
- `Documents/abelian-factor-refutation.md:581`,
  `Programs/GroupTPP/lemma_sweep.sage:28`,
  `cmd/sieve/lemmasweep/main.go:21`,
  `Programs/GroupTPP/groupsieve.sage:122,342` ->
  `Pf3-abelian-factor.md` (rescued in STATE8).
- `Proofs/GroupTPP/STPPWreath.lean:1278` ->
  `Lg1-counterexample.md` (rescued in STATE8).
- `Proofs/Scratch/mclower_inv8_slices.lean:30` ->
  `mclower-campaign.md` §S1.2 (rescued in STATE8).
- `Proofs/Erdos/Erdos542/SchinzelSzekeres.lean:67,76` ->
  `erdos542-weights.md`; harmless — all 13 LP-dual weights
  are embedded and compiled in the Lean file [M]; the
  greedy reconstruction algorithm and margin analysis are
  re-derivable from the paper; pointer is provenance-only.
- `Programs/GroupTPP/gelfand.sage`, `forge/gelfand.sage`
  -> `Cc2-ccsieve-spec.md` rev2 (rescued in STATE8).
- `Programs/GroupTPP/groupsieve.sage:76-77`,
  `census.sage`, `stratum-b-full.log` ->
  `sieve-{spec,summary}.md` (rescued in STATE8).
- `Programs/RouteC/routec_gauge_{invariants,symmetries}.sage`
  -> `route-c-gauge-dual-ciphers.md` (rescued in STATE8).
- `Programs/BilinearComplexity/b1_levelcut_222.sage` ->
  `Bf1-bottleneck.md` (rescued in STATE8).
- `Prompts/User/erdosmining` -> `candidate-ledger.md`;
  `Prompts/User/f5high-3rev.md` -> both analysis docs
  (rescued in STATE8). Prompt files are historical records;
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
