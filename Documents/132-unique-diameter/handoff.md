# UniqueDiameterCircle producer handoff

## Result and ownership

Completed new `Proofs/Erdos/Erdos132/UniqueDiameterCircle.{lean,md}` in the
assigned workspace at base `ba4dff6394ac520f2074a9d3baa7f1ca828c8020`.
Producer-only: no independent reviewer was launched; no adoption, upload,
commit/revision manipulation, matching/odd extension, or outbound coordination
was performed. Parent source inspection covered the full 319-line new Lean
file and the accompanying documentation. Coordinator whole-pair review,
fresh audit, and adoption remain pending.

The named consumer `Erdos132.UniqueDiameterCircle.unique_diameter_circle`
derives `(H ∪ I).card = N + k` and an occurring `L` with `0 < L < diam (H ∪ I)`,
maximal over every occurring positive strictly subdiametral distance, and
`1 ≤ multiplicity (H ∪ I) L ≤ N + k`. Multiplicity is the inherited actual
loop-free unordered Sym2 edge count. Original uniqueness is on the full union.
Neither hull-endpoint membership nor a chosen length/maximality certificate is
an original premise. Center is arbitrary; `N ≥ 3`, any `k ≥ 1`; no evenness,
antipodality, `k ≤ 3`, exterior, or scalar certificate restriction is introduced.
Objects, quantifiers, hypotheses, and conclusion survive unchanged.

## New work versus inherited work

New mathematics: augmented diameter preservation, disjointness/cardinality,
diameter endpoint location, and nonempty finite-distance maximum selection.
New representation/API infrastructure: translation to the inherited centered
arbitrary-I helper and transport of diameter, unique Sym2 pairs, and actual
multiplicity. The geometric counting bound reuses unchanged
`EvenThreeInteriorCircle.longest_class_bound`; it is not reproved or assumed
as a new final-input certificate.

Three checked fixture theorems provide an explicit scalene cyclic triangle,
the complete original assumptions and conclusion jointly for every positive
`k`, and the original assumptions at `k = 4`. Interiors come from the infinite
ambient open hull interior; strict interiority preserves unique diameter for
any such finite set, so no small-ball/continuity premise is required. These
are formal witnesses, not numerical experiments. No new definitions, public
instances, or axioms were introduced. Complete public inventory: eight theorems.

## Exact evidence

1. `timeout --kill-after=2s 60s lake -q build +Erdos.Erdos132.UniqueDiameterCircle`
   finished with exit status 0; see `build-output.txt`, `build-check.txt`.
   Replayed warnings are exclusively from unchanged dependencies.
2. Full `#check @...` inventory of all eight declarations, fixtures included:
   `public-signatures.txt`, name inventory `public-declarations.txt`.
3. Copy `producer-audit.lean.txt` to a disposable Scratch `.lean` leaf and run:
   `timeout --kill-after=2s 60s lake env lean -j 1 -M 4000 Proofs/Scratch/UniqueDiameterAudit.lean`.
   The exact preserved source was run with exit status 0; see `audit-check.txt`
   and `producer-audit.txt`. Every one of the eight public declarations depends
   only on `propext`, `Classical.choice`, and `Quot.sound`. The audit is not imported
   by production and survives only as text.
4. Static inventory verifies the eight signature names and eight axiom reports
   match the new source's eight public declarations exactly. No `sorry`, new
   `axiom`, `native_decide`, external implementation attribute, partial definition,
   or production `#check`/`#print`/`#eval` remains.
5. Source/dependency hashes: `source-sha256.txt`, `dependency-sha256.txt`.
   Five same-base inputs pass the old exact SHA receipt (`dependency-unchanged.txt`).
   Inherited TwoInteriorCircle also matches its exact assigned base; its check
   is appended separately to that receipt. All disposable Scratch probes removed.

## Unadopted inputs and provenance

The five same-base unchanged modules remain unadopted inputs:
DoubleEndpoint, CircleFixtures, CircleRotation, EvenThreeInteriorCircle,
EvenThreeInteriorFixtures. The last fixture module is inventoried but not imported
by the new file. Rotation provenance is exact supplied revision
`5b5a5653e5e473d51abde1b6a723a4985a0ffc40`.
Inherited TwoInteriorCircle is separately inventoried, not relabeled as newly
produced/adopted. The mathematical seed is the user-authorized complete corrected
`Documents/Erdos132Routes/DiameterGraph.md` at
`d1606b9c208c5b7b11edc36a53f8e9fa3f18c330`. Ready seed was trusted as instructed;
there was no preliminary independent paid review. No source/novelty claim is made.

No old Lean dependency, old consumer, shared helper, References, global ledger,
other station, or umbrella import was edited. Only the new pair and local receipt
directory are delivered. Temporary Scratch leaves were created and then removed.

## Effort and remaining gate

User-supplied episode start: 2026-10-11 17:47:09 UTC.
Recorded handoff preparation: 2026-10-11 18:01:27 UTC.
Observed wall-clock episode to this record: 0:14:18.
Last full build completed at 17:59:23 UTC; exact-source separate audit at
17:59:53 UTC. This is actual clock evidence, not an inferred token or paid-review
budget estimate, and is before the 18:32:09 UTC deadline.

The assigned conditional implication is complete with no remaining mathematical
bridge. Compilation, producer semantic/nonvacuity inspection, and the axiom
inventory are distinct evidence. Independent whole-pair review, fresh coordinator
audit, and dependency/consumer adoption remain unpaid external ownership gates;
this handoff does not claim they have passed. No request for resumption is needed.
