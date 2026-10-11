# HullOutlierOutside — centered n=9 outside branch

## Contract and status

The intended named consumer is the n=9 centered HullOutlier route. The original
objects are six distinct circle vertices `C`, one off-circle hull generator `u`,
and the center and a second point `z` in the **ambient interior** of the actual
augmented hull `conv(insert u C)`. All seven generators are extreme. Distances
are ordinary Euclidean distances; multiplicity is the adopted loop-free,
unordered `Sym2` edge count of the actual nine-point configuration.

The complete named consumer is `original_zero_centered_outside`, in the
zero-centered representation with arbitrary positive radius. It includes the
strict-outside and equality-boundary branches, and derives both cardinality nine
and an occurring positive nondiameter class of multiplicity one through nine.
Translation to arbitrary center is not supplied. Build and axiom/signature
receipts are retained in `Documents/132-hull-outlier-outside/`; the completion
status below records the actual checks, separately from semantic review.

## Proof map

1. `original_geometry_card_and_diameter` derives nine distinct points, preserves
   the diameter of the augmented hull on insertion of the two interiors, and
   proves positivity of that diameter. No claim identifies this hull or its
   diameter with the circle hull.
2. `original_target_or_saturation` uses the 36 actual unordered edges, reserves
   an actual diameter edge, and forces exactly three positive nondiameter
   values if every such class has at least ten edges. The six circle-to-`z`
   edges have fibers of size at most two, forcing three double fibers.
3. `original_outside_target_or_chord_obstruction` derives, rather than assumes,
   the three-element squared support, radial membership, reflected pairs with
   no axis fixed points, strict outlier projection/norm separation, a negative
   circle projection, and support-or-diameter membership of every circle chord.
4. The strict-outside exclusion uses `s=R²`, `t=‖z‖²`, `q=‖u‖²` and the three
   within-pair chord squares. The case `t=2s,q=7s/2` is excluded by cross chords
   with sum `3s` and product `s²/2`, incompatible with both being at least `s`.
   The cross equations follow from the two-dimensional Gram determinant.
5. The equality boundary uses the corrected rectangle argument: the chord
   `3s` cannot be diameter, a radial `3s` pair supplies antipodes, diameter is
   `4s`, and the third pair's four rectangle distances must occur in the support.
   Complementary squares and the Gram identity exclude the third support value.
   This is not the withdrawn claim about the `u-z` distance.

## Simultaneous original-geometry witness

`original_outside_geometry_fixture` supplies the six rational points
`(±4/5,±3/5),(0,±1)`, with `u=(6/5,0)` and `z=(11/10,0)`.
Tangent enclosing balls expose every circle point and a centered enclosing ball
exposes `u`. A rectangle proves the center is ambient interior; the open segment
from that center to `u` proves `z` is ambient interior. This witnesses all the
original hypotheses together, including strict outside and nine distinct points.
It does not assert satisfiability of saturation or target failure.
`original_outside_fixture_with_conclusion` applies the final theorem to that
simultaneous original model, preserving its original hypotheses alongside the
nine-point cardinality and actual multiplicity conclusion.

## Provenance and boundaries

Complete assignment, common directives, corrected handoff and original source
were read. Authorized corrected handoff SHA-256:
`4b61ca81c716bf7351900dee12f39772fc48548f300369b176b127bed08d883d`.
Original source `Documents/Erdos132Routes/HullOutlier.md` at
`ae43639738b1c44c1b82a9c5c0183459a41bb8f6`, SHA-256
`477b16bf60b69595fcaf11509fc78450f7c25fe5128e4e7d1beaf27c56a411a4`.
The invalid boundary paragraph in the earlier `2023b35` artifact is not used.

Imports are existing adopted `ThreeInteriorCounting` and `CircleFixtures`, with
transitive circle/radial/counting infrastructure from the named adopted
`91abfcb64c0121addbb572a06ba6d3063bfbebc4` dependency lineage. No dependencies
were copied and no shared helper was modified.

The inside-circumdisk branch, two-offcenter global contradiction, arbitrary-center
transport, larger n, and even n remain unpaid. Producer compilation, original
fixture and axiom/signature evidence are distinct from independent semantic
review and parent full-source verification; neither review gate is performed by
this producer.

Original episode consumption: 2026-10-11T18:34:54Z. Sequential replacement first
local observation: 18:49:46Z. Proof-finishing boundary: 19:11:54Z; hard deadline:
19:19:54Z. The predecessor's workspace remains untouched.

## Completion evidence (2026-10-11T19:02:52Z)

- `timeout 90s lake -q build +Erdos.Erdos132.HullOutlierOutside` exited **0**.
  The module has no errors or `sorry`; output contains only pre-existing dependency
  linter warnings. The first assembly check found a representation/API mismatch
  between a local let-bound support `S` and the unfolded support equality. It was
  repaired by a typed local equality, not by changing any mathematical premise.
- A separate one-thread, 4000 MB, 60-second audit leaf checked full signatures
  and printed axiom dependencies of **all six public declarations**, including
  the final consumer and fixture. It exited **0**. Every declaration reports
  exactly `propext`, `Classical.choice`, and `Quot.sound`.
- `original_outside_fixture_with_conclusion` compiles in the production module
  and applies the final theorem to the jointly proved rational original geometry.
  This is the non-vacuity evidence for the external premises, not a claim that
  the intermediate failure certificate is satisfiable.
- All eleven `Outside*` scratch leaves, including the audit leaf, were removed.
  The nonimported `audit-source.txt`, complete outputs, exit receipts, unchanged
  dependency hashes and `completion-receipt.json` remain under the evidence
  directory. The final production source SHA-256 is
  `731fdc5383c46a29fc17e73af73daa85448d475da230daee88934f78a0607818`.

The intended objects, universal geometry quantifiers, positive-radius and
outside hypotheses, and actual multiplicity conclusion survive unchanged in
the accepted zero-centered unit. Distinctness of the two interiors is derived
from `0 < R ≤ dist z 0`, rather than supplied redundantly. The consumer has no
free support, saturation, projection or chord-certificate premise. The new
mathematics is the strict/boundary certificate exclusions and their named
consumer connection; local let-equality, inner-product and field cancellation
repairs are representation/API infrastructure. No upstream inside-circle bridge
is claimed.

Completion was recorded about 28 minutes after original consumption, before the
proof-finishing and hard boundaries. Producer build, axiom inventory and
statement checks are complete. Parent full-source/diff/receipt inspection and
identification of the exact harness-finalized revision remain external handoff
gates; this producer has neither changed revisions nor substituted a coordinator
or independent review.
