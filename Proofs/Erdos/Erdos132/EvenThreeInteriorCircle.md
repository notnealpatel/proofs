# Erdős #132: even configurations with three circle-hull interiors

## Result and scope

The public theorem is
`Erdos132.EvenThreeInteriorCircle.even_three_interior_circle`, imported through
`Erdos.Erdos132.EvenThreeInteriorCircle`. For every even natural number
`n ≥ 10`, take `n − 3` distinct concyclic extreme vertices and three distinct
points in the **ambient interior** of their convex hull. Their union has exactly
`n` points and has an occurring positive distance strictly below its diameter
whose multiplicity among distinct unordered pairs is at most `n`.

This is the full even consumer, not a regular-polygon special case or merely a
conditional longest-class estimate. The circle center is arbitrary. The final
statement does **not** assume a unique diameter pair, antipodal endpoints, that
the center lies in the convex hull, or an endpoint-intersection certificate.
All three interiors are retained.

**Verification status:** the supplied producer records report successful Lean
compilation and a producer signature/axiom audit. This companion is a doc-only
addition to the frozen sources at assigned revision
`3c5eb5c42fad10abb4d5b46b8782a041c83f9570`; it does not report a new build or an
independent proof review. Final independent review of the exact Lean + Markdown
pair, the coordinator's fresh audit, integration, and adoption remain pending
and coordinator-owned.

## Exact public signature

The following is the source signature from
`Documents/132-even-formal/public-signature.md`, matching the production source.
Its complete elaborated form is recorded in the producer's
`Documents/132-even-formal/producer-audit.txt`. In namespace
`Erdos132.EvenThreeInteriorCircle`, `Plane` and `multiplicity` are inherited from
`Erdos132.TwoInteriorCircle`.

```lean
theorem even_three_interior_circle (n : ℕ) (H : Finset Plane) (O z w v : Plane) (R : ℝ)
    (hn : 10 ≤ n) (hEven : Even n) (hH : H.card = n - 3)
    (hcircle : ∀ h ∈ H, dist h O = R)
    (_hextreme : ∀ h ∈ H, h ∈ (convexHull ℝ (H : Set Plane)).extremePoints ℝ)
    (hz : z ∈ interior (convexHull ℝ (H : Set Plane)))
    (hw : w ∈ interior (convexHull ℝ (H : Set Plane)))
    (hv : v ∈ interior (convexHull ℝ (H : Set Plane)))
    (hzw : z ≠ w) (hzv : z ≠ v) (hwv : w ≠ v) :
    (insert z (insert w (insert v H))).card = n ∧
    ∃ d : ℝ, 0 < d ∧ d < Metric.diam ((insert z (insert w (insert v H)):Finset Plane):Set Plane) ∧
      1 ≤ multiplicity (insert z (insert w (insert v H))) d ∧
      multiplicity (insert z (insert w (insert v H))) d ≤ n
```

### Objects and guards

- `Plane := EuclideanSpace ℝ (Fin 2)` is the ordinary canonical Euclidean plane,
  with its usual distance. Its coordinate index has two elements, not zero.
- `H` is a finset, so its vertices are distinct. `10 ≤ n` gives `7 ≤ H.card`
  and prevents truncation of `n - 3`. The three pairwise inequalities are
  explicit; interiority excludes each of `z,w,v` from `H`.
- `interior (convexHull ℝ (H : Set Plane))` means ambient topological interior,
  not relative interior. The extremeness premise remains in the public
  interface, although the implemented geometric implication does not use it.
- There is no separate radius-positivity premise. The wrapper proves `0 < R`:
  the circle equation makes `R` nonnegative, and `R = 0` would identify two
  distinct hull vertices with `O`. Thus zero or negative radii do not supply
  spurious models.
- For `X = insert z (insert w (insert v H))`, the inherited definition is
  `pairs X := X.offDiag.image Sym2.mk.uncurry`. `Sym2` identifies the two
  orientations; the off-diagonal excludes loops. `mk_mem_pairs` characterizes
  membership by two endpoints in `X` and their inequality; `card_pairs` proves
  `(pairs X).card = X.card.choose 2`.
- `pairDist` is the symmetric lift of ordinary `dist`, with
  `pairDist_mk : pairDist s(a,b) = dist a b`. `multiplicity X d` is the cardinality
  of `(pairs X).filter (fun e => pairDist e = d)`. No directed counting,
  normalization factor, tagged duplication, or replacement metric is used.
- The conclusion's `1 ≤ multiplicity X d` asserts actual occurrence, in
  addition to `0 < d` and the strict subdiameter inequality. The proved size
  `X.card = n ≥ 10` keeps the diameter and pair domains nondegenerate.

## Public module inventory and provenance

All five public Lean modules below are under `Proofs/Erdos/Erdos132/`. They are
the delivered module inventory; `CircleRotation` is an unchanged dependency,
not newly proved in this doc-only addition.

| Module | Role and direct imports |
| --- | --- |
| `DoubleEndpoint.lean` | Common-point sum, strict supporting-functional bound, and `double_endpoint_unique`; imports `Erdos.Erdos132.TwoInteriorCircle`. |
| `CircleFixtures.lean` | `rectangle_mem_interior`, joint uniqueness-checkpoint example, and `rational_three_interior_fixture`; imports `DoubleEndpoint`. |
| `CircleRotation.lean` | Concrete complex-circle rotations, hull stabilizers, and the saturated-chord bridge; imports `TwoInteriorCircle`, `Mathlib.Analysis.Complex.Circle`, and `Mathlib.GroupTheory.GroupAction.CardCommute`. |
| `EvenThreeInteriorCircle.lean` | Full geometric/counting consumer and arbitrary-center public wrapper; imports `DoubleEndpoint` and `CircleRotation`. |
| `EvenThreeInteriorFixtures.lean` | Public-theorem fixture at `n = 10` and joint models for all `n ≥ 10`; imports `CircleFixtures` and `EvenThreeInteriorCircle`. |

The inherited `TwoInteriorCircle.lean` supplies `Plane`, the genuine unordered
pair definitions, convex-hull distance bounds, radial and chord capacities,
and the exact contrary-budget theorem `equality_structure`. It is reused,
not replaced by a simplified combinatorial model.

`CircleRotation.lean` comes unchanged from finalized dependency revision
`5b5a5653e5e473d51abde1b6a723a4985a0ffc40`. Its SHA256 is
`13a31899aa0cfca29c9b4ddf82661714e8660fe0744519cd61d003ebc04de0f7`.
The supplied five-file manifest is
`Documents/132-even-formal/source-sha256.txt`; all five entries passed
`sha256sum -c` in this doc-only workspace. No Lean source or compiled artifact
was edited or rebuilt here.

## Implemented proof map

Unless qualified otherwise, consumer lemma names below are in
`Erdos132.EvenThreeInteriorCircle`; inherited names are in
`Erdos132.TwoInteriorCircle`.

### 1. Prove double-endpoint uniqueness geometrically

`DoubleEndpoint.common_points_sum` proves that distinct common points `z,w`
of two equal-radius circles with distinct centers `a,b` satisfy
`z + w = a + b`. It constructs the reflected point `a + b - z`, handles the
case in which that point equals `z` by squared-norm identities, and otherwise
uses `EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two`.

`DoubleEndpoint.inner_le_on_hull` converts the uniform endpoint distance bound
on a centered circle to a lower bound for the functional `x ↦ inner ℝ z x`
on the convex hull. `DoubleEndpoint.inner_lt_of_mem_interior` makes that bound
strict at an ambient interior point when the normal is nonzero, by moving a
small distance against the normal within an interior ball.

`DoubleEndpoint.double_endpoint_unique` assumes two candidate interiors have
distance `L` to both endpoints and distance at most `L` to every hull vertex.
If the candidates differed, at least one would be nonzero. Using that candidate
as the normal makes the functional strictly above its endpoint value at both
interiors. Equal radii and endpoint distances give equal functional values at
`a,b`; their sum then contradicts `z + w = a + b`. The zero-center candidate
case is handled by swapping candidates. Antipodality is never needed.

### 2. Preserve cardinality and diameter; exclude saturated hull chords

`card_insert_three` proves size `H.card + 3` using
`dist_center_lt_radius` and the three distinctness hypotheses.
`diam_insert_three` proves that adding the three interiors leaves the actual
metric diameter unchanged, using hull containment and `dist_le_diam_hull`.

`chord_lt_card_of_unique_diameter` proves that a positive subdiametral hull
chord class has fewer than `H.card` edges **under a unique-diameter premise
at this intermediate stage**. The inherited `chord_capacity` gives the weak
bound. In the equality case,
`CircleRotation.exists_stabilizer_map_of_saturated_chord` supplies an actual
rotation preserving `H` and taking one chord endpoint to the other, neither
identity nor half-turn. That bridge uses
`CircleRotation.chord_neighbors_card_eq_two`,
`CircleRotation.mem_of_chord_neighbors_card_eq_two`, and
`CircleRotation.exists_rotation_map`: saturation forces every hull vertex to
have two chord neighbors, and geometric two-circle intersection capacity
forces rotated vertices back into `H`.

The consumer's `rotation_pair_fixed` shows that a rotation preserving an
unordered pair with a nonzero first endpoint is identity or half-turn.
Uniqueness makes the rotated diameter pair that same pair, a contradiction.
This is genuine rotation infrastructure, not an assumed orbit certificate.

### 3. Bound the largest nondiameter class

`dist_lt_vertex_bound` extends a uniform positive distance bound on hull
vertices to a **strict** bound at each ambient interior, even for an external
comparison point, by moving slightly away from that comparison point.

For an interior finset `I` and maximum nondiameter length `L`,
`longest_class_bound` proves

`multiplicity (H ∪ I) L ≤ H.card + I.card`.

Its named local checkpoints show: `hcross` bounds hull–interior distances by
`L`; `hII` excludes interior–interior `L`-edges; `honly` restricts an interior's
hull `L`-neighbors to the two unique diameter endpoints. The finset fiber
`F i = H.filter (fun h => dist i h = L)` has size at most two.
`hdouble` uses `DoubleEndpoint.double_endpoint_unique` to show that at most one
interior has two such neighbors, and `hsum` bounds all cross edges by
`I.card + 1`. The genuine `Sym2` class `Q` lies in the union of hull edges `P`
and cross-edge image `S` (`hQsub`). The strict hull bound saves one edge,
giving the displayed total bound. No disjointness or directed-edge equality
is silently substituted for these cardinality inequalities.

### 4. Derive the diameter certificate only under the contrary assumption

`zero_center_contrary` takes `H.card ≥ 7`, an off-center first interior, even
total size, and the contrary assumption that every occurring nondiameter
class has multiplicity at least `X.card + 1`. Write
`X = insert z (insert w (insert v H))` and
`T = nonDiameterDistances X`.

The radial distances from the off-center interior map all hull vertices into
`T`. `radial_card_le_two` gives `H.card ≤ 2 * T.card`; evenness and
`X.card = H.card + 3` strengthen this to `X.card - 2 ≤ 2 * T.card`.
The inherited `equality_structure` then yields

- `X.card = 2 * (T.card + 1)` and `3 ≤ T.card`;
- every class in `T` has multiplicity exactly `X.card + 1`;
- the filtered unordered pair class not strictly below the diameter has
  cardinality one.

`exists_diameter_pair` supplies hull endpoints. Diameter preservation and the
last equality derive their uniqueness in local `hunique`; it is not an extra
hypothesis of the public theorem. The maximum `L = T.max' hT` exists since
`T` is nonempty, is positive by actual distinct-pair occurrence, and is
strictly subdiametral. With `I = {z,w,v}` (cardinality three),
`longest_class_bound` gives multiplicity at most `X.card`, contradicting the
exact contrary multiplicity `X.card + 1`.

### 5. Recover the witness and arbitrary-center statement

`zero_center_witness` converts absence of the desired occurring distance into
the contrary multiplicity bound. If the first interior is zero, it swaps the
first two distinct interiors to obtain an off-center point; the third is kept.
`circle_witness` translates by `h ↦ h - O`, using
`sub_mem_interior_hull`, `multiplicity_image_isometry`, isometric diameter
preservation, and injective-image cardinality. Finally,
`even_three_interior_circle` derives positive radius, exclusion of all three
interiors from `H`, and cardinality `n`, and invokes `circle_witness`.
Thus no upstream mathematical bridge remains unpaid for this assigned even
consumer; independent validation and adoption are separate gates.

## Joint nonvacuity and boundary models

`CircleFixtures.rational_three_interior_fixture` proves all original geometric
premises jointly at `n = 10`, with center zero and radius five:

- `H = {(3,4), (−3,4), (3,−4), (−3,−4), (5,0), (−5,0), (0,5)}`;
- `z = (0,0)`, `w = (1/8,0)`, `v = (0,1/8)`.

These are actual rational-coordinate points in `Plane`. The four rectangle
corners provide an open ambient rectangle via `rectangle_mem_interior`, so
all three interiors have neighborhoods in the hull. Positive-radius sphere
strict convexity establishes extremeness of every vertex. Cardinality and
pairwise distinctness are proved.
`EvenThreeInteriorFixtures.original_hypotheses_with_witness` applies the exact
public theorem to this same model and includes its conclusion; it is not a
fixture for an impossible contrary premise.

Nonvacuity is not limited to the first even size.
`EvenThreeInteriorFixtures.original_hypotheses_all_sizes` gives joint original
geometric hypotheses for **every natural `n ≥ 10`**, including odd sizes (it
makes no odd-case conclusion). The definition `circle_point` is the radius-five
stereographic parametrization

`(5(1 − t²)/(1 + t²), 10t/(1 + t²))`.

Ground-truth examples at `t = 0,1`, `circle_point_norm`, and
`circle_point_injective` verify its meaning. Its denominator is strictly
positive. Natural-number parameters give infinitely many distinct circle
points; after removing the finite seven-point base, the proof selects `n − 10`
additional points. Disjoint union gives size `n − 3`. Interior monotonicity
retains the three original interiors, and strict convexity again supplies
extremeness. At `n = 10` the enlargement size is zero, but the retained
seven-vertex hull and three interiors are not empty or vacuous.
`original_hypotheses_every_even_size` applies the public theorem to this family
for each even `n ≥ 10` and retains both all premises and the conclusion.

The separate joint checkpoint example in `CircleFixtures` uses the rectangle
`{(±3,±4)}`, `R = L = 5`, endpoints `(3,4),(−3,4)`, and both candidate interiors
zero. It exhibits satisfiability of `double_endpoint_unique` even with
nonantipodal endpoints and a zero candidate. That theorem concludes equality;
it does not require distinct qualifying candidates. No nonvacuity assertion
is made for the contradictory premise of `zero_center_contrary`.

## Verification evidence and remaining gates

The immutable handoff and receipts are in `Documents/132-even-formal/`:

| Evidence | Recorded producer result |
| --- | --- |
| `handoff.md` | Consumer build exit 0 in 2.0s; all-size fixture build exit 0 in 2.4s; bounded-task command and exit-status account. |
| `consumer-build.txt` | Final narrow `EvenThreeInteriorCircle` build output; cached replay with style/unused-argument warnings, not a measured cold rebuild. |
| `fixture-build.txt` | Narrow `EvenThreeInteriorFixtures` build output, including both quantified family theorems. |
| `public-signature.md`, `producer-audit.txt` | Source signature and full elaborated signatures; producer audit reports only `propext`, `Classical.choice`, `Quot.sound` for the displayed consumer, rotation bridge, uniqueness, and fixture declarations. |
| `producer-audit.lean.txt` | Non-imported text of the disposable audit leaf, retained for reproducibility. |
| `source-sha256.txt` | Five frozen production-source hashes; all five verified here by `sha256sum -c`. |

The producer reports exit 0 for bounded commands
`timeout 60s lake -q build +Erdos.Erdos132.EvenThreeInteriorCircle`,
`timeout 60s lake -q build +Erdos.Erdos132.EvenThreeInteriorFixtures`, and the
one-thread audit
`timeout 60s lake env lean -j 1 -M 4000 Proofs/Scratch/EvenThreeInteriorAudit.lean`.
The handoff also records no remaining `sorry`, declared axioms, or production
exploratory commands, and only style/unused-argument warnings. These are
**producer-only** checks, not this documentation author's fresh kernel audit,
independent review, or a cold-build performance measurement.

The intended plane, finite distinct unordered pairs, arbitrary center,
quantifiers, three ambient interiors, extremeness premise, and occurring-distance
conclusion survive unchanged. Deriving redundant radius positivity and the
contrary-case unique diameter are proved steps, not added final assumptions.
The newly supplied implication is the full even theorem above; no missing
upstream implication is being hidden behind a final certificate.

The exact final `EvenThreeInteriorCircle.lean` + `EvenThreeInteriorCircle.md`
pair is now available for coordinator review, together with all dependencies
and fixture evidence. Independent whole-pair Lean/prose review, a fresh
coordinator audit (including dependency provenance), integration, and adoption
remain pending. This doc-only addition does not edit accepted prose, verification
reports, Lean bytes, or revision history, and does not claim those gates paid.
