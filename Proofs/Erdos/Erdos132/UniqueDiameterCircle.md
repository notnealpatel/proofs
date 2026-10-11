# Unique-diameter circular hull: largest nondiameter class

## Status and scope

**Producer-only, kernel-checked formalization.** This pair adds
`Erdos132.UniqueDiameterCircle` at the assigned base
`ba4dff6394ac520f2074a9d3baa7f1ca828c8020`. It has not been independently
reviewed, adopted, or uploaded. The parent owns final complete source/diff
inspection; the coordinator owns whole-pair review, fresh audit, and adoption.
There is no novelty claim and no matching-diameter or odd-case extension here.

The named final consumer is
`Erdos132.UniqueDiameterCircle.unique_diameter_circle`. It proves the exact
largest-nondiameter implication, not merely existence of some small class:
for a finite circular layer `H` with `N ≥ 3`, any finite set `I` of `k ≥ 1`
distinct ambient hull interiors, and a unique unordered diameter pair of
`X = H ∪ I`, it derives `X.card = N + k` and an **occurring maximum positive
strictly subdiametral length** `L` with actual unordered multiplicity at most
`N + k`. Occurrence also gives multiplicity at least one.

## Exact final public signature

The following is copied verbatim from the production declaration, with
`open Erdos132.TwoInteriorCircle` in scope. `Plane` is the canonical
`EuclideanSpace ℝ (Fin 2)`.

```lean
theorem unique_diameter_circle (N k : ℕ) (H I : Finset Plane) (O : Plane) (R : ℝ)
    (hN : 3 ≤ N) (hk : 1 ≤ k) (hHcard : H.card = N) (hIcard : I.card = k)
    (hR : 0 < R) (hcircle : ∀ h ∈ H, dist h O = R)
    (_hfull : (interior (convexHull ℝ (H : Set Plane))).Nonempty)
    (hInt : ∀ i ∈ I, i ∈ interior (convexHull ℝ (H : Set Plane)))
    (hunique : ∃ a ∈ H ∪ I, ∃ b ∈ H ∪ I, a ≠ b ∧
      dist a b = Metric.diam ((H ∪ I : Finset Plane) : Set Plane) ∧
      ∀ x ∈ H ∪ I, ∀ y ∈ H ∪ I,
        dist x y = Metric.diam ((H ∪ I : Finset Plane) : Set Plane) → s(x,y) = s(a,b)) :
    (H ∪ I).card = N + k ∧ ∃ L : ℝ,
      0 < L ∧ L < Metric.diam ((H ∪ I : Finset Plane) : Set Plane) ∧
      (∃ x ∈ H ∪ I, ∃ y ∈ H ∪ I, x ≠ y ∧ dist x y = L) ∧
      (∀ x ∈ H ∪ I, ∀ y ∈ H ∪ I,
        0 < dist x y → dist x y < Metric.diam ((H ∪ I : Finset Plane) : Set Plane) →
          dist x y ≤ L) ∧
      1 ≤ multiplicity (H ∪ I) L ∧ multiplicity (H ∪ I) L ≤ N + k
```

The full elaborated signatures of **all eight new public theorems**, including
all fixtures, are in `Documents/132-unique-diameter/public-signatures.txt`.
Their complete name inventory is `public-declarations.txt` in that directory.
There are no new definitions, instances, axioms, section variables, or hidden
certificate parameters in the new module.

## Representation and statement fidelity

* `H` and `I` are `Finset Plane`, so their elements are distinct. The two card
  equalities state the intended `N` and `k`; disjointness is proved, not assumed.
* `K = convexHull ℝ (H : Set Plane)`. Full dimensionality is represented by
  `K` having nonempty **ambient** interior in the two-dimensional plane, not
  relative interior. This explicit premise is redundant once `I.card = k`,
  `1 ≤ k`, and interior membership are given; it is retained to expose the
  intended representation. It is therefore named `_hfull`, not secretly used
  as a certificate for a different statement.
* Every vertex in `H` is at ordinary distance `R > 0` from the **arbitrary**
  center `O`. Neither `O = 0` nor antipodality is assumed. No exterior,
  endpoint-intersection, radial-classification, or `k ≤ 3` condition is added.
* Diameter uniqueness is genuine uniqueness in `X`, modulo exchange of
  endpoints, using `Sym2`: a distinct occurring diameter pair exists, and
  every pair at the metric diameter equals that unordered pair. Endpoint
  membership in `H` is a conclusion of a helper, not an original premise.
  The quantifier over all endpoints includes diagonal pairs, but the diameter
  is positive, so these cannot satisfy the distance-equals-diameter antecedent.
* `multiplicity X L` is the existing cardinality of the `pairDist = L` filter
  of `pairs X`. `pairs X` is `X.offDiag.image Sym2.mk.uncurry`; loops are removed
  and opposite orientations identified. Thus the theorem counts actual
  unordered edges, not ordered pairs, signed directions, or distinct supports.
* `L` is derived as the finite maximum of `nonDiameterDistances X`. The final
  quantifier controls **every** occurring positive distance below `diam X`.
  It is not a hypothesis that a conveniently chosen `L` is maximal.
* The occurring pair has explicitly unequal endpoints. `N ≥ 3` and `k ≥ 1`
  ensure all required finite domains are inhabited; positive radius and
  positive/subdiametral length guards exclude junk-value interpretations.
  No subtraction, division, derivative, infinite sum, or bounded extremum
  occurs in the final statement. The finite maximum is used only after
  proving its indexing set nonempty.

The intended objects, quantifiers, original assumptions, and conclusion
survive unchanged under these representations. No mathematical weakening or
extra load-bearing premise was used.

## Proof map and reuse boundary

1. **`diam_union_interiors`**: all augmented points lie in `K`; existing
   `dist_le_diam_hull` bounds every augmented distance. Hull inclusion gives
   the reverse inequality, hence `diam X = diam H`. The general identity also
   handles empty finite inputs correctly; the final consumer does not use
   that degenerate case.
2. **`card_union_interiors`**: `dist_center_lt_radius` makes every ambient
   interior strictly inside the circle disk, while vertices have radius `R`.
   This proves `Disjoint H I` and the card sum.
3. **`diameter_endpoint_mem_hull`**: an endpoint in `I` would give a strict
   diameter inequality by the existing `dist_lt_diam_hull`. This contradicts
   the actual diameter equality, proving both original endpoints lie in `H`.
   Original uniqueness on `X` then restricts to `H`.
4. **Finite maximum in `unique_diameter_circle`**: choose an interior `i`
   and one derived hull endpoint `a`. Disk strictness proves `i ≠ a`, and
   strict hull interiority proves `0 < dist i a < diam X`. Thus the existing
   `nonDiameterDistances X` is nonempty. Its `max'` has an actual distinct
   endpoint pair by `mem_nonDiameterDistances`, is positive and subdiametral,
   and bounds every other member. Zero distances are handled separately when
   establishing the helper's stronger bound on all subdiametral distances.
5. **Arbitrary-center `longest_class_bound`**: translation `f x = x - O`
   is an isometry. `sub_mem_interior_hull`, isometric diameter transport,
   injective image cardinalities, `Sym2.map`, and
   `multiplicity_image_isometry` transport the hypotheses and conclusion.
   The translated hull has norm `R`. This invokes the unchanged
   `EvenThreeInteriorCircle.longest_class_bound` exactly once with arbitrary
   finite `I` and the proved maximum property.
6. **Unchanged geometric counting**: that supplied helper already proves
   interior-interior edges are absent, cross edges meet the derived diameter
   endpoints, the double-endpoint budget is at most `I.card + 1`, and the
   unique-diameter circular chord class has fewer than `H.card` edges. Its
   rotation argument includes nonprimitive/pentagram rotations. This new
   consumer does not rebuild or add a certificate for those arguments.
7. Card equalities give the requested `N + k` upper bound; the actual
   occurring `Sym2` edge gives `1 ≤ multiplicity X L`.

Items 1–4 are the new load-bearing original-input/maximum bridges. Item 5 is
representation and API infrastructure. Item 6 is faithfully reused checked
geometry. There is **no unpaid mathematical bridge within this contract**;
review and dependency adoption remain outside the producer's scope.

## Joint nonvacuity

`scalene_triangle_fixture` proves a concrete model in the canonical plane:

* `A = (-1, -1/2)`, `B = (3, -1/2)`, `C = (0, 3/2)`;
* center `O = (1, -1/4)`, radius `sqrt(65/16) > 0`;
* side squares `AB² = 16`, `AC² = 5`, `BC² = 13`, so `AB` is uniquely longest;
* the open rectangle `(-1/4,1/4) × (-1/4,1/4)` lies in the ambient hull
  interior: its four corners are explicit convex combinations of `A,B,C`,
  and the inherited rectangle-interior lemma supplies ambient openness.

This is a translated version of the seed's scalene triangle, and its center
is visibly nonzero. `original_hypotheses_every_positive_k` selects a `k`-point
finite subset of the infinite open hull interior. Diameter transport and
endpoint location prove the **original** unique-diameter hypothesis on `H ∪ I`
for that same model. It invokes the final theorem, returning both all original
hypotheses and the entire largest-nondiameter conclusion for every `k ≥ 1`.
No continuity gap, small-ball condition, or new closeness premise is needed:
strict ambient interiority already prevents a new diameter endpoint.
`original_hypotheses_four_interiors` specializes the joint hypotheses at
`N = 3`, `k = 4`, explicitly witnessing a concrete instance beyond three
interiors. These are formal proofs, not numeric probes.

## Provenance and unadopted dependencies

The mathematical input is the user-authorized complete corrected seed
`Documents/Erdos132Routes/DiameterGraph.md` at
`d1606b9c208c5b7b11edc36a53f8e9fa3f18c330`, especially its largest-nondiameter
correction and arbitrary-`k` route. The new file imports the ready seed helper
without any preliminary or independent paid review.

The following existing Lean modules are unchanged and remain **unadopted
inputs** in this producer handoff:

| Module under `Proofs/Erdos/Erdos132/` | Role |
| --- | --- |
| `DoubleEndpoint.lean` | Proved scalar/double-endpoint uniqueness |
| `CircleFixtures.lean` | Ambient rectangle-interior fixture infrastructure |
| `CircleRotation.lean` | Saturated circular chords and genuine rotations |
| `EvenThreeInteriorCircle.lean` | Ready arbitrary-finite-I centered longest-class helper |
| `EvenThreeInteriorFixtures.lean` | Same-base fixture inventory; not imported by the new module |

Separately, inherited `TwoInteriorCircle.lean` supplies the plane, pairs,
multiplicity, hull/distance and translation APIs. It is not a newly produced
or newly adopted dependency in this handoff; its unchanged bytes are recorded
alongside the five same-base inputs in `dependency-sha256.txt`.

The rotation input is associated with exact revision
`5b5a5653e5e473d51abde1b6a723a4985a0ffc40`, as supplied by the user. The five
same-base module SHA-256 values are verified against
`Documents/132-even-formal/source-sha256.txt`; see the unchanged receipt below.
This records bytes and provenance, not adoption or an independent review verdict.

## Producer evidence and remaining gate

The narrow full-module Lake build and a separate temporary leaf audit check
all eight new public declarations, fixtures included. No `sorry`, new axiom,
`native_decide`, external implementation, or production probe command is used.
The public axiom inventory is confined to
`{propext, Classical.choice, Quot.sound}`. Build output may replay linter
warnings from unchanged dependencies; it does not establish a warning-free
old dependency inventory.

Receipts are in `Documents/132-unique-diameter/`:

* `build-output.txt`, `build-check.txt`: bounded narrow module build and status;
* `public-declarations.txt`, `public-signatures.txt`: complete new public inventory;
* `producer-audit.txt`, `producer-audit.lean.txt`: separate axiom audit and its
  preserved **non-imported text source**;
* `dependency-unchanged.txt`, `dependency-sha256.txt`, `source-sha256.txt`:
  unchanged seed verification and final byte receipts;
* `handoff.md`: commands, actual episode timing, fidelity, dependency/adoption
  status, and next ownership gate.

Disposable Scratch probes are removed. No umbrella module, old consumer,
shared helper, References artifact, ledger, or other station is edited. This
is a faithfully compiled complete consumer, not a disconnected helper or a
partial proof. The coordinator's whole-pair review, fresh audit, and adoption
are still pending; compilation and this producer audit are not substitutes
for those gates.
