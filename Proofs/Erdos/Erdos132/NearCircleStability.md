# Uniform qualitative near-circle stability

## Delivered statement and provenance

`Erdos132.NearCircleStability.near_circle_stability` proves the main **uniform** theorem, not only local openness. Fix `n ≥ 8` and positive `Δ, Θ, rminus, rplus, C`, with `rminus < rplus`. There exists `ε₀ > 0`, depending only on these fixed parameters, which works for every labelled configuration satisfying:

* `x : Fin (n - 2) ⊕ Fin 2 → Plane`, with the first hull label equal to zero;
* actual finite-set diameter equal to one;
* distance at least `Δ` between **every two distinct labels**;
* both closed balls of radius `Θ` about the interior labels contained in the convex hull of the hull labels;
* `‖O‖ ≤ C`, `rminus ≤ R ≤ rplus`, and ordinary-distance radial errors at most `ε`, where `0 ≤ ε < ε₀`.

The conclusion is `(points x).card = n` and an actual distance `d` with
`0 < d < Metric.diam (points x)` and `1 ≤ multiplicity (points x) d ≤ n`.
`multiplicity` is the predecessor's loop-free unordered `Sym2` finite-set count. The labelled counting helper agrees with this actual count under injectivity; positive label separation supplies injectivity. There is no unique-diameter, genericity, distinct-distance, or low-multiplicity-certificate premise. Ordinary distances are used throughout. Ambient closed-ball depth, not relative interior, is retained.

The source argument is `Documents/Erdos132Routes/Stability.md` at
`807ade24165c149a4b12fcedd0d2c4d759eb52fa`. The checked exact-circle input is
`Erdos132.TwoInteriorCircle.circle_witness`, from the unchanged predecessor in that same base. This report does not assert independent review or adoption of the new route.

The underlying `uniform_near_circle` uses `m ≥ 6` hull labels and two interior labels, permits any hull label to be the zero anchor, and concludes multiplicity at most `m + 2`. The named consumer specializes `m = n - 2` and restores the exact `n`-point cardinality. Its quantifiers and parameter dependence are unchanged from the assigned main claim.

## Proof mechanism and translation choices

1. A selected label pair's nearby distance class is eventually contained in its **entire** limiting class. Finitely many outside classes are excluded by continuity and their unequal limiting distances. Equalities within the limiting class need not persist: splitting is harmless.
2. A witnessed positive nondiameter distance remains positive and nondiameter. For the latter, choose an actual strictly longer limiting pair and preserve the strict comparison. Thus the implementation does not need a separate continuity theorem for the finite-set diameter at the limit. This is a proof simplification, not a weakening of the normalized hypotheses or final conclusion.
3. A finite hull is represented by barycentric weights in a compact standard simplex. The point/hull membership relation is closed after projecting away those weights. For a point of a limiting closed ball, translate its fixed offset from the limiting interior label to each approximating interior label; closed hull membership then preserves the entire closed-ball inclusion. Positive `Θ` gives genuine ambient interior.
4. A hypothetical failure produces bad configurations with radial errors bounded by `1 / (j + 1)`. Diameter one and an anchor at zero bound all point coordinates by one. The centre bound and radius interval give a compact product containing all labels, centres and radii. A convergent subsequence preserves label separation and both depth inclusions. The errors tend to zero, so all limiting hull labels lie on one circle of positive radius.
5. The checked exact-circle theorem supplies a limiting witness. The local selected-pair result yields nearby witnesses, contradicting the bad sequence. This establishes the uniform existential modulus.

No Hausdorff-distance or support-function development, numerical gap bound, effective modulus, semialgebraic elimination, or solution of unrestricted Erdős 132 is claimed. The source's supporting-halfspace passage is replaced by the checked barycentric argument. Natural subtraction `n - 2` is guarded by `8 ≤ n`; radius positivity is guarded by the positive lower radius bound. The inverse diameter used in the fixture is guarded by its strictly positive actual diameter.

## Simultaneous original-geometry non-vacuity

`normalized_exact_circle_fixture` starts with the unchanged predecessor's rational six-vertex unit-circle fixture and its two distinct ambient-interior points. It enumerates the six hull points, adjoins the two interior labels, proves injectivity, translates the first hull point to zero, and scales by the inverse of the positive actual eight-point diameter.

The single resulting configuration jointly satisfies:

* first hull label zero and actual diameter one;
* eight distinct points and a positive minimum pair-distance separation;
* a common positive closed-ball depth for both interior labels;
* positive compatible radius bounds and a positive centre bound;
* **exactly zero** radial error for all six hull labels;
* all six hull labels are actual extreme points of their hull.

Homeomorphic affine normalization preserves ambient interior and hull membership. The common depth is half the minimum of two positive neighborhood radii; the separation is the minimum over the nonempty finite set of loop-free label-pair distances. Bounds are chosen around the actual positive normalized radius. The fixture therefore does not demand incompatible arbitrary margins. It exhibits one simultaneous compatible `n = 8` original-geometry model, not satisfiability for every parameter tuple.

A disposable consumer probe instantiated `near_circle_stability` on this same fixture with `n = 8` and `ε = 0`, obtaining the actual eight-point cardinality and positive nondiameter multiplicity `1..8`. It compiled successfully. Production examples also check the two-point counting definitions, `Fintype.card (Labels 6) = 8`, nonemptiness of the sum label domain, and nonemptiness of `Fin (n - 2)` under the intended `8 ≤ n` guard. Generic helper statements remain valid at empty index types; the main theorem does not run on those degenerate domains.

## Compiler and audit receipts

Final production source: `NearCircleStability.lean`, 32133 bytes, SHA-256
`03b8fb25acb5ee1b7f8bde7d723b4835aab967b82844eaf345b6977f9118352b`.

After the last source edit, the following succeeded:

```sh
timeout 60s lake -q build +Erdos.Erdos132.NearCircleStability
```

Task receipt: `final-stability-build2`. The route itself had no errors or warnings. Three existing linter warnings were replayed from the unchanged `TwoInteriorCircle` dependency (unused name at line 778, unnecessary `simpa` at line 1092, unnecessary sequence focus at line 1073). No `sorry`, added axiom, native decision procedure, external implementation, or informational audit command remains in production.

A **separate imported leaf audit**, run after that build, performed `#check @name` and `#print axioms name` for all 20 public named declarations of this module and all 47 public named declarations of its only project-level producer, `TwoInteriorCircle`. Task receipt: `final-audit-and-consumer`; both the audit and the exact-fixture consumer probe exited successfully. The `#print axioms` results include recursive dependencies through Mathlib, not merely direct premises. All 67 declarations had axiom sets contained in `{propext, Classical.choice, Quot.sound}`; no `sorryAx` occurred.

The complete compiler-emitted signature/axiom inventory is retained for parent inspection at `/tmp/stability-final-audit.log` (34940 bytes), SHA-256
`4dab850181498226192c133ee5db94be230177752eddfad95d5a7b0e2b0b36c0`.
The audit source and consumer source are retained outside the workspace with the handoff artifacts; scratch probes are removed from the deliverable. No audit module is imported into production.

### Complete public declaration inventory

All entries below were individually checked with explicit `@` signatures and audited. Every entry has `{propext, Classical.choice, Quot.sound}`, except `Labels` (no axioms) and `TwoInteriorCircle.choose_even_equality` (`{propext, Quot.sound}`).

**NearCircleStability (20):**

`points`, `labelMultiplicity`, `card_points`, `multiplicity_points`,
`tendsto_pairDist`, `eventually_class_subset`, `eventually_labelMultiplicity_le`,
`eventually_injective`, `eventually_witness`, `convexHull_range`,
`isClosed_hull_relation`, `closedBall_subset_hull_limit`, `coe_points`, `Labels`,
`points_sum`, `interior_of_closedBall_subset`, `circle_limit_eventually_witness`,
`uniform_near_circle`, `near_circle_stability`, `normalized_exact_circle_fixture`.

**TwoInteriorCircle (47):**

`Plane`, `pairs`, `pairDist`, `multiplicity`, `mk_mem_pairs`, `card_pairs`,
`pairDist_mk`, `dist_lt_of_mem_interior`, `dist_le_diam_hull`, `diam_convexHull`,
`diam_pos`, `dist_lt_diam_hull`, `dist_center_lt_radius`, `radial_card_le_two`,
`card_insert_interiors`, `diam_insert_interiors`, `exists_diameter_pair`,
`nonDiameterDistances`, `mem_nonDiameterDistances`,
`hull_card_le_twice_nonDiameter_card`, `sum_nonDiameter_multiplicity`,
`nonDiameter_pair_budget`, `even_size_of_pair_budget`, `saturated_fibers`,
`choose_even_equality`, `equality_structure`, `fixed_fiber_unique`,
`reflection_preserves_saturated_hull`, `common_axis_of_swap`,
`central_symmetry_of_opposite_support`, `finite_affine_slope`,
`radial_square_affine`, `opposite_centers_of_support`, `chord_capacity`,
`center_multiplicity_bound`, `center_support_card_le_two`, `radial_mem`,
`saturated_radial_support`, `reflection_swaps_unique_diameter`,
`central_unique_card_le_two`, `zero_center_contrary`, `zero_center_witness`,
`multiplicity_image_isometry`, `sub_mem_interior_hull`, `circle_witness`,
`two_interior_circle`, `rational_circle_fixture`.

## Unchanged dependency inventory

The following working-copy SHA-256 values were compared with `jj --ignore-working-copy file show -r 807ade24165c149a4b12fcedd0d2c4d759eb52fa` and agree exactly:

| File | SHA-256 |
| --- | --- |
| `Proofs/Erdos/Erdos132/TwoInteriorCircle.lean` | `d36fdcc81b8e99f149e9ca53a8d57106563e46bbf93d70ef70b395db5faaab17` |
| `Proofs/Erdos/Erdos132/TwoInteriorCircle.md` | `55c5f008956f8f4ea64b6bac10815102fb20e2ec52df6c32cbedf8ce8b04c9a2` |
| `Documents/Erdos132Routes/Stability.md` | `ae5826a31096249faa26a5fc8647d745b7b4ed8fc5f03945be43aac4acd8b1ef` |

No other station's helper was edited, no predecessor was copied with modifications, and no new project-level dependency was introduced. Mathlib APIs supply the standard simplex, proper finite-dimensional metric compactness, continuity, and affine normalization infrastructure. New mathematical bridges are the limiting-class containment, finite-hull closed relation/depth passage, and their uniform compactness assembly.

## Effort, remaining gates, and handoff

The episode's recorded consumption time was 2026-10-11 17:47:11 UTC; its hard deadline was 18:32:11 UTC. The final source build and imported audit/consumer checks were complete by the observed clock 18:10:59 UTC (less than 24 minutes after recorded consumption). This is elapsed-clock evidence, not an invented token or CPU-time estimate. The work included local elaboration repairs and a separate normalized-fixture check; compilation of a scaffold was not counted as proof completion.

The mathematical uniform implication is complete and available to the named consumer. No unpaid mathematical bridge remains within this assignment. Effective numerical modulus extraction remains outside scope. Kernel elaboration, simultaneous non-vacuity, and the allowed-axiom audit are distinct completed checks; they do **not** constitute an independent semantic review.

Parent full-source/diff inspection and its receipt are **pending**, not claimed completed. The source pair, exact byte hashes, full imported signatures/axioms, and exported full diff are available for that inspection. The harness owns the final working-copy snapshot/revision; this document intentionally does not mislabel the earlier checkpoint as the finalized revision. The parent must attach the resulting exact finalized revision and its own inspection receipt at the finalization boundary. No independent reviewer was dispatched in this episode, no upstream adoption was performed, and the parent-owned progress artifact and coordinator-owned Ledger were left untouched.
