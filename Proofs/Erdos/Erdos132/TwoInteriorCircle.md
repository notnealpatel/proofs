# Two-interior cyclic-hull theorem

## Contract and status

The sibling Lean module now contains the full universal consumer `Erdos132.TwoInteriorCircle.two_interior_circle`, together with the joint geometric non-vacuity theorem `rational_circle_fixture`. The final production build is recorded below. Independent imported axiom audit and Lean/Markdown review remain the parent's separate gates; compilation is not being represented as completion of those gates.

The consumer quantifies over every natural `n ≥ 8`, finite planar hull `H` of cardinality `n - 2`, circle center `O` and radius `R`, and distinct points `z,w` in the **ambient interior** of `convexHull ℝ H`. Its hypotheses include all hull vertices being extreme points and all lying on the same circle. It concludes that `X = insert z (insert w H)` has cardinality exactly `n`, and that there is an ordinary distance `d` with

```text
0 < d < Metric.diam X
1 ≤ multiplicity X d ≤ n.
```

Here `Plane = EuclideanSpace ℝ (Fin 2)` with its canonical metric; finsets enforce distinct vertices. Natural subtraction is guarded by `8 ≤ n`. Radius positivity is derived, not assumed by the final consumer. No saturation, unique-diameter, reflection-invariance, opposite-center, or central-symmetry certificate was added as a premise. The extreme-point hypothesis is retained in the consumer, although the proof works under the stronger available fact that distinct points on a circle are extreme in their hull and does not need that hypothesis separately.

## Genuine pair representation

`pairs X = X.offDiag.image Sym2.mk.uncurry` excludes equal endpoints and identifies orientations. `mk_mem_pairs` supplies the exact endpoint/distinctness characterization, and `card_pairs` gives `X.card.choose 2`. `pairDist` descends ordinary distance to `Sym2`. `multiplicity` is the cardinality of the corresponding distance filter of these actual unordered pairs. The original two-real-point multiplicity-one example remains in production. `nonDiameterDistances` contains occurring distances strictly below the actual augmented diameter, not squared or proposed distances.

## Completed argument

1. Strict ambient interior implies strict distance from hull diameter and strict containment in the circle's disk. Both interior points are new vertices, and adding them does not change the hull diameter.
2. Under negation of the conclusion, every occurring nondiameter class has multiplicity at least `n+1`. An off-center interior point exists because `z ≠ w`. Two-circle intersection bounds every radial fiber by two; all-pair counting reserves an actual diameter pair.
3. The resulting binomial budget and radial lower bound force `n = 2(q+1)` and `q ≥ 3`. Equality saturates every radial fiber, every nondiameter class, and leaves exactly one unordered diameter pair.
4. A hull chord class has multiplicity at most the hull cardinality. If one interior point were the circle center, every large class would have to be one of two exceptional lengths, contradicting `q ≥ 3`.
5. Each off-center interior point gives a reflection preserving the hull without fixed hull vertices. Both reflections exchange the unique diameter endpoints, including the antipodal case. The two-dimensional perpendicularity argument puts both interior points on the same signed axis.
6. Equality of radial supports becomes an affine permutation of the finite squared-distance set. Its slope is `±1`; distinctness excludes `+1`, so the two interior points are opposite. Opposite radial supports yield central symmetry. Every antipodal hull pair is a diameter pair, so uniqueness forces at most two hull vertices, contradicting at least six.
7. `zero_center_witness` closes the full centered implication; `multiplicity_image_isometry` preserves true unordered-pair multiplicity under translation, and `sub_mem_interior_hull` transports ambient interior. `circle_witness` handles arbitrary circle centers. `two_interior_circle` derives radius positivity and the exact `n`-parameter conclusion.

No assumption that the circle center belongs to the hull interior was introduced. Signed scalar positions, rather than unsigned distances from the center, are used in the equality argument.

## Joint non-vacuity

`rational_circle_fixture` fixes the six rational unit-circle vertices

```text
(1,0), (0,1), (-1,0), (0,-1), (3/5,4/5), (-3/5,-4/5).
```

It proves their finset has cardinality six and every vertex has distance one from the origin. The first three vertices span the entire affine plane, so their hull has nonempty ambient interior. It selects an interior point `z`, a positive ball contained in that interior, and constructs a distinct interior point `w = z + (ε/2) • (1,0)`. Sphere extremeness and containment of the hull in the closed unit ball prove **all six vertices are extreme in their hull**. Thus one joint model satisfies every geometric hypothesis at `n = 8`; this is not an isolated witness for separate arithmetic hypotheses. The interior points are constructed from a proved open-ball witness, rather than asserted to be named rational coordinates.

## Verification and remaining gates

The complete centered consumer, translation bridge, arbitrary-center consumer, and final `n`-parameter consumer compiled in bounded scratch checks. The joint fixture separately compiled after adding the inner-product-space convexity instance import. They were then flattened into the production module, with no production dependency on scratch modules and no informational `#check`, `#print`, or `#eval` commands.

Final production check:

```text
timeout --kill-after=2s 60s lake -q build +Erdos.Erdos132.TwoInteriorCircle
```

Final production result: pending at the time this text was written; to be updated from the returning check.

No `sorry`, declared axioms, `native_decide`, implementation overrides, or new unproved premises were intentionally introduced. Earlier imported audits covered only the original infrastructure. The new completed consumer and joint fixture require the parent's fresh imported axiom audit and independent semantic review. There is no remaining mathematical bridge or consumer premise left unpaid in the source.

The frozen argument/reference artifacts and global ledger were left untouched. No revision was created, described, or moved by the prover. Work continued under the hard 2026-10-11 15:17 UTC cutoff; the final integration began at 15:15 UTC. These are observed timestamps, not invented usage estimates.
