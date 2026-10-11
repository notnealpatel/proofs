# HullOutlierInside — formal zero-centered inside branch

## Status and scope

**Producer implementation complete:** the original inside consumer, simultaneous original-geometry fixture, application of that consumer, and the optional centered inside/outside assembly compile. The separate imported audit prints all four full public signatures and reports exactly `propext`, `Classical.choice`, and `Quot.sound` for each theorem. This is producer evidence, not the parent inspection, coordinator independent semantic/literal gate, fresh coordinator audit, or adoption.

Consumption was supplied as **2026-10-11T19:36:57Z**. The proof-finishing boundary is **20:13:57Z**, with the hard deadline **20:21:57Z**. Implementation and the first successful all-public audit were finished by **19:48:24Z**. Preparation, implementation, and compiler repair therefore took under twelve minutes to that observed checkpoint; final evidence packaging follows it. No new mathematical discovery, subagent, paid review, `tool_think`, simulation, upstream operation, or revision management was used.

The exact assigned base is `dd8a596c04649f1eb981105f6719a33c7a4ee1a1`. Only this new Lean/Markdown pair and `Documents/132-hull-outlier-inside-formal/receipts/` are deliverables. Adopted outside and shared helpers remain byte-identical to the base. No umbrella or arbitrary-center wrapper was added.

## Exact input

The complete supplied prose is retained, including its terminal LF, in `Documents/132-hull-outlier-inside-formal/receipts/exact-input.md`:

- source identity: `576313bcaa958b9d747e9c7d47219f69d3e48fb3`;
- length: 20,564 bytes;
- SHA-256: `c7648c6d5a16143020c213600d042430679c06fa55884fd14ced3d92ab723690`.

The assignment and common instructions were read. The persisted-dispatch literal byte-comparison gate remains parent-owned; this retained input is not a claim that the parent has completed that gate.

## Public contract and translation fidelity

All names below are in `Erdos132.HullOutlierInside`.

1. **`original_zero_centered_inside`** is the primary consumer. It quantifies over an actual `Finset Plane` of six points, actual points `u,z`, and a positive real radius `R`. Circle membership is ordinary `dist c 0 = R`; the outlier satisfies `dist u 0 ≠ R`. Every generator of `insert u C` is extreme in the **same actual augmented convex hull**, and both `0` and `z` belong to its **ambient interior**. The radial guard is exactly `0 < dist z 0 < R`. Its conclusion is
   ```lean
   let X := insert (0 : Plane) (insert z (insert u C))
   X.card = 9 ∧ ∃ d : ℝ, 0 < d ∧ d < Metric.diam (X : Set Plane) ∧
     1 ≤ multiplicity X d ∧ multiplicity X d ≤ 9
   ```
   There is no saturation, support, reflection, Gram, coordinate, or outlier norm-branch premise. In particular, neither interior is assumed to lie in `convexHull ℝ C`.
2. **`original_inside_geometry_fixture`** jointly realizes all the preceding geometric hypotheses at `R=1`. Its proof also establishes the chosen `z` has ordinary distance exactly `1/2` from the center.
3. **`original_inside_fixture_with_conclusion`** retains all those geometric facts and applies **this module's primary consumer**, producing the actual nine-point cardinality and the ordinary-distance conclusion.
4. **`original_zero_centered`** is the authorized optional assembly: the same geometry, positive radius, and `z ≠ 0`, but no inside/outside condition. It splits `dist z 0 < R` versus `R ≤ dist z 0`, using the new primary theorem or the adopted public `HullOutlierOutside.original_zero_centered_outside`, respectively. The same inside fixture also jointly realizes its hypotheses and applies this combined theorem in the disposable audit example.

`Plane` is the adopted ordinary Euclidean plane. Multiplicity is the unchanged `TwoInteriorCircle.multiplicity`: filter the `Finset (Sym2 Plane)` obtained from the off-diagonal pairs, then count unordered pairs at ordinary distance `d`. The adopted `mk_mem_pairs`, `pairDist_mk`, and `card_pairs` distinguish distinct endpoints, ordinary distance, and unordered binomial cardinality. The new code introduces no definitions, alternative metric, weights, tagged points, or instances.

The intended objects, quantifiers, original hypotheses, and quantitative conclusion survive unchanged. The intentional scope restriction is the supplied zero center. Squared lengths occur only in the internal failed-target contradiction, not in the public distance conclusion.

## Connected proof map

### Original geometry to actual support

The public adopted `original_target_or_saturation` already proves actual cardinality nine and either the desired target or exactly three non-diameter ordinary classes with complete two-point `z`-circle fibers. The primary consumer takes that dichotomy; it does not assume its second branch.

In the failed-target branch, let `S` be the actual non-diameter distance support of the nine points and `T = S.image (fun d => d^2)`. Positive-distance squaring is injective on `S`, so `T.card = 3`. Every member of `T` is positive, strictly below the actual diameter squared, and realized on a genuine `z`-circle edge. The public adopted diameter identity and `dist_lt_diam_hull` show every nonzero center-incident edge is non-diameter. Therefore `s = R^2` and `t = ‖z‖^2` belong to `T`, with `0 < t < s`.

The adopted public `reflection_preserves_saturated_hull` gives an actual fixed-point-free reflection permutation of the six circle points. Local intrinsic identities supply its reflected chord square. Every actual distinct circle chord either belongs to `T` or equals the actual diameter squared. These facts are passed directly to the new private actual-point obstruction.

### Homogeneous algebra, with genuine actual chords

No similarity or radical root construction is needed. A two-dimensional Gram identity is expanded in the canonical Euclidean coordinates and checked by `ring`. The reflection formula then gives the two actual cross-chord identities

\[
(H+K)t=4st-4AB,\qquad HKt=4s(A-B)^2,
\]

where `A = inner ℝ z a`, `B = inner ℝ z b`. Distinct reflected endpoints yield **strict** Gram bounds `A^2 < st` and `B^2 < st`. Their product and the cross-chord identities show `H ≠ K`. Distinct projections separately prove the cross-endpoints differ, hence both chord squares are positive.

For fibers with radial squares `s,t`, the projections are `t/2,s/2`. Thus

\[
H+K=3s,\qquad HKt=s(s-t)^2.
\]

The actual within-`s` reflected chord has square `4s-t > 3s`, so the actual diameter square `δ` exceeds `3s`. Positivity and the sum exclude `δ` for both cross-chords. Three-element support and distinctness then exhaustively give either `{s,v}` or `{t,v}`; `{s,t}` has the wrong sum.

- **Case I:** `v=2s` and `s^2+t^2=4st`. The within-`s` chord forces `δ=4s-t`. Actual cross-chords from the `t,v` fibers have sum `3s+δ` and product `3sδ`. Factoring `(U-3s)(U-δ)=0` exhibits one actual chord of square `3s`, excluded from `{s,t,2s,δ}`.
- **Case II:** `v=3s-t`; the product identity factors as `(s+t)(t^2-3st+s^2)=0`. Since `s+t` is positive, the third projection `(s+t-v)/2=t-s` has square exactly `st`. This contradicts the strict Gram bound from its distinct reflected endpoints. It is the intrinsic version of the prose's forbidden single-point tangent fiber.

This obstruction is consumed by `original_zero_centered_inside` in the actual failed-target branch. No bridge is left unpaid. No `q=dist(u,0)^2` branch was removed or constrained, and the outside obstruction was **not** used inside.

## Simultaneous geometry and boundaries

The fixture uses the adopted public `original_outside_geometry_fixture`, which supplies actual six circle points, an off-circle extreme vertex, and simultaneous ambient interiors `0,z0` in the augmented hull at radius one, with `1 < ‖z0‖`. Keep the six points, outlier, hull, and center unchanged. Put

\[
b=1/(2\|z_0\|),\qquad z=b\,z_0.
\]

The checked proof gives `0 < b < 1`, applies `Convex.combo_interior_self_mem_interior` to `(1-b) • 0 + b • z0`, and proves `dist z 0 = 1/2` using positive norm scaling. This is a genuine interior geometry, not a witness for impossible saturation. The six-point domain is nonempty; the outlier and interiors are genuinely distinct by the original geometry/cardinality theorem and positive radial guard. There is no `Fin 0`, empty support, zero-radius, or zero-center-distance loophole.

All divisions introduced locally are guarded by the nonzero norm or `0 < t`; the fixture denominator is positive. No natural subtraction or division, totalized extremum, square root, or derivative is introduced. Boundary `dist z 0 = R` belongs only to the adopted outside/boundary branch of the combined consumer. The theorem does not claim arbitrary centers, two off-center interiors, other cardinalities, or the full hull-outlier family.

## Verification and unchanged dependency evidence

The scoped receipts contain:

- `final-build.out` and `final-build.exit`: complete narrow full-module build output and exit status;
- `audit-source.txt`: exact source of the separate temporary imported audit;
- `public-audit.out` and `public-audit.exit`: complete full `@` signatures and transitive axiom output for all four public declarations, plus the application of the combined consumer to the same simultaneous fixture;
- `public-names.txt`: exhaustive public declaration inventory;
- `dependency-inventory.json`: byte-for-byte comparisons and SHA-256 for the adopted outside module, every local transitive import, and Lake/toolchain inputs, against the exact assigned base; no prerequisite copies were necessary;
- `completion.json`: final source/input hashes, public names, check commands/exits, observed completion time, and remaining parent/coordinator gates.

The proof has no `sorry`, `admit`, declared axiom, `native_decide`, replacement implementation, exploratory command, or imported audit leaf. All four audited declarations have exactly the permitted standard three axioms. Scratch probes are removed after the audit; its source survives only as receipt text.

### Actual compiler feedback and effort

The first 60-second build timed out while rebuilding unchanged adopted dependencies, before the new module was checked. A changed 180-second check allowed the cold dependency compilation and reached the new kernel. The first kernel diagnostics were local elaboration/proof repairs: the `zero_pow` nonzero exponent argument, projection rewrites in the distinctness helper, explicit substitution in the nine support cases, and multiplying the sum equation before polynomial factorization. After those repairs the entire actual-point kernel compiled in 11 seconds. The original consumer and simultaneous fixture compiled together in 12 seconds. The optional assembly and warning cleanup then passed the final module build.

The first imported audit exited 1 solely because `pp.width` was not a recognized option; its complete output and exit are preserved as `initial-audit-option-error.*`. Removing that presentation option yielded exit 0, complete signatures, the simultaneous combined application, and all four standard-three-axiom reports. No failed check was treated as success.

The new mathematics is the homogeneous inside contradiction and its strict Gram/cross-chord connection. The representation/API work is positive squaring of actual support, public saturation/reflection/diameter assembly, and convex interior scaling of a supplied genuine fixture. Generic intrinsic Gram/reflection identities are proved locally rather than relying on private outside declarations; no shared helper was edited. No persistent mathematical or infrastructure blocker remains.

Parent full final-pair inspection and the coordinator's independent exact-literal semantic review, fresh imported audit, and adoption have **not** been performed by this producer and are not claimed here.
