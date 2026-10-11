# Four interior points: even lower-support branch

## Status and exact boundary

**Complete, kernel-checked zero-centered branch**, including the six-hull-vertex
endpoint (`n = 10`). This is not the full four-interior theorem.

The consumer is
`Erdos132.FourInteriorLowerSupport.exists_distance_of_even_lower_support`.
Its parameters are `n : ℕ`, `H I : Finset Plane`, and `R : ℝ`, where `Plane`
is the inherited ordinary Euclidean plane. Its visible hypotheses are exactly:

* `10 ≤ n`, `Even n`, and `H.card = n - 4`;
* `0 < R` and `∀ h ∈ H, ‖h‖ = R` (circle centered at zero);
* `I.card = 4`;
* every element of `I` belongs to the **ambient open interior** of
  `convexHull ℝ (H : Set Plane)`;
* every element of `I` is nonzero;
* `2 * (nonDiameterDistances (H ∪ I)).card = H.card`.

It proves `(H ∪ I).card = n` and an existential distance `d` satisfying:

* `0 < d < Metric.diam ((H ∪ I : Finset Plane) : Set Plane)`;
* distinct `a,b ∈ H ∪ I` with `dist a b = d`;
* `1 ≤ multiplicity (H ∪ I) d ≤ n`.

`X` is the actual untagged union `H ∪ I`; `S` is its actual inherited
`nonDiameterDistances`. The four interiors are distinct because `I` is a
four-element finset. No equal-radius, radial-fiber, common-support, rotation,
regular-hull, subgroup, pair-count, or final multiplicity certificate was added
to the consumer's premises. No contrary high-multiplicity premise is needed.
The inherited multiplicity counts loop-free unordered `Sym2` pairs, not
ordered pairs or hull-only pairs.

The natural subtraction in `H.card = n - 4` is guarded by `10 ≤ n`.
The proof derives `H.card + 4 = n`, `6 ≤ H.card`, and even hull cardinality.
Thus neither the hull nor the interior domain is empty; the radius is positive,
and the off-center points are genuinely nonzero. The canonical real and plane
structures are used, with no degenerate instance assumptions. The proof does
not use totalized logarithms, derivatives, division by geometric scalars, or
square roots. The half-turn and finite-group APIs have their nonempty and
positive-radius premises supplied explicitly.

## Mathematical proof and translation

Write `N = H.card` and `S = nonDiameterDistances (H ∪ I)`.

1. Strict ambient interior excludes membership in the circle hull. Consequently
   `H` and `I` are disjoint, their union has size `N+4`, and adding the interiors
   preserves the actual diameter. Each interior-to-hull distance is positive
   and strictly below that diameter.
2. Every off-center radial fiber has size at most two. Since `N = 2|S|`, the
   fiber sum saturates: for each interior, its hull-distance image equals all
   of `S`, and every fiber has size exactly two. These are deduced in
   `radial_saturation` from original geometry and actual support.
3. The checked common-support transport dependency yields a hull-preserving
   unit-circle rotation carrying any one interior to another. Four distinct
   interiors give at least four distinct rotations. The full stabilizer has
   finite order `m ≥ 4`, its action on the positive circle is free, and `m | N`.
4. Relative to a hull vertex `p`, encode the actual hull by a finite set `A` of
   unit complex coefficients, with `1 ∈ A` and `|A| = N`. The actual quotient
   support `A/A` is invariant under the stabilizer, so its cardinality is also
   divisible by `m`. Radial capacity gives
   `N ≤ |A/A| ≤ 2|S|+3 = N+3`. The **pre-antipodal bound is `N+3`, not `N+2`**:
   diameter coefficients may still number two. Divisibility by `m ≥ 4` forces
   equality; then `A/A = A`, and `A` is a subgroup. This connects to
   `hull_is_full_stabilizer_orbit`, which proves full stabilizer order `N` and
   that the actual hull is its full orbit. No quotient-angle representation or
   classification of finite circle subgroups is needed.
5. For an even full orbit, the half-turn supplies antipodes and diameter `2R`.
   From a fixed hull vertex, zero and diameter have singleton fibers, while
   every nondiameter hull chord has two distinct inverse-coefficient fibers.
   Hence `N = 2|nonDiameterDistances H|+2`.
6. There is a distance in `S` absent from the hull support. Its actual unordered
   edge set is covered by interior-interior edges and the four radial edge
   images. Saturation bounds the latter by eight. Transport proves that the
   four interiors have equal nonzero norm; inherited circle chord capacity
   bounds their internal edges by four. Thus its multiplicity is at most
   twelve, which suffices for `N ≥ 8` because `12 ≤ N+4`.
7. **New endpoint argument, replacing reflection-axis classification.** When
   `N=6`, Cauchy's theorem in the finite stabilizer supplies a nonidentity
   cubic rotation `g`. Its complex coefficient satisfies
   `g²+g+1=0`, giving `‖g-1‖²=3`. A hull vertex `p`, its rotation `a`, and
   `-a` therefore supply nondiameter chord squares `3R²` and `R²` in the
   actual support. Choose an actual nonzero interior `u` with `‖u‖<R`.
   Antipodal hull vertices and the parallelogram law give radial squared
   complementarity `t ↦ C-t`, where
   `C=2(R²+‖u‖²)` and `2R²<C<4R²`. Saturation transfers this complementarity
   to all of `S`. The complements of `R²` and `3R²` give four strictly
   ordered values
   `C-3R² < R² < C-R² < 3R²`
   in `S.image (fun d => d²)`. Its cardinality is at least four but at most
   `|S|=3`, a contradiction. `six_hull_lower_support_false` proves this
   directly from original geometry, not from a spectrum certificate.
8. The final consumer splits off `N=6`, uses that contradiction there, and
   applies the multiplicity argument for the other even values `N ≥ 8`.

The objects, quantifiers, strict-interior notion, lower-support equality, and
multiplicity conclusion survive unchanged within the accepted zero-centered
contract. Representing four points by a finset and using complex unit
coefficients instead of angles are representation infrastructure. The free-action
cardinality jump, quotient-support subgroup argument, support fiber count,
actual edge cover, and squared-complement endpoint are proved mathematical
bridges. The endpoint proof is a different elementary argument for the same
claimed exclusion; it does not change its hypotheses.

## Nonvacuity and limitations of the fixture

`original_geometry_family_nonempty` is a proved **joint unrestricted geometric
family** witness at `n=10` and `R=1`: the inherited rational six-point circular
hull has a nonempty ambient interior; its interior minus `{0}` is infinite,
so it contains a four-element finset. All geometric premises, parity, hull
cardinality, off-center distinctness, and actual union cardinality hold jointly.
This is a Lean existential proof using a concrete inherited rational fixture,
not numerical evidence or a proposed configuration.

It does **not** witness the lower-support equality or a contrary multiplicity
assumption. Indeed the endpoint theorem proves that the lower-support equality
cannot hold for this six-vertex geometric family. No impossible branch premise
is advertised as satisfiable. Establishing satisfiability of all lower-support
premises at larger sizes is not claimed or needed for this conditional branch
implication; this is distinct from the checked nonvacuity of its original
geometric domain.

## Verification receipts

Final production Lean SHA-256:
`06770a4910f6c5ddfcd6848d12fe40af962fd6ede5455861a4f6d7602512a560`.

* Narrow module build:
  `timeout 60s lake -q build +Erdos.Erdos132.FourInteriorLowerSupport`.
  The completed endpoint, combined consumer, and integrated family fixture
  compiled successfully. No `sorry`, declared axioms, `native_decide`, or
  trust-extending implementation attributes were introduced.
* A disposable leaf imported the production module and ran `#check @...` and
  `#print axioms ...` for **all 16 public declarations**. Full signatures were
  inspected: no phantom implicit variables, hidden certificate assumptions,
  or section-variable additions appeared.
* A separate parsed-output audit checked all 16 axiom lists: every list was
  **exactly `{propext, Classical.choice, Quot.sound}`**. This includes both
  the final consumer and the geometric-family witness. The audit used
  `timeout 60s lake env lean -j 1 -M 4000 Proofs/Scratch/FourAudit.lean`;
  Lean exited successfully. Audit commands are not retained in production.
* Audited public declarations: `card_union_four_interiors`,
  `diam_union_interiors`, `radial_saturation`, `exists_stabilizer_map`,
  `four_le_order_and_order_dvd_card`, `quotient_support_eq_of_small_gap`,
  `exists_subgroup_of_quotient_support_eq`, `exists_hull_coefficients`,
  `quotient_support_card_le`, `hull_is_full_stabilizer_orbit`,
  `hull_card_eq_twice_support_add_two`,
  `multiplicity_le_twelve_of_not_mem_hull_support`,
  `exists_distance_of_eight_le_hull_card`, `six_hull_lower_support_false`,
  `exists_distance_of_even_lower_support`, `original_geometry_family_nonempty`.
* Existing dependency linter warnings were replayed by Lake. They are not
  proof failures; the completed new module emitted no new warnings.
* The temporary probe, fixture, continuation, and audit leaves were removed
  after their results were consumed. The family fixture is now in production.

## Exact dependency inventory and review boundary

The following files were checked byte-for-byte against `jj --ignore-working-copy
file show -r <revision> <path>`. They are exact copies, not edits to producer
results. Paths below are relative to `Proofs/Erdos/Erdos132/`.

| File | Exact supplying revision | SHA-256 |
|---|---|---|
| TwoInteriorCircle.lean | `9b803530d2472c7742b66d64a1b34e440c4c60f4` (assigned base) | `d36fdcc81b8e99f149e9ca53a8d57106563e46bbf93d70ef70b395db5faaab17` |
| TwoInteriorCircle.md | same base | `55c5f008956f8f4ea64b6bac10815102fb20e2ec52df6c32cbedf8ce8b04c9a2` |
| ThreeInteriorCounting.lean | `f6bbed345ce67c9357a2b279b83d57dc98a0e9f7` | `1db0c49b92162704614f764f6b2ead4c4c3a24bbea04a7f54c975496a9253881` |
| ThreeInteriorCounting.md | same supplying revision | `25a195492eb5c02b5a9e1e85f9e0f7875f0c4f02c7c7593545d7ac42ff313d34` |
| ThreeInteriorRadial.lean | `d215195e16da217caa7ecb6911a35126fd251832` | `cab7c6a514b218811c6f66fbe2b22de88e5725560e78bf68cdfb86dc89777ba3` |
| ThreeInteriorRadial.md | same supplying revision | `a5df955a8e3e4f81174f24ae32fcfcc896cc699e8558fee8ded87ea61c8dd1b1` |
| CircleRotation.lean | `5b5a5653e5e473d51abde1b6a723a4985a0ffc40` | `13a31899aa0cfca29c9b4ddf82661714e8660fe0744519cd61d003ebc04de0f7` |
| RadialTransport.lean | `cf124460934eb09f3f2a90241cd809c8b3ba035c` | `db8652f3b9ccc205be41a2421011091e8263ecb2257866b649178b53d2a500f6` |
| CircleRotationTransport.lean | `ba82c72cc5741b38685cf98e06e84667a15e4fe2` | `643d6121613abf8dcca238a9e55cfce3ae857d75e127148cc571874da885aeff` |
| CircleRotationTransport.md | same supplying revision | `ac6bb9ca1d37d90792f76efe8c4e05e8b5704873c03f9c6acafe10f375b18ed5` |
| CircleRotationOrder.lean | `abeb5e430158fc5dca288318572d466a02f09afa` | `f4ca0de476f6170f2e494784cbeb0e80f8937ce0004c7bd6e3be3a833ec0adb7` |
| CircleShortChord.lean | `e5c0f42e160b5b7995ee9e2ae6e0b0e044415d7c` | `2abc6588177796237da2204a078e604f9219970627d5a3bae8f7fb5950aeb7b2` |
| ThreeInteriorCenter.lean | `49c11509b49624a6cf49b3ac3953c72bb4e80568` | `b25203d36913687bf00268381a99a6fa3840e3a4531ea0b8347eda4f2b9f5e11` |

The center file was present for inspection only and is **not imported** by this
new module. It remains unchanged. No MoreDistances implementation was edited.
The additional copied dependencies were producer-checked inputs, **not claimed
adopted or independently reviewed**. The new unit's compilation and transitive
axiom audit do not replace independent review, coordinator re-audit, or the
harness's dependency adoption gate.

Source route: `Documents/Erdos132Routes/FourInterior.md`, revision
`cf86c6bd44cdf4b95f4677f72ee4b621581798e4`, SHA-256
`85c660f4583431ba1f599ec2d72a19fe720c4b3d5337dea1e06d05b77adbba0d`.
The source's corrected `N+3` bound was preserved. The original hexagonal
reflection-axis proof was replaced by the squared-complement proof above.

## Remaining upstream work and effort

No mathematical gap remains in the named zero-centered even/all-off-center/
lower-support implication. Arbitrary-center transport is not implemented here;
zero-centering is the explicitly accepted unit boundary. Odd hull cardinality,
upper-support, and configurations with a centered interior remain outside this
unit. The full four-interior consumer still needs its other owned branch
bridges; this result must not be presented as their completion.

Observed work began at 17:47:12Z on 2026-10-11. A checked substantial checkpoint
was handed off at approximately 18:03Z, with same-agent resumption requested and
received at 18:04:21Z. By approximately 18:09Z the full branch and fixture had
compiled; the sixteen-declaration signature/axiom audit and exact dependency
comparison then succeeded. Scratch cleanup and the production source scan
finished by 18:12Z (about 25 minutes of elapsed wall-clock work from the recorded
start). This is recorded wall-clock evidence, not a token or
CPU estimate. The first endpoint build exposed only a local `let S` rewrite
mismatch; an explicit `change` repaired it, after which the endpoint compiled.
No bounded check timed out, no search experiment was substituted for proof, and
no failed final edit is handed off.
