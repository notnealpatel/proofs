# Odd three-interior off-center branch — arbitrary-center consumer

## Status and public contract

**Complete arbitrary-center original implication**, not merely a deficit
checkpoint or a zero-centered result. The final public theorem is
`Erdos132.ThreeInteriorOffCenter.circle_witness` in
`ThreeInteriorOffCenter.lean`. The checked `zero_center_witness` core is preserved.

Its premises are exactly `9 ≤ n`, `Odd n`, `H.card = n - 3`, `0 < R`,
`∀ h ∈ H, dist h O = R`, three pairwise-distinct points `u,v,w` all different
from the arbitrary center `O`, and
membership of each in the **ambient interior** of `convexHull ℝ (H : Set Plane)`.
For `X = insert u (insert v (insert w H))`, it concludes `X.card = n` and
an actual occurring real distance `d` with
`0 < d`, `d < Metric.diam (X : Set Plane)`, and `1 ≤ μ_X(d) ≤ n`.
Occurrence is explicit: `∃ a ∈ X, ∃ b ∈ X, dist a b = d`.
No common-support, equal-interior-radius, saturation, orbit, group-order, or
deficit certificate is a public premise.

The intended plane, finite sets, circle geometry, quantifiers, strict ambient
interiority, distinctness, nonzero conditions, and ordinary distance all survive
unchanged. Multiplicity is the inherited unordered **loopfree `Sym2`** multiplicity
on `TwoInteriorCircle.Plane`, not an ordered-pair surrogate. The conclusion also
records the required exact cardinality and explicit occurrence.

## Implemented original-geometry bridge

The private `not_all_large` derives every contrary-model fact from the original
geometry and the negation of the ordinary witness. The private arithmetic
`deficit_contradiction` is consumed by that bridge, which is consumed by the
public witness theorem; it is not the final exported contract.

1. Counting saturation gives `N=H.card=2*q`, `n=2*q+3`, `q≥3`, support
   `S=nonDiameterDistances X`, and all three radial fibers of size two.
2. Actual transporters `u→v` and `u→w` in the full stabilizer give `M≥3`.
   The existing group APIs supply `M∣N` and `M∣μ_H(s)` for each `s∈S`.
3. The actual unordered-pair insertion partition gives
   `μ_X(s)=μ_H(s)+6+t_s`, where `t_s=μ_{u,v,w}(s)`.
   Chord capacity guards the natural subtraction `δ_s=N-μ_H(s)`;
   contrary largeness then gives `δ_s≤2+t_s≤5` and `M∣δ_s`.
4. Every actual interior-interior pair is strictly subdiametral. The genuine
   pair-support sum gives `Σ_S t_s=3`. Attained positive hull diameter gives
   `D=μ_H(diam H)≥1`. Actual hull-pair partition, guarded subtraction identities,
   and the even-size choose identity give `Σ_S δ_s=q+D`.
5. If `M≥6`, divisibility and `δ_s≤5` give all deficits zero.
   If `M=5`, pointwise `3*δ_s≤5*t_s` gives total deficit at most five;
   `5∣2q` forces `q≥5`, contradicting `q+D≥6`.
   If `M=4`, pointwise `δ_s≤2*t_s` and divisibility of the sum by four give
   total deficit at most four. The imported even-order geometry gives actual
   antipodal closure, and the proved actual diameter-pair count gives `D=q`,
   contradicting `q+D≥6`.
   If `M=3`, the imported actual orbit theorem makes the three interiors
   equilateral. Direct enumeration of the actual three-point `Sym2` pairs
   concentrates their lengths in one occurring subdiametral class. Every other
   deficit is zero, and the exceptional deficit is at most three, contradicting
   `q+D≥4`.
6. Negating the public witness produces the required contrary largeness;
   actual distinct-pair membership establishes the lower multiplicity bound.
   Original geometry independently proves `X.card=n`.
7. `circle_witness` translates by the injective isometry `f(h)=h-O`.
   The inherited APIs preserve ambient-interior membership, hull and inserted-set
   cardinality, diameter, and genuine unordered-pair multiplicity. Nonzero
   translated interiors are exactly the explicit exclusions `u,v,w ≠ O`.
   Applying the preserved zero-centered core gives the same distance `d`;
   `Finset.mem_image` supplies preimages of both occurring endpoints, and
   `hf.dist_eq` transports their distance equality back. Thus the final theorem
   retains explicit occurrence in the ORIGINAL point set and the bound `≤n`.

## Checked infrastructure and consistency

Public infrastructure includes `multiplicity_insert`, `multiplicity_insert_three`,
`sum_multiplicity_of_pair_support`, `one_le_multiplicity_of_pair`, and
`hull_pair_partition`; actual antipodal geometry and the exact diameter count
`2*μ_H(diam H)=H.card`; and `three_le_order_of_distinct_images`.
The diameter count uses the actual map `a ↦ s(a,-a)` with fibers `{a,-a}`.

`original_offcenter_geometry_fixture` jointly realizes **all original premises**
at `n=9`, `R=1`, and the inherited six-point rational circle. An actual open ball
in the ambient interior supplies three distinct nonzero points. This fixture
contains no impossible contrary multiplicity hypothesis. Original quantified
point domains and hull sets are nonempty; under the contrary branch, `q≥3`
ensures the distance support is nonempty as well. The final leaf audit also
jointly instantiates every arbitrary-center premise at this same concrete model
with `O=0`, using `dist_zero_right`; no extra geometric premise was added.

## Producer checks

- `offcenter-original-witness`: whole-module build passed, 9.7 seconds reported
  elaboration, before removing harmless unused simp arguments.
- `offcenter-final-whole-module`: bounded `lake -q build
  +Erdos.Erdos132.ThreeInteriorOffCenter` **passed after the final Lean edit**.
  No new-module warnings remain; inherited dependency warnings are unchanged.
- `offcenter-final-signatures-axioms`: disposable leaf audit **passed**. The full
  public signature has precisely the original premises and required conclusion;
  all twelve public declarations report exactly
  `{propext, Classical.choice, Quot.sound}`. This includes the zero-centered consumer,
  and therefore its consumed private bridge and arithmetic proof.
- `offcenter-arbitrary-center-build`: bounded whole-module build **passed after
  the final Lean edit**, including `circle_witness`. There are no new-module
  warnings; inherited dependency warnings remain unchanged.
- `offcenter-arbitrary-center-audit`: disposable leaf audit **passed**. The full
  `#check @circle_witness` signature has exactly the requested arbitrary-center
  premises and original-set cardinality, occurrence, and multiplicity conclusion.
  `circle_witness`, `zero_center_witness`, and the original fixture each report
  exactly `{propext, Classical.choice, Quot.sound}`. The joint concrete model of
  all wrapper premises also compiled.
- No `sorry`, new axioms, native computation, or production diagnostic commands
  were introduced. Temporary audit/probe leaves are removed before handoff.

Producer compilation and axiom inspection are distinct from independent formal
review and the coordinator's fresh imported audit; those remain unpaid.

## Exact unmodified dependencies loaded

- Counting: `f6bbed345ce67c9357a2b279b83d57dc98a0e9f7` (already present).
- Equal-radius: `d215195e16da217caa7ecb6911a35126fd251832` (preserved).
- Orbit transport: `ba82c72cc5741b38685cf98e06e84667a15e4fe2`.
  Added unmodified `CircleRotation.lean`, `CircleRotationTransport.lean`,
  `CircleRotationTransport.md`, `RadialTransport.lean`; existing
  `ThreeInteriorRadial.lean` is byte-identical to that revision.
- Order geometry: USER-relayed `abeb5e430158fc5dca288318572d466a02f09afa`.
  Added `CircleRotationOrder.lean` unmodified; its namespace is
  `Erdos132.CircleRotation`.

Final exact-revision byte comparisons passed for the counting Lean source,
all five listed transport files, and the order Lean source. Frozen counting and
equal-radius pairs and finalized dependency sources were not edited.

## Completion boundary

The arbitrary-center wrapper is **complete**, including explicit occurrence and
exact cardinality. No original-geometry-to-deficit or translation bridge remains
unpaid for the all-three-off-center branch. The original zero-centered core is
preserved. Complementary center-status branches, independent review, coordinator
fresh audit, and adoption are not claimed here. The wrapper introduces only
representation/translation infrastructure, not new geometry or stronger
hypotheses. The separate even module was inspected read-only as a template and
was neither imported nor changed.

Work remained inside the original episode with its unchanged 17:30 UTC cutoff.
The original core compiled at 17:03 UTC; arbitrary-center closure was assigned
at 17:10:18 UTC and completed within that same episode.
