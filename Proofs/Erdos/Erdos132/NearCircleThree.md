# Uniform near-circle stability with three interiors

## Delivered contract

`Erdos132.NearCircleThree.near_circle_stability` is the new geometric consumer.
For every fixed natural `n` with `9 ≤ n`, and fixed real parameters
`Δ, Θ, rminus, rplus, C` with all five positive and `rminus < rplus`, it provides
`ε₀ > 0`. This modulus depends only on those fixed data. It works for **every**
`x : Fin (n - 3) ⊕ Fin 3 → Plane`, center `O`, radius `R`, and error `ε`
satisfying:

* `0 ≤ ε < ε₀`;
* hull label zero is anchored at the origin;
* the actual finite range `points x` has metric diameter one;
* every two distinct labels have ordinary distance at least `Δ`;
* for **each** of the three interior labels, its entire closed ball of radius
  `Θ` is contained in the convex hull of the hull labels;
* `‖O‖ ≤ C`, `rminus ≤ R ≤ rplus`;
* every hull label has radial error `|dist (x i) O - R| ≤ ε`.

The conclusion is actual cardinality `(points x).card = n` and an occurring
ordinary distance `d` with `0 < d < Metric.diam (points x)` and
`1 ≤ multiplicity (points x) d ≤ n`. The multiplicity is precisely the adopted
loop-free unordered `Sym2` finite-pair count. The lower bound asserts actual
occurrence, not merely a proposed class length. There is no parity restriction,
off-center assumption, unique diameter assumption, genericity assumption,
extremeness premise for the perturbed hull labels, or witness/certificate input.
No effective numerical value of `ε₀` is claimed.

The smaller wrapper `uniform_near_circle` uses `m ≥ 6` hull labels and three
interior labels, permits any hull label to be the origin anchor, and bounds
multiplicity by `m + 3`. The main consumer sets `m = n - 3`, with the natural
subtraction guarded by `9 ≤ n`. Separation proves injectivity and restores
actual cardinality `n`; the sum indexing is not used as a substitute for actual
point cardinality.

## Connected proof mechanism

The exact-circle bridge `exact_circle_witness` assembles the adopted three
producers on the same injective labelled limit:

1. If `m + 3` is even, its being at least nine forces at least ten points and
   at least seven hull points. `EvenThreeInteriorCircle.circle_witness` applies
   to all three ambient interiors and the actual even inserted cardinality.
2. If it is odd, each of the three labels is tested for equality to `O`.
   Injectivity excludes a second center label. The appropriate insertion
   permutation applies `ThreeInteriorCenter.one_center_circle` to the other
   two distinct off-center interiors.
3. If none equals `O`, `ThreeInteriorOffCenter.circle_witness` applies. Its
   explicit endpoint-occurrence field is redundant here because the retained
   positive multiplicity already establishes occurrence.

These branches all produce the same strict nondiameter, multiplicity `1..m+3`
conclusion in the actual limiting point set. Center permutations keep every
interior point; there is no two-label specialization or omitted third depth.

The uniform proof adapts the accepted finite-product compactness assembly:
negating uniformity chooses bad configurations with error at most
`1 / (j + 1)`. The anchor and actual diameter one bound every coordinate by
one; the center and radius hypotheses provide the other compact factors.
A convergent subsequence preserves separation and hence injectivity.
The generic adopted `closedBall_subset_hull_limit` preserves the full depth
ball for each of the three labels. Positive `Θ` gives ambient topological
interior, not relative interior. The limiting radial errors are zero and the
radius stays positive by its lower bound.

The exact-circle bridge supplies the limiting witness. The generic adopted
`NearCircleStability.eventually_witness` transports its selected occurring
pair to the nearby configurations. The entire nearby equality class is
contained eventually in the entire limiting class: old equalities may split,
but outside limiting classes cannot merge into the selected class on a common
finite tail. Positivity and a strict comparison with a longer limiting pair
persist. Diameter ties are allowed. This contradicts the chosen bad sequence.
There is no new continuity certificate premise and no circular rigidity claim.

## One simultaneous original-geometry model

`normalized_exact_circle_fixture` constructs one compatible **n = 9** model,
not a model for arbitrary prescribed margins. It uses the same concrete
six-vertex centered original geometry as the adopted center fixture:
`(±1,0), (0,±1), (3/5,4/5), (-3/5,-4/5)` on the unit circle, together with
center zero and two distinct small nonzero opposite ambient interior points.

The shared fixture existentially hides its size, so its statement does not
justify specializing its hidden `n` to nine. The new private local construction
copies that unchanged concrete argument and exposes **H.card = 6**. This is
representation infrastructure, not a strengthened mathematical assumption or
an edit to the adopted source. The six-vertex geometry has full affine span;
central symmetry and convexity establish a genuine ambient interior
neighborhood at zero. Two small opposite points lie in that neighborhood.

The new module enumerates those six hull points, labels all three interiors,
proves actual nine-point cardinality and injectivity, translates the first hull
vertex to zero, and scales by the inverse of the **positive actual diameter**.
The homeomorphic affine normalization preserves ambient hull interior.
One common positive depth is half the minimum of all **three** positive
neighborhood radii. A minimum over the nonempty finite set of actual
loop-free labelled pair lengths gives a positive common separation. Compatible
radius bounds are half and twice the normalized positive radius; the center
bound is its norm plus one. Every hull radial error is exactly zero, and the
fixture also proves genuine hull extremeness (not a consumer hypothesis).

Ground-truth examples establish `Fintype.card (Labels 6) = 9`, nonemptiness of
the sum domain even with zero hull labels, and nonemptiness of the intended
hull domain under `9 ≤ n`. The main theorem therefore does not operate on
`Fin 0` or empty hulls. The normalization inverse is guarded by positive
diameter, the circle radius by `rminus > 0`, and the depth by `Θ > 0`.

## Provenance, producer evidence, and remaining gates

All adopted project inputs are read-only at exact assigned base
`21157777a8dee5802b73027fa2acf0f6f11e5dc4`.
The primary stability source is byte-identical to its accepted source
`6da95642c4662e4595605f8ca882d3bb6399b078`:
32133 bytes, SHA-256
`03b8fb25acb5ee1b7f8bde7d723b4835aab967b82844eaf345b6977f9118352b`.
Its complete companion was supplied literally in the dispatch; its unchanged
SHA-256 is `fd3bc5fce1ca2c6e2ccb53419dff28d4d973e01a4771b232d4153ee9ea3f2cbb`.
The three exact-circle producers are the accepted modules in that same base.
The full source/API companion reading preceded implementation.

### Completed producer receipts (11 October 2026, UTC)

The full new module compiled after the **last Lean edit**, with task
`three-final-module-build2` (successful tool outcome):

```sh
timeout --kill-after=2s 60s lake -q build +Erdos.Erdos132.NearCircleThree
```

The complete retained log is
`/tmp/near-circle-three-evidence/final-build2.log`. The new module emitted no
warnings; adopted dependencies replayed their existing warnings. On resume,
the final Lean source was byte-compared successfully with the compiled
intermediate `c8db2b798826945dac1c8f6f06b0e8fd9e8ebe4f`. No Lean edit occurred
on resume; only this companion was completed. Thus that last-Lean-build receipt
remains valid.

The initially launched imported audit had a complete retained `audit.log`, but
no completion outcome was delivered before owner finalization, and it was no
longer running on resume. Its unknown exit status is **not** counted as a pass.
The same required audit was rerun in the harness resume workspace as
`three-resume-imported-audit`, with successful tool outcome and retained exit
status **0**:

```sh
timeout --kill-after=2s 60s lake env lean -j 1 -M 4000 \
  /tmp/near-circle-three-evidence/Audit.lean
```

This separate leaf imports the final module and explicitly runs `#check @`
and `#print axioms` for **all six new public declarations** and the prepared
upstream inventory: **187 declarations across 14 project modules**. The six
new signatures were read in full and retain the intended parameters and
conclusions, with no hidden section hypotheses. `Labels` is axiom-free; the
other five new declarations depend only on `propext`, `Classical.choice`, and
`Quot.sound`. Every inventoried transitive declaration's reported axiom set
was checked to be a subset of these same three. Sources and complete output:
`Audit.lean`, `public-inventory.json`, `resume-audit.log`, `resume-audit.exit`,
`six-public-signatures.txt`, and `axiom-review.json` in the same evidence
directory. This is a **producer** audit, not the coordinator's independent
fresh audit.

The separate same-fixture consumer ran as `three-resume-consumer`, with
successful tool outcome, exit status **0**, and empty diagnostics:

```sh
timeout --kill-after=2s 60s lake env lean -j 1 -M 4000 \
  /tmp/near-circle-three-evidence/Consumer.lean
```

Its existential example obtains `x, O, R, Δ, Θ, rminus, rplus, C` and **all**
shared hypotheses together from `normalized_exact_circle_fixture`, applies
`near_circle_stability 9` using those exact same margins, and applies its
universal conclusion to that exact same `x, O, R` with **ε = 0**. Exact radial
equality proves the zero-error bound; positive `ε₀` discharges the strict
error condition. No margins or configuration are chosen independently.
The returned existential retains all original simultaneous hypotheses and
adds the actual cardinality and positive strict-nondiameter multiplicity
conclusion. Its source, complete log, and exit status are `Consumer.lean`,
`consumer.log`, and `consumer.exit` in the evidence directory.

Final hygiene and exact-base dependency checks report no proof placeholders,
added axioms, unsafe computational attributes, `native_decide`, exploratory
commands, or retained Scratch probes in the deliverable. All **21** prepared
transitive adopted Lean/companion files are byte-identical to assigned base
`21157777a8dee5802b73027fa2acf0f6f11e5dc4`; the inventory was rerun on resume
without expanding its scope. `unchanged-dependencies.json` records paths,
sizes, and SHA-256 hashes. The sole source deliverables are this new production
pair. Complete final sources, literal full diff from that base, hygiene and
hash receipts, and audit/consumer sources are retained outside the repository
under `/tmp/near-circle-three-evidence/` for parent inspection.

Earlier failures were not suppressed: `three-exact-bridge` timed out (124)
during dependency rebuilding; `three-assembled-build` failed (1) on fixture
elaboration and heartbeat limits; `three-fixture-repair` failed (1) on the
local docstring/option arrangement; `three-final-module-build` failed (1) on
an unnecessary terminal `ring`. These local errors were repaired before the
successful final module build. Their logs are retained; none was reported as
a checked proof.

Supplied public consumption was **19:26:04.254595Z**; the final resumed checks
were observed completed by **19:42:39Z**, about **16½ minutes** later. This is
observed elapsed episode time, not an invented estimate of active effort. The
original implementation cutoff **20:03:04.254595Z** and hard episode deadline
**20:11:04.254595Z** remain unchanged. The geometric consumer is now available
under its stated uniform margins; applying it to an arbitrary unnormalized
configuration still requires the stated normalization, separation, radius,
and depth hypotheses. No unconditional resolution of Erdos 132 is claimed.

No independent reviewer was dispatched in this episode. Independent full-pair
semantic/literal review, the coordinator's fresh imported all-public audit,
parent final full-source/diff inspection, harness finalized-revision receipt,
and adoption remain **UNPAID/PENDING**; none is implied by producer compilation.
The harness owns the final working-copy snapshot. No source revision was
created or described here. Existing modules, References, and global Ledger
were not edited, and there was no upload/adoption or graph operation.
