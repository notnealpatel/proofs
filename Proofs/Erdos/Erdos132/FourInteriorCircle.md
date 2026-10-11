# Four ambient interiors: complete even zero-centered circular branch

## Status and consumer

**Producer-complete, kernel-checked assembly** of the user-authorized even,
all-off-center, zero-centered four-interior theorem. The lower-support premise
has been removed completely. This does not claim odd-order cases, a centered
interior, arbitrary-center transport, or the unrestricted Erdős132 conjecture.

The new module is `Erdos.Erdos132.FourInteriorCircle`; its consumer is
`Erdos132.FourInteriorCircle.four_interior_circle`. There are exactly **two new
public declarations**, the consumer and `original_geometry_and_conclusion`.
There are no new definitions, instances, axioms, section variables, or helper
certificate premises.

The final Lean source SHA-256 is
`164ccf25a4f7184101332bcd0abc4896885f961d316f063b73d8825ec9923aa9`.

## Exact contract and fidelity

```lean
theorem four_interior_circle (n : ℕ) (H I : Finset Plane) (R : ℝ)
    (hn : 10 ≤ n) (heven : Even n) (hH : H.card = n - 4)
    (hR : 0 < R) (hcircle : ∀ h ∈ H, ‖h‖ = R) (hI : I.card = 4)
    (hInt : ∀ z ∈ I, z ∈ interior (convexHull ℝ (H : Set Plane)))
    (hoff : ∀ z ∈ I, z ≠ 0) :
    (H ∪ I).card = n ∧ ∃ d : ℝ,
      0 < d ∧ d < Metric.diam ((H ∪ I : Finset Plane) : Set Plane) ∧
      (∃ a ∈ H ∪ I, ∃ b ∈ H ∪ I, a ≠ b ∧ dist a b = d) ∧
      1 ≤ multiplicity (H ∪ I) d ∧ multiplicity (H ∪ I) d ≤ n
```

`Plane` is the inherited canonical Euclidean plane, not a supplied or degenerate
instance. The circle is genuinely centered at zero with positive radius. `I`
contains exactly four distinct points because it is a finset; all four are
explicitly nonzero and belong to the **ambient** open interior of the actual
hull, not relative interior. Strict disk interiority proves `H` and `I` disjoint;
the actual untagged union has size `n`. Ordinary distance and the actual metric
diameter are preserved throughout. The final occurring pair has unequal
endpoints, and `multiplicity` is the inherited loop-free unordered `Sym2` count
on that same union, not an ordered or hull-only count.

The guard `10 ≤ n` keeps `n - 4` out of natural-subtraction truncation; the proof
derives `H.card + 4 = n` and `6 ≤ H.card`. All chosen hull and interior domains
are therefore inhabited. Positive radius, positive diameter, positive occurring
length, and distinct endpoints are proved or explicitly supplied as required.
There are no bounded subtype extrema, unguarded geometric division, derivatives,
or infinite sums in the new statement or argument. The natural subtraction in
the reused pair-budget input is guarded by `10 ≤ X.card`.

**The intended objects, quantifiers, original hypotheses, and conclusion survive
unchanged within the authorized zero-centered contract.** In particular neither
support cardinality, contrary multiplicity, unique diameter, radial saturation,
full-dimensionality, nor a pair-partition certificate appears as a premise of
the consumer. Full-dimensionality for the unique-diameter precursor is derived
from an actual member of `I`.

## Complete proof map

Let `N = H.card`, `X = H ∪ I`, and `S = nonDiameterDistances X` with `q = S.card`.

1. The unchanged lower-support geometry helpers prove actual union cardinality
   `n = N+4` and `diam X = diam H`. Strict interiority excludes circle vertices
   from `I`.
2. Negate only the desired existential conclusion, after proving cardinality.
   Every member of the actual `S` has a distinct occurring pair, hence positive
   length and positive unordered multiplicity. Failure of its upper bound
   yields `μ(d) ≥ n+1` for every `d ∈ S`. This is a local contradiction
   hypothesis, not a new theorem premise.
3. Choose an actual `z ∈ I`. Its nonzero condition and the circular hull give
   radial fiber capacity two. Each hull-to-`z` distance is positive and below
   the actual diameter, hence lies in `S`. The checked finset fiber-count API
   gives `N ≤ 2q`.
4. Split on `2q = N`. The equality case invokes the **unchanged complete**
   `FourInteriorLowerSupport.exists_distance_of_even_lower_support`, including
   its `N=6` endpoint, and contradicts the negated existential.
5. In the other case, parity of `n` makes `N` even. Since `N ≤ 2q` but equality
   fails, integer arithmetic gives `N+2 ≤ 2q`, equivalently `X.card-2 ≤ 2q`.
   Apply the unchanged actual-pair theorem `TwoInteriorCircle.equality_structure`
   to `X`, this derived radial bound, and the local contrary multiplicities.
6. **Actual all-pair partition, not an assumed budget:** the inspected proof of
   `equality_structure` uses `sum_nonDiameter_multiplicity`, `card_pairs`,
   `nonDiameter_pair_budget`, and `Finset.card_filter_add_card_filter_not`.
   The two complementary filters partition every unordered distinct-endpoint
   pair of the actual `X`. Finite diameter attainment reserves at least one
   diameter pair. Its natural binomial budget is doubled using
   `Nat.choose_two_right` and `Nat.mul_div_le`, and its equality arithmetic uses
   `choose_even_equality`. Thus it derives
   `n = 2(q+1)` and cardinality one of
   `D = {e ∈ pairs X | ¬ pairDist e < diam X}`.
   Together with `n=N+4`, this is precisely the upper-support case `2q=N+2`.
   All pairs are at most the finite-set diameter, so `D` is the actual diameter
   class. The new proof only needs its singleton cardinality, not a substituted
   count or unrelated certificate.
7. Choose an actual diameter-attaining pair `a,b ∈ X`. Since `X.card ≥ 10`,
   its diameter is positive, so `a ≠ b`. Its unordered edge belongs to `D`;
   cardinality one identifies `D = {s(a,b)}`. Any other pair at the actual
   diameter is also distinct, lies in `D`, and hence equals `s(a,b)`. This
   proves exactly the original unique-unordered-diameter contract on `X`.
8. Invoke unchanged `UniqueDiameterCircle.unique_diameter_circle` with
   `N=H.card`, `k=4`, center zero, and the original geometry. The conditions
   `3 ≤ N`, `1 ≤ k`, and ambient hull interior nonemptiness are derived; norm
   is converted to distance from zero. Its occurring longest positive
   nondiameter class has multiplicity between one and `N+4=n`, contradicting
   the same negated existential. Its maximality clause is not needed here.

This exhausts the actual support possibilities under the contrary hypothesis.
No new classification, geometric research premise, or unpaid mathematical
bridge was introduced. `n=10`, `N=6` is covered by the unchanged endpoint in
step 4 and the same upper mechanism in steps 5–8; it is not discarded by a
stronger size guard.

**New mathematics:** the parity gap connects the capacity-two lower bound to
one of the two existing consumers, and the singleton pair filter is converted
to the original unique-diameter contract. **Reused mathematics:** actual pair
partition and equality arithmetic, lower-support exclusion, and the
unique-diameter longest-class bound. **Representation/API infrastructure:**
finset unions, occurrence-to-positive-multiplicity witnesses, norm-to-distance
conversion, and local `let X` normalization. None changes the contract.

## Joint fixture and nonvacuity

`original_geometry_and_conclusion` consumes exactly the witness returned by
`FourInteriorLowerSupport.original_geometry_family_nonempty` and calls the new
consumer with **all its original hypotheses simultaneously**. It returns those
same geometric hypotheses together with actual union cardinality and the whole
new existential distance/multiplicity conclusion. There is no support or
unique-diameter premise in this fixture.

The inherited concrete witness is the rational six-point unit-circle hull and
four distinct nonzero points selected in its infinite ambient open interior,
constructed at `n=10`, `R=1`. The new fixture's public statement existentially
quantifies `n`, as the predecessor does; it does not add a fixed-`n` assertion
not exposed by that signature. Its proof uses the same supplied geometric
witness, not a separate certificate model or an inconsistent contrary branch.
The original geometric domain is jointly inhabited, and the new theorem is
actually applied on it. This is a formal proof, not a numerical experiment.

## Compiler, signature, and axiom receipts

Consumption boundary: **2026-10-11 18:22:53Z**; assigned deadline:
**19:07:53Z**. Full source and companion precursors were read; canonical bytes
were checked against their named revisions. Missing dependency inputs were
copied from canonical revisions, never from mutable peer workspaces.

* `unique-input-build`: bounded narrow build of the exact unique-diameter
  input succeeded, including its previously absent dependencies.
* `first-full-check`: failed on local `let X` rewrite normalization. Explicit
  `change` steps normalized the union card goal and diameter equality. No
  mathematical hypothesis or conclusion was changed.
* `second-full-check`: the complete new module, including the joint fixture,
  built successfully with exit status zero. Command:
  `set -o pipefail; timeout 60s lake -q build +Erdos.Erdos132.FourInteriorCircle 2>&1 | tee /tmp/four-full-second-build.txt | tail -n 25`.
  Output was inspected; no diagnostic belongs to the new module. Existing
  dependency linter warnings were replayed and are not hidden proof failures.
* `full-public-audit`: separate disposable leaf imported the production module
  and ran `#check @...` and `#print axioms ...` for **both** public declarations.
  Command: `timeout 60s lake env lean -j 1 -M 4000 Proofs/Scratch/FourFullAudit.lean`.
  It exited successfully. Both full signatures were inspected; there are no
  hidden section variables or certificate arguments. A parsed-output check
  confirmed both axiom sets are exactly
  **`{propext, Classical.choice, Quot.sound}`**.
* The new source scan confirms no `sorry`, declared axioms, `native_decide`,
  implementation trust attributes, or production informational commands.
  `set_option autoImplicit false` is present. No source definitions need a
  separate ground-truth interpretation check.
* Scratch audit source is removed after consumption; raw compiler signature
  and axiom output is preserved below in this non-imported companion.

By 18:29:43Z, the full build, all-public audit, source scan, and canonical
unchanged dependency comparison had succeeded (approximately seven minutes
from the supplied consumption boundary). This is recorded wall-clock evidence,
not a CPU/token estimate. No check timed out. Final cleanup and module rebuild
are recorded below; no untested source edit is left for the parent.

## Dependency inventory and ownership gates

Inventory below records **exact unchanged bytes**, verified with
`jj --ignore-working-copy file show -r REV PATH` and byte comparison. Every
existing dependency, especially the finalized lower-support pair, is unchanged.
The only retained newly copied common inputs are `CircleFixtures.lean`,
`DoubleEndpoint.lean`, and `EvenThreeInteriorCircle.{lean,md}`. The exact
`UniqueDiameterCircle.{lean,md}` pair is also copied unchanged. Other missing
common files not needed by this import graph were not retained.

Revision labels:

* **K3** = `91abfcb64c0121addbb572a06ba6d3063bfbebc4`: common dependencies
  reported **adopted** by the user for this unit.
* **Lower** = `cb7fa9b536ca0cb847e82a0b4341640a0d1405c8`: producer-compiled,
  producer-audited, parent-inspected; independent review **running**, not yet
  adopted at assignment.
* **Unique** = `90a43ddbe9163c0a734cf2dbf89cdfe5a979a992`: same producer/parent
  status; independent review **running**, not yet adopted at assignment.

`ThreeInteriorCenter.lean` is a retained pre-existing byte-checked file, not an
import of the new consumer. No finalized source pair, shared helper, umbrella,
MoreDistances unit, References artifact, global ledger, or external progress
artifact was edited.

The **producer implication is complete** within the stated scope. Parent
complete-source/diff/companion/receipt inspection, the coordinator's fresh
all-public audit, new-pair independent review, and dependency adoption remain
upstream gates; this handoff does not claim they have occurred. No preliminary
paid review or new independent review was dispatched inside this unit. No
upload, adoption, revision creation, or manual graph management was performed.
The harness owns the final snapshot revision.

### Exact SHA-256 inventory

| File (under `Proofs/Erdos/Erdos132/`) | Revision | SHA-256 |
|---|---|---|
| `CircleFixtures.lean` | K3 | `be88d0aebc91e7a6f7e0409d30ee85416b3d7a5e4089af37f1fd813437207285` |
| `CircleRotation.lean` | K3 | `13a31899aa0cfca29c9b4ddf82661714e8660fe0744519cd61d003ebc04de0f7` |
| `CircleRotationOrder.lean` | K3 | `f4ca0de476f6170f2e494784cbeb0e80f8937ce0004c7bd6e3be3a833ec0adb7` |
| `CircleRotationTransport.lean` | K3 | `643d6121613abf8dcca238a9e55cfce3ae857d75e127148cc571874da885aeff` |
| `CircleRotationTransport.md` | K3 | `ac6bb9ca1d37d90792f76efe8c4e05e8b5704873c03f9c6acafe10f375b18ed5` |
| `CircleShortChord.lean` | K3 | `2abc6588177796237da2204a078e604f9219970627d5a3bae8f7fb5950aeb7b2` |
| `DoubleEndpoint.lean` | K3 | `5fd7b831694e9dba1323161dcea3fb3eb4527d1e8fdbef2cdc3c5440ef7f11af` |
| `EvenThreeInteriorCircle.lean` | K3 | `3dd828e512ce849512653d3d2517ac36564a5ac58ee4a6850eb5530a0b801c58` |
| `EvenThreeInteriorCircle.md` | K3 | `48c33614104fba4a519646f328fbce01587ecbe6bb4ac8fbe9f57ca5ddae867f` |
| `RadialTransport.lean` | K3 | `db8652f3b9ccc205be41a2421011091e8263ecb2257866b649178b53d2a500f6` |
| `ThreeInteriorCenter.lean` | K3 | `b25203d36913687bf00268381a99a6fa3840e3a4531ea0b8347eda4f2b9f5e11` |
| `ThreeInteriorCounting.lean` | K3 | `1db0c49b92162704614f764f6b2ead4c4c3a24bbea04a7f54c975496a9253881` |
| `ThreeInteriorCounting.md` | K3 | `25a195492eb5c02b5a9e1e85f9e0f7875f0c4f02c7c7593545d7ac42ff313d34` |
| `ThreeInteriorRadial.lean` | K3 | `cab7c6a514b218811c6f66fbe2b22de88e5725560e78bf68cdfb86dc89777ba3` |
| `ThreeInteriorRadial.md` | K3 | `a5df955a8e3e4f81174f24ae32fcfcc896cc699e8558fee8ded87ea61c8dd1b1` |
| `TwoInteriorCircle.lean` | K3 | `d36fdcc81b8e99f149e9ca53a8d57106563e46bbf93d70ef70b395db5faaab17` |
| `TwoInteriorCircle.md` | K3 | `55c5f008956f8f4ea64b6bac10815102fb20e2ec52df6c32cbedf8ce8b04c9a2` |
| `FourInteriorLowerSupport.lean` | Lower | `06770a4910f6c5ddfcd6848d12fe40af962fd6ede5455861a4f6d7602512a560` |
| `FourInteriorLowerSupport.md` | Lower | `023d9de2e37a924cabaa64302f3c01ee169450cb7e1ddff731ba6a1417f5dc1f` |
| `UniqueDiameterCircle.lean` | Unique | `242734d06e494833541c30cf13e38377d887824f91e8431a9a57ed48e9834745` |
| `UniqueDiameterCircle.md` | Unique | `03b9f5bbec9aabd973bd4754790be925432259e09699444ad8cc2f9d28399206` |

### Final gate receipt

At **2026-10-11 18:32:52Z**, approximately ten minutes after the supplied
consumption boundary, cleanup and final checks were complete:

* `four-full-final-build` exited **zero** using the same bounded, pipefail-
  preserving narrow module build command, with log path
  `/tmp/four-full-final-build.txt`. Its 95-line output was inspected; it contains
  only replayed inherited warnings, no diagnostic from the new module. Output
  SHA-256: `95eb5f4c2d4fb66a9157b629a8275f32a600e77647d07e2a00bb6b90d81a6c3d`.
* Separate all-public audit output SHA-256:
  `f70933f59f69e503cafb24c1fe9dd8ab157baf802ecd5a602689f7aeaef9fb67`;
  its full content is preserved below. Both production declarations are
  compiled without `sorry` and have only the standard three axioms.
* Final source digest is unchanged. All 21 retained canonical input file
  comparisons passed again. Scratch no longer exists.
* Filesystem/source comparison confirmed every original file at assigned base
  `9b803530d2472c7742b66d64a1b34e440c4c60f4` unchanged. That older base has only
  the `TwoInteriorCircle` pair in this directory, so the complete filesystem
  delta from it has 21 additions, including inherited prior-unit files.
* The consumed prior-unit checkpoint
  `c5b61549e2379355a4dc4233b4d3e6d7b93abce9` contains 15 original files;
  all 15 are unchanged. Relative to that checkpoint, this unit adds exactly
  eight files: the new consumer pair and the six exact copied dependency inputs
  named above. An initial inventory expectation of eight relative to the older
  assigned base failed; correcting the comparison reference exposed this
  bookkeeping distinction, with **no original source edits** or proof change.
* The producer read the complete final Lean and companion and inspected the
  exact filesystem delta. This is **not** parent inspection or independent
  semantic review. Those gates remain pending with the coordinator.

No remaining producer proof obligation exists for the named zero-centered even
consumer. Its two precursor adoption gates and the new-pair handoff/review gates
remain review/adoption dependencies. No optional arbitrary-center theorem was
attempted. The final revision identifier is supplied by the harness snapshot,
not manually created or described here.

### Verbatim separate all-public audit output

```text
Erdos132.FourInteriorCircle.four_interior_circle : ∀ (n : ℕ) (H I : Finset.{0} Erdos132.TwoInteriorCircle.Plane)
  (R : ℝ),
  LE.le.{0} 10 n →
    Even.{0} n →
      Eq.{1} (Finset.card.{0} H) (HSub.hSub.{0, 0, 0} n 4) →
        LT.lt.{0} 0 R →
          (∀ (h : Erdos132.TwoInteriorCircle.Plane), Membership.mem.{0, 0} H h → Eq.{1} (norm.{0} h) R) →
            Eq.{1} (Finset.card.{0} I) 4 →
              (∀ (z : Erdos132.TwoInteriorCircle.Plane),
                  Membership.mem.{0, 0} I z → Membership.mem.{0, 0} (interior.{0} ((convexHull.{0, 0} ℝ) ↑H)) z) →
                (∀ (z : Erdos132.TwoInteriorCircle.Plane), Membership.mem.{0, 0} I z → Ne.{1} z 0) →
                  Eq.{1} (Finset.card.{0} (Union.union.{0} H I)) n ∧
                    ∃ d,
                      LT.lt.{0} 0 d ∧
                        LT.lt.{0} d (Metric.diam.{0} ↑(Union.union.{0} H I)) ∧
                          (∃ a,
                              Membership.mem.{0, 0} (Union.union.{0} H I) a ∧
                                ∃ b,
                                  Membership.mem.{0, 0} (Union.union.{0} H I) b ∧
                                    Ne.{1} a b ∧ Eq.{1} (dist.{0} a b) d) ∧
                            LE.le.{0} 1 (Erdos132.TwoInteriorCircle.multiplicity.{0} (Union.union.{0} H I) d) ∧
                              LE.le.{0} (Erdos132.TwoInteriorCircle.multiplicity.{0} (Union.union.{0} H I) d) n
'Erdos132.FourInteriorCircle.four_interior_circle' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
Erdos132.FourInteriorCircle.original_geometry_and_conclusion : ∃ n H I R,
  LE.le.{0} 10 n ∧
    Even.{0} n ∧
      Eq.{1} (Finset.card.{0} H) (HSub.hSub.{0, 0, 0} n 4) ∧
        Eq.{1} (Finset.card.{0} I) 4 ∧
          LT.lt.{0} 0 R ∧
            (∀ (h : Erdos132.TwoInteriorCircle.Plane), Membership.mem.{0, 0} H h → Eq.{1} (norm.{0} h) R) ∧
              (∀ (z : Erdos132.TwoInteriorCircle.Plane),
                  Membership.mem.{0, 0} I z → Membership.mem.{0, 0} (interior.{0} ((convexHull.{0, 0} ℝ) ↑H)) z) ∧
                (∀ (z : Erdos132.TwoInteriorCircle.Plane), Membership.mem.{0, 0} I z → Ne.{1} z 0) ∧
                  Eq.{1} (Finset.card.{0} (Union.union.{0} H I)) n ∧
                    ∃ d,
                      LT.lt.{0} 0 d ∧
                        LT.lt.{0} d (Metric.diam.{0} ↑(Union.union.{0} H I)) ∧
                          (∃ a,
                              Membership.mem.{0, 0} (Union.union.{0} H I) a ∧
                                ∃ b,
                                  Membership.mem.{0, 0} (Union.union.{0} H I) b ∧
                                    Ne.{1} a b ∧ Eq.{1} (dist.{0} a b) d) ∧
                            LE.le.{0} 1 (Erdos132.TwoInteriorCircle.multiplicity.{0} (Union.union.{0} H I) d) ∧
                              LE.le.{0} (Erdos132.TwoInteriorCircle.multiplicity.{0} (Union.union.{0} H I) d) n
'Erdos132.FourInteriorCircle.original_geometry_and_conclusion' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```
