# Concrete common-support orbit transport for #132

## Delivered unit

New production module: `Proofs/Erdos/Erdos132/CircleRotationTransport.lean` (156 lines).
SHA-256: `643d6121613abf8dcca238a9e55cfce3ae857d75e127148cc571874da885aeff`.
Assigned exact base: `d8dec8365290269804668552894a847e8ae0eb79`.
The harness owns final snapshot/revision creation; no revision was manually created or moved.

Public theorem:
`Erdos132.CircleRotationTransport.exists_stabilizer_map_of_saturated_common_support`.
Its exact contract is:
```lean
(H : Finset TwoInteriorCircle.Plane) (R : ℝ) (u v : TwoInteriorCircle.Plane)
(hH : 6 ≤ H.card) (hR : 0 < R) (hu : u ≠ 0) (hv : v ≠ 0)
(hcircle : ∀ h ∈ H, ‖h‖ = R)
(hsupport : H.image (fun h => dist u h) = H.image (fun h => dist v h))
(hfibers : ∀ d ∈ H.image (fun h => dist u h),
  (H.filter fun h => dist u h = d).card = 2 ∧
  (H.filter fun h => dist v h = d).card = 2) :
∃ g : CircleRotation.Stabilizer H, CircleRotation.rotate g.val u = v
```
The original Plane, actual support and actual fibers, quantifiers, hypotheses, and
full-geometric-stabilizer conclusion survive unchanged. No equal-norm, symmetry,
transporter, hull-preservation, or interior-location certificate was added.

The proof converts support-indexed fibers to the vertex-indexed API using distance
symmetry, invokes `ThreeInteriorRadial.norm_eq_of_saturated_common_support`, then
uses the existing checked `CircleRotation.exists_rotation_map` with positive radius
`‖u‖` (positive by `u ≠ 0`). That dependency already performs the complex quotient
phase construction, so no duplicate helper or new definition was needed.
`rotate_isometry` and `norm_rotate` supply isometry and origin fixation;
`RadialTransport.image_eq_of_common_support` proves actual finite-set image equality;
`CircleRotation.mem_stabilizer_iff_image` upgrades it to the FULL subgroup.

## Joint non-vacuity witness

`Erdos132.CircleRotationTransport.joint_eight_point_fixture` jointly proves:
`H.card = 8`, radius five positivity and circle membership, both nonzero centers,
`u ≠ v`, equality of actual supports, both actual fiber cardinalities equal to two,
and an actual full-stabilizer transporter with coefficient different from one.
The concrete model is precisely `{(±3,±4),(±4,±3)}`, `u = (1,0)`, `v = (0,1)`.
Eight points give nonempty hull and support domains, and in particular `6 ≤ H.card`.
The existing dependency's fixture is private, not an exported declaration. Its
concrete point data and fiber-calculation proof were reused locally, then extended
to the new public support-indexed contract and transporter. The dependency was not
modified to expose that private fixture. This is not an identity fixture.

## Compiler and audit receipts

1. Managed task `transport-build` ran
   `timeout --kill-after=2s 60s lake -q build +Erdos.Erdos132.CircleRotationTransport`
   (task limit 70 seconds). Exit 1: only the new origin-fixing proof failed after
   encoder unfolding prevented the multiplication rewrite from matching. The local
   repair proves origin fixation from `norm_rotate` and `norm_eq_zero`.
2. Managed task `joint-transport-build` ran the same narrow bounded build after that
   repair and inclusion of the joint fixture. Exit 0. No errors or sorry warnings.
   Remaining output consists of inherited dependency linter warnings; no new-module
   warning was reported. No production source edits followed this successful build.
3. Managed task `transport-signature-axioms` ran
   `timeout --kill-after=2s 60s lake env lean -j 1 -M 4000 Proofs/Scratch/CircleRotationTransportAudit.lean`
   (task limit 70 seconds). Exit 0. `#check @...` succeeded for both new public
   declarations and the three consumed equal-norm/rotation/transport APIs. Separate
   `#print axioms` reported exactly `[propext, Classical.choice, Quot.sound]` for
   BOTH new public declarations. The disposable leaf was removed, not imported by
   production. No exploratory checks/prints remain in production.

The bounded work began at consumption `2026-10-11T16:35:52Z`; successful build,
audit, source inspection, and exact dependency-byte comparisons were complete by
`2026-10-11T16:39:26Z`. No research, independent paid review, adoption, outbound
coordination, issue, reminder, References, or global-ledger work was performed.
The supplied relative interface paths were absent as written; the corresponding
files were read inside `swarm-activation-03/132-rotation-infrastructure/` and
`swarm-activation-03/132-three-interior/` instead. No mathematical blocker remains
inside the assigned implication.

## Exact unmodified dependency inventory

The following missing artifacts were included by reading exact finalized source
bytes with `jj --ignore-working-copy file show`. Successful `cmp` checks confirmed
all four included artifacts remain byte-identical to their supplied revisions.

| Artifact under `Proofs/Erdos/Erdos132/` | Exact source revision | SHA-256 |
|---|---|---|
| `CircleRotation.lean` | `5b5a5653e5e473d51abde1b6a723a4985a0ffc40` | `13a31899aa0cfca29c9b4ddf82661714e8660fe0744519cd61d003ebc04de0f7` |
| `ThreeInteriorRadial.lean` | `d215195e16da217caa7ecb6911a35126fd251832` | `cab7c6a514b218811c6f66fbe2b22de88e5725560e78bf68cdfb86dc89777ba3` |
| `ThreeInteriorRadial.md` | `d215195e16da217caa7ecb6911a35126fd251832` | `a5df955a8e3e4f81174f24ae32fcfcc896cc699e8558fee8ded87ea61c8dd1b1` |
| `RadialTransport.lean` | `cf124460934eb09f3f2a90241cd809c8b3ba035c` | `db8652f3b9ccc205be41a2421011091e8263ecb2257866b649178b53d2a500f6` |

`TwoInteriorCircle.lean` was already present and was not edited. Its SHA-256 is
`d36fdcc81b8e99f149e9ca53a8d57106563e46bbf93d70ef70b395db5faaab17`, matching
that file at all three supplied dependency revisions. No finalized workspace was
mutated and no graph management was performed.

## Consumer boundary

The reviewed odd Section 2 consumer may now derive an actual transporter in the
FULL geometric stabilizer from its original common-support/saturated-fiber contract.
No optional `MulAction.orbit` wrapper was added: the delivered certificate is the
actual rotation, not an abstract permutation. Deriving saturation/common support
from the full contrary model, odd counting/order cases, and the full consumer remain
upstream/downstream obligations. Compilation, concrete joint satisfiability, and
this producer's imported standard-axiom audit are established; independent semantic
review and integration/adoption are not claimed.
