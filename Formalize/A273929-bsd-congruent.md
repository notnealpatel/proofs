seq:     A273929 (with A003273, A006991)
claim:   bsd-congruent-number-classes
status:  open (unconditional part); conditional part
         proved in literature under BSD
stmt:    L
proof:   hard-open (contains BSD)
module:  distant: Proofs/ShearEC/ShearAddition.lean
         (same curve family)
source:  OEIS A273929 comments

CLAIM
  A273929 = squarefree numbers ≡ 5, 6, 7 mod 8.
  Statement: every such number is a congruent number
  (area of a rational right triangle; equivalently
  rank(y^2 = x^3 - n^2 x) > 0). Known conditional on
  BSD (Tunnell/Monsky lineage); the unconditional
  statement is open.

LEAN
  L: needs congruent-number def (absent), rank or a
  rational-point existence formulation (the latter
  avoids the rank layer: "exists a nontrivial
  rational point" is statable NOW with Mathlib
  WeierstrassCurve — downgrade to M if stated that
  way), and BSD for the conditional version (no
  L-function API beyond a bare LFunction def).

ROUTE
  Statement-archive. The point-existence reformulation
  is the one statable-now fragment and pairs naturally
  with the ArandaIso file's curve family.

EVIDENCE
  Density/heuristics per Cohen (random matrix theory)
  cited in A003273.
