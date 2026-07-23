seq:     A236397
claim:   peebles-sunflower-capset
status:  open
stmt:    M
proof:   hard; term-extension refutable
module:  Proofs/Erdos20/, Proofs/BilinearComplexity/
         SliceRank.lean (bridge target)
source:  OEIS A236397 comment ("Peebles conjectures",
         undated)

CLAIM
  A236397(n) = weight of the largest-weight
  sunflower-free set of width n (weight/width per
  entry's set-system convention; pin exact def from
  the entry before writing Lean). A090245(n) = maximum
  size of a capset in (Z/3Z)^n (no three distinct
  vectors summing to 0 / no line). Conjecture: for n
  even, A236397(n+1) = 2 * A090245(n).

LEAN
  Needs two new defs, both valuable independently:
  (a) capset in (ZMod 3)^n — absent from Mathlib
  (ThreeAPFree exists but not the vector-space line-
  free formulation); (b) the sunflower-free weight
  functional. The capset def is the anchor for any
  future Croot-Lev-Pach / Ellenberg-Gijswijt
  formalization against the project's own sliceRank —
  the highest-leverage bridge in this whole harvest.

ROUTE
  Conjecture itself: open; only 7-8 terms of either
  sequence known, so one new term of either sequence
  tests it. Formalization value is in the defs and the
  known small-n values (native_decide territory).

EVIDENCE
  Matches on all known terms (A236397: 1,2,4,8,20,40,
  96,224; A090245: 1,2,4,9,20,45,112).
