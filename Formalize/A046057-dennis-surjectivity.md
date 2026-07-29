seq:     A046057
claim:   dennis-gnu-surjectivity
status:  open
stmt:    M
proof:   hard
module:  Proofs/GroupTPP/ layer
source:  OEIS A046057 comment (R. Keith Dennis
         conjecture); companion A053403

CLAIM
  A046057(n) = smallest order m > 0 with exactly n
  isomorphism classes of groups of order m, or 0 if
  none exists. Dennis conjectures there are no 0's:
  every positive integer is gnu(m) for some m.
  Companion (A053403): the set of n NOT of the form
  gnu(m) for m up to the search bound is conjecturally
  finite with largest element 55487.

LEAN
  gnu def as in A000001-cdo-iteration.md. Statement:
    forall n >= 1, exists m, gnu m = n.

ROUTE
  Open; realization arguments use orders m = p*q^k
  families where gnu is computable by classification
  formulas (Holder-type). Formalizing gnu(p*q) =
  explicit formula (classical Holder) is the adjacent
  provable substance and would realize infinitely
  many values in one theorem — a genuine novel
  formalization with real proof content.

EVIDENCE
  508 realized values known below 55487 per A053403.
