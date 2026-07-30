seq:     A046057
claim:   dennis-gnu-surjectivity
status:  open
stmt:    M
proof:   hard
module:  Proofs/GroupCount/DennisSurjectivity.lean
         (CARD CORRECTION 2026-07-30: original said
         Proofs/GroupTPP/ — the gnu layer landed in
         GroupCount, not GroupTPP)
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
  (CARD CORRECTION 2026-07-30, audit-verified against
  the live entry: this line INVERTS A053403 — that
  sequence lists the values NOT yet accounted for as
  gnu(m); it has 508 known terms, the largest 55487,
  and is conjecturally finite. Writer + vacuity audit
  concur; see .tasks/main/docs/
  review-vacuity-DennisSurjectivity.md.)
