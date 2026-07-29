seq:     A061256
claim:   adams-watters-commuting-pairs
status:  open; provable with effort — resolves an
         open OEIS annotation
stmt:    M
proof:   M-L
module:  Proofs/GroupTPP/HigherCommProb.lean,
         GroupAlgebraCenter.lean
source:  OEIS A061256 comment ("it appears", Franklin
         T. Adams-Watters lineage; the commuting-
         TRIPLES statement was proved by Britnell
         2012 per entry)

CLAIM
  A061256 = Euler transform of sigma(n). Open part:
  a(n) equals the number of conjugacy classes of
  commuting ordered pairs in S_n, i.e. orbits of
  {(g,h) : gh = hg} under simultaneous conjugation.

LEAN
  Define the conjugation action of S_n on pairs
  (one line); Burnside IS in Mathlib:
  MulAction.sum_card_fixedBy_eq_card_orbits_mul_
  card_group (GroupTheory.GroupAction.Quotient).
  Euler transform side: define via the sigma product
  formula (ArithmeticFunction.sigma exists) or as the
  coefficient identity — pick the cleanest.

ROUTE
  Burnside: #orbits = (1/n!) sum_g #{commuting pairs
  fixed by g}. Fixed pairs under conjugation by g =
  commuting pairs in C(g) x C(g) intersected
  suitably; centralizers in S_n are wreath-type
  products with known structure; cycle-index
  bookkeeping should land on the Euler transform of
  sigma. Real but bounded combinatorics; medium
  confidence. Would settle the OEIS "it appears"
  outright — the cleanest possible instance of the
  project's novel-formalization-to-novel-proof bet.

EVIDENCE
  Terms match as far as computed in-entry; triples
  analogue is a proved theorem (Britnell), a strong
  plausibility signal.
