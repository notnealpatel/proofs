seq:     A060748
claim:   sondow-finiteness
status:  open
stmt:    L
proof:   hard-open
module:  none
source:  OEIS A060748 comment, Jonathan Sondow,
         2013-10-27

CLAIM
  A060748(n) = smallest m such that the curve
  x^3 + y^3 = m has rank n (-1 if none; curve is
  elliptic, birational to y^2 = x^3 - 432 m^2).
  Sondow: the sequence might be finite even under
  the "rank >= n" redefinition — i.e. ranks in the
  x^3 + y^3 = m family might be bounded.

LEAN
  L: same rank blocker as A031507 (no Mordell-Weil
  in Mathlib). Statement-archive.

ROUTE
  None; tied to unboundedness of elliptic ranks
  (open in general; known rank records for this
  family are BSD/GRH-conditional per entry).

EVIDENCE
  Known terms through small n only.
