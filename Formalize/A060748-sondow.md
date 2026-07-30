seq:     A060748
claim:   sondow-finiteness
status:  SHELVED (USER decision 2026-07-30) — do not dispatch
stmt:    L
proof:   hard-open
module:  none
source:  OEIS A060748 comment, Jonathan Sondow,
         2013-10-27

SHELVED — USER DECISION, 2026-07-30 (binding for future agents)
  Formally shelved until Mathlib grows a real Mordell-Weil
  layer (finite generation, heights, descent) — same blocker
  and same ruling as A031507. Do NOT build a conditional
  rank functional (per-statement finite-generation
  hypotheses fail the STYLE.md satisfiability bar; see the
  A031507 card for the full reasoning). The EC rank trio's
  sole survivor is A273929's rank-free point-existence
  reformulation.

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
