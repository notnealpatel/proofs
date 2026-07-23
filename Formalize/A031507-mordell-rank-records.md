seq:     A031507 (with A031508, A373795)
claim:   gpz-rank-record-growth
status:  open
stmt:    L
proof:   hard-open
module:  none
source:  OEIS A031507 comments; Gebel-Petho-Zimmer
         observation quoted by Charles R Greathouse
         IV, 2013-09-10; Elkies ANTS-XVI 2024 bound
         noted in-entry

CLAIM
  A031507(n) = smallest k > 0 such that the Mordell
  curve y^2 = x^3 + k has rank n (-1 if none).
  Only 7 terms known (1, 2, 15, 113, 2089, 66265,
  1358556). Implied growth conjecture (from GPZ
  experimental law r = O(log|k| / (log log|k|)^(2/3))):
  a(n) grows like exp(c * n (log n)^(2/3))-type —
  superpolynomial records.

LEAN
  L: requires Mordell-Weil rank (absent from Mathlib
  entirely — no finite generation, no descent, no
  Nagell-Lutz; audited 2026-07-23). Statement-archive
  until a rank layer exists.

ROUTE
  None. If a rank surrogate is ever built (points
  tensor Q), the statement becomes M but the
  mathematics stays open.

EVIDENCE
  7 known terms; rank >= 17 curves exist (Elkies);
  a(16) upper bound ~1.16 * 10^30 in-entry.
