seq:     A094870
claim:   hegarty-density
status:  open
stmt:    M
proof:   hard
module:  none
source:  OEIS A094870 comment (P. Hegarty conjecture)

CLAIM
  a(1) = 1; a(n) = minimal positive integer t not yet
  used such that no three of the chosen values form an
  arithmetic progression in order of choice (greedy
  injective no-3AP-in-sequence variant; pin exact
  condition from entry — the constraint involves
  t - a(n-i) vs a(n-i) - a(n-2i)). Known:
  3/8 <= a(n)/n < 3/2. Conjecture (Hegarty):
  a(n)/n -> 1.

LEAN
  Greedy def machinery as in the A003278 family;
  limit statement via Filter.Tendsto
  (a n / n : ℝ) atTop (nhds 1).

ROUTE
  Open; the proved sandwich 3/8 <= a(n)/n < 3/2 is
  the formalizable substance if the family is
  attacked, but it is a real analytic-combinatorial
  argument (L). Low priority relative to A003278 /
  A092482 which share the toolkit and have cheaper
  payoffs.

EVIDENCE
  Numerics consistent with density 1 in-entry.
