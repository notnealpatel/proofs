seq:     A076142
claim:   gap-sum-constant
status:  open
stmt:    M
proof:   hard
module:  none (shares defs with A003313 and A064097
         files)
source:  OEIS A076142 formulas (unattributed
         "it seems")

CLAIM
  a(n) = A064097(n) - A003313(n): the gap between
  the factor-method quasi-log upper bound and the
  true shortest-addition-chain length. Conjecture:
    (sum_{k<=n} a(k)) * log(n) / n^2 -> c
  with 0.006 < c < 0.01 — i.e. the average gap grows
  like c' * n / log n.

LEAN
  Needs BOTH the AdditionChain layer (A003313 file)
  and the quasi-log def (A064097 file); then a
  Tendsto statement over reals. Pure wiring once
  those exist.

ROUTE
  Open (averages of l(n) are hard; even the mean of
  l(n) - log2 n is delicate mathematics). Statement-
  archive; its role is to justify a(n) >= 0
  (quasi-log dominates chain length: PROVABLE — each
  factor-method decomposition yields a chain; good
  sanity theorem linking the two new def layers).

EVIDENCE
  Numeric fit in-entry.
