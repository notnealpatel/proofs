seq:     A005245
claim:   hamilton-ballinger-finiteness
status:  open
stmt:    M
proof:   hard
module:  none
source:  OEIS A005245 comment, Gordon Hamilton and
         Brad Ballinger, 2022-05-23

CLAIM
  A005245(n) = integer (Mahler-Popken) complexity:
  minimal number of 1's needed to build n from 1 using
  + and *. A348262(n) = same with + and ^ instead.
  Conjecture: A005245(n) < A348262(n) for only
  finitely many n.

LEAN
  Both complexity functions absent from Mathlib;
  define by well-founded recursion:
    c(1) = 1, c(n) = min over (a+b=n, a*b=n
    decompositions) of c(a)+c(b)
  and analogously with ^ replacing *. Finiteness
  statement via Set.Finite.

LEAN NOTE
  Historical context in-entry: Guy's question
  "c(p) = c(p-1) + 1 for primes p" is REFUTED
  (Fuller 2008, least counterexample p = 353942783) —
  do not resurrect it; it is a good sanity target for
  the def only as a bounded computation.

ROUTE
  None known; requires comparative growth theory of
  the two complexity measures.

EVIDENCE
  In-entry empirical comparison over computed ranges.
