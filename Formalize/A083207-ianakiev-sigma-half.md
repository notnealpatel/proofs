seq:     A083207
claim:   ianakiev-sigma-half-closure
status:  open
stmt:    S
proof:   hard
module:  none yet (needs IsZumkeller; see INDEX)
source:  OEIS A083207 comment, Ivan N. Ianakiev,
         2017-04-03

CLAIM
  A Zumkeller number is an n whose divisors can be
  partitioned into two sets with equal sums (so
  sigma(n) is even and each side sums to sigma(n)/2).
  Conjecture: among any 4 consecutive terms of the
  increasing enumeration of Zumkeller numbers there is
  a k such that sigma(k)/2 is itself Zumkeller.

LEAN
  Needs one new def (absent from Mathlib AND project —
  the project file Proofs/Enumerative/Zumkeller.lean is about a
  different identity):
    IsZumkeller n := exists S ⊆ n.divisors,
      2 * (sum S) = sigma 1 n
  Enumeration via Nat.nth IsZumkeller. sigma exists
  (ArithmeticFunction.sigma).

ROUTE
  None visible; distribution question about Zumkeller
  numbers with Zumkeller half-sigma. Computationally
  extendable (OEIS: verified for first 10^5 terms).

EVIDENCE
  Verified for the first 10^5 Zumkeller numbers
  (Ianakiev).
