seq:     A007691
claim:   multiperfect-subset-zumkeller
status:  open
stmt:    S
proof:   hard
module:  none yet (needs IsZumkeller; see INDEX)
source:  OEIS A083207 crossrefs ("conjectured
         subsequences: A007691, A331668, A351548")

CLAIM
  Every multiply-perfect number > 1 is a Zumkeller
  number. Multiply-perfect: n divides sigma(n)
  (A007691). Zumkeller: divisors partition into two
  equal-sum sets.

LEAN
  Defs: IsZumkeller (see A083207 files) and
    IsMultiplyPerfect n := n ∣ sigma 1 n
  (one-liner over ArithmeticFunction.sigma). Statement
  is then a one-line implication with n > 1.

ROUTE
  For sigma(n) = 2n (perfect) this is classical and
  easy (n itself is one side minus adjustments;
  perfect => Zumkeller is a known short argument —
  a good anchor lemma). For abundancy k >= 3 no
  general argument is known; ~6000 multiply-perfect
  numbers are known, all even, checkable individually
  but the general claim needs divisor-partition
  structure theory.

EVIDENCE
  Stated as conjectured subsequence in A083207; no
  counterexample among known multiply-perfect numbers.
