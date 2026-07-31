seq:     A007691
claim:   multiperfect-subset-zumkeller
status:  abundancy-2 slice PROVED unconditionally;
         nine A007691 terms certified; full claim still
         open, Coleman-conditional recorded. Lane file
         BUILT 2026-07-31 (working tree, uncommitted)
stmt:    S
proof:   hard
module:  Proofs/Enumerative/MultiperfectZumkeller.lean
         (Enumerative.MultiperfectZumkeller)
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

LEAN (landed 2026-07-31, working tree)
  Card's planned file-local defs dropped: Nat.IsMultiperfect
  (with its 0 < n guard and A007691 checks) is already in
  Enumerative.Practical and IsZumkeller in
  Enumerative.IsZumkeller; both imported, nothing restated.
  Landed sorry-free, axioms clean:
    Nat.Perfect.isZumkeller — the card's requested anchor
      lemma, UNCONDITIONAL and with no practicality or
      evenness hypothesis (so it also covers a hypothetical
      odd perfect number). Route is the direct split
      {n} vs n.properDivisors, not the card's "n minus
      adjustments". This is the A083207 xref
      "Subsequences: A000396" — recorded, not conjectured.
    IsMultiperfect.two_dvd_sum_divisors,
    IsMultiperfect.isZumkeller_of_practical — realization
      engine over the published Bhaskara Rao-Peng bridge
      (Enumerative.ZumkellerSigmaHalf).
    zumkeller_instance_{6,28,120,496,672,8128,30240,32760,
      523776} — NINE of the ten Coleman realization terms
      convert; 1 does not (sigma(1) odd, 1 not Zumkeller),
      which is exactly the A083207 xref hedge "(after their
      initial 1's)".
    isZumkeller_of_isMultiperfect_of_coleman — the
      conjecture-ordering remark as a conditional, H
      explicit, ZTS genre. Coleman => this card's claim;
      no converse claimed. Note the route is overkill on
      abundancy 2: that slice is unconditional here, while
      Coleman on the same slice already implies no odd
      perfect number exists. Open content is abundancy >= 3.
  CONSOLIDATION, no priority claimed.
