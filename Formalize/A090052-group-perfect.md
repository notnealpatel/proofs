seq:     A090052
claim:   group-perfect-uniqueness
status:  open
stmt:    M
proof:   hard
module:  Proofs/GroupCount/GroupPerfect.lean
source:  OEIS A090052 comments (unattributed
         "seems fairly certain")

CLAIM
  A090052 = group-abundant numbers: n with
  gnu(n) > n. Conjectures in-entry: (i) n = 1 is the
  only "group-perfect" number (gnu(n) = n); (ii)
  almost all n are group-deficient (gnu(n) < n),
  i.e. group-abundant numbers have density 0.

LEAN
  gnu def as in A000001-cdo-iteration.md. (i):
    forall n >= 2, gnu n ≠ n.
  (ii) needs natural density (Mathlib has
  Nat.density-flavored tooling in progress; state via
  limit of counting function / n).

ROUTE
  (i) remains open in general (it needs upper bounds on gnu
  away from 2-heavy orders and exact knowledge at them).
  `GroupCount.groupDeficient_of_prime` and
  `GroupCount.groupDeficient_prime_sq` prove every prime and every
  prime square deficient, including the edge case p=2; these settle
  infinite strata but not uniqueness. The stronger squarefree and
  cube-free strata need classification input not yet formalized.
  (ii) remains open; Pyber-type gnu upper bounds are the tool, far
  from current machinery.

EVIDENCE
  No group-perfect n found in GAP range; abundant n
  are sparse (2-group-heavy orders).
