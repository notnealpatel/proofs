seq:     A089654
claim:   erdos-all-prime-rows
status:  open
stmt:    S
proof:   hard (same blocker as A039669)
module:  none
source:  OEIS A089654 (P. Erdos conjecture per entry;
         verified to 2^77 in-entry)

CLAIM
  A089654 = table T(n,k) related to the A039669
  family (rows built from n minus powers of 2; pin
  exact T from entry before writing Lean). Erdos
  conjectures T(n,k) are all prime exactly for
  n ∈ {3, 7, 10, 22, 37, 52} and no other n.

LEAN
  Same shape and vocabulary as A039669; write both
  against a shared "all n - 2^k prime"-style
  predicate once T is pinned from the entry.

ROUTE
  Same covering-congruence gap as A039669; treat the
  two files as one campaign if ever attacked.

EVIDENCE
  Verified for n up to 2^77 per entry.
