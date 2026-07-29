seq:     A114976
claim:   parity-iff-square (and prime pattern)
status:  open
stmt:    S
proof:   M (plausible involution)
module:  Proofs/Enumerative/A051293/ (same object family)
source:  OEIS A114976 comment, unattributed

CLAIM
  a(n) = number of subsets of {1,...,n} whose
  arithmetic mean is an integer that also divides n.
  Observations-conjectures in-entry:
  (i)  a(n) = 2 iff n is prime (as for tau(n));
  (ii) a(n) is odd iff n is a square (at least for
       initial terms) — suggesting a structural
       relation to A000005 (tau).

LEAN
  Statement from powerset/filter vocabulary:
    subsets S with S.card ∣ S.sum id,
    (S.sum id) / S.card ∣ n.
  No new defs.

ROUTE
  (ii) parity claims about subset counts usually fall
  to an explicit involution on the non-symmetric part
  (e.g. reflection x ↦ n+1-x fixes mean-(n+1)/2
  subsets; count fixed points). Whether the fixed-set
  census gives "odd iff square" is unworked but this
  is a bounded, elementary investigation — good
  conjecturist/prover fodder. (i) similar flavor.

EVIDENCE
  Initial-terms observation only; weakest evidence
  base in this collection. Verify computationally
  before dispatching a prover.
