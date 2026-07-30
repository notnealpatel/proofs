seq:     A114976
claim:   parity-iff-square (and prime pattern)
status:  PROVED (2026-07-29, sorry-free; commit 6677024)
stmt:    S
proof:   M (plausible involution)
module:  Proofs/Enumerative/MeanDivisors.lean (Enumerative.MeanDivisors)
source:  OEIS A114976 comment, unattributed

FORMALIZED (2026-07-29)
  Both observations proved, plus the sharper congruence:
    a_eq_two_iff_prime      : a n = 2 ↔ n.Prime
    odd_a_iff_isSquare      : n ≠ 0 → (Odd (a n) ↔ IsSquare n)
    a_modEq_card_divisors   : a n ≡ τ(n) [MOD 2]
  Proof mechanism: the card's reflection involution x ↦ n+1-x is
  provably WRONG (does not preserve the counted family); the working
  involution is the mean-toggle (toggle membership of the element m in
  a mean-m subset). Axioms exactly {propext, Classical.choice,
  Quot.sound}; kernel decide only. Literature sweep 2026-07-29 found NO
  prior proof of (ii) or the τ congruence — first-recorded-proof
  status; see PLAN.md §6. OEIS contribution candidate.

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
