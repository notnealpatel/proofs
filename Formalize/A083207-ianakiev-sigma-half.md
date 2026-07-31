seq:     A083207
claim:   ianakiev-sigma-half-closure
status:  conjecture STATED (IanakievSigmaHalf), still
         open; lane file re-purposed and BUILT
         2026-07-31 (working tree, uncommitted)
stmt:    S
proof:   hard
module:  Proofs/Enumerative/ZumkellerSigmaHalf.lean
         (Enumerative.ZumkellerSigmaHalf)
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

LEAN (landed 2026-07-31, working tree)
  The card's def already existed in-tree
  (Enumerative.IsZumkeller) and is reused, not
  restated. Landed sorry-free, axioms clean:
    IanakievSigmaHalf — the conjecture as a Prop def
      over Nat.nth IsZumkeller, NOT proved and NOT
      assumed anywhere; sigma(k)/2 spelled
      multiplicatively so no Nat division appears;
    infinite_setOf_isZumkeller — A083207 infinite (via
      6 * 5^k and IsZumkeller.mul_of_coprime), which is
      what makes Nat.nth IsZumkeller a faithful
      enumeration rather than junk past a last term;
    nth_isZumkeller_zero / _one — enumeration pinned to
      the OEIS prefix 6, 12.
  The file also carries the settled sigma-half content
  the lane can actually prove: the PUBLISHED
  Bhaskara Rao-Peng characterization (practical n is
  Zumkeller iff sigma(n) even; arXiv:0912.0052 prop
  `proppraczu`, J. Number Theory 133 (2013) 1135-1155)
  as Nat.Practical.isZumkeller and
  Practical.isZumkeller_iff_two_dvd_sum_divisors, with
  sharpness at 18 and 70; plus the upstream
  formal-conjectures definitional delta
  (upstreamIsPractical / practical_iff_upstream).
  CONSOLIDATION, no priority claimed.

EVIDENCE
  Verified for the first 10^5 Zumkeller numbers
  (Ianakiev).
