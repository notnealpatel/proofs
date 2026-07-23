seq:     A046098
claim:   completeness-of-13-terms
status:  open (full); large bounded case PROVED in
         project (Erdos175)
stmt:    S
proof:   hard (unbounded); bounded strata done
module:  Proofs/Erdos175/NotSquarefree.lean
         (sorry-free, 5 <= n <= 2^30 for C(2n,n))
source:  OEIS A046098 (T. D. Noe search bound
         2007-04-06); Erdos problem 175 lineage

CLAIM
  A046098 = n such that C(n, floor(n/2)) is
  squarefree; known terms 0-5, 7, 8, 11, 17, 19, 23,
  71; claim: complete (no other n; verified to 10^8
  in-entry). Equivalent core (Erdos 175, proved by
  Granville-Ramare in the literature): C(2n,n) is
  not squarefree for n >= 5.

LEAN
  All vocabulary exists (Nat.centralBinom,
  Squarefree, Kummer/Legendre valuation lemmas:
  sub_one_mul_padicValNat_choose_eq_sub_sum_digits,
  Nat.factorization_choose). Project already proves
  the non-power-of-two case unboundedly and powers of
  two to 2^30 via witness primes + native_decide.

ROUTE
  Remaining gap = the power-of-two case unboundedly,
  which is the Granville-Ramare exponential-sum
  argument (L, analytic). The odd-index A046098
  completeness reduces to the same machinery — extend
  Erdos175 rather than starting fresh.

EVIDENCE
  No further term below 10^8 (OEIS); project
  verification to 2^30 on the even core.
