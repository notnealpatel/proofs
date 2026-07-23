seq:     A000670
claim:   muljadi-fubini-primes-mod4
status:  open
stmt:    S
proof:   hard
module:  Proofs/Fubini.lean
source:  OEIS A000670 comment, Paul Muljadi, 2011-01-28
         (cf. A290376, prime Fubini numbers)

CLAIM
  Every prime Fubini number greater than 3 is
  congruent to 1 mod 4. Known prime Fubini values:
  3, 13, 541, 47293, ... (indices 2, 3, 5, 7, ...;
  per A290376 no further prime up to index 12000).

LEAN
  Statement is immediate:
    forall n, (fubini n).Prime -> fubini n > 3 ->
      fubini n % 4 = 1
  using project fubini and Nat.Prime.

ROUTE
  Would follow from a full description of fubini mod 4
  (cf. A000670-bala-mod-k with k = 4: eventual period
  divides 2, apparent residues 13,11 alternating from
  n = 4 mod 16 — mod 4 that is 1,3 alternating). If
  the mod-4 periodicity instance is proved, this
  reduces to: prime values occur only at the ≡ 1
  positions or are ruled out at ≡ 3 positions — that
  second step is the open content; parity of position
  does not obviously see primality.

EVIDENCE
  All known prime Fubini numbers > 3 are ≡ 1 mod 4.
