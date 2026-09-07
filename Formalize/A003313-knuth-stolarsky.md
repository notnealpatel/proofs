seq:     A003313
claim:   knuth-stolarsky-lower-bound
status:  open
stmt:    M
proof:   hard
module:  Proofs/NumberComplexity/KnuthStolarsky.lean
source:  OEIS A003313 comment recorded by Achim
         Flammenkamp, 2016-10-26; conjecture due to
         D. E. Knuth, K. Stolarsky et al.

CLAIM
  l(n) = length of a shortest addition chain for n
  (chain 1 = a_0, a_1, ..., a_r = n, each a_i a sum
  of two earlier — not necessarily distinct — terms;
  l(n) = minimal r). v(n) = binary weight of n
  (A000120). Conjecture:
    floor(log2 n) + ceil(log2 v(n)) <= l(n).

LEAN
  `Proofs/NumberComplexity/AdditionChain.lean` now provides
  `NumberComplexity.IsAddChain`, the subtype `NumberComplexity.AdditionChain n`,
  and the shortest-length function `NumberComplexity.l`. Its `l` is the
  minimum `chainSteps` over `AdditionChain n`; `l_eq_lAsc` reconciles the
  permissive predicate with ascending chains. The target can therefore be
  stated directly against this API; no `Nat.addChainLength` exists.

ROUTE
  `NumberComplexity.knuth_stolarsky_of_binaryWeight_le_two` and
  `NumberComplexity.knuth_stolarsky_of_le_sixteen` are proved in
  `Proofs/NumberComplexity/KnuthStolarsky.lean` itself from the
  `AdditionChain` API; the binary-weight proof uses the small-step lower
  bound and does not depend on exact two-bit lengths.
  `Proofs/NumberComplexity/TwoBitAdditionChain.lean` imports
  `KnuthStolarsky` in the other direction and separately proves
  `NumberComplexity.l_two_pow_add_two_pow`, the exact length for a sum of
  two distinct powers of two. That exact helper feeds the Slizkov result,
  but is not a dependency of either Knuth–Stolarsky partial theorem.
  The full conjecture for arbitrary binary weight remains open.

EVIDENCE
  Verified by exhaustive computation for very large
  ranges (Flammenkamp/Clift chain tables).
