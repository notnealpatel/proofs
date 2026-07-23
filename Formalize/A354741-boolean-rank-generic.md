seq:     A354741
claim:   boolean-full-rank-generic
status:  open
stmt:    M
proof:   M (plausible)
module:  Proofs/BilinearComplexity/ (Boolean rank is
         an F_2-adjacent rank lower-bound tool; no
         cross-track inference)
source:  OEIS A354741 comment (unattributed
         "it appears from some empirical
         computations")

CLAIM
  T(n,k) = number of n x n Boolean matrices with
  Boolean row rank k (Boolean semiring rank; equals
  biclique cover number territory via A355333).
  Conjecture: the fraction of n x n Boolean matrices
  with FULL Boolean rank n tends to 1 as n -> infty.

LEAN
  Needs a Boolean-rank def over the (Bool, or, and)
  semiring — absent from Mathlib; Matrix rank
  machinery is field-based. Novel def with clean
  reusable value (lower bounds for F_2 flattening
  comparisons live nearby: A286331 gives the exact
  GF(2) rank distribution as a Gaussian-binomial
  closed form, a separate S-sized formalizable
  identity).

ROUTE
  The GF(2) analogue (random matrix over F_2 is
  nonsingular with probability -> prod (1 - 2^-i) —
  note: that limit is a CONSTANT ~0.2888, NOT 1, so
  the Boolean claim is genuinely different and the
  mechanism is the rigidity of Boolean row spans).
  First: verify the empirical claim computationally;
  then an inclusion-exclusion / union-bound over
  dominated-row events looks like a bounded M-sized
  probabilistic argument.

EVIDENCE
  Empirical, small n only. Verify before dispatch.
