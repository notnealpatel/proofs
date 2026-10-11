seq:     A332077
claim:   sunflower-conjecture
status:  open mathematics; faithful admission boundary implemented
stmt:    S
proof:   hard-open
module:  Proofs/Erdos/Erdos20/SunflowerConjecture.lean;
         archive Proofs/Sorry/Erdos/Erdos20/SunflowerConjecture.lean
source:  OEIS A332077 formulas and indexing convention; Erdos Problem 20

EXACT SOURCE CONVENTION
  SunOeis(m,n) is the minimal family size forcing at least n sets with
  all pairwise intersections equal, for distinct sets of cardinality
  at most m. Thus m is the size bound and n the petal count. The old
  card swapped them. OEIS uses m,n >= 1 and states
    exists C in N, forall m,n >= 1, SunOeis(m,n) <= (n*C)^m.
  There is ONE absolute C uniform in both parameters. Do not replace it
  by constants depending on the petal count or silently claim those
  quantifier patterns equivalent.

PROVED INFRASTRUCTURE
  The production module defines the minima, proves finiteness, concrete
  values, classical Erdos-Rado estimates, and a normalization bridge.
  Its project Sun uses a stricter nonempty-petal convention, not precisely
  the OEIS predicate. For example Sun(1,1)=2 but SunOeis(1,1)=1.
  The guarded conjectures for Sun and SunOeis are equivalent by
  sunflowerConjecture_iff; the direction back to Sun uses C -> 2*C.
  The original claim that the classical bound was unformalized is stale.
  No claim that this is a novel formalization is made.

SOURCE BOUNDS AND LIMITS
  OEIS records (n-1)^m <= SunOeis(m,n) <= (n-1)^m*m!+1 and the
  Rao O(n log(mn))^m / Bell-Chueluecha-Warnke O(n log m)^m bounds
  for m,n >= 2. These source statements, or the available classical
  estimates, do not establish the absolute-constant conjecture.
  Preserve m>=1 and n>=1; dropping m>=1 makes the project-Sun version
  false, as the production counterexample at m=0,n=2 shows.

IMPLEMENTATION STATUS
  The accepted boundary split moves exactly sunflower_conjecture and
  sunflower_conjecture_oeis to the matching Sorry module; the independent
  convention equivalence remains production. The build, fresh all-owned
  production axiom audit, and separate archive signature audit passed.
  Independent review passed and the boundary was adopted at
  3935f8aa7ad524d66da0c83342120e9ac62f779a. This card remains for
  metadata reconciliation before retirement. Acceptance is statement
  implementation, never mathematical closure.
