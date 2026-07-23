seq:     A391599
claim:   erdos-lovasz-3n
status:  open (asymptotics); lower bound formalizable
stmt:    M
proof:   L (known lower bound) / hard (conjecture)
module:  Proofs/Erdos20/ neighborhood
source:  OEIS A391599: conjecture attributed
         Erdos-Lovasz 1975 in-entry; recent progress
         noted in-entry (3.05n + o(1), 2026)

CLAIM
  a(n) = minimum size of an intersecting family of
  n-sets such that every set of size <= n-1 is
  disjoint from at least one member (i.e. a maximal
  intersecting n-uniform family in the covering
  sense — pin exact def from entry name). Known:
  (8/3)n - O(1) <= a(n) (Erdos-Lovasz 1975), improved
  to 3.05n + o(1) lower... (direction per entry).
  Conjecture: a(n) = 3n + O(1).

LEAN
  Mathlib has Set.Intersecting, Set.Sized,
  Finset.erdos_ko_rado; MISSING: covering/transversal
  number tau and the maximality-as-covering def —
  both new, both reusable for the whole intersecting-
  family neighborhood. Asymptotic shape via
  Asymptotics.IsBigO atTop (pattern:
  rothNumberNat_isLittleO_id).

ROUTE
  The 1975 lower-bound argument is real but sizeable
  mathematics (L). The conjecture is open. Value here
  is the tau def + small-n exact values.

EVIDENCE
  Small-n terms in-entry; bounds as cited.
