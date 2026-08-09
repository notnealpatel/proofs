seq:     A391599
claim:   erdos-lovasz-3n
status:  FORMALIZED 2026-07-30 (Proofs/Erdos/ErdosLovasz.lean,
         commit a8d9c50); the 3n + O(1) premise below is
         REFUTED, see correction
stmt:    M
proof:   L (known lower bound) / hard (conjecture)
module:  Proofs/Erdos/Erdos20/ neighborhood
source:  OEIS A391599: conjecture attributed
         Erdos-Lovasz 1975 in-entry; recent progress
         noted in-entry (3.05n + o(1), 2026)

CORRECTION (2026-07-30, vacuity-audit-confirmed against the
  paper's tex — binding for future agents)
  This card was internally inconsistent: the source line
  already cites the 2026 "3.05n" progress while the CLAIM
  below still calls a(n) = 3n + O(1) a conjecture. The
  speculation is REFUTED: Sivashankar Thm 1(ii) gives
  g(r) >= ((41 - sqrt 19)/12 - eps) r with
  (41 - sqrt 19)/12 = 3.0534... > 3, so g(r) - 3r -> infinity
  ("addressing a question of Erdos", per the paper). The
  erdosproblems.com "61/20" is a rounding of the paper's
  constant. Also: the g(5) = 13 / g(6) <= 18 results are by
  J. Barat ALONE (J. Combin. Des. 29 (2021) no. 3, 193-209);
  erdosproblems.com's Barat-Wanless pairing is wrong. The
  formalization records the speculation as a Prop and proves
  its incompatibility with Thm 1(ii) sorry-free.

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
