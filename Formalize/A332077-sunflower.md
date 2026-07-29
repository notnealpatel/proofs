seq:     A332077
claim:   sunflower-conjecture
status:  open (major)
stmt:    S
proof:   hard-open
module:  Proofs/Erdos/Erdos20/ (Sunflower.lean,
         ShiftedSunflower.lean, Spread.lean)
source:  OEIS A332077 formulas (Erdos-Rado sunflower
         conjecture, standard form)

CLAIM
  Sun(m,n) = minimal N such that every family of N
  distinct sets each of cardinality <= n contains a
  sunflower with m petals (m sets with pairwise-
  identical intersection = the common core).
  Conjecture: Sun(m,n) <= (C_m * n)^... standard form:
  for each m there is C with Sun(m,n) <= C^n
  (equivalently (O(1))^n for fixed m; entry states
  Sun(m,n) <= (n * O(1))^m form — normalize against
  the entry when writing the Lean statement).

LEAN
  Project-only vocabulary — Mathlib has NO sunflower
  def (audited 2026-07-23). Use Erdos20:
  IsSunflowerWith, HasSunflower, sunflowerNumber.
  Statement: exists C, forall n, sunflowerNumber m n
  <= (C * n)^m (indexing per project def).

ROUTE
  Open mathematics (best known: (n log m)^m family of
  bounds, Alweiss-Lovett-Wu-Zhang line). Formalizing
  the CLASSICAL Erdos-Rado bound n!*(m-1)^n against
  the project defs is the provable substance adjacent
  to this statement and is unformalized anywhere —
  strong novel-formalization target independent of
  the conjecture.

EVIDENCE
  n/a (asymptotic).
