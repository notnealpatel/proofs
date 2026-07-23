seq:     A039669
claim:   erdos-completeness
status:  open
stmt:    S
proof:   hard (covering-congruence machinery absent)
module:  none
source:  OEIS A039669 (Erdos conjecture; search bound
         M. Alekseyev 2011-12-08)

CLAIM
  A039669 = positive m such that m - 2^k is prime for
  every k >= 1 with 2^k < m. Known terms: 4, 7, 15,
  21, 45, 75, 105. Erdos conjectures the list is
  complete.

LEAN
  One-line statement:
    forall m, (forall k >= 1, 2^k < m ->
      (m - 2^k).Prime) -> m ∈ {4,7,15,21,45,75,105}
  (handle small m/edge conventions per entry). All
  vocabulary in Mathlib.

ROUTE
  Membership of each listed term: decide-level.
  Completeness: open; the standard tool (covering
  congruences a la Erdos/Polignac) has ZERO Mathlib
  presence (audited 2026-07-23) — building a covering-
  system library is the reusable L-sized prerequisite,
  itself a novel formalization territory shared with
  Sierpinski/Riesel-number statements.

EVIDENCE
  No further term below 2^120 (Alekseyev).
