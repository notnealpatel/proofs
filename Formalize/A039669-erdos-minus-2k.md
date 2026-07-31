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
  No further term below 2^120 (Alekseyev, OEIS comment
  2011-12-08) — this is the citable bound. Published: no
  term <= 2^44 (Mientka-Weitzenkamp 1969); density bound
  (Vaughan 1973, Montgomery's sieve). Cross-ref
  erdosproblems.com #1142 (OPEN).

  BOUND PROVENANCE (audited 2026-07-30). A 2^128 bound
  circulated in our notes and was pinned in INDEX as
  "supersedes 2^120". It does NOT come from the OEIS entry.
  Its only source is a 2026-05-10 forum comment on
  erdosproblems #1142 (Julian Bruns) linking a self-described
  AI-generated CRT-sieve using probabilistic primality
  (GMP mpz_probab_prime_p, 25 rounds); not submitted to OEIS,
  not peer reviewed, not independently reproduced. Do NOT
  cite 2^128. INDEX corrected.

  Full solution set of the RAW predicate for m <= 200000
  (Sage, 2026-07-30): {1, 2, 4, 7, 15, 21, 45, 75, 105}.
  m = 1 and m = 2 satisfy it VACUOUSLY (no k >= 1 has
  2^k < m), which is why the OEIS list starts at 4 (cf.
  R. Israel comment 2015-12-23). Any Lean statement of the
  conjecture lacking a 3 <= m guard is FALSE, not merely
  weak.
