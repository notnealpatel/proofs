seq:     A039669
claim:   erdos-completeness
status:  ARCHIVED 2026-07-31 (7520b62); conjecture still open
stmt:    S
proof:   hard (conjecture); window to 10^9 PROVED
module:  Erdos/Covering/ErdosMinus2k.lean
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

  LANDED 2026-07-31 (7520b62). Covering layer built at
  f2cd3df; this lane consumed it. Conjecture archived as
  the single intended sorry (erdos_1142). Window proved
  sorry-free to N = 10^9 — NOT by brute force (kernel
  costs ~60 kB/candidate; naive sweep dies near 10^4 and
  a 225k-step run took 13.9 GB) but by a proved
  covering-congruence reduction: 2 a primitive root mod q
  makes 2^k run over every nonzero residue for
  k = 1..q-1, so all m - 2^k prime forces q | m once
  m > 2^(q-1) + q. At q = 3,5,11,13,19,29 this pins m to
  1181895 mod 2363790 above 2^28+29. Next usable prime is
  37 (2 is NOT a primitive root mod 7, 17, 23, 31).

  ATTRIBUTION — THE REDUCTION IS NOT OURS. It is Chris
  Nash, 15 September 2000, on primepuzzles.net prob_003,
  in the same words and with the same threshold:
  "Suppose n is a solution, Let p be an odd prime...
  2^1, 2^2, 2^3....2^(p-1) all leave a different
  remainder after division by p. Then all solutions - if
  any exist - larger than 2^(p-1)+p must be a multiples
  of p." Nash's version is STRICTLY STRONGER than ours:
  he reaches multiples of 3*5*11*13*19*29*37*53*59*61*67
  = 558873012475635, where we stop at 29. (Our q-set is
  nonetheless the right one for a 10^9 window — q = 37
  needs m > 2^36, already past the ceiling.) Any writeup
  MUST cite Nash and must present the reduction as
  formalized background, never as a contribution. The
  same page credits Uchiyama & Yorinaga for 2^77.

  Audited 2026-07-31 after the orchestrator raised the
  reduction as possibly novel; it is not.

  PRIOR ART — not first to formalize this statement.
  google-deepmind/formal-conjectures has Erdos1142Prop in
  FormalConjectures/ErdosProblems/1142.lean, with the
  conjecture AND the 2^44 Mientka-Weitzenkamp window both
  sorry'd and the seven certificates proved. Our
  predicate matches its guarded shape (2 < m ∧ ...). The
  contribution is the sorry-free window, not the
  statement. Pushing past 2^44 would discharge their
  sorry'd variant: needs q = 37, ~230000 candidates,
  ~60x the current sweep — memory-bound on this box.

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

  Full solution set of the RAW predicate for m <= 200000:
  {0, 1, 2, 4, 7, 15, 21, 45, 75, 105}. THREE vacuous
  solutions — m = 0, 1, 2 each have no k >= 1 with
  2^k < m — which is why the OEIS list starts at 4 (cf.
  R. Israel comment 2015-12-23). Any Lean statement of the
  conjecture lacking a guard is FALSE, not merely weak.
  The landed predicate folds in `2 < m`, matching
  DeepMind's Erdos1142Prop.

  CORRECTION: the orchestrator's 2026-07-30 sweep reported
  {1, 2, 4, ...} and briefed the lane with two vacuous
  solutions. It enumerated from m = 1 and so missed
  m = 0; the writer caught it and disclosed three. Kept
  here because the off-by-one is exactly the kind of
  boundary a statement audit exists to catch.
