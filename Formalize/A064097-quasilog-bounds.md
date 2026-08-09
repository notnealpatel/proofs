seq:     A064097
claim:   cloitre-wilson-quasilog-bounds
status:  lower bound PROVED; 2.5·log upper stated,
         intended sorry (2026-07-29; commit 67b13d1)
stmt:    S
proof:   S (lower) / delicate-open (upper)
module:  Proofs/NumberComplexity/Quasilog.lean (NumberComplexity.Quasilog)
source:  OEIS A064097 formulas: Benoit Cloitre
         2002-10-30 (log n < a(n) < 2.5 log n, n > 1);
         Robert G. Wilson v 2013-08-10
         (floor(log2 n) <= a(n))

FORMALIZED (2026-07-29)
  quasilog by WF recursion on least-prime-factor splitting; OEIS
  defining clauses recovered as theorems incl. complete additivity
  quasilog_mul. Wilson's log_two_le_quasilog PROVED via the sharper
  le_two_pow_quasilog (n ≤ 2^a(n)). Cloitre's 2.5·Real.log upper bound
  stated (≤ form, strict-< deviation disclosed in docstring), intended
  sorry — HOLD tier, naive induction provably fails at c = 2.5.
  27 ground checks vs the live entry. Consumer trap documented:
  norm_num [quasilog] loops; use quasilog_of_prime /
  quasilog_of_not_prime.

CLAIM
  a : ℕ → ℕ is the completely additive function with
  a(1) = 0, a(p) = 1 + a(p-1) for p prime,
  a(mn) = a(m) + a(n). Claims: (i) floor(log2 n) <=
  a(n); (ii) a(n) < 2.5 * ln n for n > 1.

LEAN
  Def by strong recursion (p-1 < p) + extension over
  Nat.factorization via Finsupp.sum; Mathlib has the
  factorization machinery; no IsCompletelyAdditive
  predicate exists (define locally).

ROUTE (i) — provable now, high confidence:
  strong induction. Prime p: a(p) = 1 + a(p-1) >=
  1 + log2(p-1) >= log2 p for p >= 2. Composite mn:
  additivity + log2 superadditivity (Nat.log lemmas).
ROUTE (ii) — delicate, do NOT assume easy:
  naive induction needs 2 <= c * ln 2 at prime steps,
  which FAILS at c = 2.5 (2.5 ln 2 ≈ 1.73 < 2). Any
  proof must exploit that p-1 is even (two cheap
  factor-2 steps cannot repeat immediately) or track
  worst-case prime chains. Treat as open.

EVIDENCE
  Both bounds verified computationally far out
  in-entry; (ii) unproven anywhere as far as this
  sweep found.
