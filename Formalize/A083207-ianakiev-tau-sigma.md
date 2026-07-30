seq:     A083207
claim:   ianakiev-tau-sigma
status:  OPEN but REDUCED 2026-07-30 (Enumerative/
         ZumkellerTauSigma.lean, commits 8eef184 + 55b6259):
         machine-checked — the conjecture implies an open
         odd-perfect constraint; BOTH ROUTEs below are
         computationally REFUTED (d = 496 kills 6|k; 234 has
         no Zumkeller unitary divisor); do NOT re-dispatch
         without new mathematics; novelty sweep
         NO-REFERENCE-FOUND on the reduction
stmt:    S
proof:   unknown (not obviously hard)
module:  none yet (needs IsZumkeller; see INDEX)
source:  OEIS A083207 comment, Ivan N. Ianakiev,
         2020-04-24 (cf. A331668)

CLAIM
  If d > 1, d divides k, and tau(d) * sigma(d) = k,
  then k is a Zumkeller number (divisors partition
  into two equal-sum sets).

LEAN
  IsZumkeller def as in A083207-ianakiev-sigma-half.
  tau = ArithmeticFunction.sigma 0, sigma =
  ArithmeticFunction.sigma 1. Statement:
    forall d k, 1 < d -> d ∣ k ->
      (sigma 0 d) * (sigma 1 d) = k -> IsZumkeller k

ROUTE
  The hypothesis forces heavy structure on k
  (k = tau(d) sigma(d) with d ∣ k). Plausible attack:
  show k is always divisible by 6 with 9 ∤ k, or
  factor k as (Zumkeller) * (coprime) — the closure
  lemma "Zumkeller times coprime is Zumkeller" is the
  reusable engine (also needed for the Neder gap-12
  theorem, which is proved in the literature and is
  the natural anchor theorem for the IsZumkeller
  file).

EVIDENCE
  OEIS cross-reference A331668; finite verification
  implied in-entry, bound not stated.
