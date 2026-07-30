seq:     A014701
claim:   rebert-step-doubling
status:  PROVED 2026-07-30 in full (NumberComplexity/
         StepWalk.lean, commit fa83e94; novelty sweep
         NO-REFERENCE-FOUND — first recorded proof)
stmt:    S
proof:   M
module:  none (small self-contained defs)
source:  OEIS A014701 conjecture, Jean-Marc Rebert,
         2025-05-15

CLAIM
  a(n) = number of multiplications to compute x^n by
  the Chandah-sutra (binary / square-and-multiply)
  method; classically a(n) = floor(log2 n) +
  (binary weight of n) - 1. Conjecture: a(n+1) equals
  the minimal number of steps to walk from 0 to n
  where, after the first step, before each step you
  may either keep the current step length or double
  it (first step has length 1).

LEAN
  Binary-method count: define from Nat.bits
  ((Nat.bits n).length - 1 + count true - 1) — Mathlib
  has bits/size/log; a popcount def is a one-liner
  (absent upstream). The walk: an inductive minimal-
  steps def over (position, step-length) states.

ROUTE
  Elementary two-sided induction: binary expansion of
  n gives a walk (doublings = shifts, keeps = adds);
  optimality by a greedy/exchange argument on walks —
  every walk's reachable set after k steps is
  contained in an explicit interval-with-congruence
  family. Bounded, self-contained; good first-proof
  target for a prover session. Medium confidence it
  falls cleanly.

EVIDENCE
  In-entry verification over computed range.
