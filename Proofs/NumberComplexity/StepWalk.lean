/-
  LANE HALTED (2026-07-29) — stub only, no content written.

  Card: Formalize/A014701-rebert-steps.md. Flight-1 lane W4: model the
  walk as inductive reachability over (position, step) states; restate
  the classical count ADDITIVELY — a n + 2 = (Nat.bits n).length +
  popcount n for 1 ≤ n — never Nat subtraction; popcount is file-local;
  ground checks vs `oeis show A014701`.

  The writer prover crashed on an API server error mid-run and produced
  no output; this lane needs a full re-dispatch (unlike the quota-halted
  E4/E8 lanes it has no completed sibling infrastructure to wait on —
  the card is self-contained).
-/
import Mathlib

set_option autoImplicit false
