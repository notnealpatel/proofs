seq:     A007691
claim:   coleman-multiperfect-practical
status:  open
stmt:    S-M
proof:   hard
module:  none yet (needs Nat.Practical)
source:  OEIS A007691 comment, Jaycob Coleman,
         2013-10-15

CLAIM
  Every multiply-perfect number (n ∣ sigma(n)) is a
  practical number: every m <= sigma(n) — classically
  every m <= n suffices — is a sum of distinct
  divisors of n.

LEAN
  Nat.Practical is ABSENT from Mathlib (audited
  2026-07-23): define
    Nat.Practical n := forall m <= n, exists S ⊆
      n.divisors, sum S = m
  IsMultiplyPerfect as in the companion file. The
  practical-number def is independently valuable
  (novel in Lean; Stewart's structure theorem is the
  adjacent provable substance).

ROUTE
  Stewart's criterion (p_{i+1} <= sigma(prod so far)+1
  characterization of practical numbers) is the known
  tool; proving Stewart in Lean is a self-contained
  campaign that would make this conjecture verifiable
  per-instance and possibly provable for abundancy 2.

EVIDENCE
  Verified by Coleman for the first 5261 terms with
  abundancy > 2 (Flammenkamp data).
