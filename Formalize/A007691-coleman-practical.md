seq:     A007691
claim:   coleman-multiperfect-practical
status:  def layer BUILT, conjecture ARCHIVED as the
         module's single intended sorry (2026-07-30,
         commit 6b4d720); conjecture itself open
stmt:    S-M
proof:   hard (odd part OPN-hard, see LEAN note)
module:  Proofs/Enumerative/Practical.lean
         (Enumerative.Practical)
source:  OEIS A007691 comment, Jaycob Coleman,
         2013-10-15

CLAIM
  Every multiply-perfect number (n ∣ sigma(n)) is a
  practical number: every m <= sigma(n) — classically
  every m <= n suffices — is a sum of distinct
  divisors of n.

LEAN (landed 2026-07-30, commit 6b4d720)
  Nat.Practical n := 0 < n ∧ forall m <= n, exists
  S ∈ n.divisors.powerset, sum S = m — the card's
  original guard-free def was rejected by the writer:
  0 would be vacuously practical (divisors 0 = ∅ only
  reaches m = 0, but m ≤ 0 forces m = 0). Landed
  sorry-free: decidability + A005153 prefix checks,
  Practical.two_dvd, Srinivasan 2n ≤ 1 + σ(n),
  interval-extension engine, strong-σ iff, and the
  Stewart step Practical.mul_prime_pow (unordered —
  strictly stronger than the ascending-order step);
  Nat.IsMultiperfect + A007691 checks; Coleman
  archived as the single intended sorry; first ten
  A007691 terms certified sorry-free. Vacuity audit
  SOUND (2026-07-30). Novelty: first practical-number
  formalization in ANY proof assistant; all proved
  math classical — .tasks/main/docs/novelty-Practical.md.
  HARDNESS (unrecorded observation, 2026-07-30):
  Coleman + two_dvd ⟹ no odd multiperfect > 1, in
  particular no odd perfect number — the odd part of
  the conjecture is OPN-hard; the attackable fragment
  is "every even multiperfect is practical". A
  sorry-free conditional micro-theorem for this is a
  proposed follow-on.

ROUTE
  Stewart's criterion (p_{i+1} <= sigma(prod so far)+1
  characterization of practical numbers) is the known
  tool; proving Stewart in Lean is a self-contained
  campaign that would make this conjecture verifiable
  per-instance and possibly provable for abundancy 2.

EVIDENCE
  Verified by Coleman for the first 5261 terms with
  abundancy > 2 (Flammenkamp data).
