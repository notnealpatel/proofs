seq:     A000670
claim:   bala-mod-k-periodicity
status:  PROVED IN FULL — general k discharged 2026-07-30
         (commit c37e31e); k = 2, 4, 16 instances 2026-07-29
         (commit 51d04f5); file sorry-free
stmt:    S
proof:   M (fixed k) / hard (all k)
module:  Proofs/Enumerative/FubiniMod.lean (Enumerative.FubiniMod),
         against Proofs/Enumerative/Fubini.lean
source:  OEIS A000670 comment, Peter Bala, 2022-07-08
         (repeated verbatim at A354242, A002050)

FORMALIZED (2026-07-29)
  fubini_odd; fubini_add_two_modEq_four (n ≥ 1);
  fubini_add_two_modEq_sixteen (n ≥ 3) via the closed form
  (fubini n : ZMod 16) = 12 − (−1)^n; card-shape existentials with
  witnesses (N,P) = (0,1), (1,2), (3,2) and P ∣ totient k discharged;
  general-k conjecture = the sole intended sorry. Zero native_decide
  (imported native-backed simp lemmas deliberately dodged); sorry-free
  theorems at exactly {propext, Classical.choice, Quot.sound}.
  Attribution: eventual periodicity mod m is Poonen 1988 / Barsky —
  formalization, NOT a novelty candidate; see PLAN.md §6.

CLAIM
  a(n) = Fubini numbers = number of ordered set
  partitions of an n-set (project def A051293.fubini,
  Proofs/Enumerative/Fubini.lean). For every integer k >= 1 the
  sequence (a(n) mod k) is eventually periodic with
  period dividing phi(k).

LEAN
  All statement vocabulary exists: project fubini,
  Nat.totient, ZMod k or Nat.ModEq. Shape:
    exists N P, P dvd Nat.totient k ∧ P > 0 ∧
      forall n >= N, fubini (n+P) ≡ fubini n [MOD k]

ROUTE (as landed, 2026-07-30, commit c37e31e)
  Elementary, following Poonen (Fibonacci Quarterly
  26(1) 1988, 70-76; References/poonen/paper.txt), NOT
  Barsky's p-adic route: the truncation
  c k n = sum_{j<k} 2^(k-1-j) j^n of the polylog series
  satisfies the same binomial recurrence as fubini, so
  (2^k - 1) * fubini n ≡ c k n (mod k); periodicity of
  the finitely many j^n via Euler's theorem (p ∤ j) and
  nilpotence (p ∣ j) gives period phi(p^h) at prime
  powers; CRT + phi multiplicativity glues to P = phi(k).
  Vacuity audit PASS (postdoc-relayed, 2026-07-30):
  statement byte-identical, content sharp at k = 21
  (minimal period 6; every proper divisor of 12 fails).
  Novelty: LIKELY-KNOWN / first recorded proof of the
  general statement — see .tasks/main/docs/
  novelty-FubiniMod.md; entry labels still say
  "Conjecture" (A000670, A354242, A002050): OEIS
  contribution note candidate.

EVIDENCE
  OEIS: mod 16 the sequence is eventually
  1,3,13,11,13,11,... apparent period 2 from n = 4.
