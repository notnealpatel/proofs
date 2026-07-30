seq:     A000670
claim:   bala-mod-k-periodicity
status:  k = 2, 4, 16 PROVED; general k stated, intended
         sorry (2026-07-29; commit 51d04f5)
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

ROUTE
  Fixed small k (2, 4, 16, ...): finite verification
  of a closed recurrence mod k, or direct induction on
  the project recurrence; pigeonhole gives *some*
  eventual period, the phi(k) divisibility is the
  content. All k: no route with current machinery;
  literature-adjacent approach is p-adic analysis of
  the EGF 1/(2 - e^x). Project asset possibly usable:
  fubini_polylog (HasSum j^m / 2^j = 2 * fubini m).

EVIDENCE
  OEIS: mod 16 the sequence is eventually
  1,3,13,11,13,11,... apparent period 2 from n = 4.
