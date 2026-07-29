seq:     A000670
claim:   bala-mod-k-periodicity
status:  open
stmt:    S
proof:   M (fixed k) / hard (all k)
module:  Proofs/Enumerative/Fubini.lean
source:  OEIS A000670 comment, Peter Bala, 2022-07-08
         (repeated verbatim at A354242, A002050)

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
