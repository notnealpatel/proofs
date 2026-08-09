seq:     A003313
claim:   knuth-stolarsky-lower-bound
status:  open
stmt:    M
proof:   hard
module:  none (addition chains absent from Mathlib,
         audited 2026-07-23)
source:  OEIS A003313 comment recorded by Achim
         Flammenkamp, 2016-10-26; conjecture due to
         D. E. Knuth, K. Stolarsky et al.

CLAIM
  l(n) = length of a shortest addition chain for n
  (chain 1 = a_0, a_1, ..., a_r = n, each a_i a sum
  of two earlier — not necessarily distinct — terms;
  l(n) = minimal r). v(n) = binary weight of n
  (A000120). Conjecture:
    floor(log2 n) + ceil(log2 v(n)) <= l(n).

LEAN
  Defs needed (all new, none in Mathlib):
    AdditionChain : List ℕ → Prop  (or a structure)
    Nat.addChainLength n := sInf { r | ... }
  Vocabulary that exists: Nat.log 2, Nat.clog 2,
  Nat.bits / (Nat.digits 2 n).count 1 for v(n).
  The AdditionChain layer is the reusable asset —
  it unlocks this file, A230528, A014701, A064097
  comparisons, and Scholz-Brauer territory. Build it
  once, in one file, then state everything against it.

ROUTE
  Known partial results: l(n) >= log2 n + log2 v(n) -
  2.13 (Schonhage) — a Lean proof of the weaker
  classical bound l(n) >= ceil(log2 n) is the natural
  first theorem for the new def (each step at most
  doubles). The full conjecture is open mathematics.

EVIDENCE
  Verified by exhaustive computation for very large
  ranges (Flammenkamp/Clift chain tables).
