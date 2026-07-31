seq:     A089654
claim:   erdos-all-prime-rows
status:  ARCHIVED 2026-07-31 (7520b62); conjecture still open
stmt:    S
proof:   bridged to A039669 (no sorry of its own)
module:  Erdos/Covering/ErdosRows.lean
source:  OEIS A089654 (P. Erdos conjecture per entry;
         verified to 2^77 in-entry)

CLAIM
  A089654 = table T(n,k) with T(n,k) = 2*n+1-2^k for
  k >= 1, rows truncated where T(n,k) > 0 (formula is
  in-entry; PINNED 2026-07-30 against all nine listed
  rows plus the entry's own n=10 example 19,17,13,5).
  Erdos conjectures T(n,k) are all prime exactly for
  n in {3, 7, 10, 22, 37, 52} and no other n.

LEAN
  Landed against the shared predicate owned by
  Erdos/Covering/ErdosMinus2k.lean.

ROUTE
  RESOLVED 2026-07-31. The card's old guess — "same
  covering-congruence gap as A039669, treat the two files
  as one campaign" — was right that they are one
  campaign, but wrong that this file needed the covering
  machinery. A089654's conjecture is EXACTLY A039669
  restricted to odd m, reindexed by m = 2n+1:
  n in {3,7,10,22,37,52} maps onto {7,15,21,45,75,105},
  the odd terms of A039669 (4 is the only even one).
  So erdos_a089654 follows through the bridge and
  introduces NO new sorry; it is sorryAx-dependent
  through erdos_1142 only.

  forall_prime_erdosRow_iff is the content: it makes
  "A089654's conjecture is A039669's odd part"
  machine-checked rather than a remark. Proved in both an
  unguarded form (all n) and a guarded one.

  DEGENERACY. The bridge needs 0 < n: row 0 is empty,
  hence vacuously all-prime, while 2*0+1 = 1 is not a
  term. This is the A089654-side shadow of the A039669
  vacuity trap (m = 0, 1, 2 all vacuous there).

EVIDENCE
  Verified for n up to 2^77 per entry. Note this is
  weaker than A039669's 2^120 (Alekseyev) and the two
  bounds are not in conflict — the A089654 comment is
  older.

NOVELTY
  FIRST FORMALIZATION in any proof assistant. Swept
  2026-07-30 against google-deepmind/formal-conjectures
  (which has A039669 as 1142.lean but nothing for
  A089654), plby/lean-proofs, Mathlib, Isabelle AFP,
  Coq/Rocq, Mizar, HOL Light, Metamath. Details in
  .tasks/main/docs/novelty-ErdosCovering.md.
