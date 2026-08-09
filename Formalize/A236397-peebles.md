seq:     A236397
claim:   peebles-sunflower-capset
status:  FORMALIZED 2026-07-30 (commit 01060f0): poster
         Theorem 4 (A236397(n) <= A090245(n)) PROVED
         sorry-free; weight functional + sliceRank bridge
         chain sorry-free; Peebles conjecture + CLP
         slice-rank bound ARCHIVED (2 intended sorries).
         Convention pinned from the Peebles 2013 HMC poster
         (References/Peebles2013/ — the OEIS entry never
         defines it). Novelty: Thm 4 is LIKELY-KNOWN /
         first-recorded-COMPLETE-proof candidate (poster
         bare statement, thesis PDF dead, NOT subsumed by
         ASU/Naslund-Sawin asymptotic capacity result) —
         .tasks/main/docs/novelty-CapsetSliceRank.md.
         Formalization claims are route-scoped only:
         Dahmen-Holzl-Lewis ITP 2019 has EG in Lean 3.
         Conjecture itself still open; term-extension
         refutable.
stmt:    M
proof:   hard; term-extension refutable
module:  Proofs/BilinearComplexity/CapsetSliceRank.lean
         (BilinearComplexity.CapsetSliceRank), bridging
         Capset.lean, SliceRank.lean, Erdos/Erdos20/
source:  OEIS A236397 comment ("Peebles conjectures",
         undated)

CLAIM
  A236397(n) = weight of the largest-weight
  sunflower-free set of width n (weight/width per
  entry's set-system convention; pin exact def from
  the entry before writing Lean). A090245(n) = maximum
  size of a capset in (Z/3Z)^n (no three distinct
  vectors summing to 0 / no line). Conjecture: for n
  even, A236397(n+1) = 2 * A090245(n).

LEAN
  Needs two new defs, both valuable independently:
  (a) capset in (ZMod 3)^n — absent from Mathlib
  (ThreeAPFree exists but not the vector-space line-
  free formulation); (b) the sunflower-free weight
  functional. The capset def is the anchor for any
  future Croot-Lev-Pach / Ellenberg-Gijswijt
  formalization against the project's own sliceRank —
  the highest-leverage bridge in this whole harvest.

ROUTE
  Conjecture itself: open; only 7-8 terms of either
  sequence known, so one new term of either sequence
  tests it. Formalization value is in the defs and the
  known small-n values (native_decide territory).

EVIDENCE
  Matches on all known terms (A236397: 1,2,4,8,20,40,
  96,224; A090245: 1,2,4,9,20,45,112).
