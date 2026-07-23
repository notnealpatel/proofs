seq:     A085805
claim:   dihedral-permanent-16m4
status:  open
stmt:    M
proof:   unknown (bounded structure)
module:  Proofs/Xlib/CharDegrees.lean (dihedral
         degrees), DihedralTPP
source:  OEIS A085805 comment (unattributed
         "probably")

CLAIM
  A085805 = k such that the permanent of the
  character table of the dihedral group D_k is
  nonzero. Conjecture in-entry: these are exactly the
  numbers of the form 16m + 4.

LEAN
  Matrix.permanent exists in Mathlib
  (LinearAlgebra.Matrix.Permanent). Missing: the
  dihedral character table as a concrete matrix —
  Mathlib has DihedralGroup and the project has
  dihedral commProb work; the explicit table (four
  1-dim characters + 2-dim cos characters, split by
  parity of k) must be built. That table is
  independently valuable (first explicit character
  table as data in the project; feeds DihedralTPP).

ROUTE
  Permanent of the structured table should reduce to
  a trigonometric/root-of-unity product with a clean
  vanishing criterion — plausibly a finite symbolic
  computation per congruence class of k mod 16.
  Compute first (Sage side) to confirm the 16m+4
  pattern and locate the vanishing mechanism before
  any prover dispatch.

EVIDENCE
  Pattern over computed range in-entry; NOT verified
  in this sweep — treat the exact form (16m+4,
  conventions for D_k) as unpinned until the entry is
  re-read.
