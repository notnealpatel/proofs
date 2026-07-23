seq:     A062733
claim:   zabolotskii-closed-form
status:  open
stmt:    M
proof:   L
module:  Proofs/Xlib/CharDegrees.lean,
         Wedderburn.lean (machinery)
source:  OEIS A062733 comment, Andrei Zabolotskii,
         2025-05-27

CLAIM
  a(n) = maximal degree of an irreducible (complex)
  representation of SL(n,2) = GL(n,2). Conjecture:
  for n > 3 the values coincide with |column k=2 of
  A135950|, which would give the closed form
    a(n) = 2^((n-2)(n-3)/2) * (2^n - 1) *
           (2^(n-1) - 1) / 3.

LEAN
  Statement needs SL(n,2) irrep degrees: Mathlib has
  FDRep and Matrix.SpecialLinearGroup; max degree def
  is the same functional as A060938 restricted to one
  group family (share the def). M.

ROUTE
  Real representation theory of GL(n,2) (Steinberg-
  weight territory); L. The value is the STATEMENT
  plus small-n instances (n = 3: a = 8, Steinberg of
  GL(3,2) — provable with concrete character-table
  work and would be a first-in-Lean concrete character
  table for a simple group of Lie type; strong
  novelty, bounded scope).

EVIDENCE
  Coincidence with A135950 column checked for
  available terms in-entry.
