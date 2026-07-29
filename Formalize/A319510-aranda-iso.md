seq:     A319510
claim:   aranda-rank-4n
status:  iso core PROVED sorry-free
         (Proofs/Scratch/CongrCurveIso.lean, module
         Scratch.CongrCurveIso, build verified
         2026-07-23); rank corollary open
stmt:    S (iso, done) / M (rank corollary)
proof:   DONE (iso) / blocked (rank: no Mordell-Weil
         rank in Mathlib)
module:  Proofs/ShearEC/ShearAddition.lean (conventions)
source:  OEIS A319510 formula, Jose Aranda,
         2024-07-02, marked "Empirical"

CLAIM
  A319510(n) = rank of the elliptic curve
  y^2 = x^3 - n^2 x over Q (congruent-number curve;
  entry also gives a(n) = A060952(n^2)). Empirical
  claim: a(n) = a(4n).

THEOREM (sorry-free Lean, verified build)
  Scratch.CongrCurveIso (200 lines, over ℚ):
    congrCurve n := short Weierstrass a₄ = -(n^2),
      others 0  (i.e. y² = x³ - n²x)
    congrCurve_Δ : (congrCurve n).Δ = 64 * n^6
    congrCurve_isElliptic (n ≠ 0)
    congrCurveIso (hn : n ≠ 0) :
      Affine.Point (congrCurve n) ≃+
      Affine.Point (congrCurve (4 * n))
  Forward map zero ↦ zero, (x,y) ↦ (4x, 8y).
  Hypothesis n ≠ 0 is necessary (E_0 singular).
  Since 16n² = (4n)², this is E_n ≅ E_{4n}; any
  AddEquiv-invariant rank functional is equal on the
  two curves.

LEAN NOTE
  Built from scratch: Mathlib's VariableChange has NO
  point-level map (audited 2026-07-23), so this file
  fills a genuine upstream gap for the u-scaling case
  and is upstreamable independent of the OEIS claim.

RESIDUAL GAPS (both known, both required for the
  full OEIS claim)
  1. A rank definition (absent from Mathlib; interim:
     any AddEquiv-invariant functional).
  2. Definitional cross-check that A319510's a(n) is
     exactly rank(E_n) with no squarefree
     normalization or index shift (entry formula
     a(n) = A060952(n^2) supports this; re-read the
     entry before claiming the corollary).

EVIDENCE
  Aranda: empirical over computed range.
