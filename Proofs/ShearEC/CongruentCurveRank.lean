import ShearEC.ShortCurveScaling
import Mathlib.LinearAlgebra.Dimension.Basic

/-!
# Intrinsic cardinal rank of congruent-number point groups

The additive equivalence `ShortCurveScaling.congrCurveIso` is also a linear
equivalence for the canonical `ℤ`-module structures. It preserves the intrinsic
cardinal rank `Module.rank ℤ`: independent subsets transport along the inverse
linear equivalence with their cardinalities unchanged, so the suprema agree.
No finite-generation hypothesis is needed.

The statement holds for every rational parameter, including `n = 0`, where
`Point` is the group on the nonsingular locus of a singular cubic, not an
elliptic Mordell–Weil group. For nonzero parameters ellipticity is supplied by
`ShortCurveScaling.congrCurve_isElliptic`. This cardinal-rank equality does not
identify a finite natural-valued Mordell–Weil rank or the OEIS sequence A319510.
-/

set_option autoImplicit false

namespace ShearEC.CongruentCurveRank

open ShearEC.ShortCurveScaling (congrCurve congrCurveIso congrCurve_isElliptic)

/-- The rational point groups of `y² = x³ - n²x` and `y² = x³ - (4n)²x`
have equal intrinsic cardinal rank as `ℤ`-modules, for every rational `n`. -/
theorem congrCurve_rank_eq (n : ℚ) :
    Module.rank ℤ (congrCurve n).Point = Module.rank ℤ (congrCurve (4 * n)).Point :=
  (congrCurveIso n).toIntLinearEquiv.rank_eq

-- Both point-group domains are inhabited, including at the singular parameter.
example (n : ℚ) : Nonempty ((congrCurve n).Point × (congrCurve (4 * n)).Point) :=
  ⟨(0, 0)⟩

-- A concrete nonsingular member witnesses the intended elliptic setting.
example : (congrCurve 1).IsElliptic :=
  congrCurve_isElliptic (by norm_num)

end ShearEC.CongruentCurveRank
