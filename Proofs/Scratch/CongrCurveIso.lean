/-!
# Promoted to `ShearEC.ShortCurveScaling`

This scratch file's content — the `AddEquiv`
`Point (E_n) ≃+ Point (E_{4n})` for the congruent-number family
`E_n : y² = x³ - n²x` over `ℚ` via `(x, y) ↦ (4x, 8y)` — was promoted, by
generalization, to `Proofs/Xlib/ShortCurveScaling.lean`:

* `ShearEC.ShortCurveScaling.scaleEquiv` — the general unit-scaling
  isomorphism `(shortCurve F a₄ a₆).Point ≃+
  (shortCurve F (u⁴a₄) (u⁶a₆)).Point` over **any** field, with **no
  characteristic assumption** (the nonsingularity transfer is proved
  directly from the `Nonsingular` definition, not via the
  `IsElliptic`/`Δ` route used here, which silently needed `64 ≠ 0`).
* `ShearEC.ShortCurveScaling.congrCurve`, `congrCurve_Δ`,
  `congrCurve_isElliptic` — the congruent-number family, `Δ = 64n⁶`,
  ellipticity for `n ≠ 0`.
* `ShearEC.ShortCurveScaling.congrCurveIso` — this file's main theorem as
  the `u = 2` instance of `scaleEquiv`, now for **all** `n : ℚ` (the
  `n ≠ 0` hypothesis was an artifact of the `IsElliptic` route).
-/
