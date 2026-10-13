/-!
# Rank invariance under multiplication of the parameter by four — A319510

## Current archive status

Documentation-only archive of the unpaid finite-rank/sequence bridge. No imports,
definitions, theorem statements, or admissions are added here. Production now
provides both a curve-group isomorphism and an intrinsic cardinal-rank equality.
This archive does not turn the empirical OEIS claim into a proved sequence
identity.

## Remaining target and hypotheses/representation

For the congruent-number family `E_n : y² = x³ - n²x`, deduce the equality of
Mordell–Weil ranks over `ℚ` at `n` and `4n`, and identify these ranks with exactly
A319510's indexing convention. The intended sequence parameters are positive
integers, embedded into `ℚ`; no squarefree normalization, reindexing, or index
shift may replace that target. The intrinsic algebraic group rank is now
represented by `Module.rank ℤ` of the point group, without assuming finite
generation. Its identification with a finite natural-valued Mordell–Weil rank
and the finite-generation/finiteness foundation remain unpaid.

## Known prerequisites and named blocker

The inspected production header `Proofs/ShearEC/ShortCurveScaling.lean` records
`ShearEC.ShortCurveScaling.congrCurveIso`: the additive equivalence induced by
`(x,y) ↦ (4x,8y)` between the affine point groups at `n` and `4n`, for every
`n : ℚ`. It separately records `Δ = 64n⁶` and ellipticity for `n ≠ 0`.
The map covers the nonsingular locus even at the singular parameter `n = 0`;
that fact does **not** make the singular member an elliptic Mordell–Weil-rank
instance. Positive sequence parameters keep the intended elliptic models
nondegenerate.

`Proofs/ShearEC/CongruentCurveRank.lean` proves
`ShearEC.CongruentCurveRank.congrCurve_rank_eq`: for every `n : ℚ`,
`Module.rank ℤ (congrCurve n).Point = Module.rank ℤ (congrCurve (4 * n)).Point`.
This is genuine intrinsic cardinal rank, defined by Mathlib using the supremum
of cardinalities of linearly independent subsets, not a surrogate rank parameter.
The proof converts `congrCurveIso n` to an integer-linear equivalence with
`AddEquiv.toIntLinearEquiv` and applies `LinearEquiv.rank_eq`; no finite-generation
hypothesis or natural-number conversion is used. Independent subsets transport
along the inverse equivalence with the same cardinalities. The equality also
holds at `n = 0` for the nonsingular-locus group without asserting ellipticity.

Named blocker: **finite natural-valued Mordell–Weil rank foundation and exact
OEIS identification**. The new cardinal-rank theorem is an archive prerequisite,
not sequence completion. The exact OEIS OFFSET has not been exposed here, so
no precise sequence-index identification is asserted. The algebraic/analytic
rank identification is also unpaid: A319510 names ranks of `y² = x³ - n²x`
and records the empirical `a(n) = a(4n)`, but its PARI program uses
`ellanalyticrank`. PARI's primary documentation describes that routine as
computing the analytic order of vanishing, using `eps` as a numerical zero
threshold (https://pari.math.u-bordeaux.fr/dochtml/html/Elliptic_curves.html#ellanalyticrank).
No BSD claim, certified analytic-rank computation, sequence identity, or new
audit of the existing isomorphism is supplied here. Compiling this documentation
module establishes none of those missing bridges.

## Historical/source-card subsection (verbatim)

Source: `Formalize/A319510-aranda-iso.md`. The complete current card text follows;
historical metadata is not promoted to a formal declaration.

```text
# A319510 — rank invariance under `n↦4n`

- **Mathematical status:** the curve isomorphism is proved; the OEIS rank formula remains an empirical claim until a rank layer identifies it precisely.
- **Work status:** hard-blocked.
- **Remaining target:** deduce `rank(E_n)=rank(E_{4n})` for `E_n : y²=x³-n²x`, and verify that this is exactly A319510's indexing convention.
- **Proved prerequisite:** `Proofs/ShearEC/ShortCurveScaling.lean` defines `ShearEC.ShortCurveScaling.congrCurveIso`, an additive equivalence of affine point groups induced by `(x,y)↦(4x,8y)` for every `n : ℚ`; no `n≠0` hypothesis is needed, so the map also covers the singular `n=0` curve. The same module separately proves the discriminant formula and ellipticity for `n≠0`.
- **Next obligation:** add a genuine Mordell–Weil rank definition invariant under this equivalence, then pin the OEIS identification without a squarefree normalization or index shift.
```
-/
