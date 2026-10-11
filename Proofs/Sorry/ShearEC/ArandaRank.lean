/-!
# Rank invariance under multiplication of the parameter by four — A319510

## Current archive status

Documentation-only archive of the unpaid rank/sequence bridge. No imports,
definitions, theorem statements, or admissions are added here. A curve-group
isomorphism prerequisite exists in production, but this archive is not a formal
rank theorem and does not turn the empirical OEIS claim into a proved sequence
identity.

## Remaining target and hypotheses/representation

For the congruent-number family `E_n : y² = x³ - n²x`, deduce the equality of
Mordell–Weil ranks over `ℚ` at `n` and `4n`, and identify these ranks with exactly
A319510's indexing convention. The intended sequence parameters are positive
integers, embedded into `ℚ`; no squarefree normalization, reindexing, or index
shift may replace that target. A genuine rank of `E_n(ℚ)`, its finite-generation
foundation, and invariance under additive point-group equivalence are required.

## Known prerequisites and named blocker

The inspected production header `Proofs/ShearEC/ShortCurveScaling.lean` records
`ShearEC.ShortCurveScaling.congrCurveIso`: the additive equivalence induced by
`(x,y) ↦ (4x,8y)` between the affine point groups at `n` and `4n`, for every
`n : ℚ`. It separately records `Δ = 64n⁶` and ellipticity for `n ≠ 0`.
The map covers the nonsingular locus even at the singular parameter `n = 0`;
that fact does **not** make the singular member an elliptic Mordell–Weil-rank
instance. Positive sequence parameters keep the intended elliptic models
nondegenerate. The header's reference to functorial rank surrogates is not the
rank identification required by this card, and no surrogate is introduced here.

Named blocker: **genuine Mordell–Weil rank invariant and exact OEIS indexing
identification**. The existing additive equivalence is the known prerequisite,
not the missing rank theorem. This task neither rebuilds that prerequisite nor
claims a new audit of it. No rank definition, rank computation, or sequence
identity is claimed by compiling this documentation module.

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
