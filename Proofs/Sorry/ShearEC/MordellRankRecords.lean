/-!
# Mordell-curve rank records — A031507

## Current archive status

Documentation-only archive of a hard-blocked open growth problem. There are no
imports, definitions, theorem statements, or admissions in this module. Archival
placement is not a formal theorem or admission, and no rank record or growth
bound has been proved or formally stated here.

## Remaining target and hypotheses/representation

The intended object is the least positive integer `k` for which the rational
points of `y² = x³ + k` have Mordell–Weil rank `n`. The intended target is a
substantive growth assertion for those least parameters as rank varies. The
source card does not specify a growth inequality, constants, range, or rate;
**the growth inequality remains underspecified**. This archive does not choose
one. Existence of a curve of each prescribed rank, and hence existence of the
least `k` at that rank, cannot be silently assumed to define a total record
function. A future statement must handle the realized-rank domain explicitly.

Use genuine rational point groups and their Mordell–Weil rank, not a free
numerical rank parameter or a hypothesis-carried surrogate. Positivity of `k`
excludes the singular `k = 0` curve; the rank index is a nonnegative integer,
with the source's indexing convention still to be pinned. No vacuous domain of
unrealized ranks can be used as a substitute for the growth problem.

## Known prerequisites and named blocker

The inspected `ShearEC/ShortCurveScaling.lean` header supplies short-Weierstrass
point-group scaling infrastructure, not ranks, record minima, finite generation,
height bounds, or descent. It does not settle this Mordell-family growth target.

Named blocker: **unconditional Mordell–Weil rank/descent API on concrete curves**,
followed by specification of the growth claim and the record's domain/existence.
The source card reports missing usable rank, finite-generation, height, and
descent layers. A per-curve finite-generation assumption without a concrete
satisfiable instance is not a resolution. No unconditional rank instance,
unboundedness claim, record sequence identification, or growth theorem is claimed.

## Historical/source-card subsection (verbatim)

Source: `Formalize/A031507-mordell-rank-records.md`. The complete current card text follows;
historical metadata is not promoted to a formal declaration.

```text
# A031507 — Mordell-curve rank records

- **Mathematical status:** open growth problem suggested by the Gebel–Pethő–Zimmer observations recorded at OEIS A031507.
- **Work status:** hard-blocked.
- **Remaining target:** formalize and prove a substantive growth statement for the least positive `k` such that `y²=x³+k` has Mordell–Weil rank `n`.
- **Concrete blocker:** Mathlib has no usable Mordell–Weil rank, finite-generation, height, or descent layer. A theorem conditional on a per-curve finite-generation hypothesis would not furnish a satisfiable instance and is not an acceptable substitute.
- **Next obligation:** first obtain an unconditional Mordell–Weil rank/descent API capable of handling a concrete curve; only then state the record-growth target.
```
-/
