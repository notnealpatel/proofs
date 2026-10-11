/-!
# Bounded ranks in the cubic-sum family — A060748

## Current archive status

Documentation-only archive of Sondow's open finiteness question. This module has
no imports, definitions, theorem statements, or admissions. The filename names
the question, not its answer: **the bounded/unbounded decision remains unset**.
Neither boundedness nor unboundedness has been formally stated or proved here.

## Remaining target and hypotheses/representation

Determine whether the genuine Mordell–Weil ranks of the rational cubic-sum family
`x³ + y³ = m`, birational to `y² = x³ - 432m²`, are bounded over the intended OEIS
parameter domain, and then formalize the corresponding finiteness assertion.
The source card does not settle the exact parameter domain/indexing. A future
statement must specify that domain and the passage from the cubic-sum model to
the rational elliptic point group. For a nonsingular elliptic model require
`m ≠ 0`; positive integer parameters, if that is the identified source domain,
would supply this guard. The singular `m = 0` member is not an elliptic-rank
instance. No extension to every rational parameter is silently made here.

Once these objects are fixed, the bounded alternative would quantify one finite
rank bound uniformly over all intended parameters, not a per-curve bound; the
unbounded alternative would require ranks exceeding every finite bound. This is
an explanation of the decision, not a pair of Lean declarations. Any claimed
equivalence to a finiteness statement about source indices still needs its
precise sequence interpretation.

## Known prerequisites and named blocker

The inspected `ShearEC/ShortCurveScaling.lean` header provides point-group
isomorphisms for unit scaling; it does not define or compute Mordell–Weil ranks
for this family or supply the cubic-sum birational/rank bridge.

Named blocker: **unconditional rank, finite-generation, height, and descent
infrastructure on concrete family members**, followed by the parameter-domain
and finiteness bridge. The source card reports this infrastructure as absent.
No surrogate rank, assumed family-wide bound, or hypothesis encoding the answer
is admitted. Finite examples cannot decide the uniform boundedness question.

## Historical/source-card subsection (verbatim)

Source: `Formalize/A060748-sondow.md`. The complete current card text follows;
historical metadata is not promoted to a formal declaration.

```text
# A060748 — bounded ranks in the cubic-sum family

- **Mathematical status:** open conjectural finiteness question of Jonathan Sondow (OEIS A060748).
- **Work status:** hard-blocked.
- **Remaining target:** determine whether Mordell–Weil ranks in the family `x³+y³=m` (birational to `y²=x³-432m²`) are bounded, and formalize the corresponding finiteness statement.
- **Concrete blocker:** Mathlib lacks the Mordell–Weil rank, finite-generation, height, and descent infrastructure needed even to instantiate the statement on concrete curves. A hypothesis-carried surrogate rank is not an acceptable resolution.
- **Next obligation:** obtain an unconditional rank/descent API before attempting this target.
```
-/
