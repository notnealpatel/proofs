# The concrete primitive congruent number 21

**Scope:** a known finite congruent-number certificate, packaged for USER review.
This is not a claim of novel mathematics, priority, significant conjecture progress,
submission, or Palomar acceptance. USER review is pending and is the sole review gate.

## Exact selected result

Both Lean files state the same declaration,
`Palomar.CongruentTwentyOne.isPrimitiveCongruent_twentyOne`, with the literal type

```lean
Squarefree (21 : ℕ) ∧
  ∃ a b c : ℚ, 0 < a ∧ 0 < b ∧ 0 < c ∧
    a ^ 2 + b ^ 2 = c ^ 2 ∧ a * b = 2 * (21 : ℚ)
```

This means exactly that 21 is squarefree and is the area of a right triangle
with three positive rational sides. The existential domain `ℚ` is nonempty;
positivity excludes degenerate triangles. There are no theorem hypotheses and
no assumed certificate. The area condition uses multiplication, not a totalized
division operation.

The concrete witness is

- `a = 7/2`, `b = 12`, `c = 25/2`, all positive;
- `49/4 + 144 = 625/4`, hence `a² + b² = c²`;
- `(7/2) * 12 = 42 = 2 * 21`;
- 21 is squarefree (`21 = 3 * 7`).

The source proof checks the triangle using `norm_num` and squarefreeness using
its existing bounded criterion with kernel `decide`. This package does not
extend the certificate to any other integer.

## Package and source alignment

- `Challenge.lean` imports only two Mathlib modules and contains exactly one
  intentional theorem `sorry`. It defines no custom mathematical predicates.
- `Solution.lean` does not import the Challenge. It repeats the identical expanded
  statement, changes the goal to `A273929.IsPrimitiveCongruent 21` by definitional
  equality, and applies `A273929.isPrimitiveCongruent_twentyOne` from
  `Proofs/Enumerative/CongruentBSD.lean`.
- `comparator.json` selects the same fully qualified theorem name in both modules,
  permits only `propext`, `Classical.choice`, and `Quot.sound`, and enables Nanoda.
- `formalization.yaml` records provenance, scope, AI assistance, and metadata blockers.
- `verification.md` records fresh compilation, axiom output, and unrun tooling.

The source definition unfolds as `Squarefree n ∧ IsCongruentNumber n`, where
`IsCongruentNumber n` is exactly the positive rational triangle condition for
`(n : ℚ)`. No Solution-only alias changes the Challenge's model.

The imported source also archives the broad A273929 inclusion as an intended
`sorry`. That declaration is not used by the selected proof: the fresh selected
axiom audit contains only the three standard axioms. This package proves no
BSD statement, general inclusion, Mordell–Weil rank result, or original
conditional conjecture.

## Provenance and limitations

The accepted repository source revision supplied for packaging is
`55ab7d253f32b9632581cf31cc4951c2b2119533`. Its module pins OEIS A003273
(congruent numbers), A006991 (squarefree congruent numbers), and A273929
(squarefree numbers in residues 5, 6, 7 modulo 8). These provide context, not
an assumed congruence criterion. The standard interpretation is also described
in [Wikipedia, Congruent number](https://en.wikipedia.org/wiki/Congruent_number).
No external priority search or new source review is claimed.

AI assistance was material to the latest concrete certificate implementation
and this packaging: **gpt-6-astra, xhigh**, as identified by the USER's run
instructions, using Yah and Lean. The exact AI/model history of the pre-existing
infrastructure is unknown. No human formalization-author or maintainer identity
has been established; the YAML leaves those lists empty and identifies the
blockers. No external reviewer or subagent was used for packaging.

Fresh Lean checks and metadata parsing are mechanical checks, not human review.
Comparator, landrun, lean4export, and Nanoda were unavailable and were **NOT RUN**;
no installation or toolchain upgrade was attempted. See `verification.md` for
the exact evidence and remaining obligations.
