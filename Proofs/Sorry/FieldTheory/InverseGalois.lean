/-!
# Inverse Galois realization of transitive permutation groups — A002106

## Current archive status

Documentation-only archive of an open inverse-Galois/counting target. This module
contains no imports, definitions, theorem statements, or admissions. Its presence
under `Sorry/` is not a formal theorem or a Lean `sorry`. The historical card's
`stmt: L` is triage metadata, not evidence that the counting target has been
stated in Lean here. No realization or counting equality is claimed.

## Remaining target and representation

For each positive degree `n`, compare conjugacy classes of transitive subgroups
of the symmetric group on `n` letters with the classes realized by irreducible
polynomials of degree `n` over `ℚ`. The intended unresolved realization obligation
is: every such transitive permutation subgroup occurs as the image of the Galois
action on the roots of some irreducible degree-`n` polynomial over `ℚ`, after a
specified identification of those roots with the `n` letters, up to conjugacy.
An abstract group isomorphism alone does not specify this permutation action.
The counting objects, quotient by conjugacy, degree convention, and realization
predicate must be fixed before a faithful Lean statement can be supplied.

The intended hypotheses are `0 < n`, transitivity of the subgroup's natural
action, and irreducibility and degree `n` of the realizing polynomial. Over `ℚ`
separability supplies `n` distinct roots; their identification with the carrier
is part of the representation bridge. Degree zero or an empty root carrier is
not evidence of transitivity at the intended parameters.

## Known prerequisites and named blocker

The inspected Mathlib `FieldTheory/PolynomialGaloisGroup.lean` header defines
`Polynomial.Gal` via splitting-field automorphisms and describes the faithful
root action. `Polynomial.Gal.galAction_isPretransitive` gives pretransitivity on
`p.rootSet E` for irreducible `p`, with a splitting hypothesis in `E`. This is a
prerequisite on the polynomial-to-transitive-action side, not a realization
construction or a count of conjugacy classes.

Named blocker: **inverse-Galois realization and specified root-action bridge**,
with the transitive-subgroup enumeration/counting representation also unpaid.
The card's informal inequality direction depends on which count is placed on
which side; this archive asserts neither numerical inequality. Small-degree
agreement in the source is not proof of the universal equality. No surrogate
action, conditional realization certificate, or new infrastructure is introduced.

## Historical/source-card subsection (verbatim)

Source: `Formalize/A002106-inverse-galois.md`. The complete current card text follows;
historical metadata is not promoted to a formal declaration.

```text
seq:     A002106
claim:   transitive-groups-are-galois-groups
status:  open (equivalent to inverse Galois over Q)
stmt:    L
proof:   hard-open (major)
dependency: no inverse-Galois realization infrastructure exists in the project
source:  OEIS A002106 comment, Charles R Greathouse
         IV, 2014-05-28; equivalence to inverse
         Galois noted in-entry (Jianing Song,
         2025-05-26)

CLAIM
  A002106(n) = number of transitive permutation
  groups of degree n up to conjugacy in S_n.
  Comment-conjecture: this equals the number of
  groups arising as Gal(f) for irreducible degree-n
  f over Q — equivalent to the inverse Galois
  problem restricted through transitive embeddings.

LEAN
  Mathlib has Polynomial.Gal, galActionHom into
  Equiv.Perm (rootSet), transitivity for irreducible
  polynomials (galAction_isPretransitive). Missing:
  enumeration of transitive subgroups up to
  conjugacy, and everything realization-theoretic.
  L is for the counting statement; the ">=" direction
  (every Galois group of an irreducible f IS
  transitive) is already essentially in Mathlib and
  is the one formalizable fragment.

ROUTE
  Statement-archive. Do not dispatch.

EVIDENCE
  Equality holds for all n where both sides are
  known (small n).
```
-/
