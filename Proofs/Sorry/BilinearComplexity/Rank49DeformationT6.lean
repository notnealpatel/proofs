/-!
# Equivalence-aware Plus bridges between c659 and c680 — blocked documentation archive

## Archive status and interpretation

Documentation-only blocked-work archive, created at the user's direction. This module has
no imports, declarations, formal theorems, admissions, or proofs. Placement in `Sorry/` records
an unpaid obligation; it does not introduce a Lean `sorry` or certify the prose. Production
foundations are left untouched. The historical source-card subsection below preserves
the complete retired card verbatim, including historical status and provenance statements.
Compilation checks only that this documentation is a well-formed Lean file, not any
mathematical assertion or external certificate. No numerical replay was performed here.

## Actual roots, finite frontiers, and source identities

Despite the archive naming convention, this card concerns two length-47 roots, not the
49-slot T2--T4 fixture. Both are native binary 4-by-4 matrix-multiplication presentations:

* `cmd/c659-plusflip-cert/testdata/4x4x4_m47_c659_iteration5551_Z2.txt`, 4524 bytes,
  raw SHA-256 `25f47b5f37d2b7351dd5a2c5da65ff8ef5ba80ce53239d46cdfdef37e6eef403`;
* `cmd/c659-plusflip-cert/testdata/4x4x4_m47_c680_iteration4356_Z2.txt`, 4524 bytes,
  raw SHA-256 `7e65a2fa888fcd9f32d9d68fd21ab8cdafeb4a39300cc77882def8e0115483e8`.

`cmd/c659-c680-cc1-cert/constants.go` binds these roots and the c659 inverse corpus
`Programs/BilinearComplexity/c659_all_child_wedge_inverse_plus_oracle.bin`
(7775908 bytes; SHA-256 `eac882916c80e3617e542434625c999d3177ed3d1d5fd67204d1152b50ee19a2`).
Those corpus values are recorded identities, not a claim that this archive replayed it.
`frontier.go` specifies the checked root/child validity and exact-byte canonicalization;
`Programs/BilinearComplexity/rank48_plus_gateway.sage` describes the finite descriptor
contract. Variant 0 in oriented legs replaces two distinct source slots by
`(a1,b1+b2,c1), (a1+a2,b2,c2), (a1,b2,c1+c2)`, using XOR.
Each root's domain has `47*46*6 = 12972` ordered-pair/orientation descriptors and 6486
term-permutation-canonical length-48 children. All stored evaluated terms must be nonzero,
distinct, and sum to the exact target; arbitrary root parameters do not identify this task.

## Exact action and remaining decision

The target is either a standard-equivalent pair of children in these two complete
variant-0 frontiers, or a c680 child with a non-generating inverse-Plus parent
standard-equivalent to c659, with independently replayable positive or exhaustive negative
certificates. Standard equivalence combines a common term permutation with invertible
sandwich matrices `(P U Q^-1,Q V R^-1,R W P^-1)` and all six native physical outer
orientations. Native W uses trace coordinates `(k,i)`. Cyclic orientations rotate factors;
reflections transpose and reverse them. These are not merely the six leg placements in a
Plus descriptor. Over F₂ product-one scalar gauges are trivial, but the convention must
still agree with the action. `Programs/BilinearComplexity/r47_equivalence.sage` documents
that relation for length-47 inputs; it is not a completed length-48 equivalence decision.

## Foundations, evidence, and limits

`Proofs/BilinearComplexity/SchemeReplacement.lean` provides exact local replacement
semantics; `FieldNativeMoves.lean` and `FieldNativePath.lean` provide nonzero factor/native
step and strict-path foundations. None identifies these roots and discharges this finite
equivalence-aware target. Existing c659-only inverse results in
`Programs/BilinearComplexity/c659_all_child_wedge_inverse_plus_oracle.sage` and
`cmd/c659-all-child-inverse-cert/` do not cover c680 inverse-tripod cases.
`Documents/DeformationTheory.md` records root histogram obstructions and their scope;
root inequivalence does not exclude an equivalence-aware one-Plus bridge.

No literally equal canonical child bytes is only a term-permutation comparison, not
standard inequivalence. Hash or invariant agreement is not equivalence either. A negative
answer needs a checked partition of every candidate pair and every declared c680 inverse
case; limits or timeouts yield unknown. A positive `47 -> 48 -> 47` path is a same-length
bridge, not rank reduction. No conclusion follows for other variants, longer paths, scalar
extensions, minimum tensor rank, or the global move graph. No such search is launched here.

## Historical/source-card subsection — complete verbatim current card

Source: `Formalize/T6-equivalence-aware-plus-bridges.md`. The following text is preserved without modification:

# T6 — equivalence-aware Plus bridges between c659 and c680

- **Mathematical status:** finite decision problem over `F₂` for two authenticated rank-47 presentations.
- **Work status:** unstarted at the required equivalence-aware scope.
- **Remaining target:** decide, with independently replayable certificates, whether the two complete variant-0 one-Plus frontiers have standard-equivalent rank-48 children, or whether a c680 child has a non-generating inverse-Plus parent standard-equivalent to c659.
- **Available evidence:** the generated frontiers contain 12,972 descriptors and 6,486 term-permutation-canonical children per root, with no literally equal canonical child bytes. Existing c659 inverse-Plus results apply only to their declared c659 domain.
- **Next obligation:** implement/check the exact relation combining term permutation, sandwich matrices, and six outer orientations; then provide either a full positive witness or a checked partition of every candidate pair and c680 inverse-tripod case. Hash or invariant agreement is not equivalence, and any timeout leaves the result incomplete.
- **Scope:** a positive `47→48→47` path is a same-length bridge, not a rank reduction; the finite domain says nothing about other Plus variants, longer paths, scalar extensions, minimal rank, or global move-graph connectivity.
-/

