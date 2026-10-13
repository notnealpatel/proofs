/-!
# Exact scheme semantics, actions, and replacements — blocked documentation archive

## Archive status and interpretation

Documentation-only blocked-work archive, created at the user's direction. This module has
no imports, declarations, formal theorems, admissions, or proofs. Placement in `Sorry/` records
an unpaid obligation; it does not introduce a Lean `sorry` or certify the prose. Production
foundations are left untouched. The historical source-card subsection below preserves
the complete retired card verbatim, including historical status and provenance statements.
Compilation checks only that this documentation is a well-formed Lean file, not any
mathematical assertion or external certificate. No numerical replay was performed here.

## Exact target, production foundations, and conventions

The acceptance target remains a complete standard-action witness and its validity transport,
certificate transport/composition, and completeness of repeated-factor enumeration for
ordinary nontrivial two-term binary flips. Existing production APIs already provide replay
witnesses for invertible sandwiches, product-one gauges, a common slot permutation, and all
six physical orientations, as well as certificate transport/composition and repeated-factor
indexing results. This archive update does not certify additional closure of the full T1
acceptance target. Ordinary flip completeness in that local class is not completeness of
Plus, of all exact relations, or of bounded paths.
For native trace coordinates the sandwich action is
`(U,V,W) -> (P U Q^-1, Q V R^-1, R W P^-1)`; reflections transpose and reverse
legs, not merely permute slots. A gauge uses three units with product one.

`Proofs/BilinearComplexity/Scheme.lean` supplies ordered `Fin r` semantics, tensor sums,
`Scheme.Valid`, slot permutation, and row-major matrix/vector conventions. Validity includes
exact tensor equality, nonzero evaluated terms, and injectivity of evaluated terms; length
is a presentation count, only giving `RankLE r`. `SchemeAction.lean` supplies basic gauge
and orientation actions; `SchemeReplacement.lean` supplies local tensor-equality certificates
and deterministic output (increasing surviving slots followed by list-order insertions).
`SchemeFlipReduction.lean` supplies shared-factor flip identities and validity bookkeeping.
Shared slots must be distinct and outputs must pass the required nonzero/freshness checks.

`AffineCollisionNativeWitness.lean` publishes
`BilinearComplexity.AffineCollisionNativeWitness.exists_strictNativeFlip`: one concrete
binary witness with separated retained factors and a five-atom fresh context. This is not
a general collision-to-useful-operation interface, nor standard-action transport.
The historical card's accepted-revision identity is preserved below without revalidation.

## Remaining blocker and limits

`Proofs/BilinearComplexity/SchemeMoveAlgebra.lean` now proves all 41 generic move-algebra
prerequisite lemmas, with its original definitions and theorem contracts retained. These
include evaluation and occurrence-count laws, certificate-to-multiset contextual replay,
path soundness and generated-congruence laws, conditional completeness and restricted-path
bridges, successor replay, and finiteness of the normalized bounded characteristic-two M4
space. This is a generic algebraic discharge, not a concrete historical-family specification,
support-five classification, kernel presentation for a concrete proper move family, bounded
connectivity, or rank improvement. Abstract goal propositions are not proofs of those goals.
A multiset carries multiplicity even when evaluated occurrences cancel in characteristic two;
a reversed relation is not a group inverse of a decomposition. No additional full
standard-action validity-transport or ordinary-flip enumeration closure is certified by this
change; those acceptance obligations remain outside this generic prerequisite discharge.
One finite native witness cannot establish universal completeness or a rank lower bound.

## Historical/source-card subsection — complete verbatim current card

Source: `Formalize/Rank49Deformation-T1-schemes-actions-replacements.md`. The following text is preserved without modification:

# Rank-49 deformation T1 — exact scheme semantics

- **Mathematical status:** infrastructure theorem package, not a tensor-rank claim.
- **Work status:** hard-blocked; substantial public modules exist, but the acceptance target is partial.
- **Remaining target:** finish an exact standard-action witness (sandwich matrices, gauges, term permutation, and six orientations), certificate transport/composition, and the narrow theorem that repeated-factor enumeration is complete for ordinary nontrivial two-term flips over `F₂`.
- **Proved prerequisites:** `Proofs/BilinearComplexity/Scheme.lean`, `SchemeAction.lean`, `SchemeReplacement.lean`, and `SchemeFlipReduction.lean` provide ordered semantics, basic actions, deterministic local replacement, validity bookkeeping, and flip identities.
- **Proved prerequisite:** accepted main revision `4b6938dc2aa2fb5655f22433f2aeee02bf2377b3` publishes `BilinearComplexity.AffineCollisionNativeWitness.exists_strictNativeFlip`, one concrete strict native Flip witness in a five-atom fresh context. It does not supply the general collision-to-useful-operation interface or the standard-action transport.
- **Next obligation:** discharge the relevant theorem obligations in `Proofs/BilinearComplexity/SchemeMoveAlgebra.lean`, which deliberately contains `sorry`; then connect the published witness to a small independently replayed action/replacement example. A valid length-49 presentation proves only `RankLE 49`, not minimal rank.
-/

