/-!
# Stabilizer schemes, census, germs, and parameter correspondence — blocked documentation archive

## Archive status and interpretation

Documentation-only blocked-work archive, created at the user's direction. This module has
no imports, declarations, formal theorems, admissions, or proofs. Placement in `Sorry/` records
an unpaid obligation; it does not introduce a Lean `sorry` or certify the prose. Production
foundations are left untouched. The historical source-card subsection below preserves
the complete retired card verbatim, including historical status and provenance statements.
Compilation checks only that this documentation is a well-formed Lean file, not any
mathematical assertion or external certificate. No numerical replay was performed here.

## Fixed object and evidence sources

The fixed numerical object is the ordered 49-slot binary presentation in
`Programs/BilinearComplexity/rank49_t4/fixtures/4x4x4_m49_c680_iteration65_Z2.txt`
(header `4 4 4 49`, 4716 bytes; raw SHA-256
`5fc92a6bf83fc29d9527ab100bad5d72d769178b616b31a36c3c0c0b8ad9d09d`).
Its decoded-triple digest recorded in `Documents/rank49-deformation-t4.md` is
`6268c06eb811567c77a5e0f75222e8bf7ec6f8bf6f2ebf841ea0bb559353df7e`.
These are source identities, not Lean evidence. Terms are indexed from 0 through 48;
factors are 4-by-4 binary matrices flattened to 16 coordinates with bit `4*i+j`.
Tensor coordinates use index `256*i+16*j+k`. The target is the 4-by-4
matrix-multiplication tensor, not an arbitrary tensor or scheme parameter relabelled as
this instance. A replay must check all 4096 coordinates, all nonzero evaluated terms,
and pairwise distinctness, as well as binding the ordered factor data to the fixture.

The relevant synthesis is `Documents/rank49-deformation-t4.md`; the numerical
bundle is `Programs/BilinearComplexity/rank49_t4/README.md`, `manifest.json`, and
`artifacts/{stabilizer,support5_census,generic_germ,parameter_orbits}.json`.
The support stream is
`artifacts/support5_orbits-99ea851b7dec758b3e302f306f93220969df7ef26073cfc4afa384d60c71bf7b.jsonl.gz`.
These locators identify recorded external evidence, not a new replay or a formal proof.
T1--T3 production modules supply intended algebra/replay foundations, not T4's geometric
classification. The support-five census covers all 1,906,884 five-slot supports and records
63 exceptional normal directions; it does not enumerate all ambient decompositions.

## Exact remaining target and scheme-level distinction

The target is equality of the stabilizer functor/scheme over general base algebras,
including nonreduced and disconnected ones, and representability/effective action of the
appropriate quotient. Equality of field-point sets is not enough. A standard witness has
invertible P,Q,R, one common slot permutation, six physical orientations, and nonzero
product-one term gauges. The proposed scalar witness torus is `C_x = G_m^3` with
scalar sandwich matrices and compensating gauges; a trivial effective image on field
points does not prove a trivial group scheme or justify quotienting point groups.

Rotations permute scalar coordinates; reflections permute AND invert them. The diagonal
`G_m` is normalized, not central under all six actions. The documented all-outer equalizer
is diagonal `mu_2`, with Laurent ideal `(p-q,q-r,p^2-1)`; in characteristic two one
geometric point does not imply reducedness. This correction does not establish the
stabilizer scheme. The scheme-theoretic parameter correspondence, geometric support-five
integrability census, and generic Jacobian/orbit-sweep certificates remain acceptance
obligations even where field-point computations have been recorded.

## Computational tranche and its limits

The synthesis records ranks over `F₂(b)` on `G_m`: Jacobian 2155, kernel dimension
197, connected action 143, and orbit-plus-family differential 144. Its finite `GF(2^9)`
evaluations rely on explicit degree bounds below 512 and nonzero minors, not statistical
sampling. Such arithmetic needs authenticated coefficient data and replay; dimensions of
tangent spaces do not give component dimension, smoothness, reducedness, or all-order lifts.
The documented F₂/F₄ counts and field-valued parameter separation do not establish a
scheme-theoretic diagonal, a miniversal slice, or a geometric census. Finite solver coverage
must close every branch; any timeout leaves a gap. Neither finite-extension points nor the
same-support obstruction can establish global rigidity, minimal rank, or rank reduction.

## Historical/source-card subsection — complete verbatim current card

Source: `Formalize/Rank49Deformation-T4-stabilizer-germ-orbits.md`. The following text is preserved without modification:

# Rank-49 deformation T4 — stabilizer, census, germ, and parameter orbits

- **Mathematical status:** open bounded geometric/computational classification problem for one authenticated rank-49 presentation.
- **Work status:** hard-blocked; deterministic field-point and finite-census tranches are recorded, but the card's acceptance criteria are not met.
- **Remaining target:** prove the scheme-theoretic stabilizer/effective action, complete the geometric support-five integrability census, certify generic Jacobian and orbit-sweep dimensions over `F₂(b)`, and determine the full standard-equivalence correspondence between family parameters.
- **Established prerequisites:** `Documents/rank49-deformation-t4.md` records checked `F₂`/`F₄` witnesses, the exhaustive restricted first-order census, generic calculations, and corrected outer action. Rank49 T1–T3 provide the intended replay semantics.
- **Next obligation:** upgrade field-valued computations to the stated scheme/geometric claims and close every nonlinear/solver branch with replayable witnesses or finite coverage. In particular, reflections invert the diagonal parameter (`t↦t⁻¹`); the diagonal torus is not central under all six outer actions. Tangent dimension is not component dimension, and finite-extension points do not constitute a geometric census.
-/

