/-!
# Paired-circuit family on the fixed five-slot support — blocked documentation archive

## Archive status and interpretation

Documentation-only blocked-work archive, created at the user's direction. This module has
no imports, declarations, formal theorems, admissions, or proofs. Placement in `Sorry/` records
an unpaid obligation; it does not introduce a Lean `sorry` or certify the prose. Production
foundations are left untouched. The historical source-card subsection below preserves
the complete retired card verbatim, including historical status and provenance statements.
Compilation checks only that this documentation is a well-formed Lean file, not any
mathematical assertion or external certificate. No numerical replay was performed here.

## Fixed instance and family scope

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

The designated zero-based support is `{1,14,29,37,42}`, with the remaining 44
terms fixed. In the documented family `b` is a unit, `t=1+b`, `s=1+b^-1`, and
`(1+s)(1+t)=1` in characteristic two. The source is `b=1`; zero and infinity
are not fibers. According to section 4.1 of `Documents/rank49-deformation-t4.md`,
the `s` updates add hexadecimal mask `0500` to U in slots 1, 37, 42; the `t`
updates add `0070` to W_14, `9990` to U_29, `7707` to W_37, and `0070` to W_42.
These concrete updates must be bound to actual fixture factors and replayed, not supplied
as arbitrary factors together with assumptions asserting the desired instance.

## Proved foundations and unpaid acceptance bridge

`Proofs/BilinearComplexity/PairedCircuit.lean` proves the characteristic-two torus
identity, tensor cancellation, explicit normalized five-term families, all six binary
orientations, and replacement certificates. Its module header explicitly excludes the
remaining 44 terms, minimal rank, classification, integrability census, and a nontrivial
binary endpoint. Factor-matroid three-circuits are minimal factor dependencies, not
minimal dependencies of derivative blocks. The fixed-data bridge still requires actual
factor masks, the two normalized three-circuits and their minimality, complementary closure
equalities, full 49-slot validity, and transport under the complete T1 standard action.
Gauges must be product-one units and coordinate conventions must agree before comparison.

## External evidence and limits

The T4 bundle's `artifacts/parameter_orbits.json` and `artifacts/generic_germ.json`,
with provenance in `manifest.json` and `Programs/BilinearComplexity/rank49_t4/README.md`,
record Laurent replay and fiberwise validity calculations. Hash binding is not a Lean
proof of circuit equations. The bounded archive does not perform that replay. A sufficient
family is not a classification of support-five families, and its length-49 fibers show
only rank at most 49. The binary torus contains only its origin; a family over extensions
does not supply a second `F₂` point, a reduction, or global connectivity.

## Historical/source-card subsection — complete verbatim current card

Source: `Formalize/Rank49Deformation-T3-paired-circuit-gm.md`. The following text is preserved without modification:

# Rank-49 deformation T3 — paired-circuit family

- **Mathematical status:** sufficient characteristic-two construction, not a classification theorem.
- **Work status:** hard-blocked; the general and five-term algebra is proved, but the fixed 49-term presentation is not replayed in Lean.
- **Remaining target:** import an independently checkable certificate tying the support `{1,14,29,37,42}` of the authenticated rank-49 presentation to the two normalized three-circuits and all complementary closure equalities, then transport the witness under the complete T1 standard action.
- **Proved prerequisites:** `Proofs/BilinearComplexity/PairedCircuit.lean` proves the torus identity `(1+s)(1+t)=1`, the tensor cancellation theorem, explicit five-term families, all six binary orientations, and replacement certificates without `sorry`.
- **Next obligation:** replay the concrete factor masks, circuit minimality, closure equations, and 49-slot validity rather than trusting an external hash. The resulting family gives length-49 presentations; it does not prove rank 49, classify all support-five deformations, or produce a second `F₂` point.
-/

