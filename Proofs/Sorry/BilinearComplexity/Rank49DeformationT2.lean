/-!
# Restricted derivatives and scoped obstruction certificates — blocked documentation archive

## Archive status and interpretation

Documentation-only blocked-work archive, created at the user's direction. This module has
no imports, declarations, formal theorems, admissions, or proofs. Placement in `Sorry/` records
an unpaid obligation; it does not introduce a Lean `sorry` or certify the prose. Production
foundations are left untouched. The historical source-card subsection below preserves
the complete retired card verbatim, including historical status and provenance statements.
Compilation checks only that this documentation is a well-formed Lean file, not any
mathematical assertion or external certificate. No numerical replay was performed here.

## Fixed instance and representation

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

A variation has `49*3*16 = 2352` coordinates over `F₂`, with Jacobian codomain
of dimension 4096. The Jacobian is the sum of the three single-leg variations of each
triad; quadratic, cubic, and mixed coefficients are polynomial expansion coefficients.
A five-slot support fixes all other slots; its raw derivative has 240 columns. The T4
bundle describes deletion of the two local scaling directions per selected nonzero term,
leaving 230 columns. This requires a checked direct complement, not subtracting nominal
generator counts. Kernel/gauge quotients must specify the actual gauge/action submodule
and the correction domain; same-support and full-coordinate corrections are different.

## Proved foundations and exact unpaid target

`Proofs/BilinearComplexity/SchemeDeformation.lean` supplies linear, quadratic, cubic,
and mixed coefficients, restricted variation modules, quotient/cokernel obstruction
classes, truncated arcs, and scoped no-lift theorems. The abstract algebra is not the
numerical rank-49 certificate. `Scheme.lean` supplies the ordered evaluation conventions.
The unpaid bridge is replayable finite elimination for the fixed restricted Jacobian:
checked pivots/rank bounds, kernel and range witnesses, gauge quotient, and inconsistency
certificates, plus the scalar-extension soundness theorem needed for exclusions over every
field extension of `F₂`. It cannot be discharged by assuming the intended rank or obstruction
as a hypothesis on an arbitrary scheme labelled the authenticated instance.

## Evidence sources and limits

`Documents/rank49-deformation-t4.md` and
`Programs/BilinearComplexity/rank49_t4/README.md`, `manifest.json`, and
`artifacts/support5_census.json` describe external deterministic arithmetic and finite
coverage. They are not newly replayed or formally proved here. Nonzero binary minors
remain nonzero under scalar extension, but that fact alone does not identify the encoded
matrix, transport a quotient, or prove a nonlinear obstruction theorem. A same-support
no-lift certificate excludes only its specified direction and correction scope; it is not
global rigidity, finite rigidity, a component dimension, or exclusion of another point.
Finite-field checks without polynomial degree bounds do not certify a generic identity;
first-order kernels and second-order tests do not settle all-order integrability.

## Historical/source-card subsection — complete verbatim current card

Source: `Formalize/Rank49Deformation-T2-restricted-derivatives.md`. The following text is preserved without modification:

# Rank-49 deformation T2 — restricted derivatives

- **Mathematical status:** general soundness infrastructure for deformation filters.
- **Work status:** hard-blocked; the algebraic core is substantial, but certificate/scalar-extension acceptance remains.
- **Remaining target:** provide a replayable finite-elimination certificate for restricted Jacobian rank, kernel/gauge quotient, and inconsistency, together with the scalar-extension theorem needed to transport an `F₂` rank exclusion to every field extension.
- **Proved prerequisites:** `Proofs/BilinearComplexity/SchemeDeformation.lean` formalizes linear, quadratic, cubic and mixed coefficients, restricted variation modules, quotient/cokernel obstruction classes, finite truncated arcs, and scoped no-lift theorems without `sorry`.
- **Next obligation:** connect the external `4096×2352` computations to those abstract declarations through checked pivots/kernel/range witnesses. A same-support obstruction rejects only that support and correction scope; it does not prove finite or global rigidity, component dimension, or absence of another point.
-/

