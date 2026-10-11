/-!
# Border apolarity and Slip: documentation archive

## Current archive status and scope

This is a documentation-only module in `Sorry/`, not a formal statement,
proof, admission, or complete formalization. No Hilbert scheme, Slip,
smoothability, group action, or border-rank object is introduced here.
Compilation of this comment does not check the cited mathematical claims.
The dispatch named `Formalize/BorderApolarity-Slip.md`; the full current card
at this base is `Formalize/BorderApolarity-Slip-algorithm.md`, preserved below.

## Exact unpaid bridge and required objects

Buczyńska–Buczyński (arXiv:1910.01944) and Conner–Harper–Landsberg
(arXiv:1911.07981) use different source objects and field hypotheses.
The full criterion needs multigraded Hilbert functions, Hilbert functors and
schemes, the correct smoothable component/Slip membership, apolar ideals,
and the degeneration/properness argument. The finite search additionally
needs the precise group/Borel action and Borel-fixed reduction, enumeration
coverage, and soundness/completeness of rejection and acceptance certificates.
Keep the source's algebraically closed field hypotheses distinct from the
weaker infinite-field hypothesis in the current polynomial-closure test.
No exact theorem signature is asserted here: ambient dimensions, graded
pieces, group assumptions, and source-specific hypotheses must be recovered
from the cited rendering before a formal statement is written.

`Documents/BorderApolarity.md` records the CHL v1 PDF rendering separately
from a later TeX revision with shifted sections. It recommends stable labels:
BB `thm_nonsaturated_apolarity` (local compiled Thm 3.15, versus the other
revision's 4.18 numbering) and `thm_G_invariant_bVSP` (local Thm 4.3).
Do not conflate revision numbers or the two papers' hypotheses.
The card also retains arXiv:2602.11309 as a cactus-barrier boundary, not as
an implementation of the missing Hilbert/Slip criterion.

## Existing pieces and their boundaries

The header of `Proofs/AlgComplexity/Vp2/Apolarity.lean` describes the weaker
modeled `(111)` test: min-truncated dimensions, flattening images, and a
triple intersection of subspaces. The soundness core is polynomial vanishing
on an accept locus over an infinite field, not smoothable-ideal membership.
The header excludes sibling degree-three pre-tests, low-degree conciseness
constraints, higher multidegrees, extension to a graded ideal, Borel-fixedness,
and smoothability/Slip. It proves the cruder degeneracy band `n² ≤ r`, where
every tensor passes; its sharper threshold is only a remark. Passing the
modeled test is not a border-rank upper bound. These existing descriptions
were inspected, not rebuilt or independently audited in this migration.

## Historical/source-card subsection — complete current card verbatim

# Border apolarity, Hilbert schemes, Slip, and search completeness

- **Mathematical status:** published border-apolarity criteria and algorithms, only narrowly formalized.
- **Work status:** hard-blocked.
- **Remaining target:** formalize the full Buczyńska–Buczyński / Conner–Harper–Landsberg border-apolarity criterion, including multigraded Hilbert functions, the relevant Hilbert scheme and `Slip` component/smoothability membership, Borel-fixed reduction, and completeness/soundness of the finite search algorithm over its stated field hypotheses.
- **Completed narrow scope:** `Proofs/AlgComplexity/Vp2/Apolarity.lean` proves the polynomial-closure soundness of a weaker modeled `(111)` kernel test over an infinite field. That is not the full `Slip`-membership theorem, does not model smoothability or the cactus gap, and passing the test gives no border-rank upper bound.
- **Source digest:** `Documents/BorderApolarity.md` consolidates arXiv:1910.01944 and arXiv:1911.07981 while preserving their different objects, field hypotheses, and theorem-number corrections. The deleted cactus-barrier note arXiv:2602.11309 is also covered by this residual boundary: its barrier consequences do not supply the missing Hilbert/Slip formalization.
- **Next obligation:** define multigraded Hilbert functors/schemes and the smoothable component sufficiently to state `Slip` membership; prove the degeneration/properness argument; only then connect Borel-fixed enumeration and algorithmic rejection/acceptance certificates.
- **Claim boundary:** finite `(111)` linear algebra, bounded candidates, polynomial closure, and Borel-fixedness as an isolated reduction are not completion of the published criterion or algorithm.

-/
