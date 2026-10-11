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

`Conner–Harper–Landsberg, New lower bounds for matrix multiplication and det3`
(arXiv:1911.07981) has a v1 PDF rendering distinct from a later TeX
revision with shifted sections. Stable BB labels are
`thm_nonsaturated_apolarity` (local compiled Thm 3.15, versus another
revision's 4.18) and `thm_G_invariant_bVSP` (local Thm 4.3).
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

## Historical/source-card subsection — source pointers consolidated

# Border apolarity, Hilbert schemes, Slip, and search completeness

- **Mathematical status:** published border-apolarity criteria and algorithms, only narrowly formalized.
- **Work status:** hard-blocked.
- **Remaining target:** formalize the full Buczyńska–Buczyński / Conner–Harper–Landsberg border-apolarity criterion, including multigraded Hilbert functions, the relevant Hilbert scheme and `Slip` component/smoothability membership, Borel-fixed reduction, and completeness/soundness of the finite search algorithm over its stated field hypotheses.
- **Completed narrow scope:** `Proofs/AlgComplexity/Vp2/Apolarity.lean` proves the polynomial-closure soundness of a weaker modeled `(111)` kernel test over an infinite field. That is not the full `Slip`-membership theorem, does not model smoothability or the cactus gap, and passing the test gives no border-rank upper bound.
- **Source digest:** Buczyńska–Buczyński, arXiv:1910.01944, and Conner–Harper–Landsberg, arXiv:1911.07981, have different objects, field hypotheses and revision numbering. The cactus-barrier note arXiv:2602.11309 is covered only as a residual boundary: its barrier consequences do not supply the missing Hilbert/Slip formalization.
- **Next obligation:** define multigraded Hilbert functors/schemes and the smoothable component sufficiently to state `Slip` membership; prove the degeneration/properness argument; only then connect Borel-fixed enumeration and algorithmic rejection/acceptance certificates.
- **Claim boundary:** finite `(111)` linear algebra, bounded candidates, polynomial closure, and Borel-fixedness as an isolated reduction are not completion of the published criterion or algorithm.

## Necessary-direction geometric kernel (source-derived, not Lean-checked)

Buczyńska–Buczyński, *Apolarity, border rank and multigraded Hilbert
scheme*, arXiv:1910.01944, lemma `lem_strong_nonsaturated_apolarity`
and theorem `thm_nonsaturated_apolarity`, work over ℂ with a smooth
projective toric variety X embedded by L in P(H⁰(X,L)*) and a nonzero
F ∈ H⁰(X,L)*. This archive restricts the implication below to dim X ≥ 1;
this is an archive domain restriction, not a claim that the paper explicitly
states it. Fix r ≥ 1 and the generic Hilbert function
h(D)=min(r,dim H⁰(X,O(D))). Sip consists of saturated ideals of r distinct
points with this function; Slip is its closure in the reduced multigraded
Hilbert scheme. The claim retained here is only the necessary direction:
br_X(F) ≤ r implies some I ∈ Slip satisfies I ⊆ Ann(F).
The zero-dimensional case r > 1 is excluded: X=P⁰ has no r distinct
points, so Sip and its closure Slip are empty even though secant membership
holds; secant membership alone cannot imply Slip membership there.

The proof needs projectivity of this Hilbert scheme/Slip, supplied in the
source via Haiman–Sturmfels, *Multigraded Hilbert schemes*, Corollary 1.2
under its applicable grading hypotheses; it is not an automatic assumption
for an arbitrary Hilbert functor. Constant degree-L codimension h(L) makes
ρ(I)=(I_L)⊥ a morphism to Gr(h(L),H⁰(X,L)*). Pull back the universal
subbundle and PROJECTIVIZE it: the incidence variety
U={(I,[v]):I∈Slip,[v]∈P((I_L)⊥)} is closed in
Slip × P(H⁰(X,L)*), hence projective. It is this projectivization, not the
affine total space of a vector bundle, whose projection has closed image.
For I ∈ Sip its fiber is the linear span of the r points. The union of
these spans is dense in σ_r(X), by the source's generic-point/density
argument (proposition on Sip, local number 4.16 in the digest). Closedness
therefore puts every [F] ∈ σ_r(X) in the image. Choose its incidence
preimage: I_L ⊆ (Ann(F))_L. The source's degree-L lifting proposition
(local number 4.12) then gives I ⊆ Ann(F). These projectivity, morphism,
density and graded-apolar lifting assertions are external geometric inputs,
not declarations in this module. BB's extension discussion for other
algebraically closed fields is not silently substituted for the ℂ contract.

Reopen by constructing this incidence/properness bridge and the degree-L
lift over the exact source objects. Polynomial-closure `BorderRankLE` still
needs its bridge to classical secants; modeled111 supplies neither Slip,
smoothability nor a border-rank upper bound. This kernel adds no converse
acceptance certificate and no Borel enumeration completeness claim.
-/
