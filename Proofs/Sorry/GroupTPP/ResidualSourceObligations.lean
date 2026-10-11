/-!
# Group-theoretic residual source obligations: documentation archive

## Current archive status and scope

This is a documentation-only module in `Sorry/`, not a formal statement,
proof, admission, or complete formalization. Source citations and historical
status are preserved, not certified by comment compilation. No group action,
classification, exhaustive table, or asymptotic object is constructed here.
The card's blanket hard-blocked status is historical; the source inspection
qualification below records an existing right-quotient result without editing
the card or claiming a complete source audit.

## Remaining obligations, hypotheses, conventions, and missing data

The historical subsection lists all eleven exact source identifiers and
retained targets. In particular, preserve the maximal-TPP extremal hypotheses
of Murthy's additive bound (0908.3671); the equality, isoclinism, and odd-order
threshold hypotheses of Nath–Das (1009.5526); and Yadav's central-index,
Property-A, class-2 and prime-group restrictions (1011.2083). Existing class-2
infrastructure does not establish a classification up to isoclinism.

For 1104.5097 Tables 1–4, the missing certificate must cover the entire search
universe, nonabelian-group representatives, normalization, equivalences,
and all reported ratios. Search predicates or individual examples do not
certify exhaustiveness. Hedtke's 1107.5969 subgroup capacity target needs the
precise `h(G)` convention, subgroup-core and quotient hypotheses. For
1204.4641, retain the rank-bounded central-quotient hypotheses and both the
derived-group bound and supporting classification; adjacent rank APIs are
not that theorem.

For 1411.0848, the commuting-probability limit points and well-ordering
conclusions require the exact spectrum topology/order and bilinear-map
structural input. For 2112.08681, Theorems A–C concern p-elements, normal
abelian Sylow characterization, the simple-group equality case, and the
centralizer-ratio bound; ordinary commuting probability is a different
object. For 2512.16730, Conjecture 5.1 remains a conjectural extension, not a
proved consequence of the abelian-normal-prime-index `rho₀` bound. For
2605.02071, exact higher-commutativity asymptotics, finite spectrum and inverse
finite-spectrum rigidity remain beyond elementary propositions.

The card does not state the full formulas, threshold values, parameter ranges,
or classification lists for these targets. Recover those and source revisions
before choosing formal signatures. This archive does not invent them, change
the group domains, or silently add hypotheses to make a target easier.

## Existing pieces and a qualification of historical status

`Proofs/GroupTPP/CommProbBound.lean` describes the strengthened ordinary
commuting-probability lower bound, not the full equality/classification package.
`Proofs/GroupTPP/IsoclinismInvariants.lean` warns that raw conjugacy-class count
and noncentral-class count are NOT isoclinism invariants: abelian direct
products scale them. Do not substitute those false invariants for the intended
source result; normalized ratios have a different scope.
`Proofs/GroupTPP/MurthyPrimeIndex.lean` describes the finite abelian normal
subgroup of prime index `p` bound `(2p-1) β₀(G) ≤ p² |G|`, for subgroup TPP,
not Conjecture 5.1. `Proofs/GroupTPP/HigherCommProb.lean` describes elementary
product, monotonicity, submultiplicativity, and quotient results, not the
source's asymptotic and spectrum conclusions.

The preserved 1107.5973 bullet asks for the subgroup right-quotient extension
bound. At this base `Proofs/GroupTPP/RightQuotientGrowth.lean` already contains
`rightQuotient_insert_card_bounds`: for `[Group G]`, a subgroup `X` with
`[Fintype X]`, and `c ∉ X`, adjoining `c` to its carrier gives a right quotient
of size between `2 * Fintype.card X` and `3 * Fintype.card X`. Its convention
is `x * y⁻¹`, and it includes nonempty-carrier and small examples. Thus this
part is not merely finite experimental evidence or wholly missing in source.
What remains for that historical item is comparing the exact source convention
and hypotheses and identifying the named consumer; no TPP-preservation theorem
is asserted by this size bound. We inspected this declaration and proof text
but did not rebuild it or perform a new axiom/source audit in this migration.
None of these adjacent results validates the other named residuals.

## Historical/source-card subsection — complete current card verbatim

# Group-theoretic residual source obligations

This card retains distinct unresolved formalization targets from the deleted source digests. Adjacent definitions or elementary lemmas do not discharge these source-level results.

- **arXiv:0908.3671 — Murthy additive bound.** Prove the source's unresolved lower additive bound for maximal TPP triples, with its exact hypotheses and extremal cases. The current TPP API does not validate the full source statement.
- **arXiv:1009.5526 — commuting-probability results.** Formalize the Nath–Das lower-bound equality characterization, the associated isoclinism invariance, and the odd-order classification at the stated threshold. `Proofs/GroupTPP/CommProbBound.lean` and `Proofs/GroupTPP/IsoclinismInvariants.lean` provide ingredients, not the complete source results.
- **arXiv:1011.2083 — central-index/class-2 classification.** Formalize Yadav's central-index bound and the Property-A class-2 `p`-group classification up to isoclinism. Existing class-2 and isoclinism infrastructure does not establish this combined theorem.
- **arXiv:1104.5097 — exhaustive Tables 1–4.** Reproduce and validate the finite nonabelian-group TPP capacity tables, including the search universe, normalization, and all reported ratios. Existing search predicates are not an exhaustive certificate.
- **arXiv:1107.5969 — subgroup capacity.** Formalize Hedtke's `h(G)` bound and its dependence on subgroup cores and quotient data; existing subgroup-TPP definitions do not prove the capacity theorem.
- **arXiv:1107.5973 — right-quotient growth.** Prove the `2|X| ≤ |Q(X∪{c})| ≤ 3|X|` extension lemma and its exact subgroup hypotheses, rather than relying on finite examples.
- **arXiv:1204.4641 — rank-boundedness/classification.** Formalize the rank-bounded derived-group theorem and the supporting classification for finite groups with bounded central quotient rank. The current group-rank APIs do not provide the source theorem.
- **arXiv:1411.0848 — commutativity spectrum.** Formalize the Eberhard/Joseph limit-point and well-ordering results for commuting probabilities, together with the bilinear-map structural input. The existing finite commuting-probability bounds are only prerequisites.
- **arXiv:2112.08681 — `p`-element commuting probability.** Formalize Theorems A–C, including the normal abelian Sylow characterization, simple-group equality case, and centralizer-ratio bound. `Proofs/GroupTPP/CommProbBound.lean` does not contain these `p`-element results.
- **arXiv:2512.16730 — Conjecture 5.1.** Formalize the unresolved dihedral/abelian-normal-subgroup-of-prime-index conjectural extension beyond the proved `rho₀` bounds and lemmas. The existing `Proofs/GroupTPP/MurthyPrimeIndex.lean` results do not settle Conjecture 5.1.
- **arXiv:2605.02071 — higher-commutativity asymptotics.** Formalize the exact asymptotic and finite-spectrum theorem, including inverse finite-spectrum rigidity, beyond the elementary isoclinism propositions currently present.

**Status:** hard-blocked. These are named residuals, not bibliography claims or completion claims. The source references above are the exact scopes retained from their deleted digests.

-/
