# Erdős–Lovász: the exact value g(4) = 9

**Candidate status:** this directory is a review candidate, not a Palomar
submission, registration, acceptance, endorsement, or publication. Narrow Lean
and metadata checks are recorded in `verification.md`. Comparator/export/Nanoda
checks are **NOT RUN** because their executables are unavailable. Independent AI
foundations review of combined candidate
`dcf241b5a1f33b86325e82d575fa588d9a3575e6` found the formal statement and
source adaptation faithful and requested metadata corrections EF-1 and EF-2,
which this revision applies; a final-integration foundations recheck remains
pending. Independent AI vacuity review of that same exact revision passed for
the g(4) package and source proof. The present Lean files have the exact hashes
reviewed, so that vacuity result applies to their unchanged bytes. This is not
human review or approval; `verification.md` records the review scope, evidence,
and witness-recomputation limitation. USER review and the required human author,
maintainer, and authorization decisions remain pending.

## Selected result and independent model

```lean
Palomar.ErdosLovaszFour.tripathi_erdosLovaszNum_four :
  Palomar.ErdosLovaszFour.erdosLovaszNum 4 = 9
```

For a finite family `F : Finset (Finset α)`, the package model explicitly
requires:

1. every edge has cardinality `r`;
2. every two edges intersect, including the diagonal (hence no edge is empty);
3. every finite set of cardinality less than `r` is disjoint from some edge.

The third clause is exactly the absence of a cover with fewer than `r`
vertices. Since any edge of a nonempty intersecting `r`-uniform family is itself
a cover, these conditions say its transversal number is `r`. The invariant is
the natural infimum of **all** attainable edge counts over the finite labelled
ground types `Fin N`, for every `N`; it is not a bounded-ground search or a
property bundled into an unknown invariant.

`Challenge.lean` imports only `Mathlib`, defines this complete model, and has
exactly one intentional hole: the selected equality. `Solution.lean` does not
import Challenge. It repeats the identical model and theorem type in a separate
environment, proves predicate, attainable-count-set, and invariant equality
with the substantive repository definitions, and then applies the accepted
source theorem.

Both files prove that the feasible class at `r = 4` is nonempty using all
four-subsets of seven vertices, so the selected equality cannot be an artifact
of `Nat.sInf ∅ = 0`. Ground checks also accept the one-edge `r = 1` family,
reject the empty family at `r = 1` and at `r = 4` over `Fin 0`, reject a lone
four-edge because it has a one-vertex cover, and prove the honest boundary value
`g(0) = 0`. The Solution additionally proves that Tripathi's actual nine-edge
family satisfies the independently stated predicate and realizes count nine.

## Source and proof fidelity

The canonical source was freshly retrieved outside the repository with
`tool_arxiv`:

> Amit Tripathi, “A result on intersecting families with maximum transversal
> size,” [arXiv:1409.4610](https://arxiv.org/abs/1409.4610) (2014).

The abstract and main theorem state `q(4) = 9`. The final subsection, “An
Example,” gives the nine blocks

```text
{1,2,3,4},  {1,5,6,7},  {2,5,8,9},
{3,6,8,10}, {4,7,9,10}, {1,8,9,11},
{2,6,7,11}, {3,4,5,11}, {1,2,5,10}.
```

`Proofs/Erdos/ErdosLovaszFourWitness.lean` shifts labels to `0,…,10` in
`Fin 11` and proves nine distinct four-element edges, pairwise intersection,
and that every three-subset misses an edge. The substantive bridge proves this
family has transversal number four and hence gives `g(4) ≤ 9`.

Tripathi's lower proof assumes a counterexample with at most eight blocks,
uses degree reduction, identifies a five-block residual with a special family,
and finishes with a global count of vertex pairs. The Lean development follows
the degree-reduction strategy, but `ErdosLovaszFourLower.nine_le_card` replaces
the classification and final global pair count with direct finite incidence
arguments. Its hypotheses are the actual four-uniformity, intersection, and
no-small-cover conditions on a family over an arbitrary type. There is no
finite-vertex normalization, enumeration of candidate families, or assumed
classification. The repository bridges this universal lower result through
attainment of the unbounded `Fin N` infimum to `9 ≤ g(4)` and combines it with
the witness upper bound.

The historical in-source comments point to a missing
`References/Erdos/arXiv-1409-4610/paper.tex`; this package does not pretend that
path exists. Its source account is based on the canonical arXiv TeX retrieved
outside the repository during this task.

Six **unrelated** archived large-parameter/literature declarations in the
imported source still contain `sorry`. They are not used: the selected equality,
the upper and lower bounds, the universal lower helper, and the package bridge
all have standard-only axiom closures. Accordingly, v0.4 `status.sorry_count`
is zero for the selected/package proof: the one deliberate Comparator Challenge
placeholder and the six out-of-scope archives are excluded by that convention.
The selected result uses no unproved literature premise, so
`literature_dependencies` is empty while Tripathi remains the properly
attributed top-level source. This is a nontrivial formalization of known
mathematics. No novelty, first-formalization, priority, or author endorsement
claim is established.

## Package boundary and related work

- `Challenge.lean`: Mathlib-only independent statement; one target `sorry` and
  no definition holes.
- `Solution.lean`: repeated independent model, definitional source bridges,
  witness realization, proof, signatures, and focused axiom reports.
- `comparator.json`: one selected FQN and the three standard permitted axioms.
- `formalization.yaml`: v0.4 self-reporting metadata and explicit blockers.
- `verification.md`: exact narrow checks, source/cache provenance, and checks
  not run.

`Palomar/ErdosLovaszFourUpper/` is narrower related work selecting only
`g(4) ≤ 9`. This candidate neither imports nor modifies it. Nothing under
`Proofs`, `Formalize`, `Plans`, `References`, configuration, dependencies,
shared caches, or any old candidate is changed by this package.

## Automation and review boundary

The substantive exact-value proof was produced in the earlier task with
USER-specified **gpt-6-astra, xhigh**, through Yah. This separate packaging task
used USER-specified **gpt-5.6-sol, high**, also through Yah. No subagent or
reviewer was dispatched for packaging. The parent reports having inspected
diffs and freshly compiled nine substantive modules with 23 axiom audits. An
independent AI foundations review of the combined candidate at exact revision
`dcf241b5a1f33b86325e82d575fa588d9a3575e6` found the formal statement and
source adaptation faithful, subject to EF-1 and EF-2 metadata corrections now
applied; those corrections still await foundations recheck at final integration.
A separate independent AI vacuity reviewer passed the g(4) package and source
proof at the same exact revision. It checked the raw exact target, independent
model bridges, unbounded `Fin N` semantics, genuine nine-edge witness,
arbitrary-type lower bound, and attained minimum, and found no vacuity, drift,
trust, or material style issue. The unchanged current Lean hashes match the
reviewed bytes. The detailed evidence and the unsuccessful, non-evidentiary
attempt to recompute the entire 165-triple witness certificate appear in
`verification.md`. `review.status: unchecked` continues to denote the absence
of human review; neither AI review is human approval. Unknown human
formalization authors and responsible maintainers remain empty rather than
being invented.

Before any submission, the USER must supply truthful human author and
responsible-maintainer metadata, establish the submitter's maintainer status or
document approval from a responsible person, review mathematical/source
fidelity, and decide whether to authorize the external and permanent steps. No
external action was taken here.
