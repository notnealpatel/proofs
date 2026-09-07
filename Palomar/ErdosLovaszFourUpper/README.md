# Erdős–Lovász: the upper bound g(4) ≤ 9

**Technical status:** Challenge and Solution freshly elaborate in the pinned Lean
4 toolchain. The selected Solution theorem has exactly the three standard axioms
`propext`, `Classical.choice`, and `Quot.sound`. Comparator/export/Nanoda checks
are **NOT RUN** because the executables are unavailable. **USER review is
pending and is the sole review gate.** This is not an acceptance or submission claim.

## Selected result and independent model

```lean
Palomar.ErdosLovaszFourUpper.erdosLovaszNum_four_le :
  Palomar.ErdosLovaszFourUpper.erdosLovaszNum 4 ≤ 9
```

For a finite family `F : Finset (Finset α)`, the model explicitly requires:

1. every edge has cardinality `r`;
2. every two edges intersect, including the diagonal (thus no edge is empty);
3. every finite set of cardinality less than `r` is disjoint from some edge.

The third condition is exactly absence of a cover with fewer than `r` vertices.
For a nonempty intersecting `r`-uniform family, each edge is itself a cover, so
these conditions give covering number `r`. The invariant is the minimum of all
attainable edge counts over **all** finite labelled universes `Fin N`, with no
bound on `N`.

`Challenge.lean` imports **only Mathlib** and defines this complete model. It has
exactly one intentional hole, in the selected theorem. `Solution.lean` does not
import Challenge: it repeats the identical model and theorem statement, proves
predicate, edge-count-set, and invariant equality with the repository definitions,
then applies the already-proved source upper bound. Both files independently prove
that the index set at `r = 4` is nonempty, using the four-subsets of seven vertices;
the result is therefore not about the default value of an empty natural infimum.
The Solution additionally instantiates the independent predicate with the actual
nine-edge witness.

## Source, witness, and scope

Amit Tripathi, **“A result on intersecting families with maximum transversal
size,”** [arXiv:1409.4610](https://arxiv.org/abs/1409.4610) (2014), subsection
**“An Example,”** gives the family

```text
{1,2,3,4},  {1,5,6,7},  {2,5,8,9},
{3,6,8,10}, {4,7,9,10}, {1,8,9,11},
{2,6,7,11}, {3,4,5,11}, {1,2,5,10}.
```

The primary TeX was checked directly in the preceding proof task. The Lean witness
shifts each label by one, from `1,…,11` to `0,…,10` in `Fin 11`.
`Proofs/Erdos/ErdosLovaszFourWitness.lean` proves that there are exactly nine
edges, all have cardinality four, every two intersect, and each of the **165
three-element subsets** misses an edge. The semantic bridge in
`Proofs/Erdos/ErdosLovasz.lean` extends any smaller candidate cover to a triple,
excludes it, and uses `{0,1,2,3}` as an explicit four-vertex cover. This proves
covering number four and the source declaration `erdosLovaszNum_four_le`.

**Only `g(4) ≤ 9` is selected.** The separate archived equality
`tripathi_erdosLovaszNum_four` is not used. Its lower-bound obligation is not
solved or packaged here. This formalizes known mathematics; it makes no novelty,
priority, external-completeness, or author-endorsement claim.

## Package and review boundary

- `Challenge.lean`: Mathlib-only independent problem and one theorem hole.
- `Solution.lean`: repeated independent model, checked source alignment, proof.
- `comparator.json`: same selected fully qualified name, three permitted axioms,
  and `enable_nanoda: true`.
- `formalization.yaml`: v0.4 metadata and disclosed blockers.
- `verification.md`: exact checks, output, provenance, and tooling limitations.

AI assistance was material in the latest proof and packaging tasks, specified by
the USER as **gpt-6-astra, xhigh**, through Yah. Earlier invariant infrastructure
and its exact model/session history were not reconstructed. No subagent or
reviewer was dispatched for packaging. Unknown human formalization authors and
responsible maintainers remain empty in the metadata rather than being invented.
USER mathematical, attribution, and source-fidelity review remains pending.
