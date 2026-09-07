# A092482: greedy sequence with exceptional initial progression

## Candidate status

This is a review candidate, not a Palomar submission or acceptance claim. Human review is pending. The development concerns OEIS A092482: the increasing greedy sequence beginning `1, 2, 3` that permits the initial progression `(1,2,3)` and permits no other 3-term arithmetic progression. The Lean source is `Proofs/Enumerative/No3APGreedy.lean`; it imports `Enumerative.StanleyDigits`.

## Exact result and indexing

The formalization is zero-indexed: `greedySeq n = A092482(n+1)`. Its closed form is expressed using `binToTernary`, the value obtained by reading the binary expansion of an integer as a base-3 numeral (equivalently, the zero-offset form of OEIS A005836). The principal pointwise theorem is:

```lean
theorem greedySeq_add_two (m : ℕ) :
    greedySeq (m + 2) =
      1 + 2 ^ Nat.log 2 (m + 1) + binToTernary (m + 1)
```

The equivalent function theorem is `greedySeq_eq_closedForm`. The source also records the corrected sum identity, without natural-number division, in `two_mul_binToTernary_eq_sum`. The OEIS formula had a summand-index typo (`n` where `k` is required); its displayed A005836 equality also needs the zero-offset interpretation used here. The first terms are `1, 2, 3, 6, 7, 14, 15, 17, 18, …`.

A block formulation makes the indexing explicit. Define `blockStart L = 2^L + 3^L + 1` and let `Tset L` consist of offsets below `3^L` whose ternary digits are all `0` or `1` (equivalently, the range of `binToTernary` on indices below `2^L`). Then the proposed value set is

```text
{1, 2} ∪ ⋃ L, (blockStart L + Tset L).
```

The principal supporting declarations are `closedForm_eq_block`, `noThreeAPExceptSeed_Vset`, `exists_blocking`, `q_covering`, `prefixSet_two`, `range_greedySeq`, and `greedySeq_strictMono`. Together they express admissibility, blocking of every omitted candidate, the inter-block covering induction, and recovery of the exceptional seed from the greedy recursion.

## Contribution and attribution

This appears to be a formal proof of the OEIS closed form, rather than a new conjectural formula. OEIS A092482 attributes the formula entry to Jean-François Alcover (15 January 2019) and labels it “conjectured and checked up to n=512.” The recovered source and published proof note describe a blockwise proof: each block is a translate of the initial ternary-digit `{0,1}` Stanley block, while the exceptional seed produces the unbounded `2^⌊log₂ n⌋` displacement. The standard digit argument supplies within-block witnesses; `q_covering` handles the gaps between blocks.

A093682 must not be conflated with this result. It is a related array of sequences with different initial seeds and conjectured periodic corrections; A092482 is not one of its rows. The recovered materials report no published proof found, but that is only an incomplete literature search and establishes no priority. Existing Stanley-sequence literature provides context for the digit argument, but ordinary Stanley-sequence machinery does not directly apply because `{1,2,3}` is not 3-AP-free.

## Evidence, limitations, and remaining obligations

The evidence recovered here is the named Lean source and the published explanatory note. No fresh Lean compilation, axiom inspection, comparator run, or independent proof audit was performed for this candidate. The README therefore makes no claim of current verification, permitted axioms, global priority, Palomar acceptance, or human approval. The exact dependency versions and package state still need recording.

Before any submission decision, a prover should replay the source in the pinned environment, confirm the imports and principal theorem statements, inspect the complete dependency/axiom profile, and check that the source has no proof gaps. A package preparer must then draft a small Challenge and Solution bridge, an allowed-import Comparator configuration, and `formalization.yaml`, matching the current Palomar policy. Those artifacts are intentionally absent here; their statements, dependency constraints, and independent-checker results require separate review. Literature attribution and the A093682 distinction also need human confirmation.