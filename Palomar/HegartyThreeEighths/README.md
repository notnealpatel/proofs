# Hegarty’s three-eighths bound for OEIS A094870

**Status:** recovered candidate description; human review pending. This is a
formalization of published mathematics, not a claim of a new theorem or of
Palomar acceptance.

## Exact result

`Proofs/Enumerative/HegartyThreeEighths.lean` proves

```text
A094870.hegarty_three_eighths :
  ∀ n : ℕ, 3 * (n + 1) ≤ 8 * A094870.a n
```

The repository uses zero-indexing: `A094870.a n = πg(n+1)`, where `πg` is
Hegarty’s greedy permutation. Thus, with the paper’s one-based index
`N = n + 1`, the theorem is exactly `3N ≤ 8πg(N)`, or
`πg(N)/N ≥ 3/8`.

The supporting definition in `HegartyPermutation.lean` is
`A094870.a n := nextTerm (pre n)`. Here `pre n` is the reversed prefix of
earlier values, `IsCandList` expresses positivity, non-reuse, and avoidance
of the relevant three-term arithmetic progression, and `IsCand` is the
corresponding index-level predicate. `isCand_a` and `isLeast_a` establish the
greedy characterization; `a_injective` and `one_le_a` provide the permutation
infrastructure.

The three-eighths proof uses the paper’s counting strategy. It sets
`v = a n` and `K = 8v/3`, partitions `range K` according to whether values
exceed `v`, and uses `blockIdx` to witness the rejection of `v` by the greedy
rule. The resulting image sets are shown injective, separated by parity, and
contained in the prefix. The public auxiliary declaration
`card_filter_range_mod_two_eq_le` supplies the parity count. The imported
`two_mul_a_lt` is Hegarty’s proved upper bound
`2 * a n < 3 * (n + 1)`. The source reports that the published counting
argument has a parity-word typo after equation (6): the excluded values must
have parity opposite to `n`; the formal proof follows that corrected reading.

## Attribution and contribution

The primary source is Peter Hegarty, “Permutations Avoiding Arithmetic
Patterns,” *Electronic Journal of Combinatorics* 11 (2004), R39,
DOI [10.37236/1792](https://doi.org/10.37236/1792), Theorem 3.3. OEIS
A094870 records the sequence, the `3n/8 ≤ a(n) < 3n/2` bounds, and Hegarty’s
limit conjecture. The repository evidence supports a new Lean/Mathlib
formalization of Hegarty’s published theorem, not new mathematics. The
repository history records the companion development as prior in-repository
formal work; no exhaustive external-priority claim is made.

## Recovered evidence and limitations

The source comments pin the OEIS rule, attribution, indexing translation, and
paper excerpts. The ledger records retrieval of the journal landing page and
OEIS metadata. The referenced `References/doi-10.37236/1792/paper.txt` is
absent from this workspace, so page-level quotations and the parity correction
are inherited repository evidence rather than independently checked here.

`HegartyPermutation.lean` explicitly documents Hegarty’s open Conjecture 3.2:
`a(n)/(n+1) → 1`, represented by `A094870.conj_3_2` with an intended
`sorry`. This limit is not the result proposed here. Because the target
imports that module, package verification must inspect the dependency closure
and imported `sorryAx`; this README makes no fresh axiom or proof-audit claim.

No Lean elaboration, compilation, tests, or fresh verification were run under
the recovery instructions. The candidate therefore has verification status
**not run**, not passed. Human review remains pending.

## Next obligations

A prover should independently check theorem/index alignment, the corrected
parity interpretation, and the imported dependency status. If review
continues, the package must prepare a small independent Challenge, a proved
Solution bridge, one Comparator configuration, and `formalization.yaml` under
the current Palomar allowlist. Those artifacts, any dependency isolation, and
the source-text gap require review before any submission decision.
