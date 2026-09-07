# Palindrome rows of A267632

## Result

`Proofs/Enumerative/PalindromeRows.lean` formalizes the subset-counting triangle A267632. In namespace `A267632`,

- `rowSubsets n k` is the filtered family of `k`-element subsets `S ⊆ Finset.range n` satisfying
  `n ∣ ∑ i ∈ S, (i + 1)`;
- `T n k := (rowSubsets n k).card`.

Thus the encoded labels `i ∈ range n` represent `{1, …, n}` by `i ↦ i + 1`. For `1 ≤ k ≤ n`, `T n k` is the A267632 entry counting `k`-subsets of `{1, …, n}` whose ordinary label sum is divisible by `n`. The “truncated row” is `(T n 1, …, T n (n - 1))`, excluding the final entry.

The principal results are:

- `T_symm_of_dvd_total`: if `n` divides `1 + ⋯ + n`, then
  `T n k = T n (n - k)` for every `k ≤ n`, by complementation;
- `T_symm_of_odd`: for odd `n` and `k ≤ n`,
  `T n k = T n (n - k)`. Hence every odd row is palindromic after deleting its last entry, and this symmetry also includes the endpoint indices `0` and `n`;
- `T_symm_of_two_pow`: for `1 ≤ k < 2^j`,
  `T (2^j) k = T (2^j) (2^j - k)`. This is exactly the truncated-row claim for positive powers of two.

The strict power-of-two bounds are material. For `j > 0`, `T (2^j) (2^j) = 0` while `T (2^j) 0 = 1`, so the full row is not generally palindromic. For `j = 0`, the truncated row has no indices; `T 1 0 = T 1 1 = 1` is checked separately.

## Bijection

`Proofs/Enumerative/PalindromeRowsBijection.lean` is a standalone development. It defines `translateSet`, `complementTranslate`, `zeroSumSubsets`, and the explicit equivalence `complementTranslateEquiv`. The residue bridge uses `shiftedResidueSet` to identify the exact shifted natural subset predicate with zero-sum subsets of `ZMod n`; this is recorded by `shifted_row_card_eq_zeroSumSubsets`.

For `n = 2^j`, `j > 0`, and `0 < k < n`, the development obtains `t : ZMod n` with
`k * t = 2^(j-1)` in `ZMod n`. The forward map is complement in the whole residue group followed by translation by `t`; its inverse is complement followed by translation by `-t`, using the same chosen parameter. The resulting declarations are `zeroSumSubsets_card_symm_two_pow` and `shifted_row_card_symm_two_pow`.

## Attribution and contribution

OEIS A267632 records the row object and describes the truncated-row palindrome for odd `n` or powers of two as an “observation-conjecture.” The mathematical object and observation therefore are not presented as new. The odd complement argument is elementary. The power-of-two complement-plus-translation construction is formalized here as an explicit `ZMod` bijection; no priority claim is made.

The bounded repository search found no other direct formalization of A267632, its zero-sum row families, or this power-of-two map beyond the two source files named above. Bounded web searching likewise found no independently verifiable matching Lean development. This is not evidence of global priority. OEIS comments report related counting attributions to Barnes (1959) and Ramanathan (1944), but those primary works were not independently audited here. Generic Mathlib results such as `Nat.choose_symm` concern ordinary binomial rows, not this triangle.

## Limitations and status

This README records recovered declarations and provenance; it is not an independent proof audit. No fresh Lean verification was run during recovery. Human review remains pending, and no Palomar acceptance, approval, registration, or global novelty claim is made.

Before any package or submission work, a prover/package pass must prepare a small Challenge/Solution bridge, comparator configuration, `formalization.yaml`, source and authorship metadata, licence information, and allowlisted pinned imports. Those artifacts were intentionally not created in this recovery. The exact source files, their hypotheses, endpoint restrictions, and the distinction between the known OEIS observation and this formal packaging must be checked again as part of that later verification.
