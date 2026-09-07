# Mean-divisor parity

## Status

Candidate formalization; human review pending. This README records the recovered
scope and evidence only. It does not claim Palomar acceptance, global priority,
a fresh verification result, or human approval.

## Result and definitions

`Proofs/Enumerative/MeanDivisors.lean` formalizes OEIS A114976. For `n : ℕ`,
`meanDivSubsets n` is the family of nonempty subsets
`S ⊆ {1, ..., n}` for which there is an `m` satisfying

`S.sum id = m * S.card` and `m ∣ n`.

Thus the arithmetic mean of `S` is the integer `m`, and that mean divides `n`.
The multiplicative equation avoids natural-number division. The counted
quantity is `a n := (meanDivSubsets n).card`.

This is **not** a count of subsets of the divisors of `n`. The elements of each
subset range over `{1, ..., n}`; only the permitted mean is restricted to a
divisor of `n`.

The principal formal results are:

- `a_modEq_card_divisors`: `a n ≡ n.divisors.card [MOD 2]`;
- `odd_card_divisors_iff_isSquare`: for `n ≠ 0`, the divisor count is odd iff
  `n` is a perfect square;
- `odd_a_iff_isSquare`: for `n ≠ 0`, `a n` is odd iff `n` is a perfect square;
- `meanDivSubsets_prime`, `a_of_prime`, and `a_eq_two_iff_prime`: the prime
  characterization `a n = 2 ↔ n.Prime`.

Supporting declarations include `IsMeanDiv`, `meanSubsets`,
`mem_meanDivSubsets`, `mem_meanSubsets`, `odd_card_meanSubsets`,
`meanDivSubsets_eq_biUnion`, and `a_eq_sum_divisors`. The file contains 22
named declarations: four definitions, eight non-private lemmas, six theorems,
three private lemmas, and one decidability instance. It also contains 28
anonymous ground examples and 22 explicit `#print axioms` commands.

## Mechanism and attribution

The parity argument uses the mean-toggle involution. For a fixed mean `m`,
adjoining `m` when absent, or removing it from a non-singleton set when present,
preserves the mean. The singleton `{m}` is the unpaired exception, so each
admissible mean contributes an odd number of subsets. Restricting the means to
the divisors of `n` then yields the divisor-count congruence and the
square-parity corollary.

This toggle is not newly discovered here. Putnam 2002 Problem A3 considers
`T_n`, the number of all nonempty subsets of `{1, ..., n}` having an integer
mean, and proves `T_n - n` is even. The published Putnam solution recovered for
this candidate (Kedlaya–Ng, `kskedlaya.org/putnam-archive/2002s.pdf`) explicitly
uses the same toggle. The present development is therefore a formalized
divisor-restricted adaptation, not a revived “first proof” story and not a
priority claim about the involution.

## Contribution and audience

The useful contribution is a precise Lean treatment of the A114976
divisor-restricted object, its partition by unique mean, the congruence with
the divisor-counting function, and the resulting square criterion. It may be
of interest to researchers in enumerative or elementary number theory and to
formalization researchers studying finite involutions and parity arguments.
The source’s finite checks include the initial values
`1, 2, 2, 5, 2, 14, 2, 30, 11, 80` for `n = 1, ..., 10` and explicit families
at `n = 4`.

## Evidence and limitations

The recovered evidence consists of direct reading of the source and the draft
correction, the saved declaration inventory, the OEIS A114976 description, and
the published Putnam solution. The source contains no observed `sorry` text,
but this is not an independent proof audit. A prior 120-second Lean invocation
timed out; no independent compilation pass is recorded here, and no fresh
verification was run.

The parity statements require `n ≠ 0`; `a 0 = 0` is a separate degenerate
case. Ground examples do not establish a general enumeration beyond the stated
theorems. No complete literature or priority search has been established.
The development is AI-assisted, and human review remains pending.

## Next obligations

Before any package or submission decision, a prover should re-elaborate the
pinned source, inspect the principal declaration types and axiom dependencies,
and check that the informal statement preserves the divisor-mean definition.
A package pass must separately prepare and review the Challenge, Solution
bridge, Comparator configuration, and `formalization.yaml` under the current
Palomar policy. Those artifacts are intentionally not included here.
