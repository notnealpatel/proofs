# Power-of-two ternary digit counts

## Status and scope

This is a recovered Palomar candidate description for the counting/sieve development in
`Proofs/Enumerative/PowerOfTwoDigitsCount.lean`, with context from
`PowerOfTwoDigits.lean` and `PowerOfTwoDigitsBarrier.lean`. The candidate is a
formalization of an unconditional counting result, not a solution of Erdős #406. The
Palomar package, exact published commit, human review, and fresh verification are still
pending.

The ambient set is
`erdos406Set = {n : ℕ | Base3ZeroOne (2 ^ n)}`. Here `Base3ZeroOne m` means that every
base-3 digit of the *value* `m` is at most 1. The archived `Conjecture` is the open
statement that this set is finite (the source examples have exponents `0, 2, 8`, not
`0, 1, 2`). Nothing below proves that conjecture.

## Exact result and principal declarations

The new counting layer defines `SieveAt D n` as the bounded condition that the lowest
`D` ternary digits of `2 ^ n` are at most 1, and
`sieveClasses j : Finset ℕ` as the exponent residues in `range (2 * 3 ^ j)` that pass
`SieveAt (j + 1)`. Its principal theorem is:

* `card_sieveClasses (j : ℕ) : (sieveClasses j).card = 2 ^ j`.

The supporting `card_sieveClasses_succ` gives the two-of-three lift at each depth, while
`two_pow_two_mul_three_pow` supplies the period divisibility. The explicit initial
classes are recorded by `sieveClasses_zero` through `sieveClasses_three` (sizes
`1, 2, 4, 8`, with periods `2, 6, 18, 54`). The count is a count of **admissible
exponent residue classes**, not a claim that every `{0,1}` ternary string is attained by
a power of 2, and not a count of the unresolved members of `erdos406Set`.

The resulting unconditional window estimate is
`card_erdos406_filter_le (N j)`: the number of members of `erdos406Set` in
`Finset.range N` (therefore `n < N`) is at most
`2 ^ j * (N / (2 * 3 ^ j) + 1)`. The optimized form is
`card_erdos406_filter_le_log`, and the real form is
`card_erdos406_filter_le_rpow (N : ℕ) (hN : 1 ≤ N)`, with bound
`2 * (N : ℝ) ^ Real.logb 3 2`. The hypothesis and boundary convention are material.

The barrier file records the sharper interpretation: `orderOf_two_zmod_three_pow`,
`sieveAt_iff_mod_mem_sieveClasses`, `card_range_mul_filter_sieveAt`, and
`exists_two_pow_mod_eq_of_base3ZeroOne` show that every fixed finite-depth sieve is
periodic, has exactly the counted surviving classes, and admits finite-depth “fake”
solutions. `base7TwoFour_eighteen_pow_iff` is a separate contrast example, not part of
the Erdős #406 claim.

## Attribution and contribution

The parent source pins Erdős problem 406 and its references. The real bound is the
`λ = 1` specialization of Lagarias, *Ternary expansions of powers of 2* (2009),
Theorem 1.4, with the same constant 2 and exponent `log₃ 2`; Narkiewicz’s sharper
constant 1.62 is not formalized. The contribution should therefore be described as a
new formal development of the exact survivor-class recurrence, its natural-number window
bounds, and the finite-depth barrier around a known counting theorem—not as new
mathematics or a priority claim.

Recovered source evidence reports a `sorry`-free development, kernel-checked examples,
and end-of-file `#print axioms` commands. This recovery did not run Lean, a build, or a
fresh axiom audit; those reports remain source evidence rather than current verification.

## Limitations and next obligations

The full conjecture remains open; the bound grows with `N` and cannot establish
finiteness. Narkiewicz’s constant, Saye’s much larger computational range, and any claim
that the three known exponents are exhaustive are outside this result. No Palomar
acceptance, global-priority, fresh-verification, or human-approval claim is made.

Before packaging, a prover must pin an exact repository commit and re-check the three
Lean modules and their dependency/axiom surface in the pinned environment. A package
owner must then prepare the policy-required Challenge, Solution bridge, Comparator
configuration, and `formalization.yaml`, with allowlisted Challenge imports, license and
provenance/prior-formalization notes, and explicit AI and human-review disclosures.
Human review is pending; no agent review is required for this recovered README.
