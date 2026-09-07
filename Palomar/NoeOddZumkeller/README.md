# Noe's odd-Zumkeller statement: exact odd-perfect obstruction

## Candidate status

This directory records a possible Palomar candidate centered on the existing source
`Proofs/Enumerative/NoeZumkellerOdd.lean`. It is a **formalization and clarification
of known mathematics**, not a solution of the odd perfect number problem and not a
claim of new mathematical priority. Human review is pending. The development was
AI-assisted; no human approval, Palomar acceptance, or agent review is claimed.

## Exact result

The source defines a positive natural number `n` to be Zumkeller (`IsZumkeller n`)
when its positive divisors admit a partition into two equal-sum sets. It defines
`IsA174865 n` as: `n` is odd, abundant, and has even abundance. In divisor-sum
notation, this is equivalent to

```
Odd n ∧ 2 * n < σ(n) ∧ 2 ∣ σ(n).
```

Noe's universal statement is `NoeOddZumkeller`:

```
∀ n, IsA174865 n ↔ Odd n ∧ IsZumkeller n.
```

The source separates this into `NoeOddZumkellerForward` (odd Zumkeller implies
A174865) and `NoeOddZumkellerConverse` (A174865 implies Zumkeller), with
`noeOddZumkeller_iff_forward_and_converse`. Its principal structural result is
`noeOddZumkellerForward_iff_not_exists_odd_perfect`:

```
NoeOddZumkellerForward ↔ ¬ ∃ n, Odd n ∧ n.Perfect.
```

The reason is exact. A Zumkeller number is non-deficient and has even divisor sum;
upgrading `2 * n ≤ σ(n)` to strict abundance excludes precisely perfection. In the
other direction, an odd perfect number is Zumkeller by splitting `{n}` from its
proper divisors, but is not abundant. Thus `NoeOddZumkeller.not_exists_odd_perfect`
records that Noe's full biconditional would imply nonexistence of odd perfect
numbers. It does **not** establish that nonexistence.

The source also records the honest boundary repair:
`IsOddNonDeficientEvenSigma` replaces `<` by `≤`, and
`NoeOddZumkellerRepaired` is the corresponding biconditional. The forward direction
`isOddNonDeficientEvenSigma_of_odd_isZumkeller` is unconditional; the converse is
open. The bridge
`noeOddZumkeller_iff_repaired_of_not_exists_odd_perfect` makes the exact conditional
relationship explicit. Auxiliary source declarations identify the repaired claim
with the assertion that OEIS A171641 has no odd term. Concrete source witnesses
include `945` for A174865 and Zumkeller membership, and `738` as the first recorded
A171641 term.

## Attribution and recovered evidence

The source documentation pins the mathematical attribution to T. D. Noe's A083207
comment of 31 March 2010, which reports the finite match between odd Zumkeller
numbers and A174865 below `10^6`. A later Noe comment (14 November 2010) reports
that all 205,283 odd abundant numbers of even abundance below `10^8` were
Zumkeller; this is finite computation, not a universal converse theorem. A174865's
raw record attributes the sequence to Noe, but does not itself contain the
Zumkeller conjecture. The recovered draft and source therefore place the conjecture
on A083207 and make no novelty claim. The companion Neder gap result is a separate
known formalization and is outside this focused candidate.

This recovery read the named Lean source, its `IsZumkeller` dependency, the project
draft, and the saved source/policy ledger. The source text contains open statements
as `Prop` definitions rather than assuming them, and documents no `sorry` behind
the headline. Fresh compilation, proof elaboration, and axiom verification were
intentionally **not run** here, so these are not fresh verification claims.

## Limitations and next obligations

The universal converse remains open, and the forward direction is equivalent to the
open odd-perfect-number nonexistence problem. Finite OEIS checks do not close either
gap. Literature coverage in this recovery is limited to the saved OEIS evidence;
priority and completeness of prior formalizations remain unassessed.

A future prover/package pass must independently inspect the elaborated declarations,
recheck theorem/source alignment, and document axioms and automation without treating
this README as verification. A Palomar package is not prepared: it still needs
separate allowlisted `Challenge.lean` and `Solution.lean` modules, a pinned
`formalization.yaml`, Comparator configuration, and the required manifest/toolchain
and provenance metadata. The existing module imports project-specific
`Enumerative.IsZumkeller`, so Challenge import-closure compliance must be solved by
a wrapper or split rather than assumed. No such package artifacts, Comparator, or
submission have been created in this recovery.
