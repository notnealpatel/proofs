# Squarefree middle binomial coefficients: bounded odd range

**Status:** the independent Challenge and proved Solution compile separately in
Lean. The selected Solution theorem's axiom audit passes. Comparator and its
external verification tools were **not run** because their executables are
unavailable. **USER review is pending and is the sole review gate.**

## Exact result

The package selects exactly

```lean
Palomar.SquarefreeBinomialOddRange.not_squarefree_choose_half_of_odd :
  ∀ {n : ℕ}, Odd n → 72 ≤ n → n < 10 ^ 8 →
    ¬ Squarefree (n.choose (n / 2))
```

Here `n / 2` is natural division by the fixed positive integer `2`, hence
`floor(n/2)`. All mathematical constants are the ordinary Mathlib ones; there
are no package-defined predicates, alternate arithmetic structures, or hidden
certificate hypotheses. Both files check joint satisfiability at `n = 73`.
Their elaborated theorem types, including their instance arguments, were
exported as raw Lean expressions in separate environments and matched exactly.

This is **only the odd part of the bounded range `72 ≤ n < 10^8`**. It does not
prove an unbounded nonsquarefreeness theorem, classify all thirteen listed OEIS
terms, settle the excluded indices below `72`, or select the combined even-and-odd
Noe theorem.

## Source and mathematical attribution

The repository source is
`Proofs/Erdos/Erdos175/SquarefreeCentralBinom.lean`, specifically
`Erdos175.A046098.not_squarefree_choose_half_of_odd`, at source revision
`55ab7d253f32b9632581cf31cc4951c2b2119533`. `Solution.lean` is a direct bridge to
that theorem, not a second independent implementation of its proof.

The source pins [OEIS A046098](https://oeis.org/A046098), whose entry concerns
indices for which the middle binomial coefficient is squarefree. Its quoted
comment is **“No other n < 10^8. - T. D. Noe, Apr 06 2007.”** The selected result
is the restriction of that finite computational assertion to odd indices at
least `72`. This attribution is inherited from the source's recorded OEIS pin;
packaging did not perform a fresh external source or literature review.

The Lean proof does not trust Noe's computation as an axiom. For
`m = n/2 + 1`, it uses `2 * C(n,n/2) = centralBinom m`. If the binary digit sum
of `m` is at least three, the existing 2-adic identity gives a factor `4` in
the middle binomial. Otherwise, a strong-induction argument reduces positive
`m` to a power of two or a sum of two distinct powers. The bounded range makes
all exponents less than `26`, leaving 331 values. The dedicated helper
`SquarefreeCentralBinomResidual.lean` checks Kummer digit-sum certificates at
`3`, `5`, or `7` by ordinary `decide`. Its fuel-indexed digit sum is proved equal
to Mathlib's digit sum under an explicit bound. These odd-prime square factors
survive halving. No enormous binomial coefficient is evaluated.

## Trust boundary

Fresh compilation of the Solution reports exactly

```text
[propext, Classical.choice, Quot.sound]
```

There is no `sorryAx`, native-computation axiom, or custom axiom in the selected
closure. The Challenge has exactly one intentional theorem `sorry` and no
placeholder definitions. It imports only two Mathlib modules and neither the
project proof nor the Solution. The Solution does not import the Challenge.

The imported source module also contains an **unchanged even branch** depending
on `Erdos175.witness_cert`'s earlier native certificate axiom. Its combined
`noe_not_squarefree_choose_half` theorem consequently inherits that axiom.
Neither result is selected here, and the fresh selected-theorem audit confirms
that this dependency does not enter the package theorem.

## Assistance, metadata, and review

Implementation of the bounded residual and this packaging used **gpt-6-astra
with xhigh reasoning**, through Yah. Prior infrastructure was reused; its
precise model and session history were not reconstructed. No human
formalization-author or responsible-maintainer identity has been established,
so those lists remain empty in `formalization.yaml`. The project license is
recorded as MIT based on the repository's `LICENSE`; no external source license
is asserted.

No subagent or external review phase was used. USER remains the sole reviewer.
The technical checks are not mathematical or source-fidelity approval, and no
novelty, priority, acceptance, or submission claim is made. See
[`verification.md`](verification.md) for commands, source/cache provenance,
exact axiom output, and the unavailable-tooling limitations.
