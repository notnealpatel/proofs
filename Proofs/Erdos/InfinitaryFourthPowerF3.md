# Actual fourth-power f3 exclusion

Production module: `Erdos.InfinitaryFourthPowerF3`.
All symbols below are in namespace `InfinitarySuperperfect`.

## Exact consumer contract

```lean
factorization_sigma_two_ne_three_of_fourth_power
    (n m t : ℕ)
    (ht : 0 < t)
    (hfourth : n = t ^ 4)
    (hm : m = sigma n)
    (hcycle : sigma m = 2 * n) :
    m.factorization 2 ≠ 3
```

Both sums are the existing canonical infinitary divisor sum. The root may be
odd; no evenness hypothesis is added. The intermediate
`factorization_sigma_two_ne_three_of_four_dvd` assumes `0 < n`,
`∀ p ∈ n.primeFactors, 4 ∣ n.factorization p`, `oddPart n % 4 = 1`, and the
same two equations, and concludes the same exclusion.

## Proof route

Every selected forward bit has height at least two. For an odd prime `r`
dividing `1 + p^(2^j)`, the element `(p : ZMod r)` has order exactly
`2^(j+1)`: its `2^j` power is minus one, not one, and its next power is one.
This order divides `r - 1`, hence `r % 8 = 1`. The actual equality
`m = sigma n` therefore derives this residue for every actual odd prime of
`m`; mod-eight forward support is **not assumed** in either consumer theorem.

For every reverse tag, including height zero, this residue makes
`normalizedSlot q h % 4 = 1`. The new, independent valuation-three bridge
`sigma_eq_fifteen_mul_two_pow_reverseCount` reconstructs

```text
sigma m = 15 * 2^(reverseCount m) * reverseProduct m.
```

It uses `localSigma 2 3 = 15`, not the valuation-two/five bridge. Thus the odd
part of `sigma m` is three modulo four. The odd part of a positive whole
square is one modulo four, and a fourth power is a whole square.
Multiplication by two preserves the odd part, so the actual reverse equation
contradicts these residues.

## Boundary and hypothesis-block checks

The module contains checked concrete tests for the occupied bit of exponent
four, the order-eight successor divisor seventeen, normalized height zero,
and a positive odd-root forward example `sigma 81 = 82` with `81 = 3^4`.
The reverse block is jointly realized at `m = 136`: its two-valuation is
three, its actual odd support is `{17}`, and `sigma 136 = 2 * 135`.
Its reverse tag set is nonempty, its count is one, and its normalized product
is nine. The root-one boundary has `sigma 1 = 1` and fails the reverse equation.

These are **separate hypothesis-block witnesses, not a joint actual-cycle
model**. No positive fourth-power cycle is exhibited, and joint satisfiability
of the complete consumer premises is not claimed.

## Producer verification receipt

The completed module and examples passed the narrow target:

```sh
timeout 60s lake -q build +Erdos.InfinitaryFourthPowerF3
```

A separate disposable leaf importing the production module was checked with
`timeout 60s lake env lean -j 1 -M 4000 Proofs/Scratch/F3Probe.lean`.
It checked the full signatures of both consumer exports and printed axioms
for all twelve public declarations. Every dependency set was contained in
`{propext, Classical.choice, Quot.sound}`; the final fourth-power export used
exactly those three. `normalizedSlot_mod_four_of_mod_eight` used only
`{propext, Quot.sound}`. The leaf was removed after this receipt was recorded;
no audit commands are retained in production. No `sorry`, new axiom, or
native computation was introduced.

## Scope and pending independent gates

This proves only the stated conditional actual-cycle fourth-power exclusion.
It does not prove an unrestricted global f3 exclusion, the parent's necessary
prime-support shape, ratio bounds, or the bridge reducing a free-prime exponent
to exactly two. Those upstream implications remain unpaid. No integration,
adoption, global, or `References` edits are part of this pair.

The parent still owns independent literal review of both files and a fresh
import/signature/axiom audit. Producer compilation and the producer audit are
not substitutes for those independent gates.
