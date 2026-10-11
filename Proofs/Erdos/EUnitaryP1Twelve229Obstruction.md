# Exponent twelve, with an even exponent of 229

## Scope and status

`EUnitaryP1Twelve229Obstruction.lean` imports the unchanged
`Erdos.EUnitaryP1TwelveObstruction` module. It proves only the all-even-229-exponent
branch, uniformly in the positive exponent of 3. There is no assertion here about
odd exponents of 229.

The actual consumer is
`EUnitaryP1.sigmaEU_twelve_229_class_ne_of_even`. For natural numbers `b,c,t`
and a finite support `S`, its hypotheses are exactly:

- `0 < b`, `2 ≤ c`, `Even c`, and `0 < t`;
- every member of `S` is prime and differs from 2, 3, and 229;
- `Squarefree t`;
- `Nat.Coprime t (6 * 229 * ∏ q ∈ S, q)`.

Its conclusion is

```text
sigmaEU (t * 2^12 * 3^b * 229^c * ∏ q ∈ S, q^2)
  ≠ 2 * (t * 2^12 * 3^b * 229^c * ∏ q ∈ S, q^2).
```

No identity, valuation, support-size, capacity, or auxiliary certificate is a
hypothesis of this consumer or of the normalized obstruction. The intended
objects, quantifiers, hypotheses, and conclusion survive unchanged. The
multiplicativity/normalization bridge is proved in this module, so there is no
unpaid bridge to the actual consumer. Coordinator review and adoption remain
external to this candidate.

## Public declarations

1. `dvd_localA_229_of_even`: for every even `c` with `2 ≤ c`,
   `230 ∣ localA 229 c`.
2. `localA_229_le`: for every `c` with `2 ≤ c`,
   `localA 229 c ≤ 230 * 229^(c-2)`.
3. `normalized_229_ne_of_even`: under the stated hypotheses on `b,c,S`,
   
   ```text
   2061 * localA 3 b * localA 229 c * ∏ q ∈ S, (q+1)
     ≠ 2^12 * 3^(b-1) * 229^(c-1) * ∏ q ∈ S, q.
   ```
4. `sigmaEU_twelve_229_class_eq`: the checked factorization of the actual
   `sigmaEU` expression for positive `b,c,t` and the support, squarefreeness,
   and coprimality hypotheses above. This infrastructure lemma needs only
   `0 < c`, not evenness.
5. `sigmaEU_twelve_229_class_ne_of_even`: the actual consumer stated above.

## Argument

Complementary unitary exponent divisors `d` and `c/d` form an involution without
fixed points when `c` is even and at least two. They are coprime, and exactly one
is even. Since 229 is minus one modulo 230, the two terms cancel in `ZMod 230`.
This proves the uniform divisibility assertion, not just a finite check of
exponents.

The leading exponent-divisor term and a geometric bound on all the proper terms
prove `localA 229 c ≤ 230 * 229^(c-2)`. The case `c=2` is checked separately.

Assume the normalized identity for contradiction. Divisibility by 230 forces
both 5 and 23 into `S`; primality and the excluded primes rule out every other
factor on its right-hand side. Their successor factors are 6 and 24. Together
with `2061 = 9 * 229`, these imply `81 ∣ 3^(b-1)`, hence `5 ≤ b`.

Write `U = S \ {5,23}` and extract `k` from the proved divisibility, so
`localA 229 c = 230*k`. Cancellation gives the exact residual identity

```text
localA 3 b * k * ∏ q ∈ U, (q+1)
  = 128 * 3^(b-5) * 229^(c-2) * ∏ q ∈ U, q.
```

The local bound gives `k ≤ 229^(c-2)`. The evenness of `localA 3 b` and each
successor factor, together with the oddness of the other right-hand factors,
prove `U.card ≤ 6`. The reviewed support-ratio envelope therefore applies.
Canceling the positive factor `229^(c-2)` from the local-bound inequality yields

```text
128 * 3^(b-5) * ∏ q ∈ U, q
  ≤ localA 3 b * ∏ q ∈ U, (q+1).
```

For `7 ≤ b`, the reviewed uniform base-three tail estimate contradicts this
inequality and the support-ratio envelope. For `b=5`, `localA 3 5 = 82` gives
the contradiction directly. For `b=6`, `localA 3 6 = 256` exceeds the residual
seven-bit two-adic budget. These exhaust all positive `b` compatible with the
assumed identity.

Finally, the actual factorization is proved using coprime multiplicativity,
the existing exponent-twelve factorization, and the prime-power factor for 229.
An assumed actual perfectness identity cancels the positive common factor
`t * 2 * 3 * 229 * ∏ q ∈ S, q` and gives the forbidden normalized identity.

## Translation, boundary, and trust checks

- There are no new definitions, custom instances, or changes to `localA` or
  `sigmaEU`.
- The public natural-subtraction expressions have the required positive
  exponent guards; the local upper bound has `2 ≤ c`.
- Finite supports are actual `Finset ℕ` supports, so distinctness is inherent.
  Empty support is allowed, not silently ruled out.
- Compiled joint-hypothesis examples include `b=1,c=2,t=1,S=∅` and
  `b=1,c=4,t=7,S={5}`. Both are also instantiated through the actual consumer.
  Thus the hypotheses are jointly satisfiable at the smallest allowed
  exponents, and with a nonempty support and nontrivial decoration.
- The normalized boundary case `b=1,c=2,S=∅` is instantiated explicitly.
- All quantified natural-number domains are nonempty. No assumed degenerate
  algebraic instances are involved.
- No finite exponent enumeration is used as a proof of the uniform claim.
- No `sorry`, custom axiom, `native_decide`, compiler override attribute,
  partial definition, or production diagnostic command is present.

## Observed checks and costs

The narrow production build passed without warnings or errors:

```sh
timeout 60s lake -q build +Erdos.EUnitaryP1Twelve229Obstruction
```

Observed wall time: **7.29 seconds**. Receipt:
`/tmp/eunitary-p1229-production-01a127d7.log`.

A separate disposable leaf imported the production module, checked the full
signatures of all five public declarations, and printed their axiom dependencies:

```sh
timeout 60s lake env lean -j 1 -M 4000 Proofs/Scratch/P1229Audit.lean
```

Observed wall time: **2.24 seconds**. Each declaration reports exactly
`[propext, Classical.choice, Quot.sound]`. Receipt, including full signatures:
`/tmp/eunitary-p1229-audit-01a127d7.log`. The diagnostic leaf and the development
probe were removed after checking; neither is imported by production.

The development record has nine bounded Lean/build sequences: six passed and
three exposed subsequently repaired errors. The successful production build and
separate audit above are the completion evidence, not the earlier scaffolds.
These measured checks do not substitute for coordinator semantic review.

The immutable predecessor hashes remained unchanged:

- Lean: `0836d00c6d57d4e22410466ada701802de67c55c20c3622dac650ca631ec6f16`
- Markdown: `4229204fe7cddbfe64c1b147b60367c187e005a5e8668866b52d6f3f9c66ea9a`

Only the new Lean module and this companion are the deliverable candidate. No
ledger, reference artifact, reviewed predecessor, or revision graph was changed.
