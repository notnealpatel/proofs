# Exponent-twelve obstruction with arbitrary other prime exponents

## Scope and contract

This unit imports only the accepted `Erdos.EUnitaryP1TwelveObstruction`
and `Mathlib.NumberTheory.Padics.PadicVal.Basic`. The canonical definitions of
`exponentDivisors`, `localA`, and `sigmaEU` are unchanged. No unadopted 229
or 229Odd module is imported, copied into the repository, or modified.
Write `A(p,a) = localA p a` and `L(p,a) = A(p,a)/p^(a-1)`.

The checked actual consumer is

```lean
theorem EUnitaryP1.sigmaEU_twelve_ne (n : ℕ) (hn : 0 < n)
    (ha : n.factorization 2 = 12) : sigmaEU n ≠ 2*n
```

There is no restriction on any other exponent, no assumed representation,
no support cap, and no supplied capacity or certificate. Both actual
hypotheses are jointly instantiated at `n = 2^12` in the production file.

The checked normalized consumer `normalized_general_229_ne` excludes

```
2061 A(3,b) A(229,c) ∏[q∈S] A(q,e(q))
  = 2^12 3^(b-1) 229^(c-1) ∏[q∈S] q^(e(q)-1)
```

for `b ≥ 3`, `c ≥ 2`, a finite distinct support of primes other than
2, 3, and 229, and `e(q) ≥ 2` on that support. There is no assumed exponent
parity, capacity, support cardinality, or certificate. Exponents need not
be bounded. This is an exponent-twelve result, not a classification of
all exponential-unitary perfect numbers.

## General local estimates

The module proves `(p+1) | A(p,a)` when `a ≥ 2` is even, using the
complementary-unitary-divisor involution modulo `p+1`. The divisor pair
has opposite parity and contributes zero; a fixed point would force a
unitary divisor pair to both equal one, contradicting `a ≥ 2`.

For `p ≥ 2`, `a ≥ 2`, it proves
`A(p,a) ≤ (p+1)p^(a-2)`. For odd `a ≥ 3`, the sharper bound is
`A(p,a) ≤ p^(a-1)+p^(a-3)`. Proper unitary divisors are bounded through
the complementary divisor, and their distinct shifted exponents are
bounded by a geometric sum. The small exponents two and three are
handled exactly. All natural subtractions in these estimates are
protected by the stated exponent bounds.

## Actual-cost envelope

Let `r = 23/22` and `w(q) = v₂(A(q,e(q)))`. The costs are the valuations
of the actual local factors, not merely of their successors. Every active
odd-prime factor is even, so `w(q) ≥ 1`.

For even exponents, successor divisibility gives `w(q) ≥ v₂(q+1)`.
Outside `E = {5,7,13,17}`, the successor ratio obeys
`(q+1)/q ≤ r^v₂(q+1)`. For each exceptional prime put
`C(q) = ((q+1)/q)/r^v₂(q+1)`; all four corrections are at least one.
For odd exponents, the sharper local bound gives
`L(q,e(q)) ≤ 26/25 < r ≤ r^w(q)`, including the exceptional bases.

The finite-product comparison inserts each missing correction at most
once (the support is a finset), and works for empty supports and low
costs as well. Under `∑w(q) ≤ 10` it yields

```
∏ L(q,e(q)) ≤ 30222828/16178305.
```

If five is absent or has odd exponent, its correction is not needed:

```
∏ L(q,e(q)) ≤ 57927087/35592271.
```

In particular this argument does not identify an odd exponent at five
with exponent three, nor assume its valuation is one. Higher odd
exponents, including fifteen, are covered.

## Capacity and the three cases

Capacity is derived from the purported normalized identity. The factors
at three and 229 each consume a factor of two, while the odd right-hand
bases are coprime to two. Thus `∑w(q) ≤ 10`. If `b = 6`, the exact
`A(3,6) = 256` improves this to `∑w(q) ≤ 3`, hence `S.card ≤ 3`.

* If `b ≥ 4` and `b ≠ 6`, `A(3,b)/3^(b-1) ≤ 28/27`.
  Together with `A(229,c)/229^(c-1) ≤ 230/229` and the full envelope,
  the normalized left-hand ratio is strictly less than 4096.
* If `b = 6`, each local ratio is bounded by its successor ratio and
  the three-prime bound is `576/385`; with `256/243` and `230/229`
  this again contradicts the identity.
* If `b = 3`, `A(3,3) = 10` forces five into the active support.
  An even exponent there would make its factor divisible by six.
  Together with the factor nine in 2061 this would put `3^3` on the
  left, but the right has exactly `3^2`. Therefore its exponent is odd.
  Use the five-deletion envelope and the three-ratio `10/9` to obtain
  the strict contradiction.

All rational comparisons are checked by Lean. The Sage verifier is
motivation and finite evidence, not a trusted universal proof.

## Actual-factorization bridge

The bridge is complete. For positive `n`, let `F = n.primeFactors` and
`T = F.filter (fun p => 2 ≤ n.factorization p)`. Every exponent on `F` is
positive. Factor the product of every prime base out of both the actual
`sigmaEU` product (using `local_sum_eq`) and the fundamental factorization
of `n`. That common product is positive, so cancellation yields the
normalized identity over `F`. Off `T`, the exponent equals one and both
normalized factors equal one (`localA_one` and `p^0=1`), so the same
identity holds over `T`. No auxiliary representation of `n` is assumed.

Strip two using its actual exponent twelve and `localA_two_twelve`.
Prime-divisibility of the resulting identity forces three and 229 into
the active support. Remove those two bases to form `S`. The factor nine
in 2061 and coprimality of all remaining right-hand bases with three
force `3 ≤ n.factorization 3`. Apply `normalized_general_229_ne`.
Thus exponent-one decoration is canceled before any forced-prime inference.
There is no remaining upstream bridge for this exponent-twelve theorem.

## Recovery and extraction provenance

Starting pair recovered from immutable checkpoint
`e27517478109b46896d19521ad5e69e27d2accda`:

* General Lean SHA256:
  `a2cd46107b66b40d3a8809c822e8c4b45597e6744c5421cdcd17edf17db43ea2`.
* General Markdown SHA256:
  `70a65a9098f9b4bb340b1da5a58ef2c9e11e583656e17edb75b048a78118cf17`.

Both recovered hashes were compared to `jj --ignore-working-copy file show`
at that exact checkpoint. The accepted base is
`37086e5a0657b03da8abf37bc78a3168f89efef5`.

The two scoped private proofs `localA_even_of_prime_ne_two` and
`successor_ratio_le_of_card_le_three` were extracted from the checkpoint's
229Odd source (original declaration/proof ranges 126–155 and 249–300;
the accompanying examples are included as satisfiability checks).
The recovered 229Odd source SHA256
`895edb1bb749a12f6f46398302fb3d8a65a42fd855bb80c4b38fa068922ee996`
was also compared to the exact checkpoint. These are local proof
extractions, not an unadopted dependency. The old `localA_229_le` call
was replaced by `localA_le 229 c (by decide) hc`, proved in this module.
No other inherited dependency was needed.

The complete preserved mathematical argument was read before work:
`/tmp/eunitary-a12-maximal-01a127d7.md`, SHA256
`1e06cff4cb5ceac5a7ac10c1bb84d6fda95af8b1d3c491c39be861f5b60dc5ee`.
No new mathematical premise or repair was required. Changes to the recovered
proof are dependency infrastructure and concrete non-vacuity examples;
the actual consumer's quantifiers, hypotheses, canonical objects, and
conclusion are unchanged.

## Producer checks and boundaries

The final narrow module build succeeded:

```text
timeout --kill-after=2s 60s lake -q build +Erdos.EUnitaryP1TwelveGeneralObstruction
```

A separate temporary leaf importing the built module was run with
`timeout --kill-after=2s 60s lake env lean -j 1 -M 4000`.
It issued `#check @name`, `#print name` (with `pp.proofs false`), and
`#print axioms name` for all seven public declarations below.
The combined build/audit command returned `CHECK_EXIT=0`; the final build
log was empty (no warnings or errors). The probe was removed from the
workspace after its output was preserved here. No audit commands remain
in the production module.

There are no `sorry`, `admit`, declared axioms, or native proof computations.
All seven audited declarations depend only on
`{propext, Classical.choice, Quot.sound}`. This is a producer audit, not
an external coordinator review, adoption, or integration.

The local estimates' exponent bounds guard every natural subtraction.
Rational division uses positive prime bases and their positive powers.
Costs refer to actual `localA` values, with positivity checked before
valuation cancellation. Finsets provide distinct support. Empty support
is deliberately admitted by the product bounds and normalized obstruction;
it is not the sole satisfiable case. Production examples jointly instantiate
the local hypotheses, both envelopes with nonempty support `{5}`, the
normalized consumer with `b=c=3`, `S={5}`, `e(5)=15`, and the actual
consumer with `n=2^12`. The natural-number and function domains are nonempty,
and the final positivity/exponent-twelve hypotheses exclude `n=0` and `n=1`.
Odd-five costs are never fixed to one.

Episode effort: three bounded module-build invocations and one separate
leaf audit. The initial dependency-repaired module compiled; the added
concrete final witness initially failed because unrestricted `simp` reduced
`2^12` before the factorization-power rewrite. Replacing that witness's
simplification with `simp only` repaired it, and the final build plus audit
succeeded. No mathematical search, theorem weakening, or revision operation
was needed. Only this General pair is delivered; the Scratch audit is removed.

## Literal producer signature and axiom output

The complete output below preserves the full `#check` and `#print`
signatures, not just the final consumer. Coercions in the envelope statements
are to `ℚ` as explicitly declared in the Lean source; proof bodies were
suppressed, not assumed.

```text
EUnitaryP1.dvd_localA_of_even : ∀ (p c : ℕ), 2 ≤ c → Even c → p + 1 ∣ EUnitaryP1.localA p c
theorem EUnitaryP1.dvd_localA_of_even : ∀ (p c : ℕ), 2 ≤ c → Even c → p + 1 ∣ EUnitaryP1.localA p c :=
⋯
'EUnitaryP1.dvd_localA_of_even' depends on axioms: [propext, Classical.choice, Quot.sound]
EUnitaryP1.localA_le : ∀ (p a : ℕ), 2 ≤ p → 2 ≤ a → EUnitaryP1.localA p a ≤ (p + 1) * p ^ (a - 2)
theorem EUnitaryP1.localA_le : ∀ (p a : ℕ), 2 ≤ p → 2 ≤ a → EUnitaryP1.localA p a ≤ (p + 1) * p ^ (a - 2) :=
⋯
'EUnitaryP1.localA_le' depends on axioms: [propext, Classical.choice, Quot.sound]
EUnitaryP1.localA_le_of_odd : ∀ (p a : ℕ), 2 ≤ p → 3 ≤ a → Odd a → EUnitaryP1.localA p a ≤ p ^ (a - 1) + p ^ (a - 3)
theorem EUnitaryP1.localA_le_of_odd : ∀ (p a : ℕ),
  2 ≤ p → 3 ≤ a → Odd a → EUnitaryP1.localA p a ≤ p ^ (a - 1) + p ^ (a - 3) :=
⋯
'EUnitaryP1.localA_le_of_odd' depends on axioms: [propext, Classical.choice, Quot.sound]
EUnitaryP1.weighted_localA_ratio_le : ∀ (S : Finset ℕ) (e : ℕ → ℕ),
  (∀ q ∈ S, Nat.Prime q ∧ q ≠ 2 ∧ q ≠ 3) →
    (∀ q ∈ S, 2 ≤ e q) →
      ∑ q ∈ S, padicValNat 2 (EUnitaryP1.localA q (e q)) ≤ 10 →
        ∏ q ∈ S, ↑(EUnitaryP1.localA q (e q)) / ↑q ^ (e q - 1) ≤ 30222828 / 16178305
theorem EUnitaryP1.weighted_localA_ratio_le : ∀ (S : Finset ℕ) (e : ℕ → ℕ),
  (∀ q ∈ S, Nat.Prime q ∧ q ≠ 2 ∧ q ≠ 3) →
    (∀ q ∈ S, 2 ≤ e q) →
      ∑ q ∈ S, padicValNat 2 (EUnitaryP1.localA q (e q)) ≤ 10 →
        ∏ q ∈ S, ↑(EUnitaryP1.localA q (e q)) / ↑q ^ (e q - 1) ≤ 30222828 / 16178305 :=
⋯
'EUnitaryP1.weighted_localA_ratio_le' depends on axioms: [propext, Classical.choice, Quot.sound]
EUnitaryP1.weighted_localA_ratio_le_of_odd_five : ∀ (S : Finset ℕ) (e : ℕ → ℕ),
  (∀ q ∈ S, Nat.Prime q ∧ q ≠ 2 ∧ q ≠ 3) →
    (∀ q ∈ S, 2 ≤ e q) →
      (5 ∈ S → Odd (e 5)) →
        ∑ q ∈ S, padicValNat 2 (EUnitaryP1.localA q (e q)) ≤ 10 →
          ∏ q ∈ S, ↑(EUnitaryP1.localA q (e q)) / ↑q ^ (e q - 1) ≤ 57927087 / 35592271
theorem EUnitaryP1.weighted_localA_ratio_le_of_odd_five : ∀ (S : Finset ℕ) (e : ℕ → ℕ),
  (∀ q ∈ S, Nat.Prime q ∧ q ≠ 2 ∧ q ≠ 3) →
    (∀ q ∈ S, 2 ≤ e q) →
      (5 ∈ S → Odd (e 5)) →
        ∑ q ∈ S, padicValNat 2 (EUnitaryP1.localA q (e q)) ≤ 10 →
          ∏ q ∈ S, ↑(EUnitaryP1.localA q (e q)) / ↑q ^ (e q - 1) ≤ 57927087 / 35592271 :=
⋯
'EUnitaryP1.weighted_localA_ratio_le_of_odd_five' depends on axioms: [propext, Classical.choice, Quot.sound]
EUnitaryP1.normalized_general_229_ne : ∀ (b c : ℕ) (S : Finset ℕ) (e : ℕ → ℕ),
  3 ≤ b →
    2 ≤ c →
      (∀ q ∈ S, Nat.Prime q ∧ q ≠ 2 ∧ q ≠ 3 ∧ q ≠ 229) →
        (∀ q ∈ S, 2 ≤ e q) →
          2061 * EUnitaryP1.localA 3 b * EUnitaryP1.localA 229 c * ∏ q ∈ S, EUnitaryP1.localA q (e q) ≠
            2 ^ 12 * 3 ^ (b - 1) * 229 ^ (c - 1) * ∏ q ∈ S, q ^ (e q - 1)
theorem EUnitaryP1.normalized_general_229_ne : ∀ (b c : ℕ) (S : Finset ℕ) (e : ℕ → ℕ),
  3 ≤ b →
    2 ≤ c →
      (∀ q ∈ S, Nat.Prime q ∧ q ≠ 2 ∧ q ≠ 3 ∧ q ≠ 229) →
        (∀ q ∈ S, 2 ≤ e q) →
          2061 * EUnitaryP1.localA 3 b * EUnitaryP1.localA 229 c * ∏ q ∈ S, EUnitaryP1.localA q (e q) ≠
            2 ^ 12 * 3 ^ (b - 1) * 229 ^ (c - 1) * ∏ q ∈ S, q ^ (e q - 1) :=
⋯
'EUnitaryP1.normalized_general_229_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
EUnitaryP1.sigmaEU_twelve_ne : ∀ (n : ℕ), 0 < n → n.factorization 2 = 12 → EUnitaryP1.sigmaEU n ≠ 2 * n
theorem EUnitaryP1.sigmaEU_twelve_ne : ∀ (n : ℕ), 0 < n → n.factorization 2 = 12 → EUnitaryP1.sigmaEU n ≠ 2 * n :=
⋯
'EUnitaryP1.sigmaEU_twelve_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
```
