# Actual fourth-power parity obstruction

Production module: `Erdos.InfinitaryFourthPowerF3`.
All symbols below are in namespace `InfinitarySuperperfect`.

## Exact stronger consumer contracts

```lean
factorization_sigma_two_even_of_four_dvd
    (n m : ℕ)
    (hn : 0 < n)
    (he : ∀ p ∈ n.primeFactors, 4 ∣ n.factorization p)
    (hop : oddPart n % 4 = 1)
    (hm : m = sigma n)
    (hcycle : sigma m = 2 * n) :
    Even (m.factorization 2)

factorization_sigma_two_even_of_fourth_power
    (n m t : ℕ)
    (ht : 0 < t)
    (hfourth : n = t ^ 4)
    (hm : m = sigma n)
    (hcycle : sigma m = 2 * n) :
    Even (m.factorization 2)
```

Both sums are the existing canonical **infinitary** divisor sum, not the
ordinary divisor sum. The root may be odd; no evenness hypothesis is added.
The first theorem retains the positive-input hypothesis (named `_hn` in the
implementation); its proof does not need it once the other premises are given.
Neither consumer assumes the derived prime-support congruences or a reverse
reconstruction certificate.

All twelve previous public declarations and their contracts and examples are
preserved, including `factorization_sigma_two_ne_three_of_four_dvd` and
`factorization_sigma_two_ne_three_of_fourth_power`. Exclusion of valuation
three is now also an immediate mathematical corollary of evenness. Their
existing proofs have not been rewritten. The stronger result excludes **all
odd two-valuations**, not just three.

## Proof route

Every selected forward bit has height at least two. For an odd prime $r$
dividing $1+p^{2^j}$, the element $(p : \mathrm{ZMod}\ r)$ has order exactly
$2^{j+1}$: its $2^j$ power is minus one, not one, and its next power is one.
This order divides $r-1$, hence $r\equiv1\pmod8$. The actual equality
$m=\sigma(n)$ therefore derives this residue for every actual odd prime of
$m$; mod-eight forward support is **not assumed** in either consumer.

For every reverse tag, including height zero, this residue makes
$\operatorname{normalizedSlot}(q,h)\equiv1\pmod4$, hence
$\operatorname{reverseProduct}(m)\equiv1\pmod4$.
Write $b=v_2(m)$. The reusable lemma `localSigma_two_mod_four` proves

$\operatorname{localSigma}(2,b)\equiv1\pmod4$ if $b$ is even, and
$\operatorname{localSigma}(2,b)\equiv3\pmod4$ if $b$ is odd.

Indeed, the height-zero factor is three, while every factor of positive
height is one modulo four; zero belongs to `binarySupport b` exactly when
$b\bmod2=1$. The local factor is odd in either case.

The new general bridges `sigma_eq_localSigma_two_mul_raw_product` and
`sigma_eq_localSigma_two_mul_two_pow_reverseCount` reconstruct, for positive
$m$ under the stated mod-four odd-prime support,

$\sigma(m)=\operatorname{localSigma}(2,b)\,2^{\operatorname{reverseCount}(m)}\operatorname{reverseProduct}(m)$.

The raw-product bridge explicitly treats absent prime two: then $b=0$ and
$\operatorname{localSigma}(2,0)=1$. Tagged occurrences preserve multiplicity.
The odd cofactor allows `oddPart_sigma_mod_four_of_mod_eight` to conclude that
$\operatorname{oddPart}(\sigma(m))\bmod4$ is one for even $b$ and three for
odd $b$. But $\sigma(m)=2n$, `oddPart_two_mul`, and the input odd-part residue
force it to be one, so $b$ is even.

The fourth-power consumer obtains the valuation divisibilities from
`Nat.factorization_pow` and obtains the input odd-part residue from
`oddPart_mod_four_of_isSquare`, since a positive fourth power is a whole square.
No upstream premise has been replaced with an assumed parity certificate.

## Boundary and hypothesis-block checks

The local factors at $b=0,1,2,3$ are kernel-checked as $1,3,5,15$.
A new joint reverse-block example at $m=17$ checks positivity, absent prime
two (valuation zero), actual odd support one modulo eight, $\sigma(17)=18$,
and odd-part residue one. The existing reverse block at $m=136$ has valuation
three, actual odd support $\{17\}$, and $\sigma(136)=2\cdot135$; its odd-part
residue is three. Its reverse tag set is nonempty, its count is one, and its
normalized product is nine. Thus both parity branches and the absent-two
boundary are exercised with nonempty odd support.

The existing tests for the occupied bit of exponent four, the order-eight
successor divisor seventeen, normalized height zero, and the positive odd-root
forward example $\sigma(81)=82$ with $81=3^4$ are retained. The root-one
boundary has $\sigma(1)=1$ and fails the reverse equation.

These are **separate hypothesis-block witnesses, not a joint actual-cycle
model**. No positive fourth-power cycle is exhibited, and joint satisfiability
of the complete consumer premises is not claimed.

## Producer verification receipt

The extended module, consumers, and examples passed the narrow target:

```sh
timeout 60s lake -q build +Erdos.InfinitaryFourthPowerF3
```

A separate disposable leaf importing the production module checked the exact
full signatures of both new consumers, including explicit type ascriptions
for their entire contracts, with:

```sh
timeout 60s lake env lean -j 1 -M 4000 Proofs/Scratch/F3ParityAudit.lean
```

The producer leaf also printed axioms for all eighteen public declarations.
Each dependency set was contained in `{propext, Classical.choice, Quot.sound}`;
both new consumers used exactly those three. The leaf was removed after the
check; no exploratory commands remain in production. No `sorry`, `admit`, new
axiom, or `native_decide` was introduced. This is producer evidence only.

## Scope and pending independent gates

This proves only the stated conditional actual-cycle parity obstruction.
It does not establish existence or classification of cycles, an unrestricted
global f3 exclusion, the parent's necessary prime-support shape, ratio bounds,
or the bridge reducing a free-prime exponent to exactly two. Those upstream
implications remain unpaid. No other production files or `References` were
modified.

The parent still owns independent literal review of both files and a fresh
all-public import/signature/axiom audit after finalization. Producer compilation
and the producer audit do not discharge those independent gates. No novelty,
prize, adoption, or parent-completion claim is made.
