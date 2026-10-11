# Nine-odd small11-supplier forcing: completed F

## Status and exact scope

`Unitary1052NineOddSmallWitness.lean` imports only the accepted
`Erdos.Unitary1052NineOddReduction`. The accepted Reduction revision
`564890116eb65bbaaf7b9e278f5083bd5000a4cc` was inspected and confirmed to be
an ancestor of the assigned base `aa12a843069a5fc6d60a1c0fc14cf63b31dce3c3`.
The inherited proofs through `configuration_of_not_actual25` are preserved.

F is `Erdos1052.NineOdd.SmallWitness.actual19_and_actual25_of_small_witness`.
For `X = P.image (fun p => p ^ e p)`, it proves **`19 ∈ X ∧ 25 ∈ X`**.
Its arguments are exactly those of `configuration_of_not_actual25` with
`hn25` removed:

* `P.card = 9`, every supported base is prime and strictly larger than 2,
  and every supported exponent is positive;
* `11 ≤ a`, `Even a`, and the full ordinary natural-number identity
  `(2^a + 1) * ∏ p ∈ P, (p^(e p) + 1) = 2 * (2^a * ∏ p ∈ P, p^(e p))`;
* some actual component exceeds 32768;
* actual3, actual7, actual11, and actual13 belong to `X`, while actual5 does not;
* `x ∈ X`, `109 ≤ x`, `x < 32769`, and `11 ∣ x + 1`.

The objects, quantifiers, hypotheses, and conclusion are unchanged from the
assigned forcing contract. `X` is the set of actual prime-power values, not
the base set. There is no primality hypothesis on `x`, no global exponent cap,
no base5-absence hypothesis, and no configuration premise in F. The even
interval `18 ≤ a ≤ 30` is derived only inside the rejected branch; it is not
an argument or conclusion of F.

The full reviewed prose `/tmp/erdos-program-nine-odd-small-witness-forcing-01a127d7.md`
and the inherited source/documentation were read before implementation. The
already completed prose PASS was not repeated. No Witness109/373, Ledger,
assignment packet, References artifact, or other production file was edited.
No downstream consumer is imported or composed here.

## Inherited checked implications

`actual19_of_small_witness` proves `19 ∈ X` from exactly the original branch
premises. The ordinary 3-budget gives `y % 3 = 1` for actual components other
than3 and11. Odd prime powers below55 are exhaustively classified with an
exponent bound derived from that local size bound, not assumed globally.
Short-value counts and two distinct high witnesses yield the strict sorted
rational envelope `[3,7,11,13,25,31,37,109,32769]` if actual19 is absent.

`five_component` derives `5 ∈ P`, `2 ≤ e 5`, `Even (e 5)`, and
`5^(e 5) ≠ x`. This uses closure from successor20, the ordinary3 budget,
and the odd modular period of5 modulo11. Actual5 absence is not base5 absence.

`forty_three_absent` excludes actual43 via the exact ordinary11 budget.
`sole_large_five` proves that if `4 ≤ e 5`, every actual component above32768
is `5^(e 5)`, using the strict envelope
`[3,7,11,13,19,31,109,625,32769]`. Three high values are explicitly distinct.

`terminal_components_of_large_five` derives `8 ≤ e 5`,
`32769 ≤ 5^(e 5)`, actual31, and actual37. Its further envelopes are
`[3,7,11,13,19,37,43,109,32769]` and
`[3,7,11,13,19,31,55,109,32769]`.

`configuration_of_not_actual25` uses only the additional contradiction
assumption `25 ∉ X` to derive

```
5 ∈ P ∧ Even (e 5) ∧ 8 ≤ e 5 ∧
X = {x, 5^(e 5), 3, 7, 11, 13, 19, 31, 37}.
```

The set equality follows by inclusion, explicit distinctness, and cardinality9.
No configuration certificate or slot allocation is assumed by F.

## New terminal mathematics and infrastructure

`component_odd` transports oddness of supported odd prime bases to their
actual powers. In particular `x` is odd, so `x < 32769` gives
**`0 < x+1 ≤ 32768`**. Without oddness the upper endpoint would be wrong.

`terminal_sum` is representation infrastructure: the seven small fixed
values, `x ≥ 109`, and `5^(e 5) ≥ 32769 > x` are distinct, so the exact set
sum expands without dropping duplicate summands.

`two_budget` derives, rather than assumes,

```
∑ y ∈ X, padicValNat 2 (y+1) = a+1.
```

It applies `padicValNat 2` to the full identity, proves all product factors
nonzero, expands valuations of products, proves supported odd powers have
zero two-valuation, proves the binary successor has zero two-valuation for
`0 < a`, and transports the sum with `component_injOn`.

`not_terminal_configuration` closes the load-bearing contradiction:

1. Actual31 fixes base31's exponent to one. Its exact ordinary budget,
   together with the odd periods `2^5 = 1` and `5^3 = 1` modulo31, gives
   `padicValNat 31 (x+1) = 1`, hence `31 ∣ x+1`. The seven fixed successors
   `4,8,12,14,20,32,38` supply no31.
2. If `125 ∣ x+1`, coprimality with11 and31 gives `42625 ∣ x+1`.
   Positivity and the upper32768 bound contradict this. The guarded
   prime-power divisibility/valuation equivalence then gives `v5(x+1) ≤ 2`.
3. The fixed two-valuations are `2,3,2,1,2,5,1`, totaling16. The five-power
   successor has two-valuation1: in fact `5^E = 1` modulo4 for every E,
   so the formal proof uses this slightly stronger fact rather than needing
   evenness for this particular step. Let `s = v2(x+1)`. Oddness gives
   `1 ≤ s`, and divisibility `2^s ∣ x+1 ≤ 2^15` gives `s ≤ 15`.
   The exact two-budget yields `a = 16+s`; evenness of a then gives
   `18 ≤ a ≤ 30` in this contradiction branch only.
4. `binary_five_bound` kernel-checks the seven even possibilities in the
   derived interval by interval splitting and integer arithmetic, proving
   `125 ∤ 2^a+1` and hence `v5(2^a+1) ≤ 2`. No `native_decide` or unbounded
   search is used.
5. The exact five-budget has only successor20 contributing1 among the
   fixed terms; `5^E+1` contributes0. Thus
   `E = v5(2^a+1) + v5(x+1) + 1 ≤ 5`, contradicting `8 ≤ E`.

F calls the inherited configuration implication only under `¬ actual25`,
contradicts the resulting configuration, and pairs actual25 with the
inherited actual19 result. This completes the supplied mathematical argument;
there is no remaining Lean gap inside F.

## Evidence and semantic limitations

The final narrow build

```
timeout --kill-after=2s 60s lake -q build +Erdos.Unitary1052NineOddSmallWitness
```

completed successfully with no diagnostics. A separate temporary imported
leaf ran under

```
timeout --kill-after=2s 60s lake env lean -j 1 -M 4000 Proofs/Scratch/SmallWitnessAudit01a128cd.lean
```

and succeeded. Its full `#check @...` signatures for F, `two_budget`, and
`not_terminal_configuration` were inspected: F has exactly the contract
above and no hidden section parameters. All **23 named theorems**, inherited
and new, report exactly `{propext, Classical.choice, Quot.sound}`. Audit
output is preserved at `/tmp/small-witness-audit-01a128cd.txt`; the temporary
leaf was removed and is never imported into production. A byte-prefix
comparison against the assigned base confirmed that the inherited source
through `configuration_of_not_actual25` is unchanged (only the closing
namespace line moved to accommodate the additions).

Actual continuation effort: six bounded module-build attempts, four failed
and two successful, followed by one successful separate audit. The first
failure exposed the divisibility-equivalence direction and the need for an
explicit `v2(2)=1` certificate. Later local failures concerned reduction of
opaque natural valuations by `decide`, a tactic heartbeat limit, and the
normal form `1+1` versus `2` in `ZMod 4`. Explicit divisibility certificates,
a direct inequality contradiction instead of the expensive tactic call,
and a local cast repair resolved these; no larger timeout or heartbeat
allowance was needed. The first successful proof build took18 seconds and
reported only an unused evenness-argument name, renamed `_hE` before the
final clean build. No independent prose review or research campaign was run.

All production declarations use
`set_option autoImplicit false`. No new definitions, axioms, `sorry`,
`native_decide`, or exploratory commands are introduced. Finite arithmetic
certificates are small and local, not a global candidate enumeration.

The quantified domains are genuine naturals and finite sets; the full
contract enforces nine supported bases and an actual witness. The explicit
positive exponent and successor guards keep valuation/divisibility and
product manipulations off their totalized zero cases. A concrete ordinary
identity model `a=1`, `P={3}`, `e=1` (the number6) jointly realizes the
hypotheses of the new two-budget helper. Other concrete examples realize the
short-value, modular-period, and finite-set allocation helpers at nonempty
models. The rejected terminal configuration is intentionally inconsistent;
its impossibility is proved, not used as a satisfiable premise of F.

**No concrete model jointly satisfying the full original identity and all
nine-odd branch premises is exhibited.** Helper examples are not a full-branch
satisfiability certificate. Thus compilation and the conditional statement
audit are not a claim of full-contract non-vacuity, existence, novelty, or a
global nine-odd theorem.

F is available to the named downstream `interval_kernel` consumer, but that
consumer is deliberately not imported, modified, or composed here. The
UPN-to-ordinary-identity bridge and all residual/global exclusions remain
upstream or downstream obligations. Work stops at F; no integration or
adoption operation is performed.
