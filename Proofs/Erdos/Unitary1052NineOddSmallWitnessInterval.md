# Ordinary nine-odd small-witness interval consumer

## Exact contract

`Erdos1052.NineOdd.SmallWitnessInterval.interval_exclusion` retains the
natural-base arguments of
`SmallWitness.actual19_and_actual25_of_small_witness`, changing only the
witness lower bound from `109 ≤ x` to `373 ≤ x` and the conclusion to `False`.
It assumes exactly nine prime bases greater than two, positive supported
exponents, an even binary exponent `a` with `11 ≤ a`, and the **full ordinary
natural-number identity**

```text
(2^a + 1) * ∏ p ∈ P, (p^(e p) + 1)
  = 2 * (2^a * ∏ p ∈ P, p^(e p)).
```

The other retained assumptions are a component greater than 32768; actual
components 3, 7, 11, 13; absence of actual5; and an actual component `x` with
`373 ≤ x`, `x < 32769`, and `11 ∣ x + 1`. Actual membership means membership
in `P.image (fun p => p ^ e p)`, not membership in the prime-base set.
There are no actual19/actual25 hypotheses, no primality assumption on `x`,
and no global exponent cap.

## Composition and representation transport

1. Weaken `373 ≤ x` to `109 ≤ x` and call the existing forcing theorem F
   with the unchanged ordinary identity and all retained premises. This
   produces actual19 and actual25.
2. For each supported base, derive `Odd p` from primality and `2 < p`
   using `Nat.Prime.odd_of_ne_two`.
3. Use `component_injOn P e hp he` and `Finset.prod_image` to rewrite both
   actual-component products (the factors `y` and the factors `y + 1`) as
   prime-base products. Use `Nat.pow_succ` and multiplication associativity
   and commutativity to identify `2^(a+1)` with `2 * 2^a`. The resulting
   actual-product identity is proved from the original identity, not assumed.
4. Call `WitnessInterval.interval_kernel`, passing actual19/actual25 from F,
   the transported identity, derived oddness, and the original interval and
   other retained premises. Its conclusion is `False`.

This module is consumer assembly and equality representation infrastructure
only. It adds no mathematical exclusion lemma, supplier theorem, or corollary.

## Independent frozen sources

F is preserved byte-for-byte from assigned base
`6178faca4a56db2574dead6724ae48fa1b1872e3`. The independently accepted interval
source is recovered byte-for-byte with `jj --ignore-working-copy file show`
from `a3f24337e8f76940c279722c92d2f8305f5a7922`. The supplied acceptance evidence
for both implementations is taken as established, not re-reviewed. The
interval module imports the reduction infrastructure, not F; only this new
consumer imports both producers.

SHA-256 hashes (verified with `sha256sum` and byte comparisons):

| Artifact | SHA-256 |
| --- | --- |
| Preserved `Unitary1052NineOddSmallWitness.lean` | `ed20ab53e0ec8854c1a6e7558c56bc255f1da51917c8d1ba6e9e276139e17f4d` |
| Preserved `Unitary1052NineOddSmallWitness.md` | `f18e40907d891dee3790a9f3f0dc9dc6088af5de1c74ebf2664ef67dad646fb7` |
| Copied `Unitary1052NineOddWitnessInterval.lean` | `ff61264aba9397e45df6fe74671e8a5a2901a9747b3211c7b556bf434ebc27c5` |
| Copied `Unitary1052NineOddWitnessInterval.md` | `8525f5d6885dc9c4d533e68ef310f4a56c8fd109987f852c8090906e9f5ed2ce` |

## Meaning and scope

The conclusion intentionally excludes this interval configuration; it does
not assert existence of a configuration. No joint satisfiability example
for the full hypotheses can accompany an exclusion theorem proving those
hypotheses inconsistent. Consequently no full-contract non-vacuity or
existence claim is made. The domains are naturals and a finite set with
cardinality nine; positive supported exponents and actual witness membership
are retained. The full ordinary identity remains an explicit upstream
premise; no UPN-to-ordinary-identity bridge is supplied. Other witness ranges,
large-supplier construction, residual/global exclusions, and a global
nine-odd theorem remain outside this consumer.

The intended objects, quantifiers, and retained hypotheses are unchanged;
only the specified lower-bound strengthening and exclusion conclusion
change relative to F. No ledger, integration, adoption, References, or
unrelated source is modified.

## Compiler and audit receipt

The bounded background module check succeeded without warnings or errors:

```text
timeout --kill-after=2s 60s lake -q build +Erdos.Unitary1052NineOddSmallWitnessInterval
BUILD_EXIT=0
```

A separate disposable leaf imported the new consumer, checked the full
signatures of F, the interval kernel, the consumer, and
`Nat.Prime.odd_of_ne_two`, and printed the three theorem axiom dependencies:

```text
timeout --kill-after=2s 60s lake env lean -j 1 -M 4000 Proofs/Scratch/Unitary1052SmallWitnessIntervalAudit.lean
F: [propext, Classical.choice, Quot.sound]
interval_kernel: [propext, Classical.choice, Quot.sound]
interval_exclusion: [propext, Classical.choice, Quot.sound]
AUDIT_EXIT=0
```

The temporary audit leaf was removed and is not imported by production.
The new production source has no `sorry`, new axioms, `native_decide`, or
exploratory commands. This is a compiled conditional exclusion with a
standard-three axiom audit, not an existence or global-result certificate.
Actual implementation effort consisted of one consumer implementation,
a bounded module build, an incremental build receipt, and the separate
imported-signature/axiom audit; no proof repair or new mathematical argument
was needed. The exposed prover-role tools used were file/shell operations,
`leandoc`, bounded background `tool_task` checks, and `tool_yield`; no campaign
integration or revision-management operation was used.
