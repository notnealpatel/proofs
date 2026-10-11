# Support-saturation unit C

## Scope and exact base

Implemented against accepted base `8aba7fd28e5d2d30ebb2ecb3492f6a92b1bd27af`, verified as the assigned working-copy parent. Production module: `Erdos.InfinitarySupportSaturation`, importing only `Erdos.InfinitarySuperperfect`. Namespace: `InfinitarySuperperfect`.

No existing production file, References input, global ledger, or revision graph was changed. There is no integration/adoption or commit. D, E, full f2, cycle hypotheses, and new M are not proved by this module and remain outside scope; existing reverse A–B is neither reproved nor modified here.

## Exact contract and exports

Each public export takes precisely:

```lean
(n : ℕ) (hn : 0 < n) (htwo : 2 ∣ n) (hsquare : IsSquare n)
(hthree : 3 ∣ n) (hfive : 5 ∣ n)
(hbudget : (∑ p ∈ n.primeFactors,
  if p = 2 then 0 else (binarySupport (n.factorization p)).card) = 2)
```

There is no replacement of whole-square input by odd-part squareness, no support premise, shape premise, arbitrary additional hypothesis, or alternate budget definition.

- `primeFactors_eq_two_three_five_of_budget_two`: `n.primeFactors = {2, 3, 5}`.
- `support_two_three_five_of_budget_two`: `∀ p ∈ n.primeFactors, p = 2 ∨ p = 3 ∨ p = 5`.
- `mixed_shape_of_budget_two`:
  ```lean
  ∃ j k : ℕ, 1 ≤ j ∧ 1 ≤ k ∧ n.factorization 3 = 2 ^ j ∧
    n.factorization 5 = 2 ^ k ∧
    n = 2 ^ (n.factorization 2) * 3 ^ (2 ^ j) * 5 ^ (2 ^ k)
  ```

The square premise is deliberately retained on the support equality even though support saturation itself does not need it. It is load-bearing for the higher-bit bounds in the mixed shape. The positivity guard is used before every factorization reconstruction.

## Proof

1. An actual prime of a positive integer has positive valuation, by `Nat.mem_primeFactors_of_ne_zero` and `Nat.Prime.factorization_pos_of_dvd`. If its binary support were empty, `sum_binarySupport` would reconstruct zero, a contradiction. Thus its support card is positive.
2. Actual distinct primes 3 and 5 each contribute at least one to the canonical sum. Erasing 3 and then 5 gives two exact sum decompositions. Nonnegativity and the total of two force each contribution to be one and the twice-erased sum to be zero.
3. A further actual prime other than 2, 3, 5 has a positive contribution, but `Finset.single_le_sum` bounds it by that zero remainder. Hence it cannot occur.
4. The three explicit divisibilities put 2, 3, 5 in the actual support; finite-set extensionality gives equality.
5. Singleton supports give bits j, k and reconstruct the valuations as `2^j`, `2^k` using `sum_binarySupport`. Whole-square input yields even valuations through `isSquare_iff_even_factorization`, so `one_le_of_mem_binarySupport_of_even` gives `1 ≤ j` and `1 ≤ k`.
6. `Nat.prod_primeFactors_pow_factorization (ne_of_gt hn)` reconstructs n. Rewriting the proved support equality and the two valuations evaluates the finite product to the required mixed shape.

The only local function is a proof-local abbreviation of the *same* canonical summand. No new public definition or competing F is introduced. Private lemmas expose positivity, the erase-sum argument, and singleton-bit reconstruction; each is consumed by the public exports.

## Consumer and unpaid upstream bridge

The inclusion export has exactly the support type accepted by existing
`InfinitarySuperperfect.not_dvd_sigma_of_support_two_three_five` in
`Erdos.InfinitaryCanonicalSupport`. Its `hsupport` argument can be supplied by:

```lean
support_two_three_five_of_budget_two n hn htwo hsquare hthree hfive hbudget
```

Its evenness argument remains directly available as:

```lean
fun p _ => (isSquare_iff_even_factorization n hn).mp hsquare p
```

That consumer's separate prime/residue hypotheses remain separate. No consumer file was changed. Deriving these six input hypotheses from any cycle or other upstream setting is unpaid and outside C. There is no remaining mathematical gap **within C**.

## Non-vacuity and boundaries

A checked private witness theorem jointly proves all six hypotheses for
`900 = 2^2 * 3^2 * 5^2 = 30 * 30`, including the canonical budget of two. Its support and valuations are established independently using multiplication and prime-power lemmas, not any saturation export. Three production `example`s invoke the three public exports using that witness. Thus the export invocations are not proofs from incompatible premises.

At this witness both higher bits are 1; the actual support is nonempty and has all three distinct primes. The indices j, k have type ℕ (nonempty), and the conclusion explicitly requires them to be positive. All assumed support sums have actual 3 and 5 members. Zero is excluded by `hn`; one and powers of two are excluded by divisibility by 3 and 5. No reconstruction at zero, subtraction, division, or bounded empty extrema occur. No instance assumptions are introduced.

## Checks and evidence

All commands ran from the assigned workspace. Long checks were bounded tasks (70-second task deadline, 60-second command timeout with 2-second kill grace).

Final production build, including the joint witness and all three invocation examples:

```sh
set -o pipefail; timeout --kill-after=2s 60s lake -q build +Erdos.InfinitarySupportSaturation 2>&1 | tee support-saturation-build.log
```

**Result:** exit 0; no diagnostics. The generated module `.olean` was observed. Raw final build output is in `/tmp/infinitary-C-producer-01a1290f/build.log` (empty because the successful quiet build emitted nothing).

Separate producer-only leaf audit imported the built module and ran `#check @` and `#print axioms` on each export:

```sh
set -o pipefail; timeout --kill-after=2s 60s lake env lean -j 1 -M 4000 Proofs/Scratch/SupportSaturationAudit.lean 2>&1 | tee support-saturation-audit.log
```

**Result:** exit 0. All three full signatures matched the contract above. Each axiom report contained exactly `[propext, Classical.choice, Quot.sound]`. Raw output is `/tmp/infinitary-C-producer-01a1290f/producer-audit.log`. The temporary Scratch leaf was removed; no exploratory commands remain in production. The coordinator's fresh imported axiom audit and independent literal review are separate gates, not replaced by this producer check.

The producer retained evidence under `/tmp/infinitary-C-producer-01a1290f/` for station collection. These disposable artifacts are outside the tracked repository; the station can copy them to `/home/exedev/x/erdos/prize-portfolio/activation-01a1290e/infinitary-C/`.

### Feedback and actual exposure

The first implementation of all three exports compiled without a repair. Two disposable witness probes failed: `decide` could not reduce opaque prime-factorization data, and `norm_num` alone did not compute `primeFactors 900`. Replacing evaluation with exact product/prime-power API rewrites gave the compiled joint witness. One failed probe log is retained as `/tmp/infinitary-C-producer-01a1290f/witness-probe-failed.log`; it is not a production failure.

This work used six bounded Lean check tasks: two initial builds (the second retained an explicit log), two failed witness probes, the successful witness-inclusive build, and the final successful imported audit. Seven exact `leandoc` API lookups were used. Source inspection covered the assigned-base parent, Lake configuration, canonical support consumer, and square-input precedents. No external research, mathematical enumeration, reasoning subagent, or version-control mutation was used. The work adds the missing saturation mathematics and elementary representation/API infrastructure only; elaboration, statement fidelity, concrete satisfiability, and producer axiom checks are recorded separately above.
