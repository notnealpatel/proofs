# Verification record: power-of-two ternary digit counts

## Current mechanical verification

[Authoritative campaign manifest](../Wave4ComparatorEvidence.yaml): **PASS** for every declaration selected by this package’s `comparator.json`. Earlier text below is historical and superseded. Human review remains **UNCHECKED**; this makes no claim of Palomar acceptance, submission, or publication.

## Status

- **Challenge compilation:** PASS, with exactly the two intentional theorem-hole warnings.
- **Solution compilation:** PASS, performed separately from the Challenge.
- **Exact signature checks:** PASS for both selected declarations.
- **Selected theorem axiom audit:** PASS. Each selected wrapper theorem uses exactly
  `propext`, `Classical.choice`, and `Quot.sound`; neither closure contains `sorryAx`,
  `Lean.ofReduceBool`, or a custom axiom.
- **Comparator / landrun / lean4export / NanoDA:** NOT RUN because the required
  executables are absent. This record does not infer approval from ordinary Lean
  elaboration.
- **Human review:** PENDING. USER is the sole review gate; no agent or parent
  mathematical review is asserted.

## Revisions, tools, and package boundary

- Assigned campaign base: `117a6e3949ca41075e133e350e38d9d2fbfdd8e2`.
- Packaging working-copy revision observed before edits:
  `db62e83951737d9afdb6b3402e551eae2512b5c3`.
- Verification date: `2026-09-07` UTC.
- Lean: `4.33.0-rc1`, commit
  `62eed1db4d67327ec8120be05f1a1b0847d74561`,
  `x86_64-unknown-linux-gnu`, Release build.
- Lake: `5.0.0-src+62eed1d` (Lean `4.33.0-rc1`).
- Mathlib manifest revision:
  `3edb3c0658f69f197b1e501b1f7623f3f7b3898c`.
- Comparator configuration:
  `Palomar/PowerOfTwoDigitCounts/comparator.json`.

Only the five authorized files in `Palomar/PowerOfTwoDigitCounts` were created or
modified. The existing `README.md`, `Proofs/`, `References/`, root configuration, and
unrelated paths were not changed.

## Definitions and declaration inventory

Both modules independently declare the same items in namespace
`Palomar.PowerOfTwoDigitCounts`; the Solution does not import the Challenge.

- `TernaryZeroOne (m : ℕ) : Prop` is literally
  `∀ d ∈ Nat.digits 3 m, d ≤ 1`.
- `exponentCount (N : ℕ) : ℕ` is the cardinality of the filter of
  `Finset.range N`, so its boundary is `n < N` and its predicate is applied to the
  **value** `2 ^ n`.
- `SieveAt (D n : ℕ) : Prop` checks the lowest `D` ternary digits of `2 ^ n`.
- `sieveClasses (j : ℕ) : Finset ℕ` filters
  `Finset.range (2 * 3 ^ j)` at depth `j + 1`.
- `card_sieveClasses (j : ℕ)` proves the exact cardinality `2 ^ j`.
- `card_erdos406_filter_le_rpow (N : ℕ) (hN : 1 ≤ N)` is the headline
  real-cardinality upper bound `2 * (N : ℝ) ^ Real.logb 3 2`.

Ground checks in each module include the value-side facts that `1` and `4` satisfy the
literal ternary predicate while `2` does not, count checks at `N = 1` and `N = 3`, and
the first two sieve-class lists. Thus the statement does not accidentally count digits
of the exponent, use `n ≤ N`, or treat exponent `1` as a survivor. The `N = 1` theorem
example jointly witnesses satisfiability of the headline hypothesis and conclusion.

## Read-only cache provenance

No full repository build or cache reconstruction was performed. The Solution compile
read existing `.olean` files from `/home/exedev/p/proofs/.lake/build/lib/lean` through
an appended `LEAN_PATH`; that cache was not modified. Before reuse, the current
workspace and cache-source checkout were confirmed to have identical toolchain,
manifest, selected target, and direct project dependency sources:

```text
lake-manifest.json
  948a91a6b3c52e0b640d0dadc1bf84cf967403244ac590c162c005c2544a439e
lean-toolchain
  02f25adee7c1d6bf2e95b7b5b13f45b9892c7dd53ef470d5372ac60bda3df023
Proofs/Erdos/Erdos175/KummerDigits.lean
  85fecb040fe12398f4966c7ed3f83c5ed48a87c7fed8ac16d1999990a64b373f
Proofs/Enumerative/StanleyDigits.lean
  44d87c876313ab3e54824574e4b1440707287f6ca7bdacaa5b7d6538e16593b8
Proofs/Enumerative/PowerOfTwoDigits.lean
  6ba47394d18dc503b78fd09a841712519d1ab9944747d15e4f3616e165b0d9e5
Proofs/Enumerative/PowerOfTwoDigitsCount.lean
  4d7e60261251130f57ced730f198ba3b7075b7ee59a51acb149e3f9061c1daa8
```

Each hash appeared identically for the workspace and
`/home/exedev/p/proofs`. The reused target object was
`/home/exedev/p/proofs/.lake/build/lib/lean/Enumerative/PowerOfTwoDigitsCount.olean`.
Mathlib objects came from the same manifest-pinned shared package directory.

## Successful separate compilation: Challenge

Immediately before the final Challenge command, `tool_atop` reported 8 cores,
23.46 GiB total memory, 0.80 GiB used, and 22.66 GiB available. The bounded command was:

```sh
ulimit -v 8388608
timeout 180s taskset -c 0 lake env lean -M 5000 -j 1 \
  -o /tmp/yah/subagent/power2-digits-package-prover-a8aae4b/olean/Challenge.olean \
  Palomar/PowerOfTwoDigitCounts/Challenge.lean
```

Exit status: `0`. The generated object was 66,784 bytes. Exact output:

```text
Palomar/PowerOfTwoDigitCounts/Challenge.lean:55:8: warning: declaration uses `sorry`
Palomar/PowerOfTwoDigitCounts/Challenge.lean:61:8: warning: declaration uses `sorry`
card_sieveClasses : ∀ (j : ℕ), (sieveClasses j).card = 2 ^ j
card_erdos406_filter_le_rpow : ∀ (N : ℕ), 1 ≤ N → ↑(exponentCount N) ≤ 2 * ↑N ^ Real.logb 3 2
```

The retained complete log is
`/tmp/yah/subagent/power2-digits-package-prover-a8aae4b/challenge.log`.

## Successful separate compilation and axiom audit: Solution

Immediately before the Solution command, `tool_atop` reported 8 cores, 23.46 GiB total
memory, 0.81 GiB used, and 22.65 GiB available. The bounded one-core command was:

```sh
ulimit -v 18874368
timeout 300s taskset -c 0 \
  env LEAN_PATH=/home/exedev/p/proofs/.lake/build/lib/lean \
  lake env lean -M 9000 -j 1 \
  -o /tmp/yah/subagent/power2-digits-package-prover-a8aae4b/olean/Solution.olean \
  Palomar/PowerOfTwoDigitCounts/Solution.lean
```

Exit status: `0`. The generated object was 61,896 bytes. Exact output:

```text
card_sieveClasses : ∀ (j : ℕ), (sieveClasses j).card = 2 ^ j
card_erdos406_filter_le_rpow : ∀ (N : ℕ), 1 ≤ N → ↑(exponentCount N) ≤ 2 * ↑N ^ Real.logb 3 2
'Palomar.PowerOfTwoDigitCounts.card_sieveClasses' depends on axioms: [propext, Classical.choice, Quot.sound]
'Palomar.PowerOfTwoDigitCounts.card_erdos406_filter_le_rpow' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The retained complete log is
`/tmp/yah/subagent/power2-digits-package-prover-a8aae4b/solution.log`.
The imported parent contains an archived open conjecture, so safety was not inferred from
an import or declaration name. The output above is the fresh selected-declaration
`#print axioms` closure. It establishes that the selected results do not depend on the
parent's open-conjecture mechanism or on `sorryAx`.

## Bounded failed commands

Two initial Challenge attempts failed and were not counted as verification:

1. Under the same 8 GiB / 180-second / one-core bounds, the first source imported the
   nonexistent aggregate module `Mathlib.Data.Nat.Digits`; Lean exited `1` because
   `Mathlib/Data/Nat/Digits.olean` did not exist. The import was corrected to the
   allowlisted Mathlib module `Mathlib.Data.Nat.Digits.Lemmas`.
2. Under the same bounds, the next attempt exited `1` because the freshly defined
   `TernaryZeroOne` and `SieveAt` lacked local `Decidable` instances needed by
   `Finset.filter` and the ground checks. Explicit inferred instances were added; no
   theorem statement was weakened. The final command above then passed.

These early outputs were not retained as separate log files because the final log path
was intentionally overwritten; their commands, bounds, exit statuses, and failure
causes are recorded here. No Solution compilation failed.

## Comparator and independent verifier tooling

**Status: NOT RUN.** PATH checks found all four required executables absent:

```text
comparator: MISSING
landrun: MISSING
lean4export: MISSING
nanoda_bin: MISSING
```

The known local Comparator source checkout also had no built comparator executable and
its `lean-toolchain` is `leanprover/lean4:v4.34.0-rc1`, newer than this project's
`v4.33.0-rc1`. In accordance with the resource and tooling constraints, no invocation,
installation, toolchain upgrade, or verifier build was attempted. `enable_nanoda` remains
`true` in `comparator.json`; configuration was not weakened to disguise unavailable
tooling.

## Mathematical and provenance boundary

The headline is the `λ = 1` specialization of Lagarias, *Ternary expansions of powers
of 2* (2009), Theorem 1.4: constant `2` and exponent `Real.logb 3 2`. The package does
not formalize Narkiewicz's stronger constant `1.62`. It proves no finiteness statement
for `Erdos406.erdos406Set` and makes no claim that the known values `1`, `4`, and `256`
(or exponents `0`, `2`, and `8`) are exhaustive. The finite survivor theorem concerns
exponent residue classes, not all zero-one ternary strings.

All packaging and verification recorded here was AI-assisted. Human author and
responsible-maintainer identities remain unknown and are left empty in
`formalization.yaml` with explicit blockers. Human mathematical, attribution, and
source-fidelity review remains pending.
