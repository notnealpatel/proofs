# Verification record: asymptotic full Boolean row rank

## Mechanical status

- **Challenge elaboration:** **PASS**. The only warnings are the three intentional selected-theorem holes.
- **Solution direct compilation:** **PASS**, separately from the Challenge and without importing it.
- **Selected signatures:** **PASS**; all three printed signatures match the Challenge declarations.
- **Selected theorem axiom audit:** **PASS**. Each selected Solution theorem uses exactly `propext`, `Classical.choice`, and `Quot.sound`. No selected closure contains `sorryAx`, `Lean.ofReduceBool`, or a custom axiom.
- **Targeted Lake build:** **NOT COMPLETED** because Lake unnecessarily rebuilt an unchanged large prerequisite and Lean aborted with `std::bad_alloc`. A direct compilation against byte-identical, matching-toolchain prerequisite oleans passed and is the compilation evidence for the Solution.
- **Comparator:** **NOT RUN — REQUIRED TOOLING MISSING**. This is not a Comparator pass.
- **Human review:** **PENDING**. USER is the sole review gate. No submission, acceptance, publication, or human approval is claimed.

## Revisions, tools, and dependency pins

- Assigned campaign base: `117a6e3949ca41075e133e350e38d9d2fbfdd8e2`.
- Workspace revision observed during packaging: `d5a641ade7fe09444500104d5e47ab89972f6cb9`.
- Lean: `4.33.0-rc1`, commit `62eed1db4d67327ec8120be05f1a1b0847d74561`, `x86_64-unknown-linux-gnu`, Release build.
- Lake: `5.0.0-src+62eed1d` (Lean `4.33.0-rc1`).
- Mathlib manifest revision: `3edb3c0658f69f197b1e501b1f7623f3f7b3898c`.
- Project `lean-toolchain` SHA-256: `02f25adee7c1d6bf2e95b7b5b13f45b9892c7dd53ef470d5372ac60bda3df023`.
- Project `lake-manifest.json` SHA-256: `948a91a6b3c52e0b640d0dadc1bf84cf967403244ac590c162c005c2544a439e`.
- Comparator configuration: `Palomar/BooleanFullRank/comparator.json`.

The Challenge imports only four Mathlib modules. The Solution does not import the Challenge; it imports `BilinearComplexity.BooleanRankGeneric` and repeats the Challenge's definitions literally. Because both copies reduce to the same `Bool` carrier, `or`/`and` operations, finite row-span predicate, `Nat.find` minimization, finite count, and real fraction, the three source theorems close the package declarations by definitional equality (`exact`). Thus the bridge preserves least existing-row spanning rank rather than replacing it with factorization/rectangle-cover rank or rank over `ZMod 2`.

## Challenge elaboration

Immediately before the final command, `tool_atop` reported 8 cores, 23.46 GiB total memory, 0.78 GiB used, and 22.69 GiB available. The bounded one-core command compiled the Challenge to a fresh private output:

```sh
ulimit -v 22544384
timeout 240s taskset -c 0 lake env lean -M 7000 -j 1 \
  -o /tmp/yah/subagent/boolean-fullrank-package-prover-415bf0d/Challenge.olean \
  Palomar/BooleanFullRank/Challenge.lean
```

Exit status: `0`.

Exact output:

```text
Palomar/BooleanFullRank/Challenge.lean:116:8: warning: declaration uses `sorry`
Palomar/BooleanFullRank/Challenge.lean:121:8: warning: declaration uses `sorry`
Palomar/BooleanFullRank/Challenge.lean:126:8: warning: declaration uses `sorry`
@one_sub_le_fullRowRankFraction : ∀ {n : ℕ}, 2 ≤ n → 1 - ↑n ^ 2 * (3 / 4) ^ n ≤ fullRowRankFraction n
fullRowRankFraction_le_one : ∀ (n : ℕ), fullRowRankFraction n ≤ 1
fullRowRankFraction_tendsto_one : Tendsto fullRowRankFraction atTop (nhds 1)
```

Retained final log: `/tmp/yah/subagent/boolean-fullrank-package-prover-415bf0d/logs/challenge-final.log`.

There are three and only three `sorry` occurrences in the package Lean files, all in these selected Challenge theorem bodies. Solution contains none. Definitions and ground-truth examples elaborate without holes.

## Exact-source cache provenance

The user authorized read-only reuse of `/home/exedev/p/proofs/.lake/build/lib/lean`. Before reuse, the following inputs were compared:

| Input | Campaign workspace SHA-256 | `/home/exedev/p/proofs` SHA-256 | Result |
|---|---|---|---|
| `lean-toolchain` | `02f25adee7c1d6bf2e95b7b5b13f45b9892c7dd53ef470d5372ac60bda3df023` | same | exact match |
| `lake-manifest.json` | `948a91a6b3c52e0b640d0dadc1bf84cf967403244ac590c162c005c2544a439e` | same | exact match |
| `Proofs/BilinearComplexity/BooleanRank.lean` | `4a5d7acafcce95a6c7f9af5916ac61b522b4c32e3ba4eb0c04fc67e2eb432fa9` | same | exact match |
| `Proofs/BilinearComplexity/BooleanRankGeneric.lean` | `f44b2279ed080c926736481de4d8cae5cfafb63a94b46c763a18fbdb5ff2212f` | same | exact match |

The external prerequisite olean hashes were:

```text
BooleanRank.olean        6e36e6b159b93e82a13bc0a5b9156b985296575a53d545e4d4ccd7ef33a887f1
BooleanRankGeneric.olean 2df810a06dc6e774890c4794c6736920eb9253f2ed3287dce4cffe73c9468962
```

The external and campaign `lakefile.toml` files differ because the campaign root contains the current `Palomar` library configuration. This difference was not treated as source equivalence; equivalence was established for the toolchain, complete dependency manifest, and the two imported source modules. The external oleans were only used as compiled forms of those byte-identical imported sources.

## Solution compilation and axiom audit

Immediately before the final successful command, `tool_atop` reported 8 cores, 23.46 GiB total memory, 0.80 GiB used, and 22.66 GiB available. The source-verified prerequisite directory was prepended to the normal Lake environment, and the Solution was compiled to a fresh private output:

```sh
export LEAN_PATH="/home/exedev/p/proofs/.lake/build/lib/lean:$(lake env printenv LEAN_PATH)"
ulimit -v 22544384
timeout 300s taskset -c 0 lean -M 9000 -j 1 \
  -o /tmp/yah/subagent/boolean-fullrank-package-prover-415bf0d/Solution.olean \
  Palomar/BooleanFullRank/Solution.lean
```

Exit status: `0`.

Exact output:

```text
@one_sub_le_fullRowRankFraction : ∀ {n : ℕ}, 2 ≤ n → 1 - ↑n ^ 2 * (3 / 4) ^ n ≤ fullRowRankFraction n
fullRowRankFraction_le_one : ∀ (n : ℕ), fullRowRankFraction n ≤ 1
fullRowRankFraction_tendsto_one : Tendsto fullRowRankFraction atTop (nhds 1)
'Palomar.BooleanFullRank.one_sub_le_fullRowRankFraction' depends on axioms: [propext, Classical.choice, Quot.sound]
'Palomar.BooleanFullRank.fullRowRankFraction_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Palomar.BooleanFullRank.fullRowRankFraction_tendsto_one' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Retained log: `/tmp/yah/subagent/boolean-fullrank-package-prover-415bf0d/logs/solution-direct-final.log`.

These are fresh `#print axioms` commands in `Solution.lean`, not copied reports from the source file. They establish the permitted closure for each fully qualified selected theorem.

## Targeted Lake build failure

Two bounded, one-core attempts at exactly the requested target were made; no whole-repository build was run. Immediately before the first, the host had 22.26 GiB available; immediately before the second, 22.65 GiB was available. Commands used the same 21.5 GiB virtual-address ceiling:

```sh
ulimit -v 22544384
timeout 720s taskset -c 0 lake --no-ansi build \
  Palomar.BooleanFullRank.Solution
```

and, after copying the source-verified prerequisite artifacts into the campaign's private `.lake` build directory:

```sh
ulimit -v 22544384
timeout 300s taskset -c 0 lake --no-ansi build \
  Palomar.BooleanFullRank.Solution
```

Both attempts unexpectedly chose to rebuild `BilinearComplexity.BooleanRank`. After 213 seconds and 174 seconds respectively, Lean aborted with exit code `134`:

```text
libc++abi: terminating due to uncaught exception of type std::bad_alloc: std::bad_alloc
error: Lean exited with code 134
Some required targets logged failures:
- BilinearComplexity.BooleanRank
error: build failed
```

Retained logs:

- `/tmp/yah/subagent/boolean-fullrank-package-prover-415bf0d/logs/solution-build.log`
- `/tmp/yah/subagent/boolean-fullrank-package-prover-415bf0d/logs/solution-lake-final.log`

No broader build, cache reconstruction, dependency update, toolchain upgrade, or repeated Lake retry was attempted. The later successful direct compilation above avoided rebuilding the byte-identical prerequisite and is the positive mechanical result.

## Comparator status

**Status: NOT RUN (missing executables and toolchain mismatch).** No Comparator result is claimed.

A non-executing preflight found:

```text
comparator: MISSING
landrun: MISSING
nanoda_bin: MISSING
lean4export: MISSING
local comparator source lean-toolchain: leanprover/lean4:v4.34.0-rc1
project lean-toolchain: leanprover/lean4:v4.33.0-rc1
local comparator executable: MISSING
```

The locally available Comparator source therefore targets a newer Lean release than this project, and neither it nor its trusted verifier dependencies is built or installed. In accordance with the task constraint, no verifier infrastructure installation, second toolchain setup, or futile invocation was attempted. `enable_nanoda` remains `true` in the configuration as required; unavailable tooling was not bypassed by weakening the configuration.

## Declaration inventory

The package namespace is `Palomar.BooleanFullRank`. Challenge and Solution each declare the same:

- `BoolSemiring`: a fresh `Bool` carrier with `+ = Bool.or` and `* = Bool.and`;
- `BoolMatrix m n := Fin m → Fin n → BoolSemiring`;
- `rowsSum` and `rowSpan`, including the empty Boolean sum;
- `BoolRowRankLE`, requiring a subset of existing rows of cardinality at most `r` to have the full row span;
- `exists_boolRowRankLE` and `boolRowRank := Nat.find ...`, making the rank a genuine minimum rather than an asserted answer;
- `fullRowRankCount` and `fullRowRankFraction` over all square matrices;
- the selected quantitative lower bound, universal upper bound, and limit theorem.

Ground examples jointly witness the Boolean-semiring laws, matrix domain, row-sum/span definitions, rank predicate, minimization at a concrete zero matrix, and the nonvacuous `2 ≤ n` hypothesis.

## Review and attribution boundary

All package construction and verification recorded here was AI-assisted, with no subagents or agent reviewers. The mathematical source theorem in `Proofs/BilinearComplexity/BooleanRankGeneric.lean` is repository work and is also disclosed there as AI-assisted. Global novelty and priority are unestablished. No authoritative human formalization author or responsible maintainer was available, so `formalization.yaml` deliberately leaves both required identity lists empty and records that as a blocker. USER review remains pending.
