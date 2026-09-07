# Verification record: Fubini modular periodicity

## Status

- **Challenge elaboration:** PASS. Its sole warning is the intentional theorem hole.
- **Solution elaboration:** PASS, independently of the Challenge module.
- **Selected theorem type:** PASS; Challenge and Solution emitted the same full type.
- **Selected theorem axiom audit:** PASS. The Solution theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`.
- **Comparator:** NOT RUN — required verifier executables are unavailable and the available Comparator source targets a newer Lean toolchain.
- **Human review:** PENDING. USER review is the sole review gate; no submission, acceptance, or approval is asserted.

## Revisions, tools, and cache provenance

- Assigned campaign base: `117a6e3949ca41075e133e350e38d9d2fbfdd8e2`.
- Final workspace output revision observed with `jj --ignore-working-copy log -r @`: `6f15044016c55c286ee1b15c1846989f9320b629`.
- Lean: `4.33.0-rc1`, commit `62eed1db4d67327ec8120be05f1a1b0847d74561`, `x86_64-unknown-linux-gnu`, Release build.
- Lake: `5.0.0-src+62eed1d` (Lean `4.33.0-rc1`).
- Mathlib manifest revision: `3edb3c0658f69f197b1e501b1f7623f3f7b3898c`.
- Comparator configuration: `Palomar/FubiniModPeriodicity/comparator.json`.

The successful Solution elaboration reused the read-only cache at
`/home/exedev/p/proofs/.lake/build/lib/lean` through `LEAN_PATH`. Before use,
byte-for-byte comparisons succeeded for this workspace versus
`/home/exedev/p/proofs` for all of:

```text
Proofs/Enumerative/FubiniMod.lean
Proofs/Enumerative/Fubini.lean
lake-manifest.json
lean-toolchain
```

No cache was copied or reconstructed, no whole-project build was run, no
project configuration was changed, and no toolchain or verifier was installed.

## Independent declaration surfaces

`Challenge.lean` imports only these Mathlib modules:

```lean
Mathlib.Data.Nat.Choose.Sum
Mathlib.Data.Nat.ModEq
Mathlib.Data.Nat.Totient
```

`Solution.lean` does not import Challenge. It repeats the same definition and
theorem signature, proves by strong induction that its recurrence-defined
`fubini` equals `A051293.fubini`, and transports
`A000670.fubini_mod_eventuallyPeriodic_conjecture` across that local bridge.
It does not state or use a generalized `G(exp(x)-1)` theorem.

Whitespace-normalized source comparisons gave identical hashes for the two
surfaces:

```text
fubini definition                    8e6727122c9e60a409264c782f12b3475174766dc4e223516fb2f7b742571e12
fubini_mod_eventuallyPeriodic type   759989ca5fa790cb55d4f41f37fb17af5a1db7ceffb67c1382e0094ba15a25e8
```

Both modules instantiate the theorem at `k = 1`. This checks jointly that the
smallest allowed modulus is not excluded and that the existential conclusion
still requires a strictly positive period.

## Challenge elaboration

Immediately before the successful command, `tool_atop` reported 8 cores,
23.46 GiB total memory, 0.89 GiB used, and 22.57 GiB available. The successful
bounded command was:

```sh
timeout 240s lake env lean -M 6000 -j1 \
  Palomar/FubiniModPeriodicity/Challenge.lean
```

Exit status: `0`. Exact output:

```text
Palomar/FubiniModPeriodicity/Challenge.lean:31:8: warning: declaration uses `sorry`
fubini_mod_eventuallyPeriodic : ∀ (k : ℕ),
  1 ≤ k → ∃ N P, P ∣ k.totient ∧ 0 < P ∧ ∀ (n : ℕ), N ≤ n → fubini (n + P) ≡ fubini n [MOD k]
```

The complete retained log is
`/tmp/yah/subagent/fubini-periodicity-package-prover-e91a256/challenge-final.log`.
The warning is the one intended Challenge theorem hole; no definition contains
a `sorry`.

An earlier bounded Challenge attempt was not treated as verification. It
exited `1` because proposed ground examples at indices 0, 2, and 3 did not
reduce through the well-founded recursive definition using the attempted
proof terms. The exact diagnostics were:

```text
Type mismatch: rfl ... expected fubini 0 = 1
unsolved goals: ∑ x, Nat.choose 2 ↑x * fubini ↑x = 3
unsolved goals: ∑ x, Nat.choose 3 ↑x * fubini ↑x = 13
```

The final pair instead retains direct kernel-checked boundary examples at
indices 0 and 1. The failed-attempt log is
`/tmp/yah/subagent/fubini-periodicity-package-prover-e91a256/challenge.log`.

## Solution elaboration and fresh axiom audit

Immediately before elaboration, `tool_atop` reported 8 cores, 23.46 GiB total
memory, 0.90 GiB used, and 22.56 GiB available. The successful command was:

```sh
timeout 360s lake env bash -c \
  'export LEAN_PATH=/home/exedev/p/proofs/.lake/build/lib/lean:$LEAN_PATH; \
   exec lean -M 9000 -j1 Palomar/FubiniModPeriodicity/Solution.lean'
```

Exit status: `0`. Exact output:

```text
fubini_mod_eventuallyPeriodic : ∀ (k : ℕ),
  1 ≤ k → ∃ N P, P ∣ k.totient ∧ 0 < P ∧ ∀ (n : ℕ), N ≤ n → fubini (n + P) ≡ fubini n [MOD k]
'Palomar.FubiniModPeriodicity.fubini_mod_eventuallyPeriodic' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The complete retained log is
`/tmp/yah/subagent/fubini-periodicity-package-prover-e91a256/solution.log`.
This is a fresh `#print axioms` result from the final Solution source. A source
audit found no `sorry`, `native_decide`, or `Lean.ofReduceBool` in Solution.
The selected theorem therefore has exactly the permitted axiom footprint and
no `sorryAx` dependency.

## Comparator tooling blocker

**Comparator status: NOT RUN.** No Comparator pass is claimed. A PATH preflight
found all four required executables absent:

```text
comparator: MISSING
landrun: MISSING
lean4export: MISSING
nanoda_bin: MISSING
```

The available Comparator source under
`/home/exedev/p/yah-upstreams/issue-490/comparator` declares
`leanprover/lean4:v4.34.0-rc1`, newer than this project's pinned
`leanprover/lean4:v4.33.0-rc1`, and its Comparator executable is not built.
Per the package constraints, no incompatible invocation was repeated and no
verifier build, dependency reconstruction, or toolchain upgrade was attempted.
`comparator.json` keeps `enable_nanoda: true` and the explicit permitted axiom
list rather than weakening verification to bypass the missing infrastructure.

## Scope, attribution, and review boundary

The selected theorem concerns only the Fubini/ordered Bell sequence. The
Solution bridge is local and recurrence-specific. The mathematical result is
attributed to Bjorn Poonen, *Periodicity of a Combinatorial Sequence*, The
Fibonacci Quarterly 26 (1988), 70–76, especially Theorems 2 and 6. Peter
Bala's 2022 OEIS A000670 comment is recorded as a later conjectural
formulation, not as a new theorem or priority event. No unsupported Barsky
attribution is made.

All packaging and mechanical verification recorded here were AI-assisted.
No human formalization author or responsible maintainer was established, so
`formalization.yaml` leaves those required human fields empty and records them
as metadata blockers. USER mathematical and source-fidelity review remains
pending and is not replaced by this elaboration record.
