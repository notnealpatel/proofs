# Verification record: arbitrary-base fixed-divisor covering

## Current mechanical verification

[Authoritative campaign manifest](../Wave4ComparatorEvidence.yaml): **PASS** for every declaration selected by this package’s `comparator.json`. Earlier text below is historical and superseded. Human review remains **UNCHECKED**; this makes no claim of Palomar acceptance, submission, or publication.

## Status

- **Challenge elaboration:** PASS. Its only `sorry` is the intentional hole in the headline fixed-divisor theorem.
- **Solution compilation:** PASS from the independent `Solution.lean` source.
- **Exact selected signatures:** PASS.
- **Selected theorem axiom audit:** PASS. Both selected declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`; neither depends on `sorryAx`.
- **Comparator / landrun / lean4export / nanoda:** **NOT RUN** because the required executables are absent. This is not a Comparator pass.
- **Human review:** PENDING. USER is the sole review gate; no agent or parent mathematical review was performed.

## Scope and revisions

The assigned campaign base is `ee0cb27655f6bb6c37e8647c79184745017c5b24`. The pre-final working-copy revision observed with `jj --ignore-working-copy` was `30d5d5d7d7745e7e6ff7e3d57e415230fe90d062`; the harness owns the final workspace snapshot, and the exact finalized output revision is reported with the package return rather than guessed in this file.

Only these five allowlisted package files were created or modified:

- `Palomar/FixedDivisorCovering/Challenge.lean`
- `Palomar/FixedDivisorCovering/Solution.lean`
- `Palomar/FixedDivisorCovering/comparator.json`
- `Palomar/FixedDivisorCovering/formalization.yaml`
- `Palomar/FixedDivisorCovering/verification.md`

`README.md`, `Proofs/`, `References/`, root configuration, and other candidates were not modified. No subagent, reviewer, or submission operation was used.

## Toolchain and source provenance

- Lean: `4.33.0-rc1`, commit `62eed1db4d67327ec8120be05f1a1b0847d74561`, `x86_64-unknown-linux-gnu`, Release build.
- Lake: `5.0.0-src+62eed1d` (Lean `4.33.0-rc1`).
- Project `lean-toolchain` SHA-256: `02f25adee7c1d6bf2e95b7b5b13f45b9892c7dd53ef470d5372ac60bda3df023`.
- Project `lake-manifest.json` SHA-256: `948a91a6b3c52e0b640d0dadc1bf84cf967403244ac590c162c005c2544a439e`.
- Mathlib manifest revision: `3edb3c0658f69f197b1e501b1f7623f3f7b3898c`.
- Reused source `Proofs/Erdos/Covering/FixedDivisor.lean` SHA-256: `b736484a135909c4581c1186ec39609db8b5632f1e0c6e48d69b8a203e0fbc77`.

The read-only build cache at `/home/exedev/p/proofs/.lake/build/lib/lean` was reused through one coherent `LEAN_PATH` package root. Before reuse, the working source, manifest, and toolchain hashes were compared with `/home/exedev/p/proofs`; all three matched byte-for-byte. The exact reused artifacts were:

- `Erdos/Covering/FixedDivisor.olean`: SHA-256 `d454ef33fec263e7f7908ad88adfebc9e6a1720479776a238fb2923a950c2b09`, 383464 bytes.
- `Erdos/Covering/Basic.olean`: SHA-256 `eb8fee095770602eb180b4b9cef3542804d33f618ef007b2745b1f1f6547abce`, 135632 bytes.

No dependency, cache, toolchain, or whole-repository rebuild was performed. The final package Solution `.olean` was written only to the private scratch directory; its SHA-256 was `a3b9e5171dba789ee8b6dc8009b7f87b5bd05dbf8db0953fabc55f99c96a9160`.

Package-source hashes before adding this verification record were:

- `Challenge.lean`: `177e0c5a69ff7fab7fff2ae8120689ff410d9e03c23208ddc87d16a9dc3ff606`
- `Solution.lean`: `361ab0e610b97df9dff72820b998b57724f42f58c392240b75d7336c77d5a6b7`
- `comparator.json`: `d5fc114bc47a759106dfbd2dc09ffa7283d18c5fb84caa57e4e693c314890fc7`
- `formalization.yaml`: `34350e9fafe3a87ab54363c0cae5cc3ddc5920ef494c3fae86974a0392166d4c`

## Challenge elaboration

Immediately before the successful run, the host reported 8 cores, 23.46 GiB total physical memory, 0.83 GiB used, and 22.63 GiB available. The successful bounded command was:

```sh
ulimit -v 20971520
timeout 180s taskset -c 1 lake env lean -M 5000 -j 1 \
  Palomar/FixedDivisorCovering/Challenge.lean
```

Exit status: `0`. Exact relevant output:

```text
Palomar/FixedDivisorCovering/Challenge.lean:69:8: warning: declaration uses `sorry`
@IsFixedDivisorSystemBase.exists_mem_fixedDivisors_dvd : ∀ {b : ℕ} {A B : ℤ} {T : Finset (ℕ × ℕ × ℕ)},
  IsFixedDivisorSystemBase b A B T → ∀ (n : ℕ), ∃ p ∈ fixedDivisors T, ↑p ∣ A * ↑b ^ n + B
@IsFixedDivisorSystemBase.not_prime : ∀ {b : ℕ} {A B : ℤ} {T : Finset (ℕ × ℕ × ℕ)},
  IsFixedDivisorSystemBase b A B T →
    ∀ {M N n : ℕ}, (∀ p ∈ fixedDivisors T, p ≤ M) → ↑N = A * ↑b ^ n + B → M < N → ¬Nat.Prime N
```

Complete log: `/tmp/yah/subagent/fixed-divisor-package-prover-1ca793c/logs/challenge-final.log`.

The one earlier attempt used the same narrow source with an 8 GiB virtual-memory ceiling and CPU 0. It exited `1` with:

```text
libc++abi: terminating due to uncaught exception of type lean::exception: failed to create thread
```

This was treated as a resource failure, not theorem evidence. The method was changed by raising the virtual-memory ceiling to 20 GiB and moving to CPU 1; it was not retried unchanged. Complete failure log: `/tmp/yah/subagent/fixed-divisor-package-prover-1ca793c/logs/challenge-initial.log`.

## Independent Solution compilation

Immediately before the final compilation, the host reported 8 cores, 23.46 GiB total physical memory, 3.82 GiB used, and 19.64 GiB available. This left adequate physical headroom, while the process tree remained pinned to one core. The command was:

```sh
mkdir -p /tmp/yah/subagent/fixed-divisor-package-prover-1ca793c/olean/Palomar/FixedDivisorCovering
ulimit -v 18874368
export LEAN_PATH=/home/exedev/p/proofs/.lake/build/lib/lean
timeout 240s taskset -c 3 lake env lean -M 7000 -j 1 \
  -o /tmp/yah/subagent/fixed-divisor-package-prover-1ca793c/olean/Palomar/FixedDivisorCovering/Solution.olean \
  Palomar/FixedDivisorCovering/Solution.lean
```

Exit status: `0`. The emitted selected signatures match the Challenge output above. The same compilation emitted:

```text
'Palomar.FixedDivisorCovering.IsFixedDivisorSystemBase.exists_mem_fixedDivisors_dvd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Palomar.FixedDivisorCovering.IsFixedDivisorSystemBase.not_prime' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Complete log: `/tmp/yah/subagent/fixed-divisor-package-prover-1ca793c/logs/solution-final.log`.

The Solution does not import the Challenge. It repeats the same three public definitions, certificate structure, examples, and selected theorem signatures, then converts the literal package certificate to `Erdos.Covering.IsFixedDivisorSystemBase`. The headline calls the existing `.exists_mem_fixedDivisors_dvd`; the corollary calls the existing `.not_prime` with the explicit bound translated definitionally.

## Separate exact signature and axiom audit

A separate audit imported the scratch-built `Palomar.FixedDivisorCovering.Solution` artifact and checked both selected declarations and both source declarations. Immediately before this run, the host reported 0.83 GiB used and 22.63 GiB available. Command:

```sh
ulimit -v 18874368
export LEAN_PATH=/tmp/yah/subagent/fixed-divisor-package-prover-1ca793c/olean:/home/exedev/p/proofs/.lake/build/lib/lean
timeout 180s taskset -c 4 lake env lean -M 7000 -j 1 \
  /tmp/yah/subagent/fixed-divisor-package-prover-1ca793c/AxiomAudit.lean
```

Exit status: `0`. Exact output:

```text
@Palomar.FixedDivisorCovering.IsFixedDivisorSystemBase.exists_mem_fixedDivisors_dvd : ∀ {b : ℕ} {A B : ℤ}
  {T : Finset (ℕ × ℕ × ℕ)},
  Palomar.FixedDivisorCovering.IsFixedDivisorSystemBase b A B T →
    ∀ (n : ℕ), ∃ p ∈ Palomar.FixedDivisorCovering.fixedDivisors T, ↑p ∣ A * ↑b ^ n + B
@Palomar.FixedDivisorCovering.IsFixedDivisorSystemBase.not_prime : ∀ {b : ℕ} {A B : ℤ} {T : Finset (ℕ × ℕ × ℕ)},
  Palomar.FixedDivisorCovering.IsFixedDivisorSystemBase b A B T →
    ∀ {M N n : ℕ},
      (∀ p ∈ Palomar.FixedDivisorCovering.fixedDivisors T, p ≤ M) → ↑N = A * ↑b ^ n + B → M < N → ¬Nat.Prime N
'Palomar.FixedDivisorCovering.IsFixedDivisorSystemBase.exists_mem_fixedDivisors_dvd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Palomar.FixedDivisorCovering.IsFixedDivisorSystemBase.not_prime' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Erdos.Covering.IsFixedDivisorSystemBase.exists_mem_fixedDivisors_dvd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Erdos.Covering.IsFixedDivisorSystemBase.not_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Complete log: `/tmp/yah/subagent/fixed-divisor-package-prover-1ca793c/logs/axiom-audit.log`. This is the kernel declaration-level audit: there is no `sorryAx`, `Lean.ofReduceBool`, `native_decide`, or custom axiom in either selected closure.

## Metadata and static checks

- `comparator.json` parsed with `jq empty`.
- `formalization.yaml` parsed with Python `yaml.safe_load`; the parsed version was `v0.4` and there were exactly two `main_results` entries.
- A source scan found exactly one `sorry` across Challenge and Solution, at the intentional Challenge headline; it found no `native_decide`, `Lean.ofReduceBool`, or custom `axiom` declaration.
- Challenge and Solution use the same literal declarations and selected signatures. The Challenge imports only three targeted Mathlib modules; the Solution imports only `Erdos.Covering.FixedDivisor`.
- The concrete base-4 certificate example jointly instantiates all four certificate fields. It is evidence that the arbitrary-base hypotheses are satisfiable, not a replacement for the general theorem.

## Comparator tooling blocker

**Status: NOT RUN.** A PATH preflight reported all four required executables missing:

```text
comparator: MISSING
landrun: MISSING
nanoda_bin: MISSING
lean4export: MISSING
```

The locally available Comparator source requests `leanprover/lean4:v4.34.0-rc1`, whereas the project is pinned to `leanprover/lean4:v4.33.0-rc1`. Per the task constraints, no executable invocation was attempted, no verifier project was built, no toolchain was installed or upgraded, and the check was not repeated. `enable_nanoda` remains `true` in the configuration rather than being weakened to bypass the missing trusted toolchain.

## Mathematical boundary recorded by the package

The headline proves listed divisibility for every natural exponent, over integers so negative `A` or `B` need no totalized natural subtraction. It does **not** infer compositeness from divisibility alone. The selected `not_prime` corollary requires every listed divisor to satisfy `p ≤ M` and then requires `M < N`. This excludes `p=N`; without that strict proper-divisor control, the base-14 value `4*14^0+1=5` demonstrates the failure mode directly. No concrete-number novelty or prior-formalization claim is made.
