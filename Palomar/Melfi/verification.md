# Verification record: Melfi practical-number sum

## Status

- **Challenge elaboration:** PASS (the single warning is the intentional challenge hole).
- **Solution build:** PASS.
- **Selected theorem axiom audit:** PASS. The selected theorem uses only `propext`, `Classical.choice`, and `Quot.sound`; it does not depend on `sorryAx`.
- **Comparator:** NOT RUN as of this initial record. The bounded final attempt and its exact outcome are recorded in the final section below.
- **Human review:** PENDING. No human approval is asserted by this package.

## Revisions and tools

- Assigned campaign base: `8b4bc120463010dc27d1db6bde2e13bdf72280ce`.
- Packaging worktree parent observed during the final tranche: `50e7e8f61a56443cd269be2042687109fe74a167`.
- Lean: `4.33.0-rc1`, commit `62eed1db4d67327ec8120be05f1a1b0847d74561`, `x86_64-unknown-linux-gnu`, Release build.
- Lake: `5.0.0-src+62eed1d` (Lean `4.33.0-rc1`).
- Mathlib manifest revision: `3edb3c0658f69f197b1e501b1f7623f3f7b3898c`.
- Comparator configuration: `Palomar/Melfi/comparator.json`.

The theorem is source-based: `Palomar.Melfi.Solution` imports the repository theorem `Nat.even_eq_practical_add_practical` from `Enumerative.MelfiPracticalSum` and transports it across the literally matching practical-number predicate. The package does not claim that a human compared this Lean proof route with Melfi's published proof.

## Challenge elaboration

The successful bounded command was:

```sh
ulimit -v 8388608
timeout 180s lake env lean -M 5000 -j 1 Palomar/Melfi/Challenge.lean
```

Exit status: `0`.

Output:

```text
Palomar/Melfi/Challenge.lean:37:8: warning: declaration uses `sorry`
@even_eq_practical_add_practical : ∀ {n : ℕ}, Even n → 0 < n → ∃ q r, Practical q ∧ Practical r ∧ q + r = n
```

The complete retained log is `/tmp/yah/subagent/melfi-package-prover-6374804/challenge-final.log`. The `sorry` is intentional and occurs only in the challenge theorem.

## Targeted Solution build

Immediately before the successful build, the host reported 8 cores, 23.46 GiB total memory, 0.80 GiB used, and 22.66 GiB available. The command restricted the process tree to one CPU because an earlier unrestricted Lean process failed while creating a thread:

```sh
ulimit -v 22544384
timeout 720s taskset -c 0 lake --no-ansi build Palomar.Melfi.Solution
```

Exit status: `0`.

Relevant exact output:

```text
⚠ [8694/8696] Built Enumerative.Practical (27s)
warning: Proofs/Enumerative/Practical.lean:595:8: declaration uses `sorry`
info: Proofs/Enumerative/Practical.lean:1039:0: 'Nat.coleman_multiperfect_practical' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
ℹ [8695/8696] Built Enumerative.MelfiPracticalSum (6.1s)
info: Proofs/Enumerative/MelfiPracticalSum.lean:571:0: 'Nat.even_eq_practical_add_practical' depends on axioms: [propext, Classical.choice, Quot.sound]
ℹ [8696/8696] Built Palomar.Melfi.Solution (3.8s)
info: Palomar/Melfi/Solution.lean:42:0: @even_eq_practical_add_practical : ∀ {n : ℕ}, Even n → 0 < n → ∃ q r, Practical q ∧ Practical r ∧ q + r = n
info: Palomar/Melfi/Solution.lean:43:0: 'Palomar.Melfi.even_eq_practical_add_practical' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (8696 jobs).
```

The complete retained log is `/tmp/yah/subagent/melfi-package-prover-6374804/solution-build-affinity1.log`.

The imported `Enumerative.Practical` module contains the archived, unrelated theorem `Nat.coleman_multiperfect_practical`, whose proof has a `sorry`. Importing that module does not by itself put `sorryAx` in the dependency closure of the selected Melfi theorem; the fresh audit below checks this distinction directly.

## Fresh selected-theorem axiom audit

The audit source imported `Palomar.Melfi.Solution`, printed the axiom closures of the wrapper theorem, the repository Melfi theorem, and the unrelated Coleman theorem, and checked both relevant full signatures. The first attempt under an 8 GiB virtual-memory ceiling failed while reading a Mathlib `.olean`; it was not treated as theorem evidence. Immediately before the successful retry, the host reported 23.46 GiB total memory, 0.81 GiB used, and 22.65 GiB available.

Successful command:

```sh
ulimit -v 22544384
timeout 180s taskset -c 0 lake env lean -M 9000 -j 1 \
  /tmp/yah/subagent/melfi-package-prover-6374804/MelfiAxiomAudit.lean
```

Exit status: `0`.

Exact output:

```text
'Palomar.Melfi.even_eq_practical_add_practical' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nat.even_eq_practical_add_practical' depends on axioms: [propext, Classical.choice, Quot.sound]
'Nat.coleman_multiperfect_practical' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
@Palomar.Melfi.even_eq_practical_add_practical : ∀ {n : ℕ},
  Even n → 0 < n → ∃ q r, Palomar.Melfi.Practical q ∧ Palomar.Melfi.Practical r ∧ q + r = n
@Nat.even_eq_practical_add_practical : ∀ {n : ℕ}, Even n → 0 < n → ∃ q r, q.Practical ∧ r.Practical ∧ q + r = n
```

The complete retained log is `/tmp/yah/subagent/melfi-package-prover-6374804/axiom-audit.log`. This establishes that the selected theorem is independent of the archived Coleman `sorryAx`.

## Earlier bounded failures

These failures motivated the successful narrow-import and CPU-affinity configuration; none was counted as verification:

1. Broad `import Mathlib` challenge attempts under 6/10 GiB virtual-memory ceilings failed to read private `.olean` artifacts. An 18 GiB attempt crossed Lean's memory threshold. Replacing the umbrella import with the allowlisted, sufficient `Mathlib.NumberTheory.Divisors` import made the challenge elaborate under 8 GiB.
2. The first targeted Solution build used:

   ```sh
   ulimit -v 18874368
   timeout 720s lake --no-ansi build Palomar.Melfi.Solution
   ```

   It reached `[8694/8696] Building Enumerative.Practical`, then exited `1` after Lean aborted with code `134`:

   ```text
   libc++abi: terminating due to uncaught exception of type lean::exception: failed to create thread
   error: Lean exited with code 134
   ```

   Complete log: `/tmp/yah/subagent/melfi-package-prover-6374804/solution-build.log`.
3. The first standalone axiom audit used an 8 GiB virtual-memory ceiling and exited `1` with:

   ```text
   error: failed to read file '.../Mathlib/Algebra/Quaternion.olean'
   ```

   The later resource-bounded audit above passed.

## Comparator attempt

**Status: NOT RUN (required verifier executables unavailable).** This is not a Comparator pass.

Immediately before the bounded attempt, the host reported 8 cores, 23.46 GiB total memory, 0.81 GiB used, and 22.66 GiB available. The locally available Comparator source was pinned at revision `777e7f56119efc0fac34003db4efe831e0b53723`, but it declares Lean `4.34.0-rc1`, while this project is pinned to Lean `4.33.0-rc1`. Its executable had not been built. No `landrun`, `nanoda_bin`, or `lean4export` executable was installed in `PATH`. Although compatible lean4export tag `v4.33.0-rc1` resolves to commit `af5aa64bb914c3c2c781f378088dbd38acf4f804`, neither that exporter nor the other trusted verifier components was installed. Building several verifier projects and a second Lean toolchain would have violated this closing tranche's prohibition on toolchain upgrades and elaborate infrastructure setup.

The one bounded invocation attempt was:

```sh
timeout 30s lake env \
  /home/exedev/p/yah-upstreams/issue-490/comparator/.lake/build/bin/comparator \
  Palomar/Melfi/comparator.json
```

Exit status: `255`.

Exact preflight and error output:

```text
Comparator source revision: 777e7f56119efc0fac34003db4efe831e0b53723
Comparator source lean-toolchain: leanprover/lean4:v4.34.0-rc1
Project lean-toolchain: leanprover/lean4:v4.33.0-rc1
comparator executable: MISSING
landrun executable: MISSING
nanoda_bin executable: MISSING
lean4export executable: MISSING
--- bounded attempted invocation ---
timeout 30s lake env /home/exedev/p/yah-upstreams/issue-490/comparator/.lake/build/bin/comparator Palomar/Melfi/comparator.json
could not execute external process '/home/exedev/p/yah-upstreams/issue-490/comparator/.lake/build/bin/comparator'
```

Complete retained log: `/tmp/yah/subagent/melfi-package-prover-6374804/comparator-attempt.log`. The existing `comparator.json` was therefore not changed merely to bypass unavailable trusted tooling. The successful Lean build and exact `#print axioms` audit above remain technical evidence, but they are explicitly not a substitute for Comparator.

## Review boundary and metadata blocker

All implementation and packaging work disclosed here was AI-assisted. USER review is the sole review gate and remains pending. No human author of this formalization and no responsible human maintainer could be established from authoritative package material. Because Palomar metadata requires nonempty human author and responsible-maintainer identities, this is a concrete metadata blocker to submission. `formalization.yaml` leaves both required human lists empty and records the blocker explicitly rather than putting a placeholder, AI system, or invented person in a human identity field.
