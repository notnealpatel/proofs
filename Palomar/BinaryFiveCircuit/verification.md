# Verification record: binary five-circuit ambient classification

## Current mechanical verification

[Authoritative campaign manifest](../Wave4ComparatorEvidence.yaml): **PASS** for every declaration selected by this package’s `comparator.json`. Earlier text below is historical and superseded. Human review remains **UNCHECKED**; this makes no claim of Palomar acceptance, submission, or publication.

## Final technical status

- **Challenge elaboration: PASS.** The repaired independent model and concrete joint-satisfiability theorem elaborate; the only diagnostic is the intentional selected-theorem `sorry`.
- **Solution elaboration: PASS.** The final repaired Solution elaborates with no warnings or errors against the provenance-matched coherent project cache.
- **Model identity: PASS.** Challenge and Solution repeat the same 20,430-byte independent model/satisfiability block and the same selected theorem statement. They do not reuse identical names for different source and challenge definitions.
- **Semantic bridge: PASS.** `Palomar.BinaryFiveCircuit.Bridge.ambientInOrbit_iff_source` proves equivalence to the source presentation/orientation/action-witness semantics under exactly the selected theorem's hypotheses. This is a checked theorem, not an unresolved review item or an assumed completeness claim.
- **Axiom audits: PASS.** The selected theorem, orbit-equivalence theorem, and concrete satisfiability theorem each depend only on `propext`, `Classical.choice`, and `Quot.sound`.
- **Comparator / landrun / lean4export / nanoda: NOT RUN.** Required executables are unavailable; there is no independent-verifier pass.
- **Metadata: JSON and YAML parsing plus stated assertions PASS.** This is not full schema validation; human author and maintainer identities remain explicit metadata blockers.
- **USER review: PENDING.** USER is the sole reviewer. Mechanical verification is not a human-review outcome, and no submission, acceptance, or novelty is claimed.

The documentation-only finalization preserved both verified Lean files byte-for-byte and therefore did not rerun builds. Earlier failures and the invalid pre-repair pairing are retained below as superseded history, not current evidence.

## Verified bytes and identical independent statements

| Artifact | SHA-256 |
| --- | --- |
| `Challenge.lean` | `6ec93a09d659e8525dbf1344db97030c9bc39f8d9658db76c2c62a1378ae0808` |
| `Solution.lean` | `305e52187a421d05461f8e45e0eaaba835f4ed18f8783832901f5a91ed5558f6` |
| Common independent model/satisfiability block, 20,430 bytes | `4a69fde62093368030b265edeab0b3c14292f24ec4ff15d292d9cba2e7f60e24` |
| Identical selected theorem statement, excluding `:= by` and proof | `0674a92c6ae4e7fe6e84c51e832f6cfcefab00916bda50d41146f685c46546b6` |
| Preserved `README.md` | `846ad1d57da7883b157e973d5bb8ea4dc5ac6c53fbb99ee44e872e3830df7f0c` |

The common block starts at `set_option autoImplicit false` and ends immediately before the final `namespace Palomar.BinaryFiveCircuit` containing the selected theorem in Challenge; in Solution it ends immediately before `namespace Palomar.BinaryFiveCircuit.Bridge`. The statement comparison starts at `theorem finiteDimensional_ambient_fiveCircuit_classification` and ends before its ` := by`.

These exact slices were compared as strings, not merely compared by printed declaration names, and their SHA-256 digests were checked again during finalization. The shared model lives under `Palomar.BinaryFiveCircuit.Model`; the imported repository model remains under `BilinearComplexity`. Solution repeats the independent definitions rather than importing Challenge or replacing them with source aliases.

The headline remains universal in three arbitrary finite-dimensional F2 module ambients, with the original additive-group, module, and decidable-equality instances. It assumes exactly:

```lean
(hA : A.card = 2) (hB : B.card = 3) (hDisjoint : Disjoint A B)
(hEvaluation : stateEvaluation A = stateEvaluation B)
```

Its conclusion retains a unique `OrbitLabel` and paths from `A` to `B` and from `B` to `A`, both using intrinsic `AllModeMove`, both of length at most three and altitude at most four, and both factor-span confined to `A ∪ B`. No `Circuit`, chosen coordinates, orbit label, desired path, or certificate is supplied as a hypothesis. No coordinate-fixed weakening is made.

## Checked source-semantic equivalence and transport

All names in this section prefixed `Bridge` are in `Palomar.BinaryFiveCircuit.Bridge`.

1. `familyEquiv` and `labelEquiv` identify the independent four-family and thirteen-label types with the source types, with both inverse laws proved.
2. `selectedInvariant_source` derives the displayed thirteen-row pair-count table from the imported, kernel-checked `NormalizedBinaryOrbitInvariants.actualRows_eq`; the table is not assumed to be a certificate.
3. `adjacent_map_iff` and `crossCount_map` prove preservation and reflection of pair adjacency and preservation of ordered pair counts under injective coordinate embeddings. `invariant_normalized` transports those counts through any exact-span presentation.
4. `profile_perm` checks dimension-list permutation for each of the six source mode orientations. `ambientInOrbit_of_source` combines this with the source action-witness invariant theorem to prove the independent characterization from source orbit membership.
5. `invariant_label_unique` proves that the independent dimension/count data distinguish every label. For the converse direction, source classification supplies an existing source orbit; the proved label injectivity forces it to be the requested label.
6. `ambientInOrbit_iff_source` packages both directions. Its exact explicit hypotheses and result are:

```lean
[FiniteDimensional F2 U] [FiniteDimensional F2 V] [FiniteDimensional F2 W]
{A B : Model.BinaryAmbientCarrier.State U V W}
(hA : A.card = 2) (hB : B.card = 3) (hd : Disjoint A B)
(he : Model.BinaryAmbientCarrier.stateEvaluation A =
  Model.BinaryAmbientCarrier.stateEvaluation B)
(l : Model.NormalizedBinaryOrbitClassification.OrbitLabel) :
  Model.BinaryFiveCircuitCompiler.AmbientInOrbit l A B ↔
    BilinearComplexity.BinaryFiveCircuitCompiler.AmbientInOrbit
      (Bridge.labelEquiv l) A B
```

It also quantifies the same three ambient types, their additive-group and F2-module instances, and their decidable-equality instances. The source predicate on the right is the existential `ExactSpanPresentation` followed by `InOrbit` of normalized endpoints; `InOrbit` requires a mode orientation and a factorwise-GL/mode-action witness from the selected row. The bridge assumes neither the independent characterization nor source membership as a separate theorem premise: they are the two sides of its equivalence. No equivalence outside the exact displayed domain is asserted.

7. `move_iff` and `allModeMove_iff` prove equality of the independent and source intrinsic move laws by their constructors, including all six mode orders. `pathFromSource` translates concrete source paths without changing states. Its `_length`, `_altitude`, and `_vertices` theorems prove exact equalities, not just the desired bounds; `_confined` proves equivalence of factor-span confinement. States, tensor evaluation, and factor spans agree definitionally, as checked in the bridge elaboration.
8. The selected Solution theorem uses the checked orbit equivalence in both label-existence and label-uniqueness directions, and uses path transport to retain all four metric bounds and both confinement conclusions from the repository theorem.

This closes the former implementation mismatch. It does not count matching printed names as a semantic proof and does not relabel an unproved mathematical assertion as a USER-review obligation.

## Concrete joint satisfiability and boundary conditions

`Palomar.BinaryFiveCircuit.hypotheses_satisfiable`, repeated in both modules, proves:

```lean
∃ A B : State (Fin 4 → F2) F2 F2,
  A.card = 2 ∧ B.card = 3 ∧ Disjoint A B ∧
    stateEvaluation A = stateEvaluation B
```

The first factors are the four coordinate basis vectors and their sum; all second and third factors are `1`. The left endpoint uses the first two basis vectors, and the right uses the remaining two and the sum. The proof checks nonzero factors, exact cardinalities, disjointness, and the tensor identity using ordinary `decide` and tensor additivity. The ambient spaces carry the canonical finite-dimensional F2 instances. Thus all selected endpoint hypotheses are jointly satisfiable in a nonempty intended model; the theorem is not supported only by a vacuous zero-dimensional case. No nonemptiness assumption on an arbitrary ambient is needed, because the endpoint cardinality hypotheses exclude an empty carrier in any satisfying instance.

## Fresh final Lean checks

Logs below are local verification artifacts under `/tmp/yah/subagent/binary-five-package-prover-fad11ce/`; commands were bounded and single-threaded. `tool_atop` was sampled immediately before each expensive invocation.

### Challenge

Before this call, the host reported 8 cores, 23.46 GiB total memory, and 22.57 GiB available. From the assigned workspace:

```sh
ulimit -v 16777216
/usr/bin/time -f 'ELAPSED=%e MAX_RSS_KB=%M EXIT=%x' \
  timeout 180s taskset -c 1 lake env lean -M 7000 -j 1 \
  Palomar/BinaryFiveCircuit/Challenge.lean
```

Log: `challenge-final.log`.

```text
Palomar/BinaryFiveCircuit/Challenge.lean:489:8: warning: declaration uses `sorry`
ELAPSED=4.86 MAX_RSS_KB=2227892 EXIT=0
```

The warning points to the theorem declaration; the sole proof-hole token is on line 511. The concrete satisfiability theorem and the full selected signature were printed. Challenge imports only:

```text
Mathlib.Algebra.Field.ZMod
Mathlib.Data.Finset.SymmDiff
Mathlib.LinearAlgebra.Dimension.Finite
Mathlib.LinearAlgebra.FiniteDimensional.Defs
Mathlib.LinearAlgebra.TensorProduct.Finiteness
```

There are no project or Solution imports in Challenge.

### Solution

Before the final clean call, the host reported 8 cores, 23.46 GiB total memory, and 22.60 GiB available. The main tree was accessed only for its coherent cache; the subshell ensures the persistent working directory remains the assigned workspace:

```sh
(
  cd /home/exedev/p/proofs &&
  ulimit -v 16777216 &&
  /usr/bin/time -f 'ELAPSED=%e MAX_RSS_KB=%M EXIT=%x' \
    timeout 180s taskset -c 3 lake env lean -M 7000 -j 1 \
    /home/exedev/.yah/jj/01a07cfa-d323-732a-b33d-0a81d9175ff9/workspaces/dispatch-agent_O93qFZp_g4hTy7HIeGmjig/Palomar/BinaryFiveCircuit/Solution.lean
)
```

Log: `solution-final-clean.log`. Exit status is zero; the log contains no warnings or errors:

```text
ELAPSED=12.21 MAX_RSS_KB=6813392 EXIT=0
```

The final signature retains the three arbitrary ambient universes and all assumptions/conclusions listed above. Explicit `#check @...` commands also expose the bridge signatures, preventing silently added section premises from being hidden by notation. The exact axiom outputs, with line wrapping normalized, are:

```text
'Palomar.BinaryFiveCircuit.Bridge.ambientInOrbit_iff_source'
  depends on axioms: [propext, Classical.choice, Quot.sound]
'Palomar.BinaryFiveCircuit.hypotheses_satisfiable'
  depends on axioms: [propext, Classical.choice, Quot.sound]
'Palomar.BinaryFiveCircuit.finiteDimensional_ambient_fiveCircuit_classification'
  depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are audits of the actual repaired declarations, not of the obsolete source-only wrapper. They establish the displayed dependency closures; they do not audit every unrelated declaration in the imported project. The finalization rechecked the verified file hashes and did not rebuild unchanged proof files.

## Tool, source, and cache provenance

- Assigned campaign base: `ee0cb27655f6bb6c37e8647c79184745017c5b24`.
- Retained pre-repair checkpoint: `b94bff74309692e7b8efc39b5933c01ee0034b66`.
- Workspace revision observed on entry to documentation-only finalization: `de2884c036eda2c12e79c159040df98b691a5883`. This is not claimed as the final output revision; the final revision is reported in the handoff after the documentation edits, avoiding a self-referential revision identifier in this file.
- Lean: `4.33.0-rc1`, commit `62eed1db4d67327ec8120be05f1a1b0847d74561`, `x86_64-unknown-linux-gnu`, Release.
- Lake: `5.0.0-src+62eed1d` (Lean `4.33.0-rc1`).
- Mathlib manifest revision: `3edb3c0658f69f197b1e501b1f7623f3f7b3898c`.
- `lean-toolchain` SHA-256: `02f25adee7c1d6bf2e95b7b5b13f45b9892c7dd53ef470d5372ac60bda3df023`.
- `lake-manifest.json` SHA-256: `948a91a6b3c52e0b640d0dadc1bf84cf967403244ac590c162c005c2544a439e`.
- `Proofs/BilinearComplexity/BinaryFiveCircuitTheorem.lean` SHA-256: `83cb99f3c8ce5afa858c57f220cdc38b83d1fe13366e18845fbb22bf0cdd2dfe`.
- Cached `/home/exedev/p/proofs/.lake/build/lib/lean/BilinearComplexity/BinaryFiveCircuitTheorem.olean` SHA-256: `316c2de715fc17063d3356a1c78bedf57f5251e5e1864452bcfb965d3d4ad4a9`.

The assigned workspace and `/home/exedev/p/proofs` have identical toolchain and manifest files. All **157** `.lean` files directly under `Proofs/BilinearComplexity` were compared byte-for-byte with their main-tree counterparts: **zero differences**, including the exact source theorem. The final Solution invocation resolves imports from one coherent source-matched cache, not a mixture of partially rebuilt workspace modules and main-cache artifacts. No main-tree project or cache output was requested: the commands were `lake env lean` without `-o` or a build. The earlier persistent `cd` was corrected when identified; final invocations use a subshell. No verifier, toolchain, or dependency installation was performed.

## Superseded historical failures and incomplete evidence

The following records are deliberately retained. None is substituted for the final repaired checks.

1. **Early Challenge iterations:** `challenge-1`/`challenge-2` iterations had ordinary local elaboration errors. `challenge-3.log` subsequently passed with the then-intentional theorem hole, but it describes the older model and is not the final Challenge check.
2. **First targeted workspace Lake build:** the command below reached source prerequisite job `8723/8793`, then failed with exit status 1:

   ```sh
   ulimit -v 22544384
   timeout 720s taskset -c 2 lake --no-ansi build \
     Palomar.BinaryFiveCircuit.Solution
   ```

   ```text
   libc++abi: terminating due to uncaught exception of type lean::exception:
   failed to create thread
   ```

   Log: `solution-build.log`. No Solution elaboration error was reported, but this build did not establish a package pass. It was not repeated unchanged. The method switched to the provenance-matched coherent cache; no whole-repository rebuild or cache reconstruction followed. A cold build of the complete source dependency tree remains unverified here.
3. **Invalid pre-repair pair:** `solution-direct-cache.log` proved and audited a source-only wrapper. At checkpoint `b94bff...`, Challenge instead used an independent invariant characterization under source-looking names, with no machine-checked equivalence. Separate elaboration and similar printed names did **not** establish a matching package. The prior wording treating this as merely a review item was incorrect and is superseded by the actual independent-model copy and checked bridge now present.
4. **Earlier satisfiability attempts:** a temporary model initially could not import an unbuilt Challenge module; later `model-2.log` and `model-3.log` failed at tensor-equality elaboration. Those attempts were not integrated and establish no theorem. The repaired `hypotheses_satisfiable` proof is now integrated in both files and verified by the final logs.
5. **Bridge development:** `bridge-1.log` through `bridge-4.log` record failed scratch elaborations while resolving dependent indexing, finite row types, recursive path equations, and finite checks. `bridge-5.log` passed the repaired semantic bridge, satisfiability example, and selected theorem. Scratch errors are not current Solution errors.
6. **Final warning cleanup:** `solution-final.log` passed in 12.18 seconds with three unused-module-section-variable warnings on path metric lemmas. Only the corresponding `omit` declarations changed afterward; `solution-final-clean.log` then passed the final bytes with no warnings or errors. The current Solution digest is the clean checked digest in the table above.

## Package and metadata audits

The final source scan finds no `native_decide`, `Lean.ofReduceBool`, `sorryAx`, declared `axiom`, `@[implemented_by]`, `@[extern]`, `@[csimp]`, or `partial def` in either package Lean file. Searching for `sorry` returns exactly:

```text
Palomar/BinaryFiveCircuit/Challenge.lean:511:  sorry
```

Solution has no proof holes. The selected theorem's closure independently confirms the absence of unpermitted axioms.

`comparator.json` parses and selects only `Palomar.BinaryFiveCircuit.finiteDimensional_ambient_fiveCircuit_classification`, with permitted axioms `propext`, `Quot.sound`, and `Classical.choice`; `enable_nanoda` remains `true`. `formalization.yaml` parses as YAML and records schema version `v0.4`, the repaired equivalence and transport, empty human author/maintainer lists, empty reviewers, and pending USER review. Parsing and assertions do not constitute full metadata-schema validation.

The allowlist audit against the assigned base covers exactly:

```text
Palomar/BinaryFiveCircuit/Challenge.lean
Palomar/BinaryFiveCircuit/Solution.lean
Palomar/BinaryFiveCircuit/comparator.json
Palomar/BinaryFiveCircuit/formalization.yaml
Palomar/BinaryFiveCircuit/verification.md
```

README retains its recorded hash. No changes to `Proofs`, `References`, `Formalize`, root configuration, or other packages are part of this work. Documentation-only finalization did not alter the verified Challenge or Solution bytes. Integration is left to the parent.

## Comparator and independent verifier boundary

**NOT RUN: required executables unavailable.** The recorded preflight was:

```text
comparator: MISSING
landrun: MISSING
nanoda_bin: MISSING
lean4export: MISSING
Comparator revision: 777e7f56119efc0fac34003db4efe831e0b53723
Comparator toolchain: leanprover/lean4:v4.34.0-rc1
Comparator executable: MISSING
```

The available, unbuilt Comparator source targets a newer Lean than this project's `4.33.0-rc1`. No installation, compatibility repair, verifier build, or second toolchain was attempted. The identical-source-block check and Lean semantic bridge are their own evidence; neither is described as a Comparator or independent-kernel pass.

## Attribution and review boundary

No external primary source, prior formalization, or novelty evidence was established. Repository theorem/compiler files supply the implementation provenance, not an external attribution or a human mathematical audit. AI assistance was material; the metadata distinguishes the requested repair-model designation from independently verified runtime provenance. Unknown human author and responsible-maintainer identities remain empty rather than invented, with explicit blockers.

USER remains the sole reviewer. The formal semantic mismatch is resolved by Lean, while human review and the unavailable independent-verifier run remain separate, pending matters.
