# Verification record: restricted monomial-shear addition chains

## Status

- **Challenge elaboration:** PASS. Its only warning is the intentional headline theorem hole.
- **Substantive source prerequisite:** PASS, compiled separately and retained in a scratch cache.
- **Solution elaboration:** PASS, separately from Challenge and without importing it.
- **Selected theorem axiom audit:** PASS. The wrapper theorem and substantive source theorem use only `propext`, `Classical.choice`, and `Quot.sound`; neither uses `sorryAx`.
- **Comparator / landrun / lean4export / nanoda:** **NOT RUN — tooling blocker.** Required executables are unavailable and the observed Comparator source is pinned to a newer Lean release.
- **Human review:** PENDING. USER is the sole review gate; no human approval is asserted.

## Revisions, pins, and source relationship

- Assigned campaign base: `ee0cb27655f6bb6c37e8647c79184745017c5b24`.
- Workspace revision observed before the harness's final output snapshot: `e2a54bfdb1eb3aea886d1e95f67c2d989add5c5d` (change `nomtyqqvzpkupumsvrsnpwwsntpqwkqr`). The harness, not this prover, owns final jj snapshotting and integration.
- Lean: `4.33.0-rc1`, commit `62eed1db4d67327ec8120be05f1a1b0847d74561`, `x86_64-unknown-linux-gnu`, Release build.
- Lake: `5.0.0-src+62eed1d` (Lean `4.33.0-rc1`).
- Mathlib manifest revision: `3edb3c0658f69f197b1e501b1f7623f3f7b3898c`.
- Comparator configuration: `Palomar/ShearAdditionChains/comparator.json`.

`Palomar.ShearAdditionChains.Solution` imports the singular substantive module
`ShearEC.ShearAdditionChain`. It does not import Challenge. It repeats all challenge definitions, proves listwise equivalence of the two addition-chain inductives, and defines both directions of a trace-preserving translation between the duplicate and repository monomial-program inductives. The two `shearCount` transport lemmas are proved, as are equality of both positive-input minima. The selected theorem then uses the existing substantive theorem. The plural source file `Proofs/ShearEC/ShearAdditionChains.lean` is not used as evidence.

The model is restricted to one exponent-1 input register and fresh-target operations which select two old source indices, prepend their exponent sum, and retain every old register. The result is not an unrestricted `ShearCircuit` optimum and makes no clean-scratch, reversible/EC, or inversion optimality claim. At zero both empty `Nat` infima have junk value zero; the selected theorem guards with `n ≠ 0`.

## Hash and cache provenance

Project configuration and substantive source hashes:

```text
02f25adee7c1d6bf2e95b7b5b13f45b9892c7dd53ef470d5372ac60bda3df023  lean-toolchain
5fea1b2cc353a49df4d727bd77e43a01c074130fcb099610fe0320d8d7a1906f  lakefile.toml
948a91a6b3c52e0b640d0dadc1bf84cf967403244ac590c162c005c2544a439e  lake-manifest.json
4cb025015618c37d16d51cd5a3bf107bef0e75a36e741f42d4a35f1a6e1d89a6  Proofs/ShearEC/ShearAdditionChain.lean
e54e801ec8e141daef8dab13f241fe12e8374c6d9ea1722894da253bdbacdea0  Proofs/NumberComplexity/AdditionChain.lean
dcf32d2bbc44b403ffdcc03903b33a00f0d600dd51da68d4ce19f8c625df7110  Proofs/ShearEC/ShearCircuit.lean
```

The corresponding files under `/home/exedev/p/proofs` had identical hashes for `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`. This established exact toolchain/manifest/config matching before use of that read-only main cache. The reused and newly compiled object hashes were:

```text
d9bab8bbb1a30732fdae3cd9aeb1228d39f88ed67c4e25c0aa615583ebf27f1e  /home/exedev/p/proofs/.lake/build/lib/lean/NumberComplexity/AdditionChain.olean
40a15c460009cd1786e7875dfa54da27eb98c482b8507f2e076cbec9d72a1acd  /home/exedev/p/proofs/.lake/build/lib/lean/ShearEC/ShearCircuit.olean
d372cc7bc50fb5560bab0c5fc068589d6763fda5bd4a5e119c908f9ea1e442b8  /tmp/yah/subagent/shear-chains-package-prover-ba225a0/olean/ShearEC/ShearAdditionChain.olean
```

Final checked Lean package-source hashes:

```text
e89a7489d0a57b6336fc549180a9b088b4dfb0a76905fc9415d31bc09acf4163  Palomar/ShearAdditionChains/Challenge.lean
be395eb7100bf37380e8a3cf0998a8f51fb493f5fd23f8b560e31e819d77c43a  Palomar/ShearAdditionChains/Solution.lean
```

## Challenge elaboration

Immediately before the final check, the host reported 8 cores, 23.46 GiB total memory, 4.18 GiB used, and 19.28 GiB available. The command was:

```sh
ulimit -v 22544384
timeout 240s taskset -c 0 lake env lean -M 9000 -j 1 \
  Palomar/ShearAdditionChains/Challenge.lean
```

Exit status: `0`.

Exact output:

```text
Palomar/ShearAdditionChains/Challenge.lean:160:8: warning: declaration uses `sorry`
minimumMonomialShears_eq_l : ∀ (n : ℕ), n ≠ 0 → minimumMonomialShears n = l n
```

The warning is the intentional challenge hole. There are no sorry occurrences in Challenge definitions and no sorry occurrences in Solution. Retained log:
`/tmp/yah/subagent/shear-chains-package-prover-ba225a0/challenge-final.log`.

## Targeted substantive prerequisite compilation

The main cache already contained matching `NumberComplexity.AdditionChain` and `ShearEC.ShearCircuit` objects, but not the singular substantive `ShearEC.ShearAdditionChain` object. Immediately before the targeted compilation, the host reported 8 cores, 23.46 GiB total memory, 1.40 GiB used, and 22.07 GiB available. No full repository build or cache reconstruction was performed.

```sh
mkdir -p /tmp/yah/subagent/shear-chains-package-prover-ba225a0/olean/ShearEC
ulimit -v 22544384
timeout 720s taskset -c 0 \
  env LEAN_PATH=/home/exedev/p/proofs/.lake/build/lib/lean \
  lake env lean -M 9000 -j 1 \
  -o /tmp/yah/subagent/shear-chains-package-prover-ba225a0/olean/ShearEC/ShearAdditionChain.olean \
  Proofs/ShearEC/ShearAdditionChain.lean
```

Exit status: `0`. Relevant output included:

```text
minimumMonomialShears_eq_l : ∀ (n : ℕ), n ≠ 0 → minimumMonomialShears n = l n
'ShearEC.ShearAdditionChain.minimumMonomialShears_eq_l' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Retained log: `/tmp/yah/subagent/shear-chains-package-prover-ba225a0/source-build.log`.

To give the scratch package root a coherent import layout, matching read-only cached `NumberComplexity` and `ShearEC.ShearCircuit` artifacts were linked into that scratch root. No file in the read-only cache and no source file was modified.

## Separate Solution elaboration and axiom audit

Immediately before the final check, the host reported 8 cores, 23.46 GiB total memory, 5.46 GiB used, and 18.00 GiB available. The command was:

```sh
ulimit -v 22544384
timeout 360s taskset -c 0 \
  env LEAN_PATH=/tmp/yah/subagent/shear-chains-package-prover-ba225a0/olean:/home/exedev/p/proofs/.lake/build/lib/lean \
  lake env lean -M 9000 -j 1 \
  Palomar/ShearAdditionChains/Solution.lean
```

Exit status: `0`.

Exact output:

```text
minimumMonomialShears_eq_l : ∀ (n : ℕ), n ≠ 0 → minimumMonomialShears n = l n
ShearEC.ShearAdditionChain.minimumMonomialShears_eq_l : ∀ (n : ℕ),
  n ≠ 0 → ShearEC.ShearAdditionChain.minimumMonomialShears n = NumberComplexity.l n
'Palomar.ShearAdditionChains.isAddChain_iff_source' does not depend on any axioms
'Palomar.ShearAdditionChains.MonomialShearProgram.shearCount_toSource' depends on axioms: [propext]
'Palomar.ShearAdditionChains.MonomialShearProgram.shearCount_ofSource' depends on axioms: [propext]
'Palomar.ShearAdditionChains.minimumMonomialShears_eq_source' depends on axioms: [propext, Classical.choice, Quot.sound]
'Palomar.ShearAdditionChains.l_eq_source_l' depends on axioms: [propext, Classical.choice, Quot.sound]
'ShearEC.ShearAdditionChain.minimumMonomialShears_eq_l' depends on axioms: [propext, Classical.choice, Quot.sound]
'Palomar.ShearAdditionChains.minimumMonomialShears_eq_l' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Thus the exact selected signature is:

```lean
@Palomar.ShearAdditionChains.minimumMonomialShears_eq_l :
  ∀ (n : ℕ), n ≠ 0 →
    Palomar.ShearAdditionChains.minimumMonomialShears n =
      Palomar.ShearAdditionChains.l n
```

The selected closure is a subset of the permitted set and contains no `sorryAx`, `Lean.ofReduceBool`, or custom axiom. No `native_decide`, `@[implemented_by]`, `@[extern]`, or `@[csimp]` is used by the package. Retained log:
`/tmp/yah/subagent/shear-chains-package-prover-ba225a0/solution-final.log`.

## Earlier bounded failures

These were development failures and were not counted as verification:

1. The first Challenge elaboration exposed ambiguous constructor parameters, a singleton proof gap, and an invalid dependent elimination in a ground check. Those statements were made explicit and the next check passed.
2. The first Solution attempt against the newly created scratch source object could not locate `ShearEC.ShearCircuit.olean` in that first package root. The exact matching cached dependency artifacts were linked into the scratch root rather than triggering a broad Lake build.
3. Intermediate Solution checks exposed a missing local nonempty-trace lemma, attempted use of `le_iInf` where the relevant Nat construction is not a `CompleteLattice`, and field-notation namespace ambiguity on source-typed values. These were replaced by a proved trace-length lemma, `Nat.sInf_mem` attainment, and explicit qualified translation names. The final checks above passed.

Successful objects and all logs were preserved; no low-memory or low-`ulimit` failure was retried unchanged.

## External verifier tooling blocker

**Status: NOT RUN.** This is not a Comparator, landrun, lean4export, or nanoda pass.

Preflight found no `comparator`, `landrun`, `lean4export`, or `nanoda_bin` executable in `PATH`. The observed Comparator checkout at revision
`777e7f56119efc0fac34003db4efe831e0b53723` had no built executable and declared:

```text
leanprover/lean4:v4.34.0-rc1
```

The project is pinned to Lean `4.33.0-rc1`. Installing verifier projects, building a second/newer toolchain, or upgrading dependencies was outside the authorized scope, so no external-verifier invocation was attempted. `comparator.json` retains `enable_nanoda: true` and the exact fully qualified theorem name rather than weakening configuration to bypass missing tooling.

## Review and metadata boundary

All package implementation and verification work was AI-assisted. No mathematical review agent or other reviewer was used. USER review is the sole review gate and remains pending. Human formalization-author and responsible-maintainer identities were not available, so `formalization.yaml` leaves those required lists empty and records concrete blockers rather than inventing identities. Established addition-chain mathematics is attributed as background; novelty, priority, and prior formalization of this exact restricted-model correspondence remain unestablished.
