# Verification: Erdős–Lovász g(4) ≤ 9

## Current mechanical verification

[Authoritative campaign manifest](../Wave4ComparatorEvidence.yaml): **PASS** for every declaration selected by this package’s `comparator.json`. Earlier text below is historical and superseded. Human review remains **UNCHECKED**; this makes no claim of Palomar acceptance, submission, or publication.

## Status and scope

- **Challenge fresh elaboration: PASS**, with exactly the one intentional selected-theorem hole.
- **Solution fresh elaboration: PASS**, with no warnings or holes.
- **Independent-model/source bridge: PASS**, proved in Lean before applying the source bound.
- **Selected Solution axiom closure: PASS**, exactly `propext`, `Classical.choice`, `Quot.sound`.
- **Model and selected statement identity: PASS**, identical shared model text and theorem headers.
- **JSON/YAML parsing and configuration consistency: PASS**; this is not an external schema certification.
- **Change-scope audit: PASS**, six new files under `Palomar/ErdosLovaszFourUpper/`, no existing tracked-file changes.
- **Comparator, lean4export, and Nanoda: NOT RUN**, executables unavailable.
- **USER review: PENDING**, the only review gate. Technical checks are not human review or endorsement.

Only the existing upper bound is selected. The full equality and all archived
literature declarations remain outside the selected proof's dependency closure.

## Independent semantics and alignment

Both files define, within `Palomar.ErdosLovaszFourUpper`:

```lean
def IsErdosLovaszFamily {α : Type*} (r : ℕ) (F : Finset (Finset α)) : Prop :=
  (∀ A ∈ F, A.card = r) ∧ (∀ A ∈ F, ∀ B ∈ F, ¬ Disjoint A B) ∧
    ∀ S : Finset α, S.card < r → ∃ A ∈ F, Disjoint A S

def erdosLovaszCards (r : ℕ) : Set ℕ :=
  {k | ∃ (N : ℕ) (F : Finset (Finset (Fin N))), IsErdosLovaszFamily r F ∧ F.card = k}

noncomputable def erdosLovaszNum (r : ℕ) : ℕ := sInf (erdosLovaszCards r)
```

The model contains no externally assumed predicate or desired-property hypothesis.
The family is uniform and intersecting, and every candidate smaller cover is
explicitly excluded. `N` ranges over all naturals, not a bounded search universe.
Both files independently prove `erdosLovaszCards_four_nonempty` using all
four-subsets of seven vertices. Thus `g(4)` is not the default natural infimum
of an empty index set. Ground checks also include the singleton family, rejection
of the empty family at `r=1`, and the honest value `g(0)=0`.

The Solution's three bridge declarations are proved by `Iff.rfl` or `rfl`:

```text
@isErdosLovaszFamily_iff_source : ∀ {α : Type u_1} (r : ℕ) (F : Finset (Finset α)),
  IsErdosLovaszFamily r F ↔ _root_.IsErdosLovaszFamily r F
erdosLovaszCards_eq_source : ∀ (r : ℕ), erdosLovaszCards r = _root_.erdosLovaszCards r
erdosLovaszNum_eq_source : ∀ (r : ℕ), erdosLovaszNum r = _root_.erdosLovaszNum r
```

This establishes actual definitional alignment; merely printing the same short
names would not suffice. Only after these bridges does the selected proof rewrite
the invariant and apply `_root_.erdosLovaszNum_four_le`. The Solution also proves
that the actual `witnessFour` satisfies the independent predicate and realizes
edge count nine. Challenge imports only `Mathlib`; Solution imports only
`Erdos.ErdosLovasz`, never Challenge. The two environments are compiled separately.

The shared model block, including its ground checks and nonemptiness proof, was
compared byte-for-byte. The selected theorem headers are identical:

```lean
theorem erdosLovaszNum_four_le : erdosLovaszNum 4 ≤ 9
```

The selected fully qualified declaration is
`Palomar.ErdosLovaszFourUpper.erdosLovaszNum_four_le`. Fresh `#check @...`
output confirms the complete, hypothesis-free signature above. The underlying
predicate has type `{α : Type u_1} → ℕ → Finset (Finset α) → Prop`, the
edge-count set has type `ℕ → Set ℕ`, and the invariant has type `ℕ → ℕ`.

## Fresh compilation and axiom output

Immediately before Challenge compilation, `tool_atop` reported 22.28 GiB
available. The bounded command, from the assigned workspace, was:

```sh
timeout 150 taskset -c 2 /usr/bin/time -f 'elapsed=%e peak_rss_kb=%M' \
  lake env lean -j1 -M65536 Palomar/ErdosLovaszFourUpper/Challenge.lean
```

Exit status: **0**. Elapsed **13.49 s**, peak RSS **6,674,008 KiB**.
Relevant output:

```text
Palomar/ErdosLovaszFourUpper/Challenge.lean:68:8: warning: declaration uses `sorry`
erdosLovaszNum_four_le : erdosLovaszNum 4 ≤ 9
'Palomar.ErdosLovaszFourUpper.erdosLovaszNum_four_le' depends on axioms:
  [propext, sorryAx, Classical.choice, Quot.sound]
```

The Challenge's `sorryAx` is intentional and confined to its selected theorem.
No definition contains a hole.

Immediately before Solution compilation, `tool_atop` reported 19.89 GiB
available. The separately bounded command was:

```sh
timeout 150 taskset -c 2 /usr/bin/time -f 'elapsed=%e peak_rss_kb=%M' \
  lake env lean -j1 -M65536 Palomar/ErdosLovaszFourUpper/Solution.lean
```

Exit status: **0**, no warnings. Elapsed **4.62 s**, peak RSS **6,677,444 KiB**.
Exact selected output:

```text
'Palomar.ErdosLovaszFourUpper.erdosLovaszNum_four_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'erdosLovaszNum_four_le' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The independent nonemptiness theorem and all three bridges also report exactly
the same three standard axioms. The source and selected package theorem do not
report `sorryAx`, despite the unrelated archived declarations in the imported
source module. A Lean-source scan finds no `native_decide`, `Lean.ofReduceBool`,
custom `axiom`, `implemented_by`, `extern`, or `csimp`, and no Solution `sorry`.
No failed Lean attempt occurred in this packaging tranche. The high `-M` setting
accommodates imported private-olean accounting; it is not measured physical RSS.

Complete logs are retained outside the repository at:

- `/tmp/yah/subagent/prove-erdos-lovasz-four-upper-f04c151/package-challenge.log`
- `/tmp/yah/subagent/prove-erdos-lovasz-four-upper-f04c151/package-solution.log`

## Source, cache, and toolchain provenance

- Accepted main source revision: `55ab7d253f32b9632581cf31cc4951c2b2119533`.
- Packaging workspace starting revision: `14e1f10b7b50d024935b3476556c12423b598147`.
- Lean `4.33.0-rc1`, commit `62eed1db4d67327ec8120be05f1a1b0847d74561`.
- Mathlib manifest revision: `3edb3c0658f69f197b1e501b1f7623f3f7b3898c`.

SHA-256 values of unchanged prerequisite sources and pins:

```text
d5621fa55b0f486b64cd7d33f7b3a5e3097dcfedb556b58446dbdd237e77b692  Proofs/Erdos/ErdosLovasz.lean
8e5ba9bb67e0b17abe449715fc4bedde6e91c1ed6a44e3e85fa728e521b645eb  Proofs/Erdos/ErdosLovaszFourWitness.lean
1665066d0673fbe757423c739542096edf15a4273f888a8cafa51e0263a42b4c  Proofs/Erdos/CoveringNumber.lean
948a91a6b3c52e0b640d0dadc1bf84cf967403244ac590c162c005c2544a439e  lake-manifest.json
02f25adee7c1d6bf2e95b7b5b13f45b9892c7dd53ef470d5372ac60bda3df023  lean-toolchain
```

The two target sources were compared directly against accepted revision `55ab7d…`.
All three source files, the manifest, and the toolchain also match the read-only
main workspace `/home/exedev/p/proofs` byte-for-byte. Mathlib/package dependencies
resolve through the pre-existing `.lake/packages` symlink to that workspace.
The Erdos prerequisite oleans reused here were compiled locally from these exact
sources in the preceding proof task, not reconstructed or copied during packaging:

```text
379c5412e7272cb1b09b8e77d8e8455e7274eb1ad843ec8676a4d57212b9dec6  Erdos/CoveringNumber.olean
a1339417dd53a30c9de5ea5cf030be6874689801c865d5c6ae4c219d06ed3abe  Erdos/ErdosLovasz.olean
bb7f49a8082c2f6337e20a653f2a63bfae679d09406c1f97020409bb7bcceff0  Erdos/ErdosLovaszFourWitness.olean
```

Both new Lean targets were elaborated from their current source, not loaded from
stale package oleans. No `Proofs/` source, existing package or README, immutable
reference, manifest, dependency, toolchain, or root configuration was changed.

## Metadata, scope, and external-tool checks

`comparator.json` was parsed with Python's JSON parser and
`formalization.yaml` with PyYAML 6.0.1. Checks confirm version `v0.4`, matching
Challenge/Solution modules and selected FQN, exactly the three permitted axioms,
`enable_nanoda: true`, one intentional Challenge hole, no Solution hole, and empty
human author/maintainer/reviewer fields. This is syntax and targeted consistency
validation, not an external v0.4 schema-validation or submission-readiness claim.

A read-only comparison with the packaging starting revision checked the exact
serialized paths and bytes of all 1,628 existing regular files and separately
confirmed that both existing tracked symlink targets were unchanged. Initial
tree-audit scripts mishandled those two pre-existing dangling `.yah/skills/`
symlinks; the corrected comparison passed without modifying them. A filesystem
allowlist check, excluding existing ignored/runtime directories, found exactly
these six additional files:

```text
Palomar/ErdosLovaszFourUpper/README.md
Palomar/ErdosLovaszFourUpper/Challenge.lean
Palomar/ErdosLovaszFourUpper/Solution.lean
Palomar/ErdosLovaszFourUpper/comparator.json
Palomar/ErdosLovaszFourUpper/formalization.yaml
Palomar/ErdosLovaszFourUpper/verification.md
```

Executable preflight both in the ordinary environment and under `lake env`
reported `comparator`, `landrun`, `lean4export`, `nanoda`, and `nanoda_bin` as
**NOT FOUND**. Consequently Comparator/export/external-kernel checks are
**NOT RUN**, not passed. No setup, installation, alternate toolchain, whole-repo
build, or verifier infrastructure work was attempted. The configuration retains
`enable_nanoda: true` for a later authorized run.

Tripathi's nine blocks were checked against the primary TeX in the preceding
proof task, with the one-based to zero-based label shift documented in README.
The package makes no novelty, priority, endorsement, or acceptance claim. Material
AI assistance is disclosed in `formalization.yaml`; unknown human authors and
maintainers remain explicit metadata blockers. USER-only review is pending.
