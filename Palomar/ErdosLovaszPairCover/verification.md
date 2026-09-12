# Verification: elementary Erdős–Lovász pair-cover bound

## Current mechanical verification

[Authoritative campaign manifest](../Wave4ComparatorEvidence.yaml): **PASS** for every declaration selected by this package’s `comparator.json`. Earlier text below is historical and superseded. Human review remains **UNCHECKED**; this makes no claim of Palomar acceptance, submission, or publication.

## Outcome summary

- **Challenge targeted elaboration: PASS**, with exactly one deliberate hole,
  in the one selected theorem.
- **Solution targeted elaboration: PASS**, with no holes, warnings, or errors.
- **Selected theorem signature equality: PASS** by raw `#check @...` output and
  identical theorem headers.
- **Independent model/source alignment: PASS** by Lean-checked `Iff.rfl`/`rfl`
  bridges for the predicate, attainable-count set, and invariant.
- **Positive-parameter existence and attainment: PASS** independently in both
  files and again through the source's `erdosLovaszNum_mem` theorem.
- **Selected transitive axiom closure: PASS**, exactly `propext`,
  `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
- **JSON and YAML parsing/internal consistency: PASS**. This is not Palomar
  schema or intake certification.
- **Current Palomar identity/authorization contract: BLOCKED**. Human authors,
  responsible maintainers, and authorization are unknown.
- **Comparator, lean4export, Landrun, and NanoDa: NOT RUN**, because the
  executables are unavailable. No tool or dependency was installed.
- **Independent AI foundations review at the old exact candidate: FINDINGS
  ISSUED**. At combined revision
  `dcf241b5a1f33b86325e82d575fa588d9a3575e6`, it affirmed the formal
  statement/model as faithful and required provenance correction PC-1. This is
  not human approval or corrected-revision approval; the corrected metadata
  still awaits final foundations recheck.
- **Independent AI vacuity review at the same exact candidate: PASS** on frozen
  Challenge SHA-256
  `80d50b25af6a8266a7c2402149a1a74afdd5dd9f44e58cb20cbe41ec07a004ae`
  and Solution SHA-256
  `b825d9ba1a28136cad53a1a44fe7085e0949136b37dea80b9925e28d434aecde`.
  It reported no semantic, trust, or material-style findings. This is not human
  approval or approval of the corrected metadata; human review remains pending.

## Statement and model fidelity

Both Lean files define the following complete model inside
`Palomar.ErdosLovaszPairCover`:

```lean
def IsErdosLovaszFamily {α : Type*} (r : ℕ) (F : Finset (Finset α)) : Prop :=
  (∀ A ∈ F, A.card = r) ∧ (∀ A ∈ F, ∀ B ∈ F, ¬ Disjoint A B) ∧
    ∀ S : Finset α, S.card < r → ∃ A ∈ F, Disjoint A S

def erdosLovaszCards (r : ℕ) : Set ℕ :=
  {k | ∃ (N : ℕ) (F : Finset (Finset (Fin N))),
    IsErdosLovaszFamily r F ∧ F.card = k}

noncomputable def erdosLovaszNum (r : ℕ) := sInf (erdosLovaszCards r)
```

The family predicate is uniform, intersecting including the diagonal, and
excludes every transversal of cardinality below `r`. The diagonal excludes an
empty edge. For `0 < r`, an edge itself is an `r`-vertex transversal, so this is
exactly the intended transversal-number-`r` condition. The cardinality set
ranges over every `Fin N`, for unrestricted `N`; no bounded universe or
externally supplied predicate is used.

A text audit compared the actual declaration blocks between Challenge and
Solution byte-for-byte. The predicate, edge-count set, invariant, all-positive
nonemptiness theorem, and attainment theorem all matched. Their block SHA-256
values were respectively:

```text
ea2580af3e7904b25d2498e7ae1432466632bd4c17a7c582274581c95fad3124  predicate
f653e0038661058f1b8376865a06bee4f810623b941a5efc7739d4fe4e292b43  attainable counts
d210cfdccf11f5362aacaed16dbb03a2226cc580af0e037be6b63f3e0bc43dff  natural infimum
9575b695edb8c4cc9c52b1bddb9cd9e3e2bfa4e54732e4726127bfbf6dea444f  positive-r nonemptiness
2d9c87bbdbfcab2ba98c31395c36ceb5013e3c52d3b04a83d35fa76098008a6a  attainment
```

In the Solution, Lean proves:

```text
@isErdosLovaszFamily_iff_source :
  ∀ {α : Type u_1} (r : ℕ) (F : Finset (Finset α)),
    IsErdosLovaszFamily r F ↔ _root_.IsErdosLovaszFamily r F
erdosLovaszCards_eq_source :
  ∀ (r : ℕ), erdosLovaszCards r = _root_.erdosLovaszCards r
erdosLovaszNum_eq_source :
  ∀ (r : ℕ), erdosLovaszNum r = _root_.erdosLovaszNum r
```

The first is `Iff.rfl`; the other two are `rfl`. Thus alignment was checked
against source declarations rather than inferred from matching notation. The
additional `erdosLovaszNum_mem_via_source` bridge rewrites both independent
definitions and applies `_root_.erdosLovaszNum_mem hr`, confirming actual
source attainment for every positive `r`.

Both files prove all-positive nonemptiness with the family of all `(m+1)`-sets
on `2m+1` vertices, then apply `Nat.sInf_mem`. This audits the guard on the
totalized infimum. At `r=0`, the empty family on `Fin 0` honestly qualifies and
realizes zero. At `r=1`, the empty family on `Fin 0` fails while the singleton
edge family qualifies. At `r=2`, the triangle qualifies and realizes three.
The Solution also checks sharpness of the selected inequality at `r=1,2`.

The selected header occurs exactly once in each file and is identical:

```lean
theorem two_mul_sub_one_le_erdosLovaszNum {r : ℕ} (hr : 0 < r) :
    2 * r - 1 ≤ erdosLovaszNum r
```

Raw `#check` output from both separate elaborations is identical:

```text
@two_mul_sub_one_le_erdosLovaszNum :
  ∀ {r : ℕ}, 0 < r → 2 * r - 1 ≤ erdosLovaszNum r
```

The guard `0 < r` is material both to positive-parameter attainment and to the
intended untruncated reading of `2*r-1`. It is not hidden in a typeclass or
introduced as an answer-equivalent assumption.

## Proof path audit

The selected Solution proof first rewrites by
`erdosLovaszNum_eq_source`, then applies
`_root_.two_mul_sub_one_le_erdosLovaszNum hr`. The accepted source theorem
obtains `⟨N,F,hF,hcard⟩` from `erdosLovaszNum_mem hr`, so it reasons about the
actual minimum family rather than applying a lower bound directly to an empty
`sInf`.

Its family-level input is the proved source theorem
`IsErdosLovaszFamily.two_mul_sub_one_le_card`. That theorem derives a
transversal from `exists_isTransversal_two_mul_card_le`, which works over an
arbitrary ground type and proves `2*T.card ≤ F.card+1`. Strong induction removes
two intersecting edges at a time, adds a shared vertex, and separately handles
an unpaired edge. The no-small-cover clause forces `r ≤ T.card`; arithmetic
then yields `2*r-1 ≤ F.card`. The structural theorem is not selected by
Comparator.

The selected package and source declarations report:

```text
'Palomar.ErdosLovaszPairCover.two_mul_sub_one_le_erdosLovaszNum'
depends on axioms: [propext, Classical.choice, Quot.sound]

'two_mul_sub_one_le_erdosLovaszNum'
depends on axioms: [propext, Classical.choice, Quot.sound]
```

The independent nonemptiness, independent attainment, three definitional model
bridges, and source-attainment bridge report the same standard three axioms.
A source scan over Challenge, Solution, and
`Proofs/Erdos/ErdosLovaszPairCover.lean` found no `native_decide`,
`Lean.ofReduceBool`, custom `axiom`, `implemented_by`, `extern`, or `csimp`.
It found exactly one bare `sorry`, the selected Challenge placeholder, and none
in Solution or the pair-cover source.

## Targeted Lean runs

No whole-project build, Lake build, dependency setup, or cache write was
performed. Each target was run in a separate, serial Lean process pinned to CPU
1, with the verified read-only parent `LEAN_PATH`. `tool_atop` was checked
immediately before every launch and always reported more than 22 GiB available,
well above the required 8 GiB floor.

Challenge command:

```sh
export LEAN_PATH="$(cat /home/exedev/.yah/jj/01a07cfa-d323-732a-b33d-0a81d9175ff9/workspaces/integration-01a07e7e-f92e-703e-bc9d-30491380f682/.lake/verification/three-proofs/lean-path.txt)"
timeout 150 taskset -c 1 /usr/bin/time -f 'elapsed=%e max_rss_kib=%M' \
  lake env lean -j1 -M16384 Palomar/ErdosLovaszPairCover/Challenge.lean
```

Pre-launch available memory: **22.43 GiB**. Exit status: **0**. Elapsed:
**5.38 s**. Peak RSS: **6,680,436 KiB**. The only warning was the deliberate
selected-theorem hole. Its printed closure contains `sorryAx`, as expected for
Challenge:

```text
[propext, sorryAx, Classical.choice, Quot.sound]
```

Solution command used the same environment and limits with `Solution.lean`.
Pre-launch available memory: **22.44 GiB**. Exit status: **0**. Elapsed:
**4.84 s**. Peak RSS: **6,684,940 KiB**. There were no warnings or holes.

A preliminary Challenge launch failed in 0.75 s because the module docstring
was placed before `import Mathlib`; Lean requires imports first. The import was
moved to the first line before the successful finalized runs. This was a source
layout error, not a proof or model failure.

Final logs are private scratch artifacts, not repository files:

```text
/tmp/yah/subagent/palomar-pair-cover-0f83444/challenge.log
/tmp/yah/subagent/palomar-pair-cover-0f83444/solution.log
```

## Source, olean, and pin provenance

- Assigned and accepted base: `dbe40a6bf54ae15b54e0a62fe7e35f274ed77c13`.
- Lean: `4.33.0-rc1`, commit
  `62eed1db4d67327ec8120be05f1a1b0847d74561`.
- Mathlib manifest revision:
  `3edb3c0658f69f197b1e501b1f7623f3f7b3898c`.
- Verified read-only olean root:
  `/home/exedev/.yah/jj/01a07cfa-d323-732a-b33d-0a81d9175ff9/workspaces/integration-01a07e7e-f92e-703e-bc9d-30491380f682/.lake/verification/three-proofs/lib/lean`.

The recorded `LEAN_PATH` also contained the optional entry
`/home/exedev/p/proofs/.lake/packages/Cli/.lake/build/lib/lean`, which did not
exist. The independent AI vacuity reviewer omitted that entry and successfully
compiled the six reviewed package Lean modules separately. Thus the absent
`Cli` olean directory was irrelevant to the reviewed packages; it is a shared
record caveat, not a package dependency or proof failure.

The assigned workspace sources and pins were hashed directly and matched the
parent verification records and corresponding parent files byte-for-byte:

```text
1665066d0673fbe757423c739542096edf15a4273f888a8cafa51e0263a42b4c  Proofs/Erdos/CoveringNumber.lean
8e5ba9bb67e0b17abe449715fc4bedde6e91c1ed6a44e3e85fa728e521b645eb  Proofs/Erdos/ErdosLovaszFourWitness.lean
fdb41a35199c400e4fb0c1e55fa6275df79064b4a3490cf8552140d97510967b  Proofs/Erdos/ErdosLovaszFourLower.lean
e9e5baa006136071d0b986ca7c54e3c455af5f6a412c3d1e38c4f1f9f17dd605  Proofs/Erdos/ErdosLovasz.lean
c6f7a51e7efbd7bbe12abab16b0113bad12019d5c3ad950f3c15bc3b2f6a1ae3  Proofs/Erdos/ErdosLovaszPairCover.lean
02f25adee7c1d6bf2e95b7b5b13f45b9892c7dd53ef470d5372ac60bda3df023  lean-toolchain
948a91a6b3c52e0b640d0dadc1bf84cf967403244ac590c162c005c2544a439e  lake-manifest.json
```

The imported pair-cover olean is the one recorded by the parent verification:

```text
6397af8051294b17baed7c364863a27ec0f111ed5aa478bcf24e450871063351  Erdos/ErdosLovaszPairCover.olean
```

No source, pin, shared cache, dependency, configuration, or pre-existing
Palomar package was changed. No temporary Lean source or `Scratch` file remains.
The finalized output consists of exactly six regular files under the new
`Palomar/ErdosLovaszPairCover/` directory.

## Metadata, policy, literature, and external tools

The public `https://palomar-registry.org/how-to-submit` page and its linked
policy were read freshly. The checked policy snapshot was
`PalomarRegistry/PalomarPolicy` commit
`e9c8c238f5695b10f75db7175648a1d0195352c1`; the upstream
`formalization.yaml` documentation snapshot was commit
`99c678e569c7c4c0772db297c5ddd5e4c9b6322e`.

Python's JSON parser accepted `comparator.json`; PyYAML 6.0.1 accepted
`formalization.yaml`. A consistency script confirmed the module names, sole
selected FQN, three permitted axioms, `enable_nanoda: true`, metadata main
result, one Challenge hole, zero Solution holes, and the two literal imports.
The Challenge has 123 lines and 5,174 bytes, below Palomar's preferred and hard
review limits.

The metadata was also checked programmatically against the read-only current
v0.4 JSON Schema. The schema permits `independently-proves` and
`agent-reviewed`; the check found exactly one schema error:

```text
$.project.authors: minItems 1, got 0
```

This is the already disclosed unknown-author blocker. The schema itself does
not require a nonempty maintainer array, but current Palomar policy does, and
submission authorization also remains unknown. The installed environment had
neither `check-jsonschema` nor Python's `jsonschema` package, so no external
validator was installed or invoked; the recorded check used a read-only local
Draft-07 structural validator over every construct present in the v0.4 schema.

Preflight with `command -v`, both ordinarily and under `lake env`, found no
`comparator`, `landrun`, `lean4export`, `nanoda`, or `nanoda_bin`. External
Comparator/export/NanoDa verification is consequently **NOT RUN**, not passed.
The configuration retains `enable_nanoda: true` for later authorized Palomar
verification.

For literature scope, canonical primary TeX was freshly retrieved from
arXiv:2504.05406v1, *Erdős-Ko-Rado Theorems for Paths in Graphs* by Neal
Bushaw, James Danielsson, and Glenn Hurlbert (version 1, 7 April 2025). In
§3.1, “Elementary Observations,” Fact 17 (`f:basicUpperBound`) states exactly
that every intersecting family `F` satisfies
`τ(F) ≤ ⌈|F|/2⌉`. Its proof pairs the sets arbitrarily, selects one element of
each pair's intersection, and selects one element from a possible unpaired
set. Hence `τ(F)=r` gives `2*r-1 ≤ |F|`, which is exactly the structural lemma
and elementary implication used by the Lean source proof.

This paper was located after the recorded Lean proof construction, and the Lean
proof neither imports nor assumes Fact 17. The chronology is not described as
retrieval-blind discovery and supports no global novelty or priority claim.
The metadata therefore records the paper with the schema-supported relationship
`independently-proves`. The Erdős–Lovász 1975 paper is now `background`: it
supplies the invariant and stronger historical `8r/3-3` bound, not the selected
proof. Sivashankar's arXiv:2606.24878 remains background for `3r-4` and the
stronger asymptotic result. The candidate makes no novelty, significance,
priority, or source-author-endorsement claim.

An independent AI foundations review of exact combined candidate revision
`dcf241b5a1f33b86325e82d575fa588d9a3575e6` affirmatively found the statement
and model faithful but issued material provenance correction PC-1. This
revision records the finding and correction; that earlier review is not human
approval and is not approval or review of the corrected revision. Final
foundations recheck of the corrected metadata remains pending.

A separate independent AI vacuity review passed at that same exact revision on
the frozen Lean source hashes
`80d50b25af6a8266a7c2402149a1a74afdd5dd9f44e58cb20cbe41ec07a004ae`
for Challenge and
`b825d9ba1a28136cad53a1a44fe7085e0949136b37dea80b9925e28d434aecde`
for Solution. It checked all three package/source proofs, separately compiled
the six reviewed package Lean modules, checked raw types and the model, and
confirmed that selected closures use only the standard three axioms. It
reported no semantic, trust, or material-style findings. This PASS applies to
those exact reviewed Lean bytes, not the corrected metadata; it is not human
approval, and human review remains pending.
