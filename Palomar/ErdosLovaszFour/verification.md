# Verification: exact Erdős–Lovász value g(4) = 9

## Current mechanical verification

[Authoritative campaign manifest](../Wave4ComparatorEvidence.yaml): **PASS** for every declaration selected by this package’s `comparator.json`. Earlier text below is historical and superseded. Human review remains **UNCHECKED**; this makes no claim of Palomar acceptance, submission, or publication.

## Status and scope

- **Challenge separate fresh elaboration: PASS**, with exactly the one
  intentional selected-theorem hole and no definition hole.
- **Solution separate fresh elaboration: PASS**, with no warning or hole.
- **Independent-model/source bridge: PASS**, by definitional equalities checked
  in Lean before applying the accepted source equality.
- **Selected equality and lower/upper dependency axiom closures: PASS**, each
  exactly `propext`, `Classical.choice`, `Quot.sound`.
- **Model and selected theorem identity: PASS**: the shared model blocks are
  byte-identical and the target headers match in the two separate files.
- **JSON/YAML parsing and focused configuration consistency: PASS**. This is
  not external v0.4 schema certification.
- **Change-scope audit: PASS**: the six additions are all under
  `Palomar/ErdosLovaszFour/`; no old candidate or substantive source changed.
- **Comparator, lean4export, Landrun, and NanoDa: NOT RUN**, because the
  executables are unavailable. No tool was installed.
- **Independent AI foundations review at combined candidate
  `dcf241b5a1f33b86325e82d575fa588d9a3575e6`: FAITHFUL WITH METADATA
  CORRECTIONS REQUESTED.** It found the formal statement and source adaptation
  faithful and requested EF-1 and EF-2, applied here. Those corrections await
  foundations recheck at final integration.
- **Independent AI vacuity review at that exact revision: PASS FOR THE g(4)
  PACKAGE AND SOURCE PROOF.** No `VACUOUS`, `DRIFT`, `TRUST`, or material
  `STYLE` finding was reported. The result applies to the present unchanged
  Lean bytes by exact hash match; detailed scope and limitations are below.
- **Human review: NOT RUN.** `review.status: unchecked` denotes this absence and
  is not contradicted by the independent AI vacuity PASS.
- **External submission, verification, review, registration, and publication:
  NOT RUN**.

The accepted base supplied for this package is
`dbe40a6bf54ae15b54e0a62fe7e35f274ed77c13`. The substantive source endpoint is
`tripathi_erdosLovaszNum_four : erdosLovaszNum 4 = 9`. Six unrelated archived
literature declarations in its imported module retain intentional `sorry`s.
None is consumed by the selected declaration or any lower/upper bridge audited
below. Under the v0.4 convention, `status.sorry_count` is therefore zero for the
selected/package proof: its one intentional Comparator Challenge placeholder is
excluded, as are those six unrelated archives. Since the selected theorem and
all of its premises are proved, `literature_dependencies` is empty; Tripathi
remains recorded as the top-level mathematical source.

## Independent AI vacuity review

At exact reviewed revision
`dcf241b5a1f33b86325e82d575fa588d9a3575e6`, the independent AI reviewer
returned **PASS** for both the g(4) package and source proof. It checked the raw
exact-value target, the independent model and its definitional source bridges,
quantification over all `Fin N` rather than a bounded-ground surrogate, the
genuine nine-edge witness, the arbitrary-ground-type lower bound, and
attainment of the natural minimum. It reported no `VACUOUS`, `DRIFT`, `TRUST`,
or material `STYLE` finding.

The reviewer freshly compiled `Challenge.lean` and `Solution.lean` separately
and checked that the selected target, source lower theorem, and witness closures
used exactly `propext`, `Classical.choice`, and `Quot.sound`. It confirmed these
frozen SHA-256 values:

```text
d234f327fa99f5810d8e33734fb441aa97263c7847b8f03d617bcd4579de7294  Palomar/ErdosLovaszFour/Challenge.lean
70cd4a5e6ae26246248f0cc042a92bbf1837dc732182943068cffb71fe6430d0  Palomar/ErdosLovaszFour/Solution.lean
```

The present Lean files match those hashes exactly, so the vacuity conclusion
applies to their unchanged bytes. This does not extend the earlier foundations
review to the corrected EF-1/EF-2 metadata, which still awaits foundations
recheck at final integration, and it is not human review or approval.

For the fresh package compilation, the reviewer successfully excluded a
nonexistent optional `Cli` dependency output path from the recorded `LEAN_PATH`.
Comparator and NanoDa remained unavailable and were **NOT RUN**. A redundant
attempt to re-run the entire 165-triple witness with `decide` timed out at
800,000 heartbeats after 117.73 seconds. That timeout is not positive evidence,
and the reviewer did **not** independently recompute the full certificate. The
witness trust basis was instead the freshly compiled source parent `.olean`
with verified hash and standard-only axiom closure, together with successful
fresh package compilation, source inspection, and smaller re-reduced checks.

## Independent statement and guards

Both files define, within `Palomar.ErdosLovaszFour`:

```lean
def IsErdosLovaszFamily {α : Type*} (r : ℕ) (F : Finset (Finset α)) : Prop :=
  (∀ A ∈ F, A.card = r) ∧ (∀ A ∈ F, ∀ B ∈ F, ¬ Disjoint A B) ∧
    ∀ S : Finset α, S.card < r → ∃ A ∈ F, Disjoint A S

def erdosLovaszCards (r : ℕ) : Set ℕ :=
  {k | ∃ (N : ℕ) (F : Finset (Finset (Fin N))),
    IsErdosLovaszFamily r F ∧ F.card = k}

noncomputable def erdosLovaszNum (r : ℕ) : ℕ :=
  sInf (erdosLovaszCards r)
```

This quantifies over every finite labelled ground type `Fin N`; `N` is not
bounded. Uniformity, pairwise intersection, and absence of every smaller cover
are data of the predicate, not hypotheses pinning an unknown invariant. The
Challenge imports only `Mathlib`.

Both environments elaborate checks that:

- `{{0}}` over `Fin 1` is admissible at `r=1`;
- the empty family is not admissible at `r=1`;
- the empty family over the empty ground type `Fin 0` is not admissible at
  `r=4`;
- a lone four-element edge is uniform and intersecting but is not admissible,
  because it has a smaller cover;
- `1` is an attained edge count at `r=1`;
- `erdosLovaszNum 0 = 0` is an honest boundary value attained by the empty
  family, rather than an accidental empty-index-set value;
- `erdosLovaszCards 4` is nonempty, witnessed by all four-subsets of `Fin 7`.

The last check guards the selected parameter against the totalized value of
`Nat.sInf ∅`. The Solution also checks the genuine Tripathi object:

```lean
example : IsErdosLovaszFamily 4 witnessFour ∧ witnessFour.card = 9 := ...
example : (9 : ℕ) ∈ erdosLovaszCards 4 := ...
```

Those examples elaborate using the independently stated package predicate and
its proved source bridge.

## Signature and model alignment

A byte comparison of the shared model—from `set_option autoImplicit false`
through `erdosLovaszCards_four_nonempty`—reported:

```text
model_bytes_equal True 2974 2974
target_header_challenge 1
target_header_solution 1
challenge_sorry_tokens 1
solution_sorry_tokens 0
challenge_imports ['import Mathlib']
solution_imports ['import Erdos.ErdosLovasz']
```

The one shared selected header is:

```lean
theorem tripathi_erdosLovaszNum_four : erdosLovaszNum 4 = 9
```

The selected fully qualified declaration is
`Palomar.ErdosLovaszFour.tripathi_erdosLovaszNum_four`. Lean printed its full,
hypothesis-free type exactly as `erdosLovaszNum 4 = 9`. It also printed:

```text
@IsErdosLovaszFamily : {α : Type u_1} → ℕ → Finset (Finset α) → Prop
erdosLovaszCards : ℕ → Set ℕ
erdosLovaszNum : ℕ → ℕ
erdosLovaszCards_four_nonempty : (erdosLovaszCards 4).Nonempty
@isErdosLovaszFamily_iff_source : ∀ {α : Type u_1} (r : ℕ)
  (F : Finset (Finset α)),
  IsErdosLovaszFamily r F ↔ _root_.IsErdosLovaszFamily r F
erdosLovaszCards_eq_source : ∀ (r : ℕ),
  erdosLovaszCards r = _root_.erdosLovaszCards r
erdosLovaszNum_eq_source : ∀ (r : ℕ),
  erdosLovaszNum r = _root_.erdosLovaszNum r
```

The three source-alignment theorems are proved by `Iff.rfl` or `rfl`. Only after
these bridges does the Solution rewrite the independent invariant and apply
`_root_.tripathi_erdosLovaszNum_four`. Challenge and Solution are never imported
together; they were elaborated in separate Lean processes.

## Fresh narrow compilation and exact axiom output

The packaging lane first checked every prerequisite source and both pins against
the parent's recorded `source.sha256` and `pins.sha256`; every entry reported
`OK`. A private module root contained one read-only symlink for the `Erdos`
namespace to the parent's verified olean root. Target oleans and logs were
written only under `/tmp/yah/subagent/palomar-four-exact-a9820de/`; no shared
cache or repository `.lake` directory was written.

Immediately before Challenge compilation, `tool_atop` reported 21.78 GiB
available. The bounded, single-job command was equivalent to:

```sh
LEAN_PATH="<private-module-root>:<parent-recorded-LEAN_PATH>" \
  timeout 180 taskset -c 2 /usr/bin/time \
  lake env lean -j1 -M16384 \
  -o <private-output>/Palomar/ErdosLovaszFour/Challenge.olean \
  Palomar/ErdosLovaszFour/Challenge.lean
```

Exit status **0**; elapsed **6.33 s**; peak RSS **6,709,652 KiB**. Exact relevant
output:

```text
Palomar/ErdosLovaszFour/Challenge.lean:77:8: warning: declaration uses `sorry`
tripathi_erdosLovaszNum_four : erdosLovaszNum 4 = 9
'Palomar.ErdosLovaszFour.tripathi_erdosLovaszNum_four' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
```

`sorryAx` is expected only in the Challenge target.

Immediately before Solution compilation, `tool_atop` reported 22.43 GiB
available. The same bounded command shape compiled `Solution.lean` to its own
private output. Exit status **0**; elapsed **4.84 s**; peak RSS **6,712,036 KiB**.
There were no warnings. Exact axiom lines:

```text
'Palomar.ErdosLovaszFour.erdosLovaszCards_four_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
'Palomar.ErdosLovaszFour.isErdosLovaszFamily_iff_source' depends on axioms: [propext, Classical.choice, Quot.sound]
'Palomar.ErdosLovaszFour.erdosLovaszCards_eq_source' depends on axioms: [propext, Classical.choice, Quot.sound]
'Palomar.ErdosLovaszFour.erdosLovaszNum_eq_source' depends on axioms: [propext, Classical.choice, Quot.sound]
'Palomar.ErdosLovaszFour.tripathi_erdosLovaszNum_four' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosLovaszFourLower.nine_le_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'IsErdosLovaszFamily.nine_le_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'tripathi_nine_le_erdosLovaszNum_four' depends on axioms: [propext, Classical.choice, Quot.sound]
'erdosLovaszNum_four_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'tripathi_erdosLovaszNum_four' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Thus the selected package theorem, universal lower helper, family-level lower
bridge, infimum lower bridge, witness upper bound, and source equality all omit
`sorryAx` and use only the permitted standard three. A focused source scan found
no `native_decide`, `Lean.ofReduceBool`, custom `axiom`, `implemented_by`,
`extern`, or `csimp` in Challenge, Solution, `ErdosLovaszFourWitness.lean`, or
`ErdosLovaszFourLower.lean`.

Private log paths:

```text
/tmp/yah/subagent/palomar-four-exact-a9820de/challenge.log
/tmp/yah/subagent/palomar-four-exact-a9820de/solution.log
```

No whole-project build, `lake build`, dependency installation, prerequisite
recompilation, or shared-cache write was performed in this packaging task.

## Source and proof-dependency account

The canonical TeX for Tripathi, arXiv:1409.4610, was retrieved with
`tool_arxiv` outside the repository and read directly. It defines an
intersecting `k`-family, covering set, and transversal size; states the main
result `q(4)=9`; proves the lower half by a degree argument under a hypothetical
family of length at most eight; and gives the nine-block family in “An Example.”
The source therefore supports the exact selected statement.

The Lean signature formalizes the same quantity as the minimum edge count over
all finite labelled ground types, using the equivalent no-small-cover
predicate. The package bridges that literal predicate, its attainable count
set, and its infimum definitionally to the substantive source declarations.
For the upper bound, the actual nine blocks are checked. For the lower bound,
Lean follows Tripathi's degree reduction but replaces the paper's residual
classification and final global pair count with direct incidence arguments.
The universal helper works over arbitrary types from actual uniformity,
intersection, and cover hypotheses. It neither enumerates finite vertex sets
nor assumes a classification. The equality proof depends on those two proved
halves only.

The historical source comment's missing repository path
`References/Erdos/arXiv-1409-4610/paper.tex` was not used or recreated. The
canonical retrieval above is disclosed instead.

## Policy, provenance, and toolchain

On 2026-09-08, `https://palomar-registry.org/how-to-submit` and its submission
host `llms.txt` were freshly read. The linked Palomar policy was freshly cloned
read-only outside the repository at exact policy commit
`e9c8c238f5695b10f75db7175648a1d0195352c1`; `CONTRIBUTING.md` and the relevant
protocol headings were inspected. The candidate follows the small independent
Challenge/Solution shape, one Comparator configuration, permitted-axiom list,
Mathlib-only Challenge closure, source/related-work disclosures, and explicit
review limitations.

Current policy mechanically requires nonempty **human** `project.authors` and
`project.responsible_maintainers`, and submission requires a responsible author
or maintainer of the substantive work or approval from one. No identities or
approval were provided, and inventing them is forbidden. Both metadata lists
therefore remain empty and are a deliberate, disclosed **submission blocker**,
not a passing schema result. The smallest remaining USER decisions are to
supply truthful human author and responsible-maintainer entries, establish the
authorization relationship, review mathematical and source fidelity, complete
the final-integration foundations recheck of the EF-1/EF-2 corrections, and
separately decide whether any external submission or later registration should
occur.

Project/toolchain facts:

```text
accepted package base: dbe40a6bf54ae15b54e0a62fe7e35f274ed77c13
Lean 4.33.0-rc1, commit 62eed1db4d67327ec8120be05f1a1b0847d74561
Mathlib manifest revision: 3edb3c0658f69f197b1e501b1f7623f3f7b3898c
root licence: MIT (matches formalization.yaml)
```

Matched source/pin SHA-256 values:

```text
1665066d0673fbe757423c739542096edf15a4273f888a8cafa51e0263a42b4c  Proofs/Erdos/CoveringNumber.lean
8e5ba9bb67e0b17abe449715fc4bedde6e91c1ed6a44e3e85fa728e521b645eb  Proofs/Erdos/ErdosLovaszFourWitness.lean
fdb41a35199c400e4fb0c1e55fa6275df79064b4a3490cf8552140d97510967b  Proofs/Erdos/ErdosLovaszFourLower.lean
e9e5baa006136071d0b986ca7c54e3c455af5f6a412c3d1e38c4f1f9f17dd605  Proofs/Erdos/ErdosLovasz.lean
c6f7a51e7efbd7bbe12abab16b0113bad12019d5c3ad950f3c15bc3b2f6a1ae3  Proofs/Erdos/ErdosLovaszPairCover.lean
948a91a6b3c52e0b640d0dadc1bf84cf967403244ac590c162c005c2544a439e  lake-manifest.json
02f25adee7c1d6bf2e95b7b5b13f45b9892c7dd53ef470d5372ac60bda3df023  lean-toolchain
```

Reused verified parent olean SHA-256 values:

```text
b536aa4507d6ab644b4056d32bb57e68560c5af354688a1048848a9a6d230b12  Erdos/CoveringNumber.olean
c9ac1b78b36da0895223a07e5435e37661b6a1f639ba9db14ebf158f648781e1  Erdos/ErdosLovaszFourWitness.olean
41439660f493f9d95d366efbcf9dc68ca88dcf9c29917de896aadcd92cdaca3d  Erdos/ErdosLovaszFourLower.olean
f86779d2bdad0c404b396c49367b714d1a0a2892fc36be32be982823afd00c44  Erdos/ErdosLovasz.olean
6397af8051294b17baed7c364863a27ec0f111ed5aa478bcf24e450871063351  Erdos/ErdosLovaszPairCover.olean
```

These came from the USER-designated read-only parent output root. Source/pin
matches were verified before reuse. The private module namespace was kept
separate so no namespace roots overlaid each other.

## Metadata and unavailable checks

Python parsed `comparator.json`; PyYAML 6.0.1 parsed `formalization.yaml`.
Focused assertions confirmed v0.4, matching Challenge/Solution modules and
selected FQN, exactly three permitted axioms, `enable_nanoda: true`,
`status.sorry_count: 0`, an empty `literature_dependencies` list, one intentional
Challenge placeholder, no Solution hole, `review.status: unchecked`, and empty
human identity fields. The zero package-proof sorry count follows the v0.4
convention and does not deny either the excluded Challenge placeholder or the
six unrelated imported archives. Because current policy requires nonempty human
author and maintainer lists, metadata is intentionally blocked pending
USER-supplied facts; no claim of schema validity or submission readiness is
made.

Executable preflight, both normally and under `lake env`, reported all of
`comparator`, `landrun`, `lean4export`, `nanoda`, and `nanoda_bin` as **NOT
FOUND**. Therefore Comparator, export, sandboxed verification, and independent
NanoDa kernel checks are **NOT RUN**, not passed. No alternate verifier,
toolchain, dependency, or package was installed.

The parent reports a prior diff inspection and fresh compilation of nine
substantive modules with 23 axiom audits. Separately, the independent AI
foundations review at exact prior revision
`dcf241b5a1f33b86325e82d575fa588d9a3575e6` found the formal statement and
source adaptation faithful and requested EF-1 and EF-2. Those metadata fixes
are applied here and await foundations recheck at final integration. The
independent AI vacuity review at that exact revision passed the g(4) package and
source proof, with the evidence and witness-recomputation limitation recorded
above. Its conclusion applies to the present unchanged Lean bytes by exact hash
match. `review.status: unchecked` records that no human review occurred; no
human author, maintainer, endorsement, novelty, acceptance, or approval is
inferred.

The exact added files are:

```text
Palomar/ErdosLovaszFour/README.md
Palomar/ErdosLovaszFour/Challenge.lean
Palomar/ErdosLovaszFour/Solution.lean
Palomar/ErdosLovaszFour/comparator.json
Palomar/ErdosLovaszFour/formalization.yaml
Palomar/ErdosLovaszFour/verification.md
```

No temporary Scratch source remains. No external action was taken.
