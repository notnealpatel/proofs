# Verification: complete bounded A046098 classification

## Result summary

| Check | Result |
| --- | --- |
| Independent Challenge elaboration | **PASS**, exit 0; one intentional theorem-hole warning |
| Separate Solution elaboration | **PASS**, exit 0; no warnings or errors |
| Challenge/Solution elaborated type identity | **PASS**, byte-identical raw expressions |
| Package/source elaborated type identity | **PASS**, byte-identical raw expressions |
| Selected Solution axiom audit | **PASS**, exactly the three permitted axioms |
| Parent fresh source compilation | **PASS**, supplied coherent logs and artifacts validated against this base |
| JSON/YAML parsing and package consistency | **PASS** |
| Upstream formalization.yaml JSON-schema validator | **NOT RUN**, `jsonschema` executable/module unavailable |
| Current Palomar metadata intake | **BLOCKED**, required human authors and maintainers are unknown and empty |
| Comparator / `lean4export` / Landrun / NanoDa | **NOT RUN**, executables unavailable |
| Independent foundations/fidelity AI review | **PASS**, 2026-09-08, frozen Lean bytes at reviewed integration `dcf241b5a1f33b86325e82d575fa588d9a3575e6` |
| Independent vacuity/trust AI review | **PASS**, 2026-09-08, no vacuity, drift, trust, or material style findings |
| Human review | **PENDING** |

This is a technical candidate report for parent review, not human approval,
submission, acceptance, or registration.

## Exact declaration and independent statement surface

The sole Comparator declaration is
`Palomar.SquarefreeBinomialClassification.squarefree_choose_half_iff`. Both
package files freshly printed its complete type as:

```text
@squarefree_choose_half_iff : ∀ {n : ℕ},
  n < 10 ^ 8 → (Squarefree (n.choose (n / 2)) ↔
    n ∈ {0, 1, 2, 3, 4, 5, 7, 8, 11, 17, 19, 23, 71})
```

The implicit source binder is therefore an actual all-`n` quantifier. The
strict bound is an ordinary premise, not an answer-bearing assumption. Both
files independently check that `0`, `71`, and `99999999` satisfy the bound,
that `100000000` does not, and that the displayed Finset contains `0` and `71`
but not `72`.

`Challenge.lean` is 40 lines and 1,691 bytes. Its only imports are:

```lean
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Squarefree
```

It has one `sorry` token, located at the selected theorem proof, and no
definitions or definition holes. It has no project, source-proof, or Solution
import. `Solution.lean` has no `sorry` and imports only
`Erdos.Erdos175.SquarefreeCentralBinom`; it does not import the Challenge. Its
proof is the direct bridge:

```lean
exact Erdos175.A046098.squarefree_choose_half_iff hlt
```

No package-defined model exists. Consequently the semantic bridge uses exactly
Mathlib's `Nat`, `Nat.choose`, `Squarefree`, `Finset`, membership, order, natural
power, and natural division. Natural division is by the fixed nonzero number
`2`, so the effective operation is floor division and no zero-divisor junk case
is reachable.

## Statement and source alignment

The selected physical source is
`Proofs/Erdos/Erdos175/SquarefreeCentralBinom.lean` at accepted base
`dbe40a6bf54ae15b54e0a62fe7e35f274ed77c13`, declaration
`Erdos175.A046098.squarefree_choose_half_iff`. Its source header is:

```lean
theorem squarefree_choose_half_iff {n : Nat} (hlt : n < 10^8) :
    Squarefree (n.choose (n/2)) ↔
      n ∈ ({0,1,2,3,4,5,7,8,11,17,19,23,71} : Finset Nat)
```

Three separate audit environments imported respectively the Challenge package
artifact, the Solution package artifact, and the source artifact, then dumped
the declaration types as raw `Lean.Expr` values. All three logs were
byte-identical, with SHA-256:

```text
f8317c486f47fb5ad7a6813ecd42847a90ccd3c02037e7343f927137b28f1483
```

This is stronger than a comparison of pretty-printed headers, but it is not
represented as a Comparator run.

The physical source audit separately inspected the exact theorem, its below-72
lemma, the combined even/odd exclusion, the thirteen factorization proofs, the
odd residual module, the even central-binomial dependency, and the end-of-file
axiom report. In particular:

- `n = 0` is proved on the positive side (`C(0,0) = 1`);
- `71` is proved squarefree and `72` nonsquarefree;
- the range guard remains strict at `10^8`;
- the ten small odd residual exclusions are exactly
  `9, 15, 31, 33, 35, 39, 47, 63, 65, 67`;
- even and odd branches are combined only after separately proving the
  `72 ≤ n < 10^8` exclusion;
- `Erdos175.witness_cert` now transports an ordinary kernel-checked
  fuel-21 digit-sum certificate and does not use native computation;
- the 331 larger odd residual cases use ordinary `decide` carry certificates.

The package's proof account in `README.md` was checked against this physical
architecture. The later independent foundations/fidelity AI review also passed
this source alignment at the frozen Lean hashes recorded below; neither check
is represented as human review.

## Source, artifact, and pin provenance

The assigned working-copy revision is a child whose sole parent is the required
accepted base `dbe40a6bf54ae15b54e0a62fe7e35f274ed77c13`. `jj file show` at that
base, this workspace, and the parent integration workspace gave identical bytes
for the four source modules. The verified input hashes are:

| Input | SHA-256 |
| --- | --- |
| `SquarefreeCentralBinom.lean` | `3ffa0700a11c939ba39d1da4b30fbd55829596f37108b430f2b0c53e224b3486` |
| `SquarefreeCentralBinomResidual.lean` | `65b282918521eb1194a4f62c2c8ddad2cc0d2f3f9f68b696790a0921480bf1a7` |
| `NotSquarefree.lean` | `aabf55e50044ea5ef527576af5309a30482b5c30f6cc8dc8bb50cc686fb33173` |
| `SquarefreeCentralBinomCertificates.lean` | `9d09f1452a04972aef6910ff530176a73e31803b07f34922b299a0ded142fdef` |
| `lean-toolchain` | `02f25adee7c1d6bf2e95b7b5b13f45b9892c7dd53ef470d5372ac60bda3df023` |
| `lakefile.toml` | `5fea1b2cc353a49df4d727bd77e43a01c074130fcb099610fe0320d8d7a1906f` |
| `lake-manifest.json` | `948a91a6b3c52e0b640d0dadc1bf84cf967403244ac590c162c005c2544a439e` |

The parent supplied a coherent read-only artifact root at:

```text
/home/exedev/.yah/jj/01a07cfa-d323-732a-b33d-0a81d9175ff9/workspaces/
integration-01a07e7e-f92e-703e-bc9d-30491380f682/.lake/verification/
three-proofs/lib/lean
```

(The displayed path is line-wrapped only.) Its `source.sha256`, `pins.sha256`,
`olean.sha256`, `lean-path.txt`, `run.sh`, per-module logs, and `axioms.log` were
read and cross-checked before reuse. Relevant artifact hashes are:

| Artifact | SHA-256 |
| --- | --- |
| `SquarefreeCentralBinomCertificates.olean` | `b6c6004831db57b9ca90ff075c6505286ef2b265fdb171a9b3d4cd381d7a37a3` |
| `NotSquarefree.olean` | `c5ff789488f17d1dc7a289a05aeef5a3b5105125422e864e65d0b4dc1aab169b` |
| `SquarefreeCentralBinomResidual.olean` | `9a0016ceab9f54d5a3ed5036cb8292c1a16008d6ae63a5629cac761d4a525bb9` |
| `SquarefreeCentralBinom.olean` | `3cc731e531180822d8ce8f6fbf6ad251200c26d2e18b1ea1ae0e1015ebfd7908` |

The parent compile script used `timeout 180 taskset -c 0 lean -j1 -M16384` and
compiled each source serially. The four relevant logs ended successfully with
no warnings; elapsed times were respectively 1.26, 1.94, 3.08, and 3.26 seconds
for Certificates, NotSquarefree, Residual, and the selected source module. This
is parent-supplied **fresh source compilation evidence**, distinguished from
this lane's fresh package compilation below.

Toolchain and dependency pins are Lean `4.33.0-rc1`, commit
`62eed1db4d67327ec8120be05f1a1b0847d74561`, Lake
`5.0.0-src+62eed1d`, and Mathlib manifest revision
`3edb3c0658f69f197b1e501b1f7623f3f7b3898c`.

## Fresh package checks in this lane

Before every Lean launch, `tool_atop` reported more than 22 GiB physical memory
available on the 23.46 GiB host, above the required 8 GiB threshold. Every Lean
process ran serially on CPU 0 with one worker, a 2,048 MB Lean heap limit, and a
120-second timeout. No Lake or full build was run. No dependency setup or shared
cache write was performed. Package artifacts and audit files lived under the
private scratch directory
`/tmp/yah/subagent/palomar-bounded-binomial-175625c/checks`.

With `PARENT_LEAN_PATH` equal to the exact contents of the supplied
`three-proofs/lean-path.txt`, the package commands were:

```sh
LEAN_PATH="$PARENT_LEAN_PATH" timeout 120 taskset -c 0 lean -j1 -M2048 \
  Palomar/SquarefreeBinomialClassification/Challenge.lean \
  -o "$SCRATCH/challenge/lib/lean/Palomar/SquarefreeBinomialClassification/Challenge.olean"

LEAN_PATH="$PARENT_LEAN_PATH" timeout 120 taskset -c 0 lean -j1 -M2048 \
  Palomar/SquarefreeBinomialClassification/Solution.lean \
  -o "$SCRATCH/solution/lib/lean/Palomar/SquarefreeBinomialClassification/Solution.olean"
```

Both exited `0`. The Challenge's sole warning was:

```text
Palomar/SquarefreeBinomialClassification/Challenge.lean:33:8: warning: declaration uses `sorry`
```

The Solution had no warning and printed:

```text
'Palomar.SquarefreeBinomialClassification.squarefree_choose_half_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

The private Challenge and Solution namespace roots were kept separate, then
prepended individually to the verified parent dependency path for the two type
audits. The source type audit used only the parent path. This avoids namespace
root overlay and prevents one same-named package declaration from replacing the
other. All three audits exited `0`; their raw logs matched as reported above.
Temporary `.lean` audit sources and private compiled package artifacts were
removed after checks. No output was written under a shared `.lake` tree.

Final package source hashes, excluding this report itself, are:

| File | SHA-256 |
| --- | --- |
| `Challenge.lean` | `2cfd723bc0a39f29284e073d9312683b4b15307e6ee4504d85aaa5c1be2c1331` |
| `Solution.lean` | `df8fa0385020df7052430f65078de2a7d03e2d76699cbab96832d695ad961cb4` |
| `comparator.json` | `5c54acb549d7115b16c297d4d9323601d6a5a2edc72464de2e02818e26397c96` |
| `formalization.yaml` | `a5a322797e8301bdcc9f2ef1a79eb7d2403698f4644b4519aa6ebf97d52cb978` |
| `README.md` | `2986e8927dc8ae3c41e6724b03ca08ff0f20b0a481b9e912f211bfe9093f8b1f` |

## Independent AI review record

Two independent AI reviews completed with PASS results on 2026-09-08 against
reviewed integration
`dcf241b5a1f33b86325e82d575fa588d9a3575e6`. Their review scope is frozen to:

```text
Challenge.lean  2cfd723bc0a39f29284e073d9312683b4b15307e6ee4504d85aaa5c1be2c1331
Solution.lean   df8fa0385020df7052430f65078de2a7d03e2d76699cbab96832d695ad961cb4
```

The foundations/fidelity reviewer reported **PASS with no required
corrections**. It found the theorem faithful to Noe's finite assertion and the
exact thirteen-value list; confirmed the strict `n < 10^8` guard, floor
interpretation of natural division, and ordinary Mathlib `Squarefree`; and
accepted the source-proof, pin, and certificate-provenance account as correctly
scoped. It independently used the canonical OEIS web-context fallback after the
local CLI failed because an SSH clone was unauthorized. This supplied source
confirmation, not a novelty, priority, human-approval, or endorsement claim.

The vacuity/trust reviewer likewise reported **PASS**, with no `VACUOUS`,
`DRIFT`, `TRUST`, or material `STYLE` finding. It separately compiled the
Challenge in 1.23 seconds and Solution in 1.27 seconds, each at approximately
1.87 GiB; verified raw type equality between Challenge, Solution, and source;
confirmed a genuine all-`Nat` domain under the strict guard, the valid `n = 0`
case, and the absence of answer-bearing hypotheses; and independently
kernel-reduced the full `Fin 31` witness certificates, `Fin 26` power-and-sum
certificates, and `Fin 72` small-odd certificates using `decide`. The selected
closure used only `propext`, `Classical.choice`, and `Quot.sound`; the separately
checked power/sum certificate closure used only `propext`.

An optional nonexistent CLI output path was omitted by that reviewer. Its
absence did not affect any build or checked declaration and was explicitly not
a trust finding. Comparator and NanoDa remain **NOT RUN**.

These are scoped independent AI reviews of the frozen Lean bytes, not human
mathematical, attribution, fidelity, or Palomar approval and not automatic
approval of metadata edited afterward. Human authors, maintainers, submission
authorization, source endorsement, and review remain unknown or pending. The
parent will review the final combined metadata before any publication.

## Axiom and trust audit

The fresh selected Solution report is exactly the allowlist
`{propext, Classical.choice, Quot.sound}`. The parent source audit reports the
same closure for all selected bridge dependencies, including
`Erdos175.witness_cert`, the even classification, the even and odd bounded
exclusions, the below-72 classification, the small and large residual
certificates, the combined bounded exclusion, and the final equivalence. Greps
of the source and axiom logs found no selected dependency on `sorryAx`,
`Lean.ofReduceBool`, a custom axiom, or native trust.

This declaration-level transitive axiom audit was independently corroborated
by the vacuity/trust AI reviewer for the frozen Lean hashes. The source's
self-audits and parent compilation/diff checks remain distinct provenance, and
no human foundations, semantic, or mathematical review is claimed.

## Policy, source, and literature checks

The current submission page was freshly read at
<https://palomar-registry.org/how-to-submit>. Its linked PalomarPolicy was
inspected read-only at revision
`e9c8c238f5695b10f75db7175648a1d0195352c1`; the linked starter repository at
`128a6c5ce5f48622e69927ccd639cbff401022e8`; and the formalization.yaml standard
at `99c678e569c7c4c0772db297c5ddd5e4c9b6322e`. The package follows the current
Challenge/Solution, dependency, Comparator, source relationship, AI disclosure,
scope, and review contracts except for the two deliberately unresolved human
identity requirements described below.

A fresh web-context retrieval of <https://oeis.org/A046098> confirmed the title,
all thirteen terms, and the attributed comment **“No other n < 10^8. - T. D.
Noe, Apr 06 2007.”** The attribution is to Noe's computational comment, not to
the complete OEIS entry or an unbounded theorem. Limited searches for A046098,
squarefree middle binomial coefficients, and prior Lean formalizations found
OEIS, MathWorld summaries, and related central-binomial literature but no exact
prior formalization. This supports only a scoped no-reference-found disclosure;
it does not establish novelty, priority, or firstness.

The pre-existing `Palomar/SquarefreeBinomialOddRange` package was inspected
read-only and is listed in metadata as a narrower related candidate. It selects
only odd `n` with `72 ≤ n < 10^8`; it is not imported or treated as a registered
dependency.

## Metadata and unavailable tooling

Python's JSON parser and a duplicate-key-rejecting PyYAML loader accepted the
Comparator and metadata files. Local assertions confirmed exactly one selected
theorem, no selected definitions, precisely the three allowed axioms,
`enable_nanoda: true`, source-based provenance, the two distinct AI phases,
zero proof-development sorries, and `review.status: unchecked`. The upstream
JSON-schema validator was not available and was not installed.

Preflight found no `Comparator`, `comparator`, `lean4export`, `landrun`,
`nanoda`, or `nanoda_bin` executable. Comparator/export/NanoDa checks are
therefore **NOT RUN**, not passed or failed. No verifier or dependency was
installed.

Current Palomar policy mechanically requires nonempty human-only
`project.authors` and `project.responsible_maintainers`. No authoritative names
or submission authorization were supplied. In accordance with the instruction
not to invent identities, both arrays remain empty and the blocker is explicit
in `formalization.yaml` and `README.md`. A responsible human must provide those
two lists and establish authorization before this candidate can satisfy intake.
Source-author contact and endorsement are also unknown and no endorsement is
asserted.

Original source-proof assistance (`gpt-6-astra`, xhigh, Yah) is recorded
separately from this packaging phase (`gpt-5.6-sol`, high, Yah). Two independent
AI reviews of the frozen Lean bytes are recorded above. No completed human
review or Palomar approval is claimed. The parent must review the final combined
metadata before publication.
