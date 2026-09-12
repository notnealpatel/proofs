# Verification: bounded odd squarefree-binomial range

## Current mechanical verification

[Authoritative campaign manifest](../Wave4ComparatorEvidence.yaml): **PASS** for every declaration selected by this package’s `comparator.json`. Earlier text below is historical and superseded. Human review remains **UNCHECKED**; this makes no claim of Palomar acceptance, submission, or publication.

## Status and selected declaration

- **Independent Challenge compilation:** PASS, exit `0`; the only warning is its
  intentional selected theorem `sorry`.
- **Separate Solution compilation:** PASS, exit `0`, with no warnings or errors.
- **Selected Solution axiom audit:** PASS, exactly `propext`, `Classical.choice`,
  and `Quot.sound`; no `sorryAx`, native-computation axiom, or custom axiom.
- **Statement identity:** PASS, both textual theorem headers and raw elaborated
  Lean expression types match exactly in separate environments.
- **JSON/YAML parsing and local configuration consistency:** PASS. This is not a
  claim of an unavailable external schema or Comparator validation.
- **Comparator / external Nanoda verification:** NOT RUN; required executables
  are absent. No installation or toolchain change was attempted.
- **Human review:** PENDING. USER is the sole reviewer.

The only selected declaration is
`Palomar.SquarefreeBinomialOddRange.not_squarefree_choose_half_of_odd`:

```lean
theorem not_squarefree_choose_half_of_odd {n : ℕ} (hn : Odd n)
    (h72 : 72 ≤ n) (hlt : n < 10 ^ 8) : ¬ Squarefree (n.choose (n / 2))
```

This header is byte-identical in Challenge and Solution. Both files freshly
printed:

```text
@not_squarefree_choose_half_of_odd : ∀ {n : ℕ}, Odd n → 72 ≤ n → n < 10 ^ 8 → ¬Squarefree (n.choose (n / 2))
```

The exact fresh Solution axiom output was:

```text
'Palomar.SquarefreeBinomialOddRange.not_squarefree_choose_half_of_odd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## Independence, semantics, and nonvacuity

`Challenge.lean` imports only:

```lean
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Squarefree
```

It contains no project import, Solution import, or mathematical definition. Its
single intentional hole is the selected theorem proof. `Solution.lean` imports
only `Erdos.Erdos175.SquarefreeCentralBinom` and proves the identical statement
with:

```lean
exact Erdos175.A046098.not_squarefree_choose_half_of_odd hn h72 hlt
```

There is no Challenge import and no premise carrying the desired answer. The
binary digit-sum split and finite certificates are internal to the source proof,
not additional hypotheses on the package theorem.

Both files independently kernel-check joint satisfiability at `n = 73`:
`Odd 73`, `72 ≤ 73`, and `73 < 10^8`. They also check `73 / 2 = 36`. Thus the
index domain is nonempty, the lower and upper guards coexist, and the floor
interpretation is concrete. Division is by the fixed nonzero natural number `2`;
no totalized zero-divisor case is involved.

For a stronger identity check than pretty-printed signatures, each freshly
compiled package module was imported into its own audit environment. The same
command was run separately, never importing Challenge and Solution together:

```lean
open Lean in
run_cmd do
  let env ← getEnv
  match env.find? `Palomar.SquarefreeBinomialOddRange.not_squarefree_choose_half_of_odd with
  | none => throwError "selected theorem is absent"
  | some info => logInfo (reprStr info.type)
```

The two complete raw expression dumps were compared with `cmp` and were
byte-identical. Both SHA-256 values are:

```text
591f333e5a2d5a7c3062e2a927b79dc6a9f753ed29c0dd08d5023552d09ea2b2
```

The dump explicitly identifies `Nat`, `Odd`, `Squarefree`, `Nat.choose`, and the
canonical natural-number instances (`Nat.instSemiring`, `Nat.instMonoid`,
`Nat.instDiv`, and the comparison/numeral/power instances). There are no private
model constants whose semantics could differ across files. This check is not
represented as a Comparator run.

## Source and cache provenance

The selected repository sources match revision
`55ab7d253f32b9632581cf31cc4951c2b2119533`. Packaging began in the persisted lane
workspace at revision `22e96d0e28c01b013bdcc4aa0389239ec4b31ddd`; the selected
sources were compared byte-for-byte with the supplied source revision using
`jj --ignore-working-copy file show`, and with `/home/exedev/p/proofs`. All three
source files and the toolchain, Lake configuration, and manifest matched.
No repository source was edited during packaging.

Toolchain and dependency pins:

- Lean `4.33.0-rc1`, commit `62eed1db4d67327ec8120be05f1a1b0847d74561`,
  `x86_64-unknown-linux-gnu`, Release.
- Lake `5.0.0-src+62eed1d`.
- `lean-toolchain`: `leanprover/lean4:v4.33.0-rc1`.
- Mathlib manifest revision: `3edb3c0658f69f197b1e501b1f7623f3f7b3898c`.

SHA-256 values for exact inputs:

| Input | SHA-256 |
| --- | --- |
| `Proofs/Erdos/Erdos175/SquarefreeCentralBinom.lean` | `d2dbc564cbdf7d8fdedd0d8a3655ab5e278ece91df781a7e2b60e5f82022f40f` |
| `Proofs/Erdos/Erdos175/SquarefreeCentralBinomResidual.lean` | `f5edc424b403267bdeb2606ecca8abf80143bad2962fb5f78803d5d8f8518db6` |
| `Proofs/Erdos/Erdos175/NotSquarefree.lean` | `a606f54092876c902ed69a60b1329a7fd061ef3fa372c9d41d1efb159f63009c` |
| `lean-toolchain` | `02f25adee7c1d6bf2e95b7b5b13f45b9892c7dd53ef470d5372ac60bda3df023` |
| `lakefile.toml` | `5fea1b2cc353a49df4d727bd77e43a01c074130fcb099610fe0320d8d7a1906f` |
| `lake-manifest.json` | `948a91a6b3c52e0b640d0dadc1bf84cf967403244ac590c162c005c2544a439e` |

The main checkout's selected artifact set was **not used**: its residual helper
`.olean` was absent, and its target `.olean` differed from the artifact produced
by the earlier successful lane proof build. Matching source files alone were
not treated as evidence that this incomplete main artifact set was current.

Instead, the persisted coherent local proof artifacts were reused. They came
from the earlier successful builds of the exact source bytes above. A fresh,
bounded `lake --no-build` check reported all relevant targets up-to-date. This
is a **source/cache consistency check with replayed logs**, not a fresh source
proof compilation. Only the new package files and temporary type-audit files
were freshly elaborated during packaging. Shared Mathlib artifacts were reused
without rebuilding the dependency cache.

The reused local artifacts under
`.lake/build/lib/lean/Erdos/Erdos175/` have hashes:

| Artifact | SHA-256 |
| --- | --- |
| `NotSquarefree.olean` | `bb97c9b8270e84b9d3daa3da959b3ccdb6b18e8bb3b04540515539870c1d7838` |
| `SquarefreeCentralBinomResidual.olean` | `37549ca1b2f65451a6882d11b194176337774b5a268bd6c20c7f0d1d47ea10fa` |
| `SquarefreeCentralBinom.olean` | `a8c3a80c4d1f48f994fab4dcc3b9d8a815d28139ffb7fc254546e657caf44a64` |

## Commands and fresh outputs

All commands ran with the persistent working directory in the assigned
workspace. `tool_atop` was called before every Lean/cache verification call;
available memory was at least `21.74 GiB` on the reported `23.46 GiB` host.
Lean checks were restricted to one core, one Lean worker, a `2048 MB` Lean
memory limit, and a `120` second timeout. No virtual-address-space cap, global
build, package installation, or dependency upgrade was used.

In the commands below, `TMP` abbreviates
`/tmp/yah/subagent/prove-binomial-residual-5b9503a/package`.
The source-cache check was:

```sh
timeout 120 taskset -c 2 lake --no-cache --no-build build \
  Erdos.Erdos175.SquarefreeCentralBinom
```

Exit `0`; exact final line: `All targets up-to-date (1178 jobs).` No source
module was rebuilt. The new package modules were compiled independently:

```sh
timeout 120 taskset -c 2 lake env lean -j1 -M2048 \
  Palomar/SquarefreeBinomialOddRange/Challenge.lean \
  -o "$TMP/oleans/Palomar/SquarefreeBinomialOddRange/Challenge.olean"

timeout 120 taskset -c 2 lake env lean -j1 -M2048 \
  Palomar/SquarefreeBinomialOddRange/Solution.lean \
  -o "$TMP/oleans/Palomar/SquarefreeBinomialOddRange/Solution.olean"
```

Both exited `0`. The Challenge's sole warning was:

```text
Palomar/SquarefreeBinomialOddRange/Challenge.lean:24:8: warning: declaration uses `sorry`
```

The Solution's fresh signature and axiom output appear at the start of this
report. The two type-audit files imported the respective compiled module and
used the raw-expression command above. They were run separately as:

```sh
LEAN_PATH="$TMP/oleans:$(lake env printenv LEAN_PATH)" \
  timeout 120 taskset -c 2 lean -j1 -M2048 "$TMP/ChallengeType.lean"

LEAN_PATH="$TMP/oleans:$(lake env printenv LEAN_PATH)" \
  timeout 120 taskset -c 2 lean -j1 -M2048 "$TMP/SolutionType.lean"
```

Both exited `0`, and `cmp` on the two logs exited `0`. Temporary audit sources
and generated package `.olean` files were removed after verification; logs are
retained outside the repository:

- `$TMP/source-cache-check.log`
- `$TMP/challenge.log`
- `$TMP/solution.log`
- `$TMP/challenge-type.log`
- `$TMP/solution-type.log`

The verified package source hashes are:

| File | SHA-256 |
| --- | --- |
| `Challenge.lean` | `73553bef8c0a63a3a7c9597df6dddf22d5c9b0f8d68b34d3bbdde497a7f71320` |
| `Solution.lean` | `3fdea7739892791f00a75320c82522e4a31d0f61a47989dd4564b6061ea7a9ce` |
| `comparator.json` | `7fbf3e061ecd267d5c91d5885db2745defeef10cf559e04453f063a5fab1f9ef` |

## Metadata, allowlist, and unavailable tools

Python's JSON parser and PyYAML `6.0.1` parsed the two metadata files. Structural
checks followed the repository's six-file packages and `v0.4` convention:
exact module names, exactly one selected theorem, precisely the three allowed
axioms, `enable_nanoda: true`, one Challenge hole, zero definition holes, zero
Solution holes, empty human identity lists, and the recorded model identifier.
A comment-stripped Lean-source scan confirmed the Challenge's sole `sorry`,
Solution's absence of holes or native/custom proof constructs, and import
independence. These checks do not claim full validation by an external schema
tool.

The packaging baseline recorded 1628 pre-existing paths. Their size and
modification time remained unchanged, and content hashes for Lean, Markdown,
JSON, YAML, TOML, the toolchain file, and license remained unchanged. In
particular, every existing README was untouched. The only package outputs are
the six new files in `Palomar/SquarefreeBinomialOddRange/`: `README.md`,
`Challenge.lean`, `Solution.lean`, `comparator.json`, `formalization.yaml`, and
`verification.md`. No `Proofs`, existing `Palomar` package, `References`,
`Formalize`, or root configuration file was changed.

`command -v` preflight found no `comparator`, `landrun`, `lean4export`, `nanoda`,
or `nanoda_bin` executable. Comparator and external Nanoda verification were
therefore **NOT RUN**, not failed or passed. No installation was attempted.
The configuration keeps `enable_nanoda: true` and only the selected theorem
for later USER-controlled verification. No package compilation attempt failed;
the incomplete main artifact set was discovered and rejected before use.

## Scope, attribution, and review boundary

The theorem covers precisely odd `n` in `[72, 10^8)`. It does not select an
unbounded analytic result, the full thirteen-term classification, or the
combined Noe theorem. The source's earlier native certificate axiom remains in
the unchanged even branch and consequently in its combined theorem; the fresh
Solution axiom audit above excludes that dependency from this selection.

Attribution to T. D. Noe concerns the source's recorded finite-computation
comment in OEIS A046098. The repository proof instead checks bounded Kummer
certificates in the kernel. The package did not repeat the external source
retrieval or perform an independent literature review. Implementation and
packaging used gpt-6-astra with xhigh reasoning through Yah; precise prior
infrastructure model/session details are unknown. Human author and maintainer
identities are left empty rather than invented. The MIT project license is
supported by the existing repository `LICENSE`, not inferred for external
sources. USER review remains pending and is the sole review gate; none of these
technical checks constitutes novelty, priority, acceptance, or submission.
