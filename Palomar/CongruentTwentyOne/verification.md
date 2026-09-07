# Verification: concrete primitive congruent number 21

## Results and limits

- **Fresh Challenge compilation: PASS**, exit 0; exactly one intentional theorem
  `sorry` warning. No `sorry` definitions or custom model definitions exist.
- **Fresh Solution compilation: PASS**, exit 0, no warnings or errors.
- **Selected Solution axiom audit: PASS**: exactly `propext`, `Classical.choice`,
  and `Quot.sound`; no `sorryAx`, native computation axiom, or custom axiom.
- **Statement identity: PASS at the literal-source level**, with the identical
  fully qualified theorem name and expanded standard-Mathlib statement. Both
  files compiled independently; Solution's `change` also checked definitional
  equality with the source predicate. This is not a Comparator pass.
- **JSON and YAML parsing: PASS** using Python's `json` and PyYAML 6.0.1.
  This is not validation against an external v0.4 metadata schema.
- **Comparator / landrun / lean4export / Nanoda: NOT RUN**, executables unavailable.
- **USER review: PENDING**, the sole review gate. Mechanical checks are not human
  mathematical, source-fidelity, or attribution review.

## Exact selected statement

Both files have namespace `Palomar.CongruentTwentyOne` and the byte-identical header:

```lean
theorem isPrimitiveCongruent_twentyOne :
    Squarefree (21 : ℕ) ∧
      ∃ a b c : ℚ, 0 < a ∧ 0 < b ∧ 0 < c ∧
        a ^ 2 + b ^ 2 = c ^ 2 ∧ a * b = 2 * (21 : ℚ) := by
```

This asserts squarefreeness and a positive rational right triangle of area 21,
without hypotheses. The type `ℚ` is inhabited, explicitly checked by `⟨0⟩` in
both files; positivity excludes zero or negative side lengths. The statement has
no division, truncated subtraction, hidden free parameters, or custom instances.
No separate proved copy of the selected claim appears in Challenge.

Challenge imports only `Mathlib.Data.Nat.Squarefree` and
`Mathlib.Algebra.Order.Field.Rat`. Solution imports only
`Enumerative.CongruentBSD`, not Challenge. Neither file defines a custom predicate.
The Solution bridge is:

```lean
  change A273929.IsPrimitiveCongruent 21
  exact A273929.isPrimitiveCongruent_twentyOne
```

The source predicate unfolds as `Squarefree 21 ∧ IsCongruentNumber 21`, with
`IsCongruentNumber` and `IsCongruentArea` giving exactly the displayed existential
condition. The numeral cast is definitionally equal to `(21 : ℚ)`. The elaborated
bridge passed. There is no Solution-only alias or differing Challenge definition.

## Fresh compilation commands and output

Commands were run from the assigned workspace, with explicit `LEAN_PATH`; no
main-worktree write, Lake build, dependency rebuild, or toolchain change occurred.
The existing Mathlib package cache was reused read-only. There was no heavy
per-lane parallel fan-out and no low virtual-memory limit.

Immediately before Challenge compilation, `tool_atop` reported **22.01 GiB
available** out of 23.46 GiB. The actual bounded command was:

```sh
mkdir -p .lake/build/lib/lean/Palomar/CongruentTwentyOne
LEAN_PATH="$(printf '%s:' .lake/packages/*/.lake/build/lib/lean)" \
  /usr/bin/time -f 'elapsed=%e max_rss_kb=%M exit=%x' \
  timeout 120 lean -j1 -M 4096 -R . \
  -o .lake/build/lib/lean/Palomar/CongruentTwentyOne/Challenge.olean \
  Palomar/CongruentTwentyOne/Challenge.lean
```

Fresh output (only line wrapping normalized):

```text
Palomar/CongruentTwentyOne/Challenge.lean:20:8: warning: declaration uses `sorry`
isPrimitiveCongruent_twentyOne : Squarefree 21 ∧ ∃ a b c, 0 < a ∧ 0 < b ∧ 0 < c ∧ a ^ 2 + b ^ 2 = c ^ 2 ∧ a * b = 2 * 21
'Palomar.CongruentTwentyOne.isPrimitiveCongruent_twentyOne' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
elapsed=1.26 max_rss_kb=1856228 exit=0
```

Immediately before Solution compilation, `tool_atop` reported **20.94 GiB
available**. The actual bounded command was:

```sh
LEAN_PATH=".lake/build/lib/lean:$(printf '%s:' .lake/packages/*/.lake/build/lib/lean)" \
  /usr/bin/time -f 'elapsed=%e max_rss_kb=%M exit=%x' \
  timeout 120 lean -j1 -M 8192 -R . \
  -o .lake/build/lib/lean/Palomar/CongruentTwentyOne/Solution.olean \
  Palomar/CongruentTwentyOne/Solution.lean
```

Fresh output:

```text
isPrimitiveCongruent_twentyOne : Squarefree 21 ∧ ∃ a b c, 0 < a ∧ 0 < b ∧ 0 < c ∧ a ^ 2 + b ^ 2 = c ^ 2 ∧ a * b = 2 * 21
'Palomar.CongruentTwentyOne.isPrimitiveCongruent_twentyOne' depends on axioms: [propext, Classical.choice, Quot.sound]
elapsed=7.38 max_rss_kb=6696748 exit=0
```

Both files run the exact commands
`#check @Palomar.CongruentTwentyOne.isPrimitiveCongruent_twentyOne` and
`#print axioms Palomar.CongruentTwentyOne.isPrimitiveCongruent_twentyOne`.
The pretty-printer elides the rational binder type in its output; the identical
full source headers above explicitly retain `a b c : ℚ`.

Logs retained in the workspace's ignored build area:

- `.lake/congruent21-challenge.log`
- `.lake/congruent21-solution.log`

Both new Lean files passed on their first compilation attempts. No failed or
cached target compilation is counted as a fresh result.

## Toolchain and cache provenance

- Accepted source revision supplied by USER:
  `55ab7d253f32b9632581cf31cc4951c2b2119533`.
- Lean `4.33.0-rc1`, commit `62eed1db4d67327ec8120be05f1a1b0847d74561`,
  `x86_64-unknown-linux-gnu`, Release.
- Mathlib manifest revision: `3edb3c0658f69f197b1e501b1f7623f3f7b3898c`.
- `.lake/packages` resolves to `/home/exedev/p/proofs/.lake/packages`, so the
  prerequisite package sources and caches are the identical directories, used
  read-only. Workspace and main configuration hashes matched exactly:

| Input | SHA-256 |
| --- | --- |
| `lean-toolchain` | `02f25adee7c1d6bf2e95b7b5b13f45b9892c7dd53ef470d5372ac60bda3df023` |
| `lake-manifest.json` | `948a91a6b3c52e0b640d0dadc1bf84cf967403244ac590c162c005c2544a439e` |
| `lakefile.toml` | `5fea1b2cc353a49df4d727bd77e43a01c074130fcb099610fe0320d8d7a1906f` |
| `Proofs/Enumerative/CongruentBSD.lean` | `4ac04f10ac12f62611add53438b53676a88794a84b97d532ac10d01bb852e8b4` |
| Private `Enumerative/CongruentBSD.olean` | `6115d578072d5be263c6de27f0fec622aa93b4433508dbc7ec5e76e0e60e3390` |

The source hash also matched the exact accepted revision through read-only
`jj --ignore-working-copy file show` followed by `cmp`. The imported
`CongruentBSD.olean` is the private artifact freshly compiled in the preceding
concrete-certificate tranche from this exact source; it was not taken from a
possibly stale main project cache. Its recorded fresh build exited 0 in 12.49 s
with peak RSS 7,167,916 KiB under `timeout 180 lean -j1 -M 8192 -R Proofs`.
The log `.lake/congruent21-fresh.log` records both source declarations' exact
three-standard-axiom closures. That unchanged prerequisite was reused here,
not represented as freshly rebuilt during packaging.

Fresh package source and artifact hashes:

| File | SHA-256 |
| --- | --- |
| `Challenge.lean` | `eb7f9cece5ca646eca42f593b0f92d6ae3911a95b5cfc0b315f1c95560321977` |
| `Solution.lean` | `23c5339eb25b28b0ddafad38a2d4498ca19264761699b4d87aeca06aadbdcef1` |
| `Challenge.olean` | `a0130de6ff04e804acc6cafb60ed2ef54c7b8c0d3c5f644263c9467b33350664` |
| `Solution.olean` | `023ba537fe4b740549d20a6e54d1d16b63261b1ea0fefe56fac1b4dec901c03d` |

## Metadata, tooling, and write scope

A Python check parsed `comparator.json` and `formalization.yaml`, confirmed the
same selected fully qualified declaration, the exact three permitted axioms,
`enable_nanoda: true`, YAML version `v0.4`, and empty unknown author/maintainer
lists. It extracted and compared both theorem headers byte-for-byte, checked
independent imports, and found exactly one Challenge `sorry`. Solution contains
none of `sorry`, `axiom`, `native_decide`, `Lean.ofReduceBool`, `implemented_by`,
`extern`, or `csimp`.

`command -v` found none of `comparator`, `landrun`, `lean4export`, `nanoda`, or
`nanoda_bin`. Consequently those checks are **NOT RUN**, not passed. No verifier
installation, external review, broad build, or schema-validation claim is made.
The configuration leaves Nanoda enabled for later USER-controlled checking.

The authorized tracked write scope is exactly these six new files:

1. `Palomar/CongruentTwentyOne/README.md`
2. `Palomar/CongruentTwentyOne/Challenge.lean`
3. `Palomar/CongruentTwentyOne/Solution.lean`
4. `Palomar/CongruentTwentyOne/comparator.json`
5. `Palomar/CongruentTwentyOne/formalization.yaml`
6. `Palomar/CongruentTwentyOne/verification.md`

Only ignored workspace `.lake` logs and fresh build artifacts accompany them.
No `Proofs` source, existing Palomar package or README, root README, `References`,
`Formalize`, manifest, configuration, or toolchain file was edited during
packaging. No temporary probe source was created.

The imported archival `A273929.a273929_subset_a006991` still has its intentional
`sorry`, outside the selected theorem's closure. The package claims only the
known concrete term 21, not progress on the general inclusion, BSD, or rank.
AI assistance was material (latest implementation and packaging run attribution:
USER-designated gpt-6-astra, xhigh); prior infrastructure history and human
identities remain unknown. USER review and the YAML metadata blockers remain
unresolved; no submission or acceptance is implied.
