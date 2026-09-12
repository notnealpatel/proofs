# Verification: A092482 Challenge/Solution pair

## Current mechanical verification

[Authoritative campaign manifest](../Wave4ComparatorEvidence.yaml): **PASS** for every declaration selected by this package’s `comparator.json`. Earlier text below is historical and superseded. Human review remains **UNCHECKED**; this makes no claim of Palomar acceptance, submission, or publication.

## Scope and statement alignment

`Challenge.lean` is independent of the claimed answer: it imports only `Mathlib`, defines
`binToTernary n` as `Nat.ofDigits 3 (Nat.digits 2 n)`, and constructs the increasing
greedy sequence from `{1}` using `Nat.find`.  Its legality predicate permits the ordered
progression `(1, 2, 3)` and forbids every other strictly ordered three-term arithmetic
progression.  Thus the exceptional third seed value is produced by the greedy rule rather
than inserted into the sequence definition.

`Solution.lean` repeats those declarations and does not import the Challenge.  It proves
that separately generated decision procedures select the same least legal extension,
inducts over prefix sets, obtains pointwise equality with
`_root_.A092482.greedySeq`, and then applies the existing
`A092482.greedySeq_add_two`.  The selected declaration text is identical in both files;
a textual diff of the theorem headers exited `0`.  Fresh `#check` output from each file
was identical:

```text
Palomar.A092482.greedySeq_add_two : ∀ (m : ℕ),
  Palomar.A092482.greedySeq (m + 2) = 1 + 2 ^ Nat.log 2 (m + 1) + Palomar.A092482.binToTernary (m + 1)
```

This retains the zero-indexing convention `greedySeq r = OEIS a(r+1)` and the required
`m + 1` input to both `Nat.log` and the zero-offset binary-to-ternary map.

## Toolchain and dependencies

- Lean: `4.33.0-rc1`, commit `62eed1db4d67327ec8120be05f1a1b0847d74561`.
- `lean-toolchain`: `leanprover/lean4:v4.33.0-rc1`.
- Mathlib revision from `lake-manifest.json`:
  `3edb3c0658f69f197b1e501b1f7623f3f7b3898c`.
- Solution import: `Enumerative.No3APGreedy`; that source imports
  `Enumerative.StanleyDigits`, whose digit definition was inspected directly.
- Source SHA-256 values at verification time:
  - `No3APGreedy.lean`: `1a010474d46536d71d91104e37d4c371a3da2c498865286322b06f8dbfab3ba1`
  - `StanleyDigits.lean`: `44d87c876313ab3e54824574e4b1440707287f6ca7bdacaa5b7d6538e16593b8`

Before every expensive command, `tool_atop` showed at least 22.47 GB available out of
23.46 GB.  Lean help confirmed that `-M` is a megabyte allocation limit and `-j` controls
Lean threads.  Lake's displayed build help had no serial-job switch, so missing project
modules were compiled individually with one Lean thread.

## Commands and results

The already successful source prerequisites were produced serially with these bounded
commands (verbose output was redirected to scratch logs):

```sh
ulimit -v 18874368
timeout 300s lake env lean -M12000 -j1 Proofs/Enumerative/StanleyDigits.lean \
  -o .lake/build/lib/lean/Enumerative/StanleyDigits.olean \
  -i .lake/build/lib/lean/Enumerative/StanleyDigits.ilean
# exit 0

ulimit -v 18874368
timeout 600s lake env lean -M12000 -j1 Proofs/Enumerative/No3APGreedy.lean \
  -o .lake/build/lib/lean/Enumerative/No3APGreedy.olean \
  -i .lake/build/lib/lean/Enumerative/No3APGreedy.ilean
# exit 0
```

Final separate checks used:

```sh
ulimit -v 18874368
timeout 180s lake env lean -M12000 -j1 Palomar/A092482/Challenge.lean
# exit 0; sole warning: declaration uses `sorry` at the intentional challenge hole

ulimit -v 18874368
timeout 180s lake env lean -M12000 -j1 Palomar/A092482/Solution.lean
# exit 0; no warnings or errors
```

Fresh selected-theorem axiom output from the final Solution run was:

```text
'Palomar.A092482.greedySeq_add_two' depends on axioms: [propext, Classical.choice, Quot.sound]
```

A scan of `Solution.lean` found no `sorry`, `native_decide`, `Lean.ofReduceBool`, custom
`axiom`, `implemented_by`, `extern`, or `csimp`.  The only `sorry` in the pair is the
intentional Challenge theorem hole.

## Failed attempts retained as verification history

Initial 6 GiB and 10 GiB virtual-memory caps were too small to read the full Mathlib
private olean environment; raising the virtual cap to 18 GiB while retaining Lean's
12 GB allocation limit succeeded.  A targeted Lake build failed with
`failed to create thread`, so it was not retried unchanged; the serial direct Lean
commands above replaced it.  The first alignment attempt used `rfl`, which correctly
failed because the duplicated `Nat.find` definitions use separately generated decidable
instances.  Attempts to rewrite only equality of projected prefix sets then failed due
to dependent invariant proofs.  The final proof avoids that obstruction: it compares the
two least choices using `Nat.find_spec`/`Nat.find_min'`, transports only across an equality
between explicit Finset variables, and proves prefix equality by `congrArg₂ insert`.

These checks establish the technical package checkpoint only.  They do not claim human
approval, Palomar acceptance, novelty, or priority; human review remains pending.
