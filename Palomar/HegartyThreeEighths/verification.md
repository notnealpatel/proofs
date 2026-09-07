# Verification: Hegarty three-eighths Challenge/Solution pair

## Status

- **Challenge elaboration:** PASS. Its sole warning is the intentional theorem hole.
- **Repository theorem compilation:** PASS.
- **Solution elaboration and definition-alignment bridge:** PASS.
- **Selected theorem axiom audit:** PASS. The closure is exactly `propext`,
  `Classical.choice`, and `Quot.sound`; it does not include `sorryAx`.
- **Comparator:** NOT RUN because the required verifier executables are unavailable.
- **Human review:** PENDING. USER review is the sole review gate; no review by an agent or
  parent is claimed.

## Statement and definition alignment

Both `Challenge.lean` and `Solution.lean` independently contain the same ordinary greedy
construction and selected theorem statement. They import no package file from one another.
The Challenge imports only `Mathlib`; the Solution imports the existing substantive proof
through `Enumerative.HegartyThreeEighths`.

A prefix is a reversed `List Nat`. `IsCandList v t` requires all three defining conditions:

1. `1 <= t` (positivity);
2. `t ∉ v` (non-reuse);
3. for every `j` with `2*j+2 <= v.length`,
   `t + v.getD (2*j+1) 0 != 2*v.getD j 0` (the exact forbidden arithmetic progression).

`nextTerm` uses `Nat.find`, after a proof that an admissible value always exists, and thus
selects the least candidate. The recursion satisfies
`pre (n+1) = nextTerm (pre n) :: pre n`, and `a n = nextTerm (pre n)`. Consequently `a n`
is zero-indexed and represents Hegarty's one-indexed `pi_g(n+1)`. Ground checks cover the
empty prefix, positivity, non-reuse behavior, the forbidden progression `(1,2,3)`,
`listMax`, the first least choice, `pre 0`, `a 0 = 1`, and the theorem boundary `n=0`.

The Solution does not assume definitional equality between separately generated `Nat.find`
instances. `nextTerm_eq_source` proves equality of least choices in both directions using
`Nat.find_spec` and `Nat.find_min'`. `pre_eq_source` then inducts over explicit reversed
prefix lists, and `a_eq_source` identifies the package sequence with `A094870.a`. The final
proof applies `A094870.hegarty_three_eighths` only after this alignment.

A textual extraction of the two selected theorem headers produced identical text:

```text
theorem hegarty_three_eighths (n : ℕ) : 3 * (n + 1) ≤ 8 * a n
```

Fresh `#check` output was:

```text
hegarty_three_eighths : ∀ (n : ℕ), 3 * (n + 1) ≤ 8 * a n
```

The fully qualified selected declaration is
`Palomar.HegartyThreeEighths.hegarty_three_eighths`.

## Toolchain and pinned inputs

- Assigned campaign base: `117a6e3949ca41075e133e350e38d9d2fbfdd8e2`.
- Lean: `4.33.0-rc1`, commit `62eed1db4d67327ec8120be05f1a1b0847d74561`,
  `x86_64-unknown-linux-gnu`, Release build.
- Lake: `5.0.0-src+62eed1d` (Lean `4.33.0-rc1`).
- `lean-toolchain`: `leanprover/lean4:v4.33.0-rc1`.
- Mathlib manifest revision: `3edb3c0658f69f197b1e501b1f7623f3f7b3898c`.
- Source SHA-256 values:
  - `HegartyPermutation.lean`:
    `3709801adf78641b7798fb6595cdfd40f57bf4ae1a63f78489874f709473319e`
  - `HegartyThreeEighths.lean`:
    `9c14d20b8ec57a622418e3841618950965585908d20d675c0aea003bdd18202c`
  - `lake-manifest.json`:
    `948a91a6b3c52e0b640d0dadc1bf84cf967403244ac590c162c005c2544a439e`
  - `lean-toolchain`:
    `02f25adee7c1d6bf2e95b7b5b13f45b9892c7dd53ef470d5372ac60bda3df023`
  - reused `HegartyPermutation.olean` (both read-only original and scratch copy):
    `c1245710457974515ace3b6205eafd34c93709ffae9582d51bafcc330ec7fdf6`
  - newly compiled scratch `HegartyThreeEighths.olean`:
    `139f2b26e56255e970320dc5d14eb3b61cdf985d14782b60d9e29d00e9dfc63d`

The corresponding source, manifest, and toolchain hashes under
`/home/exedev/p/proofs` matched exactly. Its read-only
`Enumerative/HegartyPermutation.olean` was therefore reused through a private scratch copy.
The target `HegartyThreeEighths.olean` was absent there and was compiled from the exact
workspace source into the private scratch directory. No repository cache, dependency,
toolchain, root configuration, `Proofs/`, `References/`, or README file was modified.

## Commands and exact results

Immediately before the successful Challenge check, `tool_atop` reported 23.46 GiB total,
0.84 GiB used, and 22.62 GiB available. The bounded command was:

```sh
ulimit -v 18874368
timeout 180s lake env lean -M12000 -j1 \
  Palomar/HegartyThreeEighths/Challenge.lean
```

Exit status: `0`. Exact relevant output:

```text
Palomar/HegartyThreeEighths/Challenge.lean:107:8: warning: declaration uses `sorry`
hegarty_three_eighths : ∀ (n : ℕ), 3 * (n + 1) ≤ 8 * a n
```

Immediately before compiling the missing repository target, `tool_atop` reported 23.46 GiB
total, 2.29 GiB used, and 21.17 GiB available. With `LEAN_PATH` pointing to the verified
read-only prerequisite cache, the bounded one-core command was:

```sh
mkdir -p /tmp/yah/subagent/hegarty-package-prover-c38627e/oleans/Enumerative
export LEAN_PATH=/home/exedev/p/proofs/.lake/build/lib/lean
ulimit -v 18874368
timeout 660s taskset -c 0 lake env lean -M12000 -j1 \
  Proofs/Enumerative/HegartyThreeEighths.lean \
  -o /tmp/yah/subagent/hegarty-package-prover-c38627e/oleans/Enumerative/HegartyThreeEighths.olean \
  -i /tmp/yah/subagent/hegarty-package-prover-c38627e/oleans/Enumerative/HegartyThreeEighths.ilean
```

Exit status: `0`. Exact selected output:

```text
'A094870.card_filter_range_mod_two_eq_le' depends on axioms: [propext, Classical.choice, Quot.sound]
hegarty_three_eighths : ∀ (n : ℕ), 3 * (n + 1) ≤ 8 * a n
'A094870.hegarty_three_eighths' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Immediately before the successful Solution check, `tool_atop` reported 23.46 GiB total,
3.81 GiB used, and 19.65 GiB available. After placing the exact verified prerequisite
artifact beside the newly compiled target in the private scratch import root, the command
was:

```sh
export LEAN_PATH=/tmp/yah/subagent/hegarty-package-prover-c38627e/oleans
ulimit -v 18874368
timeout 240s taskset -c 0 lake env lean -M12000 -j1 \
  Palomar/HegartyThreeEighths/Solution.lean
```

Exit status: `0`. The in-file fresh signature and axiom audit emitted exactly:

```text
hegarty_three_eighths : ∀ (n : ℕ), 3 * (n + 1) ≤ 8 * a n
'Palomar.HegartyThreeEighths.hegarty_three_eighths' depends on axioms: [propext, Classical.choice, Quot.sound]
```

A final source scan found no `sorry`, `native_decide`, `Lean.ofReduceBool`, custom `axiom`,
`implemented_by`, `extern`, or `csimp` in `Solution.lean`. The only `sorry` in the package
pair is the intentional Challenge theorem hole.

Complete retained logs are:

- `/tmp/yah/subagent/hegarty-package-prover-c38627e/logs/challenge-second.log`
- `/tmp/yah/subagent/hegarty-package-prover-c38627e/logs/source-target-build.log`
- `/tmp/yah/subagent/hegarty-package-prover-c38627e/logs/solution-second.log`

## Failed attempts retained

The first Challenge check exposed two ground-check tactic errors: the negative progression
example had not introduced the conjunction hypotheses, and the `a 0` checks had not
unfolded `pre 0`. These were corrected without changing any definition or theorem
statement; the successful full Challenge check is recorded above.

The first Solution invocation found the newly compiled target artifact but failed because a
`LEAN_PATH` package root is not merged module-by-module with the later root: it looked for
`Enumerative/HegartyPermutation.olean` beside the target. The exact already verified
prerequisite artifact was copied into that private scratch root, after which the unchanged
Solution passed. This was an import-layout issue, not a proof failure. No failed attempt was
counted as verification evidence.

## Comparator tooling blocker

**Comparator status: NOT RUN.** The configured Comparator was not invoked and this is not a
Comparator pass. Preflight found no `comparator`, `landrun`, `lean4export`, or `nanoda_bin`
executable in `PATH`. The locally present Comparator source declares
`leanprover/lean4:v4.34.0-rc1`, newer than this project's pinned `v4.33.0-rc1`, and its
executable is absent. Building verifier infrastructure or a second toolchain was prohibited,
so no futile execution or infrastructure build was attempted. `comparator.json` retains the
fully qualified theorem name, the three allowed axioms, and `enable_nanoda: true` for later
USER-controlled verification.

## Attribution, open conjecture, and review boundary

The selected result is Hegarty's published Theorem 3.3 (DOI 10.37236/1792), not new
mathematics. It is the **proved lower bound**, not Hegarty's open Conjecture 3.2 asserting
`a(n)/(n+1) -> 1`. The imported archive contains that conjecture as the separate intended
`sorry` declaration `A094870.conj_3_2`; the fresh selected-theorem axiom output above proves
that the wrapper does not depend on its `sorryAx`.

Repository notes report a corrected parity word in the published counting proof, but the
referenced extracted paper text is absent from this workspace. This package preserves that
attribution as inherited source commentary and does not upgrade it to independently
human-checked evidence. No broad literature sweep or additional review stage was performed.
All package preparation here was AI-assisted. Human formalization-author and responsible-
maintainer identities remain unknown and are left empty in `formalization.yaml`; USER review
is pending and is the only review gate.
