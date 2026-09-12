# Verification record: Noe odd-Zumkeller forward obstruction

## Current mechanical verification

[Authoritative campaign manifest](../Wave4ComparatorEvidence.yaml): **PASS** for every declaration selected by this package’s `comparator.json`. Earlier text below is historical and superseded. Human review remains **UNCHECKED**; this makes no claim of Palomar acceptance, submission, or publication.

## Mechanical status

- **Challenge elaboration:** **PASS**. Its sole warning is the intentional selected-theorem hole.
- **Solution direct compilation:** **PASS**, independently of Challenge and without importing it.
- **Selected signature:** **PASS**. Challenge and Solution print the same fully quantified type.
- **Selected theorem axiom audit:** **PASS**. The Solution theorem depends exactly on `propext`, `Classical.choice`, and `Quot.sound`; its closure contains no `sorryAx`, `Lean.ofReduceBool`, or custom axiom. Neither package file uses `native_decide`.
- **Comparator:** **NOT RUN — REQUIRED TOOLING MISSING**. This is not a Comparator pass.
- **Human review:** **PENDING**. USER is the sole review gate. No submission, acceptance, publication, or approval is claimed.

## Revisions, tools, and dependency pins

- Assigned campaign base: `ee0cb27655f6bb6c37e8647c79184745017c5b24`.
- Working-copy revision observed during packaging: `4fd0eb12a161e6c8cdf01452f9e96a74fa3aade3` (the mutable jj workspace later reported parent `ee0cb276`; the harness owns final snapshotting).
- Lean: `4.33.0-rc1`, commit `62eed1db4d67327ec8120be05f1a1b0847d74561`, `x86_64-unknown-linux-gnu`, Release build.
- Lake: `5.0.0-src+62eed1d` (Lean `4.33.0-rc1`).
- Mathlib manifest revision: `3edb3c0658f69f197b1e501b1f7623f3f7b3898c`.
- Project `lean-toolchain` SHA-256: `02f25adee7c1d6bf2e95b7b5b13f45b9892c7dd53ef470d5372ac60bda3df023`.
- Project `lake-manifest.json` SHA-256: `948a91a6b3c52e0b640d0dadc1bf84cf967403244ac590c162c005c2544a439e`.
- Comparator configuration: `Palomar/NoeOddZumkeller/comparator.json`.

The selected declaration has the following exact type in both modules:

```text
Palomar.NoeOddZumkeller.noeOddZumkellerForward_iff_not_exists_odd_perfect :
  (∀ (n : ℕ), Odd n → IsZumkeller n → IsA174865 n) ↔
    ¬∃ n, Odd n ∧ n.Perfect
```

The left side retains the universal logical modality and the right side retains negated existence. `IsA174865 n` unfolds to oddness, strict `2 * n < σ(n)`, and even `σ(n)`. It is not weakened to `≤`.

## Independent declaration surfaces

`Challenge.lean` imports only:

```lean
Mathlib.NumberTheory.Divisors
```

It does not import any project module. Challenge and Solution independently repeat these declarations in `Palomar.NoeOddZumkeller`:

- `IsZumkeller n`: `0 < n` together with a literal finite subset of `n.divisors` whose sum equals the sum of its complement;
- `IsAbundant n`: the strict divisor-sum inequality `2 * n < σ(n)`;
- `IsA174865 n`: `Odd n ∧ IsAbundant n ∧ Even σ(n)`;
- decidability instances for all three predicates;
- the selected universal-forward/odd-perfect equivalence.

The theorem type itself displays both open propositions literally rather than hiding either one behind an opaque conjecture parameter. The Solution does not import Challenge. Its `isZumkeller_iff_source` is `Iff.rfl`; its `isA174865_iff_source` uses the repository's proved divisor-sum characterization and `even_iff_two_dvd`. The proof then transports the already proved repository theorem in both directions.

Ground checks cover `0`, Zumkeller `6`, abundant `12`, non-abundant perfect `6`, and A174865 member `945`. A separate example jointly establishes that `945` is odd, Zumkeller, and in A174865. Another establishes the strict boundary: `6` is perfect and Zumkeller with even divisor sum but is not abundant. Thus neither positivity nor the `<` versus `≤` distinction is hidden by vacuity.

## Challenge elaboration

Immediately before the successful check, `tool_atop` reported 8 cores, 23.46 GiB total memory, 1.51 GiB used, and 21.96 GiB available. Because one core was already saturated by concurrent work, the final process was restricted to core 1:

```sh
ulimit -v 22544384
timeout 240s taskset -c 1 lake env lean -M 7000 -j 1 \
  -o /tmp/yah/subagent/noe-zumkeller-package-prover-f13a49f/Challenge.olean \
  Palomar/NoeOddZumkeller/Challenge.lean
```

Exit status: `0`. Exact output:

```text
Palomar/NoeOddZumkeller/Challenge.lean:61:8: warning: declaration uses `sorry`
noeOddZumkellerForward_iff_not_exists_odd_perfect : (∀ (n : ℕ), Odd n → IsZumkeller n → IsA174865 n) ↔
  ¬∃ n, Odd n ∧ n.Perfect
```

Retained log:
`/tmp/yah/subagent/noe-zumkeller-package-prover-f13a49f/logs/challenge-final.log`.
Its SHA-256 is `d8f6a29fe03caeb89163c25b5fe1a5dd04e0a1c4d2094649c37fa4fc21dd57ca`.
The fresh Challenge olean SHA-256 is `d7fda96a119b4253faf76ae080d08cf64bac13d276a6b95fdd47390ebd37eb17`.

## Exact-source cache provenance

The user authorized read-only reuse of `/home/exedev/p/proofs/.lake/build/lib/lean`. Before reuse, `cmp -s` returned status `0` for each workspace/reference pair below:

| Input | SHA-256 in both trees |
|---|---|
| `lean-toolchain` | `02f25adee7c1d6bf2e95b7b5b13f45b9892c7dd53ef470d5372ac60bda3df023` |
| `lake-manifest.json` | `948a91a6b3c52e0b640d0dadc1bf84cf967403244ac590c162c005c2544a439e` |
| `Proofs/Enumerative/NoeZumkellerOdd.lean` | `4becd8e751e5dc58413b1141149efbae267560e0b52071d10ae524f919ce31ab` |
| `Proofs/Enumerative/IsZumkeller.lean` | `8c05eac90219cf366fa042da13852f82c59363661bad7fed00ec6e270be93909` |

The reused read-only oleans were:

```text
Enumerative.NoeZumkellerOdd.olean  5ac1f25e946df212367f5dccf05a643d771b37c9b0d1a7e14b5e948133896c92
Enumerative.IsZumkeller.olean       413b2f9c3051aa908a8916e8ead515b1372ca64ed608579e74628dbdf6b6561f
```

The external path was prepended to the coherent `lake env printenv LEAN_PATH`; no cache was copied or reconstructed. No whole-project build, dependency update, project configuration change, or toolchain installation was performed.

## Solution compilation and fresh axiom audit

Immediately before the final successful compilation, `tool_atop` reported 8 cores, 23.46 GiB total memory, 0.83 GiB used, and 22.63 GiB available. The command was:

```sh
BASE_PATH="$(lake env printenv LEAN_PATH)"
export LEAN_PATH="/home/exedev/p/proofs/.lake/build/lib/lean:$BASE_PATH"
ulimit -v 22544384
timeout 300s taskset -c 1 lean -M 9000 -j 1 \
  -o /tmp/yah/subagent/noe-zumkeller-package-prover-f13a49f/Solution.olean \
  Palomar/NoeOddZumkeller/Solution.lean
```

Exit status: `0`. Exact output:

```text
noeOddZumkellerForward_iff_not_exists_odd_perfect : (∀ (n : ℕ), Odd n → IsZumkeller n → IsA174865 n) ↔
  ¬∃ n, Odd n ∧ n.Perfect
'Palomar.NoeOddZumkeller.noeOddZumkellerForward_iff_not_exists_odd_perfect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

This output comes from the final Solution's own `#check` and `#print axioms`, not from a copied source report. Exit success establishes that every declaration and ground example elaborated and the generated proof passed kernel checking. Retained log:
`/tmp/yah/subagent/noe-zumkeller-package-prover-f13a49f/logs/solution-final.log`.
Its SHA-256 is `cad06eb3a6450938068098bfba56485d1f7059bf4a3d47264826e65d4a98e063`.
The fresh Solution olean SHA-256 is `698677d3333fc4bdfe954a5267a3e5d13a4f2d4b6dfb4aa33abd78c20a813f80`.

A source scan found exactly one `sorry` token across the two Lean files, at the intentional Challenge theorem body. Solution contains no `sorry`, `native_decide`, `Lean.ofReduceBool`, or `axiom` declaration.

## Earlier bounded failures and method changes

No failed attempt was treated as theorem evidence.

1. The first narrow-import Challenge attempt lacked explicit decidability instances and also used the unavailable `norm_num` tactic. It exited `1`. The final source adds transparent finite decidability instances and uses kernel `decide`; retained log: `/tmp/yah/subagent/noe-zumkeller-package-prover-f13a49f/logs/challenge.log`.
2. A later Challenge attempt reached the explicit `945` witness but exceeded the default recursion/heartbeat bounds. The final check scopes larger elaboration bounds only around that concrete finite ground check and then passed. This did not change any definition or theorem statement.
3. The first Solution compile proved and printed the selected theorem but exited `1` because independently recomputing the large `945` ground witness caused kernel excessive-memory detection. The final Solution instead transports the repository's already kernel-checked `isZumkeller_945` and `isA174865_945` facts through the proved predicate bridges. The selected proof and statement were not weakened. Retained failed log: `/tmp/yah/subagent/noe-zumkeller-package-prover-f13a49f/logs/solution.log`.

## Comparator tooling blocker

**Status: NOT RUN.** No Comparator, lean4export, or NanoDA result is claimed.

A non-executing preflight found:

```text
comparator: MISSING
landrun: MISSING
lean4export: MISSING
nanoda_bin: MISSING
local comparator executable: MISSING
local comparator source lean-toolchain: leanprover/lean4:v4.34.0-rc1
project lean-toolchain: leanprover/lean4:v4.33.0-rc1
```

The only available Comparator source targets a newer Lean release, and neither it nor its required verifier executables is built or installed. Per the task constraints, no incompatible invocation, verifier installation, cache reconstruction, or second-toolchain setup was attempted. `comparator.json` retains `enable_nanoda: true` and the three permitted axioms rather than weakening verification to bypass missing tools.

## Scope and review boundary

The package proves an equivalence/obstruction only. It does **not** prove Noe's full odd-Zumkeller biconditional, the converse from A174865 membership to Zumkeller membership, any general abundance-to-Zumkeller result, or the nonexistence of odd perfect numbers. It includes no unrelated Neder result. The finite OEIS observations are not used as a universal proof and no novelty claim is made.

All package construction and mechanical verification recorded here was AI-assisted. No subagents or agent reviewers were used. No authoritative human formalization author or responsible maintainer was established, so `formalization.yaml` leaves those required human fields empty and records them as blockers. USER review remains pending and is not replaced by these mechanical checks.
