# Verification record: mean-divisor subset parity

## Mechanical status

- **Challenge compilation:** **PASS**. It was compiled separately; the only
  warnings are the three intentional selected-theorem holes.
- **Solution compilation:** **PASS**. It does not import the Challenge.
- **Literal-definition bridge:** **PASS**. The Solution proves equality with the
  repository count before applying any repository theorem.
- **Selected signatures:** **PASS**. Fresh `#check` output agrees between
  Challenge and Solution for all three selected declarations.
- **Selected theorem axiom audit:** **PASS**. Each fresh `#print axioms` closure
  is exactly `propext`, `Classical.choice`, and `Quot.sound`; none contains
  `sorryAx`, `Lean.ofReduceBool`, or a custom axiom.
- **Comparator:** **NOT RUN — REQUIRED TOOLING MISSING**. This is not a
  Comparator pass.
- **Human review:** **PENDING**. USER is the sole review gate. No human approval,
  submission, publication, or acceptance is claimed.

## Statement and definition alignment

`Challenge.lean` imports only `Mathlib.NumberTheory.Divisors` and
`Mathlib.Data.Nat.ModEq`. It independently defines

```lean
def IsMeanDiv (n : ℕ) (S : Finset ℕ) : Prop :=
  ∃ m, S.sum id = m * S.card ∧ m ∣ n

def meanDivSubsets (n : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 n).powerset.filter fun S => S.Nonempty ∧ IsMeanDiv n S

def a (n : ℕ) : ℕ := (meanDivSubsets n).card
```

Thus the counted objects are literally nonempty subsets of `{1, ..., n}`. They
are **not** subsets of `n.divisors`: only their integer mean `m` must divide
`n`. The multiplicative mean equation avoids totalized natural-number division.
The Challenge's finite decision procedure bounds the existential mean witness;
no result is encoded in the definition.

The Solution repeats these definitions and statements without importing the
Challenge. It imports `Enumerative.MeanDivisors` and proves
`meanDivSubsets_eq_source` using `Finset.filter_congr`; the predicate comparison
is reflexive after unfolding the two `IsMeanDiv` definitions. It derives
`a_eq_source`, then transports the three already-proved repository theorems.
This explicit bridge is needed because the two finite filters carry separately
constructed decidability instances and are not definitionally identical as
`Finset` values merely by unfolding.

Ground checks cover the predicate (`IsMeanDiv 4 {1, 3}`), the separate zero
convention `a 0 = 0`, the first value, `a 4 = 5`, the complete five-element
family at `n = 4`, a parity instance at `n = 6`, the square instance at `n = 4`,
and the prime instance at `n = 5`. In particular, the square theorem retains
the material hypothesis `n ≠ 0`; it does not silently absorb the `a 0 = 0`
convention.

The selected declarations are:

```text
Palomar.MeanDivisorParity.a_modEq_card_divisors
Palomar.MeanDivisorParity.odd_a_iff_isSquare
Palomar.MeanDivisorParity.a_eq_two_iff_prime
```

The first two are the mandatory parity/square pair. The third is the focused,
already-existing prime characterization.

## Attribution and source relation

The mathematical proof in `Proofs/Enumerative/MeanDivisors.lean` partitions the
counted subsets by their unique mean. For each permitted mean `m`, toggling the
element `m` pairs the mean-`m` subsets except for the singleton `{m}`, leaving
an odd contribution. Summing over divisor means gives the divisor-count parity,
and the source proves the divisor-count square criterion from the prime
factorization formula.

The toggle is attributed to the Putnam 2002 A3 solution (Kedlaya–Ng), where it
is used for all integer means. This development is a divisor-restricted
adaptation. The package makes no novel-involution, first-proof, or priority
claim. No broad literature survey was performed.

## Toolchain, revision, and exact cache provenance

- Assigned campaign base: `ee0cb27655f6bb6c37e8647c79184745017c5b24`.
- Working-copy revision after the four initial package artifacts were written:
  `5a2ed780` (the final harness revision may change when this record is added).
- Lean: `4.33.0-rc1`, commit
  `62eed1db4d67327ec8120be05f1a1b0847d74561`,
  `x86_64-unknown-linux-gnu`, Release build.
- Lake: `5.0.0-src+62eed1d` (Lean `4.33.0-rc1`).
- Mathlib manifest revision:
  `3edb3c0658f69f197b1e501b1f7623f3f7b3898c`.
- Comparator configuration:
  `Palomar/MeanDivisorParity/comparator.json`.

The existing source has numerous ground computations and a repository-recorded
historical timeout. It was not needlessly recompiled. The authorized read-only
artifact
`/home/exedev/p/proofs/.lake/build/lib/lean/Enumerative/MeanDivisors.olean` was
used only after byte-for-byte comparisons established exact matches for the
source, complete manifest, and toolchain:

| Input | SHA-256 | External comparison |
|---|---|---|
| `Proofs/Enumerative/MeanDivisors.lean` | `0c06f111c8e950faa29d4cbfd40967b9326248fa2193a20d2968deda4035507a` | exact match |
| `lake-manifest.json` | `948a91a6b3c52e0b640d0dadc1bf84cf967403244ac590c162c005c2544a439e` | exact match |
| `lean-toolchain` | `02f25adee7c1d6bf2e95b7b5b13f45b9892c7dd53ef470d5372ac60bda3df023` | exact match |
| reused `MeanDivisors.olean` | `98e519f78ca5ae4975cd0c8512675b4e572ede3547e8d964bf7edc1e0f902921` | authorized read-only cache |

Final source and fresh output hashes are:

| Artifact | SHA-256 |
|---|---|
| `Challenge.lean` | `dd8ddf0a5d4168c1c8931ae27879b0b43ca2506c3dea8d8caaed18a705bfa3b9` |
| `Solution.lean` | `d2a9891346eb580aa598d91aa593dc6de75b174e5c6a6ec87eee382e53ddf08d` |
| `comparator.json` | `0e1d181e82d7078c1b306b636581cbcf204410d5732733f6f7f73b16dc3a7ffd` |
| `formalization.yaml` | `74bea4682d206898e2a32e4650174105337b4f44ce289a172a9ab97c053a9042` |
| fresh private `Challenge.olean` | `25a217f74f404e49a529ddfcf291adc16540e5781cd8353b4dfe2e11516fab5f` |
| fresh private `Solution.olean` | `e7859cc132780e9831541707cf23390255c280740516a96f592c7d7a97f9e0c1` |

No root configuration, `Proofs/`, `References/`, unrelated candidate, or README
file was changed.

## Separate Challenge compilation

Immediately before the final command, `tool_atop` reported 8 cores, 23.46 GiB
total memory, 0.93 GiB used, and 22.53 GiB available. The one-core bounded
command was:

```sh
ulimit -v 22544384
timeout 240s taskset -c 0 lake env lean -M 9000 -j 1 \
  -o /tmp/yah/subagent/mean-divisor-package-prover-e0f9b18/Challenge.olean \
  Palomar/MeanDivisorParity/Challenge.lean
```

Exit status: `0`. Exact output:

```text
Palomar/MeanDivisorParity/Challenge.lean:60:8: warning: declaration uses `sorry`
Palomar/MeanDivisorParity/Challenge.lean:64:8: warning: declaration uses `sorry`
Palomar/MeanDivisorParity/Challenge.lean:68:8: warning: declaration uses `sorry`
a_modEq_card_divisors : ∀ (n : ℕ), a n ≡ #n.divisors [MOD 2]
@odd_a_iff_isSquare : ∀ {n : ℕ}, n ≠ 0 → (Odd (a n) ↔ IsSquare n)
a_eq_two_iff_prime : ∀ (n : ℕ), a n = 2 ↔ Nat.Prime n
```

Retained log:
`/tmp/yah/subagent/mean-divisor-package-prover-e0f9b18/logs/challenge-final.log`.
The three and only three `sorry` occurrences in the package Lean files are
these intentional Challenge theorem holes.

## Separate Solution compilation and axiom audit

Immediately before the final command, `tool_atop` reported 8 cores, 23.46 GiB
total memory, 0.92 GiB used, and 22.54 GiB available. The source-verified cache
was prepended to the coherent Lake package roots:

```sh
export LEAN_PATH="/home/exedev/p/proofs/.lake/build/lib/lean:$(lake env printenv LEAN_PATH)"
ulimit -v 22544384
timeout 300s taskset -c 0 lean -M 9000 -j 1 \
  -o /tmp/yah/subagent/mean-divisor-package-prover-e0f9b18/Solution.olean \
  Palomar/MeanDivisorParity/Solution.lean
```

Exit status: `0`. Exact output:

```text
a_modEq_card_divisors : ∀ (n : ℕ), a n ≡ #n.divisors [MOD 2]
@odd_a_iff_isSquare : ∀ {n : ℕ}, n ≠ 0 → (Odd (a n) ↔ IsSquare n)
a_eq_two_iff_prime : ∀ (n : ℕ), a n = 2 ↔ Nat.Prime n
'Palomar.MeanDivisorParity.a_modEq_card_divisors' depends on axioms: [propext, Classical.choice, Quot.sound]
'Palomar.MeanDivisorParity.odd_a_iff_isSquare' depends on axioms: [propext, Classical.choice, Quot.sound]
'Palomar.MeanDivisorParity.a_eq_two_iff_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Retained log:
`/tmp/yah/subagent/mean-divisor-package-prover-e0f9b18/logs/solution-final.log`.
A final source scan found no `sorry`, `native_decide`, `Lean.ofReduceBool`,
custom `axiom`, `implemented_by`, `extern`, or `csimp` in `Solution.lean`.

## Bounded failed attempts

No failed attempt was counted as verification evidence.

1. The first Challenge compilation used only
   `Mathlib.NumberTheory.Divisors`. It exited `1`: the `[MOD 2]` parser was not
   imported, the resulting missing theorem made its `#check` fail, and the
   ground prime check used unavailable `norm_num`. The method was changed by
   adding the narrow `Mathlib.Data.Nat.ModEq` import and using kernel `decide`
   for the concrete prime. Retained log:
   `/tmp/yah/subagent/mean-divisor-package-prover-e0f9b18/logs/challenge.log`.
2. The first Solution bridge attempted to close the source results using only
   `simpa` after unfolding. It exited `1` with visually identical expected and
   actual finite-filter types: the separately generated decidability instances
   prevented definitional equality, and the unfinished wrapper declarations
   consequently displayed `sorryAx`. Retained log:
   `/tmp/yah/subagent/mean-divisor-package-prover-e0f9b18/logs/solution.log`.
   The method was changed to an explicit `Finset.filter_congr` proof followed by
   `a_eq_source`; the final compilation and fresh audits then passed with no
   `sorryAx`.
3. An intermediate attempt added `classical` to the failed extensional `simp`
   proof, but the same finite-filter goal remained. It was not repeated; the
   proof method was changed to `Finset.filter_congr`.

No full repository build, source-cache reconstruction, dependency update,
toolchain upgrade, verifier installation, or parallel Lake fan-out was run.

## Comparator tooling blocker

**Comparator status: NOT RUN.** A non-executing preflight found:

```text
comparator: MISSING
landrun: MISSING
lean4export: MISSING
nanoda_bin: MISSING
local comparator toolchain: leanprover/lean4:v4.34.0-rc1
local comparator executable: MISSING
project toolchain: leanprover/lean4:v4.33.0-rc1
```

The locally available Comparator source targets a newer Lean release than the
project, and none of the required verifier executables is installed. In
accordance with the task constraints, no invocation, infrastructure install,
or second-toolchain setup was attempted. `comparator.json` retains fully
qualified theorem names, the three permitted axioms, and
`"enable_nanoda": true` for later USER-controlled verification.

## Metadata and review blockers

All package construction and checks recorded here were AI-assisted. No prover
subagents, agent reviewers, or parent mathematical review were used. The
identities of the human formalization author and responsible human maintainer
were not authoritatively available, so `formalization.yaml` leaves both
required lists empty and records this as a submission blocker rather than
inventing identities. USER mathematical, attribution, and source-fidelity
review remains pending and is the sole review gate.
