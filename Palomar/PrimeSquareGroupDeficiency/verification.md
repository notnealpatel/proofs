# Verification: prime-square group deficiency

## Current mechanical verification

[Authoritative campaign manifest](../Wave4ComparatorEvidence.yaml): **PASS** for every declaration selected by this package’s `comparator.json`. Earlier text below is historical and superseded. Human review remains **UNCHECKED**; this makes no claim of Palomar acceptance, submission, or publication.

## Final mechanical status

- **Challenge: PASS**, checked independently with only Mathlib on its import path.
  Its sole warning and sole proof hole are the selected theorem's intentional `sorry`.
- **Source prerequisite: PASS**, freshly compiled from the accepted source bytes into
  this workspace. An old main-tree `GroupPerfect.olean` was not used as evidence.
- **Solution and semantic bridge: PASS**, with no warnings or errors.
- **Selected axiom closure: PASS**, exactly `propext`, `Classical.choice`, and
  `Quot.sound`; neither the source result nor the bridge nor Solution uses `sorryAx`.
- **Independent model/header identity: PASS**, compared as exact strings, not just names.
- **JSON/YAML parsing and local consistency assertions: PASS**; full schema validation
  was not run.
- **Comparator / landrun / lean4export / nanoda: NOT RUN**; executables are absent.
- **USER review: PENDING**, and USER is the sole reviewer. No agent or parent review,
  submission, acceptance, novelty, or priority claim is made.

Only the six new files in this package are authored changes. No `Proofs/` source,
existing package, existing README, immutable reference, Formalize note, or root
configuration was changed during packaging. Generated logs and the freshly compiled
prerequisite are local ignored `.lake/` verification artifacts.

## Exact independent model and selected statement

Both files contain the same model from `set_option autoImplicit false` through the first
`end Palomar.PrimeSquareGroupDeficiency`, inclusive:

| Item | Bytes | SHA-256 |
| --- | ---: | --- |
| Common independent model | 3118 | `35616a824f184436bfecb7f8befbcd302f620a1f2282fc2a17c13dff34e459ac` |
| Challenge.lean | 4195 | `486abdc2daa93b3ecfadf03d08997d205d19fd18059cdc52e6985998d613961b` |
| Solution.lean | 5613 | `8253c98bbbce7c3ed809ed520339cab0d005339a16f81ea1c2206eeac74f19f3` |

The identical selected header, excluding ` := by` and the proof, is:

```lean
theorem groupDeficient_prime_sq {p : ℕ} (hp : p.Prime) : groupCount (p ^ 2) < p ^ 2
```

Header SHA-256: `109332147add9275a752aa0b9143de47045975f8aa7bc2bcc3b6676540f85932`.
The selected FQN is `Palomar.PrimeSquareGroupDeficiency.groupDeficient_prime_sq` in
both modules. Solution imports no Challenge, and the repeated definitions are not
replaced by source aliases.

The model has three substantive definitions:

1. `Isomorphic G H` for actual Mathlib `Group (Fin n)` structures requires a bijection
   preserving their multiplication tables. No arithmetic group instance on `Fin n`
   is substituted for either structure.
2. `groupIsoSetoid n` packages exactly that relation, with reflexivity, symmetry, and
   transitivity proved by the identity, inverse, and composite bijections.
3. `groupCount n := Nat.card (Quotient (groupIsoSetoid n))` counts the isomorphism
   classes. `finiteGroupStructures` injects structures into finite multiplication
   tables using `Group.ext`; `finite_isoClasses` proves the quotient finite for every
   `n`. Thus no infinite-cardinality default is involved.

`isomorphic_iff_nonempty_mulEquiv` checks the relation against Mathlib's standard notion.
The fully explicit diagnostic confirms the statement is equivalent to:

```lean
∀ {n : ℕ} (G H : Group (Fin n)),
  Isomorphic G H ↔ Nonempty (@MulEquiv (Fin n) (Fin n) G.toMul H.toMul)
```

All groups of order `n` can be numbered by `Fin n`, so the domain is unrestricted
finite groups of the given order, not a family assumed to satisfy the answer. The
prime guard is explicit and is proved at `2` and `3` in both files. Solution also
checks each guard jointly with the deficiency conclusion. `groupCount_zero` proves
zero's empty-group count directly; zero is excluded from the selected prime-square
domain, which has `p ≥ 2` and hence `p² ≥ 4`.

## Checked bridge and fresh signatures

The bridge uses `GroupCount.GroupStructure.equivGroup n`, the source equivalence from
explicit table structures to Mathlib group structures. Its inverse preserves and
reflects the isomorphism relation definitionally (`Iff.rfl`). `Quotient.congr` therefore
gives `Bridge.isoClassEquiv`. `Nat.card_congr`, together with the existing source lemma
`GroupCount.gnu_eq_natCard`, proves `Bridge.groupCount_eq_gnu` for **all natural `n`**,
not merely prime squares. There is no unproved semantic completeness assertion.

Fresh Solution `#check @...` output:

```text
@Isomorphic : {n : ℕ} → Group (Fin n) → Group (Fin n) → Prop
finite_isoClasses : ∀ (n : ℕ), Finite (Quotient (groupIsoSetoid n))
groupCount : ℕ → ℕ
Bridge.isoClassEquiv : (n : ℕ) → Quotient (groupIsoSetoid n) ≃ GroupCount.IsoClass n
Bridge.groupCount_eq_gnu : ∀ (n : ℕ), groupCount n = GroupCount.gnu n
@GroupCount.groupDeficient_prime_sq : ∀ {p : ℕ}, Nat.Prime p → GroupCount.GroupDeficient (p ^ 2)
@groupDeficient_prime_sq : ∀ {p : ℕ}, Nat.Prime p → groupCount (p ^ 2) < p ^ 2
```

The source predicate `GroupCount.GroupDeficient n` unfolds to `GroupCount.gnu n < n`.
The final two-line proof rewrites by the all-n bridge and applies the source theorem.
Its mathematics is the classical count `gnu(p²) = 2` and `2 < 4 ≤ p²`, not an open
uniqueness or density claim.

Fresh axiom output for the bridge and selected results:

```text
'Palomar.PrimeSquareGroupDeficiency.Bridge.isoClassEquiv' depends on axioms: [propext, Quot.sound]
'Palomar.PrimeSquareGroupDeficiency.Bridge.groupCount_eq_gnu' depends on axioms: [propext, Classical.choice, Quot.sound]
'GroupCount.groupDeficient_prime_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Palomar.PrimeSquareGroupDeficiency.groupDeficient_prime_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The definition `groupCount`, `groupCount_zero`, `finite_isoClasses`, and `prime_guards`
also report the three standard axioms. The isomorphism/MulEquiv agreement reports only
`Quot.sound`. The Challenge headline reports `sorryAx` in addition to the three standard
axioms, as expected for its single selected hole; that is not a Solution proof claim.
The package contains no sorry definitions. A source-token scan of Solution finds no
`sorry`, `native_decide`, `Lean.ofReduceBool`, custom `axiom`, `implemented_by`, `extern`,
or `csimp`.

## Pinned sources and cache provenance

- Accepted source revision: `55ab7d253f32b9632581cf31cc4951c2b2119533`.
- Packaging workspace revision at resumption: `1bd7b759777b1695ef96da0530191dbfad82c624`.
- Lean `4.33.0-rc1`, commit `62eed1db4d67327ec8120be05f1a1b0847d74561`,
  `x86_64-unknown-linux-gnu`, Release.
- Toolchain file: `leanprover/lean4:v4.33.0-rc1`.
- Mathlib manifest revision: `3edb3c0658f69f197b1e501b1f7623f3f7b3898c`.

The four GroupCount sources were byte-compared to the accepted revision. The current
sources of `Structures`, `Gnu`, `CdoIteration`, and `GroupPerfect` also match the read-only
main tree. Manifest, toolchain, and root Lake configuration match that tree. Package
sources and package caches are reached through the existing `.lake/packages` symlink.

| Input | SHA-256 |
| --- | --- |
| Structures.lean | `34a65a8c171a50e5c83c540dfb8705af3f4a3557c782cd26a197c46db2185115` |
| Gnu.lean | `7eda1977d94f06e84c6271dbb1998931602f97f28955eb586b2444b1dff8c90c` |
| CdoIteration.lean | `bac68c98e7f065a5db6225ae5694fee0e3e092fb1162e58f7518ff61f65bef95` |
| GroupPerfect.lean | `9b171b4525980cb95c9c5255ea86b703b59262db6e86d0b3c40c6ea18b7c653d` |
| lean-toolchain | `02f25adee7c1d6bf2e95b7b5b13f45b9892c7dd53ef470d5372ac60bda3df023` |
| lake-manifest.json | `948a91a6b3c52e0b640d0dadc1bf84cf967403244ac590c162c005c2544a439e` |
| Reused Structures.olean | `c5c17253109ce009ca594c3fc614f4c52b4055b26f8a80f5c22447fd3e24cc45` |
| Reused Gnu.olean | `c5de22d547421d287c25986b3f1e568f38e3af1fb4a106c986832a72320a4792` |
| Reused CdoIteration.olean | `39411ff2ef74c8dfecc8fed89987701daea672c4bcd2d1c117d008576be10ba5` |
| Fresh workspace GroupPerfect.olean | `756f758d5a8c0ea481a22190a0b8defc3643a060aaa62e63a72f71fb234552b5` |

`GroupPerfect.lean` was freshly compiled into the workspace even though an old target
cache existed in the main tree. Three workspace-local symlinks point to the verified
read-only prerequisite `.olean` files for `Structures`, `Gnu`, and `CdoIteration`.
Solution's project import root is this coherent local GroupCount directory, containing
the fresh target and those three links. No main-tree files were written, no dependency
or toolchain was upgraded, and no whole-repository build or cache reconstruction ran.

## Bounded commands and results

All commands ran from the assigned workspace. Every Lean call was preceded immediately
by `tool_atop` to check physical memory headroom; no virtual-address-space ulimit was
imposed. Calls used one core, `-j1`, `-M8192`, and a 120-second timeout. The command
prefix defining package paths was expanded as follows:

```sh
PKG_PATH="$(printf '%s:' /home/exedev/p/proofs/.lake/packages/*/.lake/build/lib/lean)"
```

Each command below re-establishes that shell variable when run in a separate shell.
No Challenge or Solution cached target was imported as a substitute for checking its
source file.

### Challenge, separate Mathlib-only check

```sh
LEAN_PATH="$PKG_PATH" timeout 120 /usr/bin/time \
  -f 'ELAPSED=%e MAX_RSS_KB=%M EXIT=%x' taskset -c 0 lean -j1 -M8192 \
  Palomar/PrimeSquareGroupDeficiency/Challenge.lean
```

Available memory: **21.77 GB**. Result: **exit 0**, **1.15 seconds**,
maximum RSS **1,734,616 KiB**. The sole warning points to line 84, the selected theorem.
The selected signature and its expected Challenge-hole axiom output were printed.

### Fresh source target, without editing the source

```sh
LEAN_PATH="${PKG_PATH}/home/exedev/p/proofs/.lake/build/lib/lean" \
  timeout 120 /usr/bin/time -f 'ELAPSED=%e MAX_RSS_KB=%M EXIT=%x' \
  taskset -c 0 lean -j1 -M8192 Proofs/GroupCount/GroupPerfect.lean \
  -o .lake/build/lib/lean/GroupCount/GroupPerfect.olean
```

Available memory: **22.44 GB**. Result: **exit 0**, **4.24 seconds**,
maximum RSS **6,717,340 KiB**. The only warnings were the original archived open
conjectures at lines 298 and 333. The selected source result and `gnu_prime_sq` each
reported only `[propext, Classical.choice, Quot.sound]`. The original sorries remain
unchanged and are not dependencies of the selected theorem.

### Solution, separate check with fresh source target

```sh
LEAN_PATH="$PWD/.lake/build/lib/lean:$PKG_PATH" timeout 120 /usr/bin/time \
  -f 'ELAPSED=%e MAX_RSS_KB=%M EXIT=%x' taskset -c 0 lean -j1 -M8192 \
  Palomar/PrimeSquareGroupDeficiency/Solution.lean
```

Available memory: **22.47 GB**. Result: **exit 0**, **4.00 seconds**,
maximum RSS **6,672,900 KiB**, with no warnings or errors. The printed signatures and
axioms above are from this fresh check.

Retained local logs under `.lake/proof-audit/prime-square-package/`:

- `challenge-1.log` — initial failed elaboration, described below;
- `challenge-final.log` — final successful independent Challenge check;
- `source-fresh.log` — freshly compiled source target and source axiom audit;
- `solution-final.log` — successful Solution and bridge checks.

The first Challenge attempt failed in the auxiliary isomorphism/MulEquiv agreement:
structure-update notation and implicit projections selected `Fin.instMul` instead of
`G.toMul`. The correction supplies every multiplication argument explicitly to
`@MulEquiv.mk`, `@MulEquiv.toEquiv`, and `@MulEquiv.map_mul'`. This preserves the
intended statement and prevents the ambient-arithmetic ambiguity. Only the corrected
successful check counts as evidence; the failed attempt was not counted as a pass.

## Metadata and independent-verifier boundary

`command -v` preflight found none of `comparator`, `landrun`, `lean4export`, `nanoda`,
or `nanoda_bin` in PATH. They were not installed or built. **Comparator and nanoda
were NOT RUN**, and no independent-kernel/comparison success is claimed.
`comparator.json` nevertheless selects the identical FQN, allows only `propext`,
`Classical.choice`, `Quot.sound`, and retains `enable_nanoda: true` for later checking.

Python's JSON parser and PyYAML 6.0.1 parsed the package metadata; local assertions
checked v0.4, module paths, the selected name, the exact axiom allowlist, the enabled
nanoda flag, one Challenge hole, zero Solution holes, empty human-author/maintainer
and reviewer lists, and the unchecked review status. These are syntax/consistency
checks, **not full schema validation**. Empty human metadata and pending USER review
remain blockers. The README and YAML disclose material AI assistance, gpt-6-astra
with xhigh for the latest implementation/package, unknown prior infrastructure models,
and classical rather than novel mathematics.
