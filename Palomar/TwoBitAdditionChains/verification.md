# Verification — two-bit addition-chain doubling

## Current mechanical verification

[Authoritative campaign manifest](../Wave4ComparatorEvidence.yaml): **PASS** for every declaration selected by this package’s `comparator.json`. Earlier text below is historical and superseded. Human review remains **UNCHECKED**; this makes no claim of Palomar acceptance, submission, or publication.

Verification date: **2026-09-07**. This report concerns exactly the six new
files in `Palomar/TwoBitAdditionChains/`, not other packages.

## Current status

| Check | Result |
| --- | --- |
| Fresh standalone Challenge elaboration | **PASS**, one intentional selected-theorem hole |
| Fresh standalone Solution elaboration | **PASS**, no warnings or errors |
| Independent/source chain and minimum bridge | **PASS**, kernel-checked |
| Selected Solution axiom closure | **PASS**, exactly the three permitted axioms |
| Model blocks and selected theorem headers | **BYTE-IDENTICAL** between files |
| Fully qualified elaborated theorem-type output | **IDENTICAL** between files |
| JSON and YAML syntax parsing | **PASS** |
| Exact six-file scope; preexisting-file preservation | **PASS** |
| Comparator / export / Nanoda | **NOT RUN**, executables unavailable |
| USER review | **PENDING**, sole review gate |

The selected theorem is
`Palomar.TwoBitAdditionChains.l_two_mul_eq_add_one_of_binaryWeight_le_two`.
No unrestricted Slizkov or Knuth–Stolarsky conjecture is selected or proved.
Mechanical checks here are not a mathematical-novelty, human-review,
submission, or acceptance claim.

## Faithful model and bridge

Challenge imports only `Mathlib`; Solution imports
`NumberComplexity.SlizkovDoubling`, not Challenge. The shared model is independently
written in each file, with these visible definitions:

1. `IsAddChain [1]` is the initial chain. Every extension is `(a+b)::c`, where
   `a` and `b` already occur in `c` and `c` is itself a chain.
2. `chainSteps c = c.tail.length` counts additions.
3. `AdditionChain n` is the subtype of chains with head `n`.
4. `l n` is the natural infimum of these actual lengths.
5. `binaryWeight n = n.bitIndices.length` is Mathlib's binary-ones count.

The common code proves positivity of chain values, chain existence for each
positive target, an upper bound from every actual chain, and attainment of the
minimum. Thus the infimum is neither over an invented predicate nor empty on
the intended domain. It also proves the absence of a chain for zero and checks
`l 0 = 0`, the totalized empty-infimum value, separately from the honest
`l 1 = 0`. The selected statement explicitly retains `0 < k`.

Ground checks include `[1]`, `[2,1]`, `[3,2,1]`, rejection of the empty list,
chain-length counts, binary weights at `0,1,9,7`, and jointly satisfiable
guards at `k = 1` and `k = 9`. The latter has two separated binary ones.

The Solution does not claim definitional equality of separately declared
inductive types. Its private `isAddChain_iff_source` proves both directions
by induction. Its private `l_eq_source` proves that the sets of attainable
lengths coincide by translating each chain witness without changing its list
or length. Equality of the infima follows, including their common value at
zero. Only then does the final proof apply
`NumberComplexity.l_two_mul_eq_add_one_of_binaryWeight_le_two`.

The source convention allows repeated and non-increasing values. Its
`NumberComplexity.l_eq_lAsc` connects the minimum with the usual strictly
ascending convention. No shear or circuit surrogate, arbitrary supplied
function, or global lower-bound hypothesis appears in the challenge.

## Exact statement and axiom output

Both files contain this identical theorem header:

```lean
theorem l_two_mul_eq_add_one_of_binaryWeight_le_two {k : ℕ} (hk : 0 < k)
    (hv : binaryWeight k ≤ 2) : l (2 * k) = l k + 1
```

Both final runs used `set_option pp.fullNames true in #check @...`, producing
identical output that identifies the package's own model:

```text
@Palomar.TwoBitAdditionChains.l_two_mul_eq_add_one_of_binaryWeight_le_two : ∀ {k : ℕ},
  0 < k →
    Palomar.TwoBitAdditionChains.binaryWeight k ≤ 2 →
      Palomar.TwoBitAdditionChains.l (2 * k) = Palomar.TwoBitAdditionChains.l k + 1
```

The Solution printed:

```text
'Palomar.TwoBitAdditionChains.l_two_mul_eq_add_one_of_binaryWeight_le_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.Palomar.TwoBitAdditionChains.Solution.0.Palomar.TwoBitAdditionChains.isAddChain_iff_source' does not depend on any axioms
'_private.Palomar.TwoBitAdditionChains.Solution.0.Palomar.TwoBitAdditionChains.l_eq_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NumberComplexity.l_two_mul_eq_add_one_of_binaryWeight_le_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Challenge's selected theorem intentionally reports
`[propext, sorryAx, Classical.choice, Quot.sound]`; it is the package's only
hole. There are no incomplete definitions. Solution has no `sorry`,
`native_decide`, `Lean.ofReduceBool`, custom axiom, `implemented_by`, `extern`,
or `csimp`. The imports contain the two separate archived open conjectures,
but the selected Solution closure above contains neither dependency.

## Fresh separate commands

Each command ran from the assigned workspace with no whole-repository build,
no heavy fan-out, and no package-file cross-import:

```sh
timeout 120 /usr/bin/time -v lake env lean -j1 -M12288 \
  Palomar/TwoBitAdditionChains/Challenge.lean

timeout 120 /usr/bin/time -v lake env lean -j1 -M12288 \
  Palomar/TwoBitAdditionChains/Solution.lean
```

Both returned **exit status 0**. The final Challenge run took **4.68 s** with
maximum RSS **6,676,988 KiB**. Its only warning was the intentional hole at
line 139. The final Solution run took **4.91 s** with maximum RSS
**6,680,524 KiB**, without warnings. These were fresh elaborations of the
final Lean source, not checks inferred from cached package artifacts.

`tool_atop` was called immediately before each expensive invocation, as
required for the shared host. The final two calls reported **22.45 GiB** and
**22.49 GiB** physically available, respectively, on a **23.46 GiB**, eight-core
host. No low virtual-address-space limit was imposed. No concurrent heavy jobs
were launched by this packager.

Local diagnostic logs remain outside the six-file package in the ignored
workspace cache:

- `.lake/two-bit-package/challenge-fullnames.log`
- `.lake/two-bit-package/solution-fullnames.log`

The exact relevant outputs are reproduced above so package readers do not
need those ephemeral paths.

## Toolchain and source/cache provenance

- Lean: `4.33.0-rc1`, commit
  `62eed1db4d67327ec8120be05f1a1b0847d74561`.
- `lean-toolchain`: `leanprover/lean4:v4.33.0-rc1`.
- Mathlib manifest revision:
  `3edb3c0658f69f197b1e501b1f7623f3f7b3898c`.
- Accepted source-result revision:
  `55ab7d253f32b9632581cf31cc4951c2b2119533`.

Exact comparisons matched all four prerequisite `.lean` sources and the
manifest, toolchain, and root configuration against `/home/exedev/p/proofs`.
Read-only `jj --ignore-working-copy file show -r 55ab7d...` also gave the
same hashes for all four prerequisite sources. The assigned packaging
workspace has unrelated historical differences from that accepted revision;
none was modified or included in this package.

| Input | SHA-256 |
| --- | --- |
| `lean-toolchain` | `02f25adee7c1d6bf2e95b7b5b13f45b9892c7dd53ef470d5372ac60bda3df023` |
| `lake-manifest.json` | `948a91a6b3c52e0b640d0dadc1bf84cf967403244ac590c162c005c2544a439e` |
| `lakefile.toml` | `5fea1b2cc353a49df4d727bd77e43a01c074130fcb099610fe0320d8d7a1906f` |
| `AdditionChain.lean` | `e54e801ec8e141daef8dab13f241fe12e8374c6d9ea1722894da253bdbacdea0` |
| `KnuthStolarsky.lean` | `594f05857e33bed617a49aed8885f790c1732e94c0cd9159b51ae185c1be1844` |
| `TwoBitAdditionChain.lean` | `c7acd2e19fca0b1197ba2f18696ac2cafb9beb34ed5fbeaed675b7c2d5c24c63` |
| `SlizkovDoubling.lean` | `d9cfe5af2f9af84ee1b1a8832a5c7339240de12d80166f33c5372e879eed2390` |

Source paths in the last four rows are under `Proofs/NumberComplexity/`.

The private `NumberComplexity` cache contains a coherent four-module import
set. `AdditionChain.olean` and `KnuthStolarsky.olean` are read-only links to
verified main-cache prerequisites. `TwoBitAdditionChain.olean` and
`SlizkovDoubling.olean` are regular local files freshly built during the
preceding proof phase from the exact unchanged source hashes above. Their
source-result audits were repeated through the Solution import. The main
cache's helper artifact is absent, and its older Slizkov artifact was **not**
used. This avoids mixing an old source theorem with the new package.

| Imported artifact | SHA-256 |
| --- | --- |
| `AdditionChain.olean` | `d9bab8bbb1a30732fdae3cd9aeb1228d39f88ed67c4e25c0aa615583ebf27f1e` |
| `KnuthStolarsky.olean` | `2e8b88ac41d44d4128c9f232136a3a18a2fff220fbc70ef4401963d24d150259` |
| `TwoBitAdditionChain.olean` | `107501f329b2c520dda1118a6c7ff4f163885e7e4e9a9e153841474609a5ba9e` |
| `SlizkovDoubling.olean` | `4d8e4d22b179e58fb4b60f075b14fea3639ff7b6654b2c2dd304771798ec9a2a` |

No packaging command wrote a source or output through a main-cache symlink.
No cache reconstruction, dependency/toolchain change, configuration change,
or shared source edit occurred.

## Structural and metadata checks

A Python check compared the complete common-model blocks byte-for-byte and
separately compared the selected theorem headers. It also checked the final
full-name theorem-type output for equality, verified that Challenge's only
import is Mathlib and that Solution does not import Challenge, and counted
exactly one Challenge `sorry` and none in Solution. These are explicit
source/output identity checks, **not a substitute for an unrun Comparator**.

Python's `json` parser and PyYAML **6.0.1** `safe_load` parsed the metadata.
Assertions checked YAML `version: v0.4`, empty unknown-human identity and
reviewer lists, the selected declaration and module paths, the single-theorem
Comparator allowlist, exactly `propext`, `Classical.choice`, `Quot.sound`, and
`enable_nanoda: true`. This is syntax and package-consistency validation, not
an external YAML-schema or Comparator pass.

The directory contains exactly:

```text
README.md
Challenge.lean
Solution.lean
comparator.json
formalization.yaml
verification.md
```

A before/after SHA-256 inventory found all **1,628 preexisting non-cache
files unchanged**, including the landed `Proofs` source and existing package
files. Only the six listed source artifacts were added. Ignored `.lake`
diagnostics are not package additions. No scratch proof file remains, and
no immutable/reference input or existing README was created or modified.

## Corrected attempt and unavailable tools

The first Challenge run failed in ground examples because numerical chain
constructors needed explicit summands, and direct dependent elimination of a
concrete invalid singleton did not elaborate. The positive examples now
specify `a` and `b`, and the negative example checks the empty-list rejection.
No definition or selected theorem statement was weakened. Subsequent full
Challenge runs passed. The Solution bridge passed on its first attempt.
The last two fresh runs added fully qualified type printing to expose model
identity and are the final-source checks recorded above.

Quick `command -v` preflight found no `comparator`, `landrun`, `lean4export`,
`nanoda`, or `nanoda_bin`. Therefore Comparator, export, and Nanoda are
**NOT RUN**, not passed. No verifier installation or tool setup was attempted.
`comparator.json` retains the strict single selected FQN, the three permitted
axioms, and `enable_nanoda: true` for later USER-controlled verification.

## Attribution and review boundary

This package wraps the landed elementary bounded-family proof; it does not
assert mathematical novelty or external priority. OEIS context is inherited
from the source transcriptions; no new literature review or endorsement is
claimed. The task attributes the latest proof and packaging to materially
AI-assisted work using **gpt-6-astra, effort xhigh**. Earlier foundational
infrastructure details are unknown. Human author and responsible-maintainer
identities were not established and remain empty in metadata.

No subagents or external reviewers were used. USER review is pending and is
the sole review gate. None of the mechanical checks constitutes submission
or acceptance.
