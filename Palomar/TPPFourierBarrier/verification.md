# Verification record: BCGPU TPP Fourier barrier

## Current mechanical verification

[Authoritative campaign manifest](../Wave4ComparatorEvidence.yaml): **PASS** for every declaration selected by this package’s `comparator.json`. Earlier text below is historical and superseded. Human review remains **UNCHECKED**; this makes no claim of Palomar acceptance, submission, or publication.

## Status

- **Challenge compilation:** PASS. It produced an `.olean`; its only warning is the intentional challenge theorem hole.
- **Solution compilation:** PASS. It produced a separate `.olean` using the already-built, provenance-checked GroupTPP cache.
- **Challenge/Solution theorem pair:** PASS for exact emitted `#check` signature equality (`diff` exit status `0`).
- **Selected theorem axiom audit:** PASS. The fresh `#print axioms` closure is exactly `propext`, `Classical.choice`, and `Quot.sound`.
- **Forbidden proof mechanisms:** none found in the Solution. There is no `sorry`, `native_decide`, `Lean.ofReduceBool`, custom `axiom`, `implemented_by`, `extern`, or `csimp` in the selected proof.
- **Comparator:** **NOT RUN** because all required verifier executables are missing and the available Comparator source targets a newer Lean version.
- **Human review:** **PENDING**. USER is the sole review gate. This record does not claim human approval, Palomar acceptance, registration, or submission.

## Scope and revisions

The assigned campaign base was
`117a6e3949ca41075e133e350e38d9d2fbfdd8e2`. Only these files were created:

- `Palomar/TPPFourierBarrier/Challenge.lean`
- `Palomar/TPPFourierBarrier/Solution.lean`
- `Palomar/TPPFourierBarrier/comparator.json`
- `Palomar/TPPFourierBarrier/formalization.yaml`
- `Palomar/TPPFourierBarrier/verification.md`

The pre-existing `README.md`, `Proofs/`, `References/`, other candidates, and root configuration were not modified. The exact finalized working-copy revision is reported by the completing agent after the final immutable status check; embedding a jj working-copy commit ID here would itself change that ID.

## Versions and source provenance

- Lean: `4.33.0-rc1`, commit `62eed1db4d67327ec8120be05f1a1b0847d74561`, `x86_64-unknown-linux-gnu`, Release build.
- Lake: `5.0.0-src+62eed1d` (Lean `4.33.0-rc1`).
- Mathlib manifest revision: `3edb3c0658f69f197b1e501b1f7623f3f7b3898c`.
- Project `lean-toolchain` SHA-256: `02f25adee7c1d6bf2e95b7b5b13f45b9892c7dd53ef470d5372ac60bda3df023`.
- Project `lake-manifest.json` SHA-256: `948a91a6b3c52e0b640d0dadc1bf84cf967403244ac590c162c005c2544a439e`.
- Comparator configuration: `Palomar/TPPFourierBarrier/comparator.json`.

The Solution reused GroupTPP `.olean` files from
`/home/exedev/p/proofs/.lake/build/lib/lean` read-only through `LEAN_PATH`.
Before reuse, the workspace and cache-owner copies of `lean-toolchain` and
`lake-manifest.json` were compared byte-for-byte and matched. The workspace and
cache-owner source files for `BCGPUBarrier.lean`, `CharDegrees.lean`, and
`FourierBarrier.lean` were also compared byte-for-byte and all matched. Their
workspace source hashes were:

```text
BCGPUBarrier.lean  3a78e3c2f3a464294e890fd004a031b0286804c6c86afad5216bad701d10f5f2
CharDegrees.lean   f7b3ef11285866b43a996489a4b518f4b8fb72db26562df5438875ad8424945b
FourierBarrier.lean 85267099015c90706d1dc2c9b2dec8536b0b92a345b1f27732639adfb4f24404
```

The reused `.olean` hashes were:

```text
BCGPUBarrier.olean 6ae7513d5011e4552b86494cf19c34f54e1bbbabd74a62db3ffd20fca14a32d1
CharDegrees.olean  0fbfe7b5fab0af235d4a1c88a6574d37f4153f64f6e9f980684b9e52966f6a38
FourierBarrier.olean 23c239f3be3e5508a752cb69b283406ff9a2b1840d07c1da84239a3ca021089f
```

No whole-repository build, cache reconstruction, dependency update, toolchain
upgrade, or verifier installation was performed.

## Source attribution and fidelity

The primary source is Jonah Blasiak, Thomas Church, Henry Cohn, Joshua A.
Grochow, and Chris Umans, *Matrix multiplication via matrix groups*,
arXiv:2204.03826. The already-retrieved source
`/home/exedev/downloads/01a07cfa-d323-732a-b33d-0a81d9175ff9/arXiv-2204-03826/paper.tex`
was inspected at lines 164--169. It defines

```text
n(G) = min { dim pi : pi irreducible and dim pi > 1 }
```

for finite nonabelian `G`, then states Theorem 3.2 (`thm:gowerstrick`) with the
same inequality packaged here. In particular, the source does **not** define
`n(G)` as the minimum dimension among merely nontrivial representations, which
could incorrectly select nontrivial linear characters.

The Challenge defines the ordinary objects independently using only targeted
Mathlib imports. Character degrees are the composition lengths of the isotypic
components of the regular complex group algebra. The minimum filters those
degrees by `1 < d`. The Solution repeats the definitions without importing the
Challenge, proves the character-degree and minimum bridges, converts the local
TPP definition definitionally, and applies the source-based existing theorem
`GroupTPP.BCGPUBarrier.bcgpu_thm_3_2`. It does not substitute an abstract
analytic decomposition or a free `n` parameter, and it does not package an
asymptotic omega theorem.

## Declaration list

Both Challenge and Solution declare the same ordinary interface:

- `Palomar.TPPFourierBarrier.TripleProductProperty`
- `Palomar.TPPFourierBarrier.characterDegrees`
- `Palomar.TPPFourierBarrier.minIrrepDimGTOne`
- `Palomar.TPPFourierBarrier.characterDegrees_eq_isotypic_lengths`
- `Palomar.TPPFourierBarrier.minIrrepDimGTOne_eq_filtered_min`
- `Palomar.TPPFourierBarrier.tpp_card_product_le_fourier_barrier`

The Solution additionally proves the internal bridge declarations:

- `Palomar.TPPFourierBarrier.characterDegrees_eq_groupTPP`
- `Palomar.TPPFourierBarrier.minIrrepDimGTOne_eq_groupTPP`

The files include a concrete satisfiability check using singleton subsets of the
nonabelian group `Equiv.Perm (Fin 3)`. The only intentional hole is the selected
theorem in `Challenge.lean`; definitions contain no holes, and
`Solution.lean` is sorry-free.

## Separate Challenge compilation

Immediately before the final command, `tool_atop` reported 8 cores, 23.46 GiB
total memory, 7.50 GiB used, and 15.96 GiB available. This left sufficient
headroom for the bounded 8,000 MiB Lean allocation. The exact command was:

```sh
set -o pipefail && timeout 300s taskset -c 0 lake env lean -M 8000 -j 1 \
  -o /tmp/yah/subagent/tpp-fourier-package-prover-c85e218/Challenge.olean \
  Palomar/TPPFourierBarrier/Challenge.lean 2>&1 | \
  tee /tmp/yah/subagent/tpp-fourier-package-prover-c85e218/challenge-final.log
```

Exit status: `0`. Output:

```text
Palomar/TPPFourierBarrier/Challenge.lean:74:8: warning: declaration uses `sorry`
@tpp_card_product_le_fourier_barrier : ∀ {G : Type u_1} [inst : Group G] [inst_1 : Fintype G] [DecidableEq G]
  {S T U : Finset G},
  (∃ a b, a * b ≠ b * a) →
    TripleProductProperty S T U →
      ↑S.card * ↑T.card * ↑U.card ≤ ↑(Fintype.card G) ^ (3 / 2) / √↑(minIrrepDimGTOne G) + ↑(Fintype.card G)
```

The output artifact was 58,440 bytes with SHA-256
`b4c62682a02cf49350cf70b5a0c994d04daac6bbc7f5a2804e223abcc94dd0dd`.

## Separate Solution compilation and axiom audit

Immediately before the final command, `tool_atop` reported 8 cores, 23.46 GiB
total memory, 0.85 GiB used, and 22.61 GiB available. The exact command was:

```sh
set -o pipefail && \
LEAN_PATH="/home/exedev/p/proofs/.lake/build/lib/lean:${LEAN_PATH:-}" \
timeout 300s taskset -c 0 lake env lean -M 12000 -j 1 \
  -o /tmp/yah/subagent/tpp-fourier-package-prover-c85e218/Solution.olean \
  Palomar/TPPFourierBarrier/Solution.lean 2>&1 | \
  tee /tmp/yah/subagent/tpp-fourier-package-prover-c85e218/solution-final.log
```

Exit status: `0`. Exact audit output after the signature was:

```text
'Palomar.TPPFourierBarrier.tpp_card_product_le_fourier_barrier' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

The output artifact was 67,384 bytes with SHA-256
`e8c3453009b78a5ad945f0d445c2f36356e4a9facfa4471ce5e72ffef8b14f8e`.
Because `#print axioms` was elaborated afresh in the Solution source, this is a
fresh selected-declaration audit, not an inference from imports. Its closure is
a subset of the Comparator allowlist and excludes `sorryAx`.

## Pair signature comparison

The complete multiline `#check` signature was extracted independently from the
final Challenge and Solution logs. The exact comparison command was:

```sh
diff -u \
  /tmp/yah/subagent/tpp-fourier-package-prover-c85e218/challenge-final-signature.txt \
  /tmp/yah/subagent/tpp-fourier-package-prover-c85e218/solution-final-signature.txt
```

Exit status: `0`, with no diff. Thus the selected declarations have identical
elaborated signatures, including the universe, typeclass parameters,
nonabelianness witness, local TPP predicate, real casts, exponent, square root,
and strictly-greater-than-one character-degree minimum.

## Earlier bounded failure

The first narrow-import Challenge check used:

```sh
timeout 300s taskset -c 0 lake env lean -M 8000 -j 1 \
  Palomar/TPPFourierBarrier/Challenge.lean
```

It exited `1` because `Mathlib.RingTheory.Length` had not yet been imported:

```text
Palomar/TPPFourierBarrier/Challenge.lean:36:44: error(lean.unknownIdentifier): Unknown constant `Module.length`
Palomar/TPPFourierBarrier/Challenge.lean:52:20: error(lean.unknownIdentifier): Unknown constant `Module.length`
```

The missing targeted Mathlib import was added. The unchanged bounded strategy
then passed, including both final artifact-producing compilations above. The
complete failed log is
`/tmp/yah/subagent/tpp-fourier-package-prover-c85e218/challenge-1.log`.
There were no resource failures.

## Comparator and Nanoda

**Status: NOT RUN; this is not a Comparator or Nanoda pass.** Preflight found no
`comparator`, `landrun`, `lean4export`, or `nanoda_bin` executable in `PATH`, and
`/home/exedev/p/yah-upstreams/issue-490/comparator/.lake/build/bin/comparator`
does not exist. The available Comparator source declares
`leanprover/lean4:v4.34.0-rc1`, while this project is pinned to
`leanprover/lean4:v4.33.0-rc1`. Following the task constraint, no installation,
second toolchain, source build, or futile repeated invocation was attempted.
`comparator.json` retains `enable_nanoda: true` and the explicit permitted axiom
list for eventual USER-side verification with compatible installed tools.

## Review and metadata boundary

All package implementation and verification work recorded here was materially
AI-assisted. No authoritative human formalization author or responsible
maintainer identity was available, so `formalization.yaml` leaves those human
identity lists empty and records the resulting metadata blockers. USER review
remains pending and is the only requested review phase.
