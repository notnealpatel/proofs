# Verification record: gcd sunflower almost-prime layer

## Current mechanical verification

[Authoritative campaign manifest](../Wave4ComparatorEvidence.yaml): **PASS** for every declaration selected by this package’s `comparator.json`. Earlier text below is historical and superseded. Human review remains **UNCHECKED**; this makes no claim of Palomar acceptance, submission, or publication.

## Status

- **Challenge elaboration:** PASS. Its only warning is the intentional hole in the selected challenge theorem.
- **Solution elaboration:** PASS, separately from the Challenge and without importing it.
- **Selected dependency axiom closure:** PASS. The wrapper theorem, source theorem, and imported Erdős–Rado bound each use exactly `propext`, `Classical.choice`, and `Quot.sound`.
- **Comparator / landrun / lean4export / nanoda:** NOT RUN. Required executables are absent and the available Comparator source targets a newer Lean version.
- **Human review:** PENDING. USER review is the only review gate; no approval or submission claim is made.

## Scope and source relation

The selected declaration is
`Palomar.GcdSunflower.card_le_of_isAlmostPrime`. Challenge and Solution contain
literal, independent copies of these definitions:

```lean
def EqualPairwiseGcd (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
    a ≠ b → c ≠ d → Nat.gcd a b = Nat.gcd c d

def GcdPatternFree (r : ℕ) (A : Finset ℕ) : Prop :=
  ∀ S ∈ A.powersetCard r, ¬ EqualPairwiseGcd S

def layerSet (N a : ℕ) : Finset (Fin (N + 1)) :=
  {q ∈ Finset.univ | IsPrimePow (q : ℕ) ∧ (q : ℕ) ∣ a}
```

Thus the pairs are explicitly required to be distinct within each pair, while
`powersetCard r` supplies `r` distinct elements. `Nat.IsAlmostPrime k a` is the
Mathlib predicate `a ≠ 0 ∧ Ω a = k`; `Ω` counts prime factors with
multiplicity. This is not a squarefree or distinct-prime-factor statement.

The Solution proves the selected theorem by transporting these literal
predicates to `Erdos535.card_le_of_isAlmostPrime` from
`Proofs/Erdos/Erdos535/GcdSunflower.lean`. That source theorem uses the
prime-power `layerSet` encoding and the imported
`erdos_rado_sunflower_same_card` bound. No source file was repaired or changed.

This package does not select the optional sharp `k = 1` result. It does not
solve Erdős Problem #535, prove a `c_r^k` improvement, formalize the corrected
coprime-quotient auxiliary conjecture, or assert an effective interval estimate
for `f_r(N)`.

## Pins and read-only cache provenance

- Assigned campaign base: `ee0cb27655f6bb6c37e8647c79184745017c5b24`.
- Lean: `4.33.0-rc1`, commit `62eed1db4d67327ec8120be05f1a1b0847d74561`, `x86_64-unknown-linux-gnu`, Release build.
- Lake: `5.0.0-src+62eed1d`.
- Mathlib manifest revision: `3edb3c0658f69f197b1e501b1f7623f3f7b3898c`.
- Comparator configuration: `Palomar/GcdSunflower/comparator.json`.

The workspace had no local `.lake/build/lib/lean`. The successful Solution
elaboration reused `/home/exedev/p/proofs/.lake/build/lib/lean` as a read-only
prefix of `LEAN_PATH`. Before doing so, the relevant workspace and cache source
inputs were compared exactly:

```text
65d6d9de41718c32e616edd3972bd4786870074007033625546b9e64dccf9972  Proofs/Erdos/Erdos535/GcdSunflower.lean
65d6d9de41718c32e616edd3972bd4786870074007033625546b9e64dccf9972  /home/exedev/p/proofs/Proofs/Erdos/Erdos535/GcdSunflower.lean
1cf79edc9e2f5ce48ea00e1beee6bace37743bf07986b9c9243a7ba651e0c2b5  Proofs/Erdos/Erdos20/ErdosRado.lean
1cf79edc9e2f5ce48ea00e1beee6bace37743bf07986b9c9243a7ba651e0c2b5  /home/exedev/p/proofs/Proofs/Erdos/Erdos20/ErdosRado.lean
948a91a6b3c52e0b640d0dadc1bf84cf967403244ac590c162c005c2544a439e  lake-manifest.json
948a91a6b3c52e0b640d0dadc1bf84cf967403244ac590c162c005c2544a439e  /home/exedev/p/proofs/lake-manifest.json
5fea1b2cc353a49df4d727bd77e43a01c074130fcb099610fe0320d8d7a1906f  lakefile.toml
5fea1b2cc353a49df4d727bd77e43a01c074130fcb099610fe0320d8d7a1906f  /home/exedev/p/proofs/lakefile.toml
02f25adee7c1d6bf2e95b7b5b13f45b9892c7dd53ef470d5372ac60bda3df023  lean-toolchain
02f25adee7c1d6bf2e95b7b5b13f45b9892c7dd53ef470d5372ac60bda3df023  /home/exedev/p/proofs/lean-toolchain
```

The reused object hashes were:

```text
ebcaee3effc633ea7ea33674c84791951216e96454f03d2ce6b3ee131a01da26  Erdos/Erdos535/GcdSunflower.olean
cd42136e2abc26583f8a1e03790019e02c7c5105efa070cdecec10a7bcff9c94  Erdos/Erdos20/ErdosRado.olean
```

Their sizes were 568472 and 473512 bytes respectively. This was coherent reuse
under the same package root, manifest, Lake file, source files, and toolchain;
no cache reconstruction or broad build was performed.

## Challenge elaboration

Immediately before the final command, the host reported 8 cores, 23.46 GiB
physical memory, 0.83 GiB used, 22.63 GiB available, and no swap use. The
bounded one-core command was:

```sh
ulimit -v 22544384
timeout 240s taskset -c 3 lake env lean -M 6000 -j 1 \
  Palomar/GcdSunflower/Challenge.lean
```

Exit status: `0`.

Exact relevant output:

```text
Palomar/GcdSunflower/Challenge.lean:67:8: warning: declaration uses `sorry`
EqualPairwiseGcd : Finset ℕ → Prop
GcdPatternFree : ℕ → Finset ℕ → Prop
layerSet : (N : ℕ) → ℕ → Finset (Fin (N + 1))
@card_le_of_isAlmostPrime : ∀ {r k : ℕ},
  2 ≤ r → ∀ {A : Finset ℕ}, (∀ a ∈ A, k.IsAlmostPrime a) → GcdPatternFree r A → A.card ≤ (r - 1) ^ k * k !
```

Retained log:
`/tmp/yah/subagent/gcd-sunflower-package-prover-2802a23/challenge-final.log`.
The Challenge imports only Mathlib modules and contains one intentional `sorry`,
in the selected theorem. Definitions contain no holes.

## Separate Solution elaboration and fresh axiom audit

Immediately before the final command, the host reported 8 cores, 23.46 GiB
physical memory, 0.83 GiB used, 22.63 GiB available, and no swap use. The
bounded one-core command was:

```sh
LEAN_PATH_REUSED="/home/exedev/p/proofs/.lake/build/lib/lean:$(lake env printenv LEAN_PATH)"
export LEAN_PATH="$LEAN_PATH_REUSED"
ulimit -v 22544384
timeout 300s taskset -c 6 lean -M 8000 -j 1 \
  Palomar/GcdSunflower/Solution.lean
```

Exit status: `0`.

Exact theorem signatures:

```text
@Palomar.GcdSunflower.card_le_of_isAlmostPrime : ∀ {r k : ℕ},
  2 ≤ r → ∀ {A : Finset ℕ}, (∀ a ∈ A, k.IsAlmostPrime a) →
    Palomar.GcdSunflower.GcdPatternFree r A → A.card ≤ (r - 1) ^ k * k !

@Erdos535.card_le_of_isAlmostPrime : ∀ {r k : ℕ},
  2 ≤ r → ∀ {A : Finset ℕ}, (∀ a ∈ A, k.IsAlmostPrime a) →
    Erdos535.GcdPatternFree r A → A.card ≤ (r - 1) ^ k * k !

@erdos_rado_sunflower_same_card : ∀ {n k r : ℕ}
  (family : Finset (Finset (Fin n))), 1 ≤ r →
  (∀ S ∈ family, S.card = k) →
  (r - 1) ^ k * k ! < family.card → HasSunflower family r
```

Exact axiom output:

```text
'erdos_rado_sunflower_same_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos535.card_le_of_isAlmostPrime' depends on axioms: [propext, Classical.choice, Quot.sound]
'Palomar.GcdSunflower.card_le_of_isAlmostPrime' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Retained log:
`/tmp/yah/subagent/gcd-sunflower-package-prover-2802a23/solution-final.log`.
This fresh environment-level audit checks the selected imported dependency
closure, rather than inferring safety merely from the absence of a warning.
There is no `sorryAx`, `native_decide`, `Lean.ofReduceBool`, or custom axiom in
the displayed closure.

A mechanical source extraction also confirmed that the three definition bodies
and selected theorem statement are byte-for-byte identical between Challenge
and Solution; only the proof body differs. `comparator.json` parsed as JSON and
`formalization.yaml` parsed with PyYAML.

## Corrected bounded failures

These failed runs were not treated as verification evidence:

1. The first Challenge attempt exited `1`. The initial package draft omitted
   explicit decidability instances for the two finite predicates, omitted the
   `Nat` scoped factorial notation, and included a negative `layerSet` check
   that did not close by kernel reduction. Lean reported failed `Decidable`
   synthesis and parse errors at `k !`. The instances and scope were added and
   the unnecessary negative computation was removed. Retained log:
   `/tmp/yah/subagent/gcd-sunflower-package-prover-2802a23/challenge.log`.
2. A second Challenge attempt exited `1` because importing the factorial module
   alone did not open its scoped notation. Adding `open scoped Nat` fixed the
   parser error. Its output was superseded by the final retained log.
3. The first Solution audit attempt exited `1` only because the audit line
   incorrectly qualified the globally declared sunflower theorem as
   `Erdos535.erdos_rado_sunflower_same_card`. The proof itself elaborated and
   both gcd theorem closures printed successfully. Correcting the audit name to
   `erdos_rado_sunflower_same_card` produced the final successful run.

No low-virtual-memory failure was repeated, and no whole-repository build,
cache reconstruction, toolchain upgrade, dependency upgrade, or verifier
installation was attempted.

## Comparator and external verifier blocker

**Status: NOT RUN.** One availability preflight found no `comparator`,
`landrun`, `nanoda_bin`, or `lean4export` executable in `PATH`; the known
Comparator executable path
`/home/exedev/p/yah-upstreams/issue-490/comparator/.lake/build/bin/comparator`
was also absent. The locally available Comparator source uses
`leanprover/lean4:v4.34.0-rc1`, whereas this project is pinned to
`leanprover/lean4:v4.33.0-rc1`. Accordingly, no invocation was possible and no
installation, build, alternate-toolchain setup, or repeated attempt was made.
This is a blocker, not a Comparator pass. `enable_nanoda` remains `true` in the
configuration as required; it was not weakened to bypass unavailable tooling.

## Review and attribution boundary

All packaging work was AI-assisted. No subagent, reviewer agent, or parent
mathematical review was used. USER review remains pending and is the sole
review gate. The reduction is attributed cautiously to the classical Erdős
argument and the consumed bound to Erdős–Rado; the detailed 1964/1973
bibliography remains incomplete. This record makes no novelty, priority,
acceptance, approval, or submission claim.
