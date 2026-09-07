# Verification: integer complexity of powers of three

## Status

- **Challenge elaboration:** PASS. Its only warning is the intentional headline-theorem hole.
- **Solution elaboration:** PASS, with independent literal definitions and an explicit transport to the repository definition.
- **Challenge/Solution alignment:** PASS. Mechanical extraction found identical shared definitions and identical selected theorem headers.
- **Selected axiom closure:** PASS. It is exactly `propext`, `Classical.choice`, and `Quot.sound`; it does not contain `sorryAx`.
- **Open-conjecture isolation:** PASS. A fresh print shows that the imported powers-of-two theorem does contain `sorryAx`, while both the selected wrapper and source powers-of-three theorem do not.
- **Comparator / landrun / lean4export / nanoda:** NOT RUN. The required executables are unavailable and the available Comparator source targets a newer Lean version.
- **Human review:** PENDING. USER review is the sole review gate; no agent, parent, or independent review is claimed.

## Formal object, boundary, and source bridge

`Challenge.lean` imports only `Mathlib.Order.Lattice.Nat`. Both Challenge and Solution independently declare `Palomar.IntegerComplexityPowersOfThree.Expr` with constructors `one`, `add`, and `mul`, recursive natural-number `eval`, and recursive leaf-count `cost`. Both define

```lean
noncomputable def complexity (n : ℕ) : ℕ :=
  ⨅ e : {e : Expr // e.eval = n}, e.1.cost
```

rather than defining the answer from a source theorem. The index subtype is empty at zero, so its natural infimum there is a junk convention. The selected statement retains `1 ≤ b`; at `b = 0`, `3^0 = 1` has complexity one but `3*0 = 0`. A concrete package example instantiates the hypothesis and conclusion jointly at `b = 1`.

Solution does not import Challenge. It imports `NumberComplexity.DoublingConjecture`, defines recursive translations `Expr.toSource` and `Expr.ofSource`, and proves that both preserve evaluation and cost. `complexity_eq_source` proves equality of the independent and source infima on positive inputs: one inequality maps a source minimizing witness, and the other uses `Nat.sInf_mem` for the nonempty local witness range and maps its attained minimum back. Only after this minimization transport does the selected proof apply `NumberComplexity.complexity_three_pow`.

The imported file also contains the separate intended open theorem `NumberComplexity.complexity_two_pow`. It is not used by the wrapper. The fresh axiom comparison below makes that separation mechanical; this package does not claim or select the powers-of-two conjecture.

## Revision, toolchain, and exact cached inputs

- Assigned campaign base: `ee0cb27655f6bb6c37e8647c79184745017c5b24`.
- Harness working-copy change: `xzqwsmoqnwuxvoovssrvklqosvyyqvnz` (`Campaign prover: integer-three-package-prover`), whose parent is the assigned base. Its content-addressed commit ID changes when this verification record itself is written; the final post-write ID is therefore reported in the completion response rather than embedded self-referentially here.
- Lean: `4.33.0-rc1`, commit `62eed1db4d67327ec8120be05f1a1b0847d74561`, `x86_64-unknown-linux-gnu`, Release build.
- Lake: `5.0.0-src+62eed1d` (Lean `4.33.0-rc1`).
- Mathlib manifest revision: `3edb3c0658f69f197b1e501b1f7623f3f7b3898c`.

The targeted repository oleans already existed in the read-only main cache `/home/exedev/p/proofs/.lake/build/lib/lean`. Before reuse, every relevant source pin in the workspace was compared with `/home/exedev/p/proofs` and matched exactly:

```text
lean-toolchain
  02f25adee7c1d6bf2e95b7b5b13f45b9892c7dd53ef470d5372ac60bda3df023
lake-manifest.json
  948a91a6b3c52e0b640d0dadc1bf84cf967403244ac590c162c005c2544a439e
Proofs/NumberComplexity/IntComplexity.lean
  4d7d3da17a8d075546c3ebcb4cf5354b8b37ed5db81ba2ca0fb07e32f64204be
Proofs/NumberComplexity/DoublingConjecture.lean
  506f800448cad5c2a703ae59fe8b1429934c60dc2b068155ef3c595f8eccbb57
```

The reused artifact hashes were:

```text
IntComplexity.olean
  ebbd41011935b73b0adc102ac331ee197f196122238a0a277c780f68185c3936
DoublingConjecture.olean
  ecd6ea3620b85912dfef59577bcc21d33d5f6fa68efcadcf595d85933c97e0cf
```

A coherent package-root `LEAN_PATH` put that exact main-cache root before the Lake-generated dependency roots. No cache was reconstructed or modified, and no dependency, toolchain, project configuration, `Proofs/`, `References/`, or README file was changed. The preserved candidate README's SHA-256 was `9600fa6b13086ad0aadc097d05dcd1a36b6b559f8f1f7b171ffd708770e471c7`.

## Challenge elaboration

Immediately before the final command, `tool_atop` reported 8 cores, 23.46 GiB total memory, 3.50 GiB used, and 19.96 GiB available. The bounded one-core command was:

```sh
timeout 180s taskset -c 0 lake env lean -M 5000 -j 1 \
  Palomar/IntegerComplexityPowersOfThree/Challenge.lean
```

Exit status: `0`. Exact output:

```text
Palomar/IntegerComplexityPowersOfThree/Challenge.lean:56:8: warning: declaration uses `sorry`
@Palomar.IntegerComplexityPowersOfThree.complexity_three_pow : ∀ {b : ℕ},
  1 ≤ b → Palomar.IntegerComplexityPowersOfThree.complexity (3 ^ b) = 3 * b
```

Retained log: `/tmp/yah/subagent/integer-three-package-prover-40b1184/challenge-final.log`.

## Solution elaboration and selected axiom audit

Immediately before the final Solution command, `tool_atop` reported 8 cores, 23.46 GiB total memory, 0.84 GiB used, and 22.62 GiB available. The matching read-only cache was used by:

```sh
export LEAN_PATH="/home/exedev/p/proofs/.lake/build/lib/lean:$(lake env printenv LEAN_PATH)"
timeout 240s taskset -c 0 lake env lean -M 9000 -j 1 \
  Palomar/IntegerComplexityPowersOfThree/Solution.lean
```

Exit status: `0`. Exact output:

```text
@Palomar.IntegerComplexityPowersOfThree.complexity_three_pow : ∀ {b : ℕ},
  1 ≤ b → Palomar.IntegerComplexityPowersOfThree.complexity (3 ^ b) = 3 * b
'Palomar.IntegerComplexityPowersOfThree.complexity_three_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'NumberComplexity.complexity_three_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'NumberComplexity.complexity_two_pow' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

Retained log: `/tmp/yah/subagent/integer-three-package-prover-40b1184/solution-final.log`.

Thus the selected closure is exactly the three axioms allowed in `comparator.json`, is a subset of the permitted trusted closure, and excludes `sorryAx`. The contrast with `NumberComplexity.complexity_two_pow` confirms that merely importing the module does not contaminate the selected dependency closure.

## Mechanical pair and source checks

A Python extraction took the public `Expr` declaration, its `eval` and `cost`, their ground checks, and the independent `complexity` definition from each file, then compared the extracted text with `diff -u`. It separately extracted and compared the complete docstring and theorem header through `:= by`. Exact result:

```text
SHARED_DEFINITIONS_IDENTICAL=YES
THEOREM_HEADERS_IDENTICAL=YES
JSON_PARSE=PASS
YAML_PARSE=PASS
```

A source scan found no `native_decide`, `Lean.ofReduceBool`, custom `axiom`, `implemented_by`, `extern`, or `csimp` in either Lean module. The only code occurrence of `sorry` is the intentional Challenge theorem at line 58; Solution contains none. (The prose phrase “axiom closure” is not a declaration.) The first four finalized package-file hashes, before writing this verification record, were:

```text
Challenge.lean     5a0f68001f41fc0bf8c753f1f5f005eb4e05491638b3f1fab8d9e6235c6ba4b6
Solution.lean      d43d0210df71ab8b38fb1c9a554b0239c7ab169021a7dc49bf5aeea84d67e7e3
comparator.json    a50eee6e18b47df0b97eb6bea6e5723ba04aa7960981fc247ccb4c6f1f721361
formalization.yaml 2f7da078bf32235341df8a69863388951a88bac0c944349419b5530fb4c28d33
```

## Failed proof-development attempt

The first Solution elaboration exited `1` at the reverse minimization inequality:

```text
Palomar/IntegerComplexityPowersOfThree/Solution.lean:121:11: error: typeclass instance problem is stuck
  CompleteLattice ?m.57
```

That attempt incorrectly tried the generic complete-lattice lemma `le_iInf`; naturals have the intended `sInf` operation but are not a complete lattice. The method was changed rather than retried unchanged: the final proof establishes nonemptiness of the local witness-cost range, uses `Nat.sInf_mem` to obtain an attaining local expression, and translates that expression to the source syntax. The subsequent and final elaborations passed. Retained failed log: `/tmp/yah/subagent/integer-three-package-prover-40b1184/solution-first.log`.

## Comparator tooling blocker

**Status: NOT RUN. This is not a Comparator, landrun, lean4export, or nanoda pass.** A bounded preflight reported:

```text
comparator=MISSING
landrun=MISSING
lean4export=MISSING
nanoda_bin=MISSING
Comparator source lean-toolchain: leanprover/lean4:v4.34.0-rc1
Project lean-toolchain: leanprover/lean4:v4.33.0-rc1
```

The available Comparator source therefore targets a newer toolchain than this pinned project, and its executable and all three external verifier executables are absent. In accordance with the task constraints, no installation, verifier build, toolchain upgrade, or futile/repeated invocation was attempted. `comparator.json` nevertheless retains the fully qualified selected theorem, exactly the three permitted axioms, and `enable_nanoda: true` for later USER-controlled verification.

## Attribution and review boundary

This is a formalization of known mathematics, not a first-proof or novelty claim. Attribution is inherited from the preserved candidate README and repository source: OEIS A005245 for Mahler–Popken complexity; the classical lower bound credited to Selfridge/Coppersmith; and Iraids et al., arXiv:1203.6462, Theorem `cbounds2`, for the cited base-three result. No broad literature search or human source comparison was performed in this package task.

All package preparation was AI-assisted. No authoritative human formalization author or responsible maintainer identity was available, so `formalization.yaml` leaves those required human fields empty and records them as submission blockers rather than inventing identities. USER review remains pending and is the sole review stage.
