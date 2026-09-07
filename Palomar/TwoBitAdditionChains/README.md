# Exact doubling for addition chains with at most two binary ones

**Status:** Challenge and Solution independently typecheck in the pinned Lean
project; the Solution's selected theorem has only the three permitted axioms.
Comparator/Nanoda **NOT RUN** because their executables are unavailable.
**USER review is pending.** This is not a submission, acceptance, or mathematical
novelty claim.

## Selected result

```lean
Palomar.TwoBitAdditionChains.l_two_mul_eq_add_one_of_binaryWeight_le_two :
  ∀ {k : ℕ}, 0 < k → binaryWeight k ≤ 2 → l (2 * k) = l k + 1
```

Here `l k` is the minimum number of additions in an **actual addition chain**
reaching `k`, and `binaryWeight k = k.bitIndices.length` counts its binary ones.
The family includes every power of two and every sum of two distinct powers,
including separated positions such as `9 = 1 + 8`. The bound is on binary
weight, **not** on the numerical size of `k`.

This equality is stronger than the requested restricted Slizkov inequality
`l k ≤ l (2 * k) + 1`. It does **not** solve the unrestricted Slizkov doubling-gap
question or the Knuth–Stolarsky conjecture. Both remain separately archived as
open conjectures in the repository; neither occurs in the selected proof's
axiom closure.

## Independent challenge semantics

`Challenge.lean` imports **only Mathlib**. Its model is explicit:

- `IsAddChain [1]` starts a chain. Its only extension rule prepends `a + b`
  when both summands already occur in the tail. Equal summands are allowed.
- Lists are reversed chronologically, so the head is the target.
- `chainSteps c = c.tail.length` counts additions rather than list elements.
- `AdditionChain n` is the subtype of actual chains with head `n`.
- `l n` is the natural infimum of their lengths, not an arbitrary supplied
  function or a function constrained by a desired global bound.
- The file proves that every positive target has a chain and that the minimum
  is attained. No chain reaches zero; `l 0 = 0` is the empty-infimum junk value.
  The selected theorem therefore retains **`0 < k`**.
- `binaryWeight` is exactly Mathlib's `Nat.bitIndices` length. Checks include
  weights at `0, 1, 9, 7`, joint guards at `k = 1` and `k = 9`, chain examples,
  and `l 0 = l 1 = 0` with their distinct meanings explained.

The permissive list convention allows repeated or non-increasing entries.
The repository's `NumberComplexity.l_eq_lAsc` proves that its minimum agrees
with the ordinary strictly ascending-chain convention. This is not a shear,
circuit, or other surrogate complexity measure.

The Challenge has exactly one intentional hole, at the selected theorem, and
no incomplete definitions.

## Solution bridge and source proof

`Solution.lean` does **not** import Challenge. It repeats the same independent
model and the same selected theorem header. Checks found the model blocks and
headers byte-identical, and full-name Lean output identifies the package's
own `l` and `binaryWeight` in both theorem types.

The two independently declared chain predicates are not silently identified.
The Solution proves their equivalence by induction on each predicate. It then
proves equality of the sets of attainable chain lengths, hence equality of
the independent minimum and `NumberComplexity.l`. Only after that bridge does
it apply the source theorem.

The source result is at accepted repository revision
`55ab7d253f32b9632581cf31cc4951c2b2119533`:

- `Proofs/NumberComplexity/SlizkovDoubling.lean`:
  `NumberComplexity.l_two_mul_eq_add_one_of_binaryWeight_le_two`.
- `Proofs/NumberComplexity/TwoBitAdditionChain.lean`:
  `l_two_pow_add_two_pow`, together with binary-digit classification.
- `Proofs/NumberComplexity/AdditionChain.lean` and `KnuthStolarsky.lean`:
  supporting chain definitions and the binary-weight abbreviation.

The elementary two-bit construction doubles through `2 ^ b`, then adds the
already present `2 ^ a` for `a < b`. It takes `b + 1` additions and is optimal:
`b` additions cannot produce a value greater than `2 ^ b`. Doubling shifts both
bit positions by one. The source proof does not enumerate large chains or
assume either open conjecture.

## Verification and limitations

See [verification.md](verification.md) for exact commands, source/cache
provenance, theorem-type output, axiom output, and the corrected initial
Challenge elaboration attempt.

- Challenge: **PASS**, with its one intentional theorem-hole warning.
- Solution and semantic bridge: **PASS**; selected closure is exactly
  `propext`, `Classical.choice`, `Quot.sound`.
- JSON/YAML parsing, import separation, identical models/statements, and the
  six-file write allowlist: **PASS**.
- Comparator/Nanoda: **NOT RUN**. The configuration selects only the theorem
  above, permits exactly those three axioms, and retains `enable_nanoda: true`.
  No replacement verifier infrastructure was installed or built.
- Human mathematical, attribution, and source-fidelity review: **PENDING**,
  with USER as the sole review gate.

The latest substantive proof and packaging are disclosed as AI-assisted using
**gpt-6-astra, reasoning effort xhigh**, as attributed by the task. Earlier
foundational-infrastructure model details are unknown. No human formalization
author or responsible maintainer identity was established; the corresponding
metadata lists are empty. OEIS A003313, A000120, and A230528 provide the
inherited sequence/question context, not a claim of new mathematics or an
independently completed literature-priority review.
