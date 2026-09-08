# Squarefree middle binomial coefficients: complete bounded classification

## Candidate status

This is a Palomar **candidate for parent review**, not a submitted, accepted, or
registered Palomar entry. The independent Challenge and proved Solution compile
separately, their selected declarations have the same elaborated type, and the
Solution axiom audit is within Palomar's three-axiom allowlist. Two independent
AI reviews completed with PASS results on 2026-09-08 against reviewed integration
`dcf241b5a1f33b86325e82d575fa588d9a3575e6` and the frozen Lean hashes recorded
in `verification.md`. Comparator, `lean4export`, and NanoDa were **not run**
because those executables are not available in this environment.

Current Palomar policy requires nonempty human-only `project.authors` and
`project.responsible_maintainers`. No authoritative human identities were
provided, and none have been inferred from repository ownership or the licence.
Those lists therefore remain empty in `formalization.yaml`, making the metadata
**not mechanically submit-ready** until a responsible human supplies accurate
names. Submission authorization and source-author endorsement are also unknown.

## Exact selected result

The package selects one theorem:

```lean
Palomar.SquarefreeBinomialClassification.squarefree_choose_half_iff :
  ∀ {n : ℕ}, n < 10 ^ 8 →
    (Squarefree (n.choose (n / 2)) ↔
      n ∈ ({0, 1, 2, 3, 4, 5, 7, 8, 11, 17, 19, 23, 71} : Finset ℕ))
```

Thus every natural `n` under the **strict** bound `10^8` is quantified. Natural
number division by the fixed nonzero divisor `2` is floor division. The theorem
uses Mathlib's ordinary `Nat`, `Nat.choose`, `Squarefree`, `Finset` membership,
division, order, and power. It introduces no mathematical definition, alternate
model, answer-bearing premise, or certificate hypothesis.

The theorem is explicitly bounded. It neither states nor proves an unbounded
classification, a finiteness theorem for all indices, new analytic mathematics,
or a priority claim. At the boundaries, `n = 0` is included and has
`C(0,0) = 1`; `71` is the last listed positive index; `72` is excluded; and
`100000000` lies outside the theorem. The Challenge and Solution check the
nonempty range and these membership/bound facts independently.

## Source alignment and attribution

`Solution.lean` is a direct bridge to the exact repository declaration

```lean
Erdos175.A046098.squarefree_choose_half_iff {n : Nat}
    (hlt : n < 10^8) :
  Squarefree (n.choose (n/2)) ↔
    n ∈ ({0,1,2,3,4,5,7,8,11,17,19,23,71} : Finset Nat)
```

in `Proofs/Erdos/Erdos175/SquarefreeCentralBinom.lean` at accepted base
`dbe40a6bf54ae15b54e0a62fe7e35f274ed77c13`. The package target and source have
the same elaborated proposition; the bridge does not modify the signature.

The mathematical source is the OEIS entry
[A046098](https://oeis.org/A046098), specifically T. D. Noe's attributed comment
of 6 April 2007, **“No other n < 10^8.”** The entry lists the thirteen indices
in the theorem. This package treats that comment as a finite computational
assertion, not as a published proof, an unqualified conjecture-closure story, or
an unbounded claim. A fresh retrieval of the OEIS page through the available web
search tool confirmed the sequence description, terms, comment, attribution,
and date. No endorsement by Noe is known or asserted.

A limited fresh web search found the OEIS entry, MathWorld summaries, and
literature about the related central-binomial theorem, but no prior Lean
formalization of this exact bounded A046098 classification. That is only a
scoped no-reference-found report, not evidence of novelty or priority.

The existing
[`Palomar/SquarefreeBinomialOddRange`](../SquarefreeBinomialOddRange/README.md)
candidate is related but strictly narrower: it selects only odd `n` satisfying
`72 ≤ n < 10^8`. It was inspected for package conventions and was not changed.

## Proof architecture

The repository proof is computational but kernel checked:

1. For even `n`, `n.choose (n / 2)` is a central binomial coefficient. The
   bounded central-binomial classification excludes even values from `72`
   onward. Its power-of-two branch uses `Erdos175.witness_cert`; at this base
   that certificate is transported from an ordinary kernel-checked,
   fuel-bounded digit-sum computation and no longer uses native trust.
2. For odd `n ≥ 72`, the identity
   `2 * C(n, floor(n/2)) = centralBinom (floor(n/2) + 1)` reduces the case with
   at least three binary ones to a repeated factor `2`. The remaining
   power-of-two or two-power-sum cases are reduced to 331 bounded candidates;
   ordinary `decide` verifies carry certificates at one of `3`, `5`, or `7`.
3. Even and odd cases are assembled to exclude every `72 ≤ n < 10^8`.
4. Below `72`, the thirteen listed cases are proved squarefree by explicit
   products of distinct primes. The even classification and a small odd
   certificate exclude the other cases, including the ten residual odd indices
   `9, 15, 31, 33, 35, 39, 47, 63, 65, 67`.
5. The below-`72` equivalence is combined with the `72 ≤ n < 10^8` exclusion.

The source explicitly proves the sharp transition: `C(71,35)` is squarefree and
`C(72,36)` is not. It also checks `n = 0`. The strict upper guard is never
silently widened to `n ≤ 10^8`.

## Trust, production, and review boundary

The selected Solution theorem and its transitive proof closure report exactly
`propext`, `Classical.choice`, and `Quot.sound`. The closure contains no
`sorryAx`, `Lean.ofReduceBool`, native-computation axiom, custom axiom,
`@[implemented_by]`, `@[extern]`, or `@[csimp]`. The Challenge has one
intentional theorem hole and no definition holes. It imports only the two
needed Mathlib modules; the Solution does not import it.

The original proof development used **gpt-6-astra with xhigh reasoning through
Yah**. This candidate packaging used **gpt-5.6-sol with high reasoning through
Yah**. These are separate phases and are disclosed separately in the metadata.
No human author, maintainer, or reviewer is invented.

The source modules contain self-audits, and the parent supplied fresh serial
compilation, diff, pin, source-hash, and axiom logs at the accepted candidate.
This packaging lane independently checked source alignment and compiled the
package files. Two further independent AI reviews completed on 2026-09-08 at
reviewed integration `dcf241b5a1f33b86325e82d575fa588d9a3575e6`:

- the foundations/fidelity reviewer passed the exact finite Noe assertion,
  thirteen-value list, strict bound, floor division, Mathlib squarefreeness,
  source proof, pins, and certificate provenance without required correction;
- the vacuity/trust reviewer reported no vacuity, drift, trust, or material style
  finding after fresh package compilation, raw-type comparison, boundary and
  hypothesis audits, independent kernel reductions of representative `Fin 31`,
  `Fin 26`, and `Fin 72` certificates, and axiom checks.

Those reviews apply to the frozen `Challenge.lean` and `Solution.lean` bytes
whose hashes are recorded in `verification.md`. They are independent AI review,
not human mathematical, attribution, or fidelity review, and do not automatically
approve later metadata changes. Human authorship, maintenance, authorization,
and review remain unresolved; the parent will review the combined metadata
before any publication. See [`verification.md`](verification.md) for exact
scope, timings, provenance, outputs, and unresolved decisions.

The repository licence is MIT. This describes the repository software licence,
not a licence for the OEIS entry or its comment.
