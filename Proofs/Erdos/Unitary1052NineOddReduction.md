# Uniform nine-odd exponent-one reduction at three

## Status and exact consumer

Production module: `Erdos.Unitary1052NineOddReduction`.
Namespace: `Erdos1052.NineOdd`.
Principal theorem: `three_mem_and_exponent_one`.

The complete uniform necessary condition is proved in Lean. Its expanded signature, obtained from a separate importing leaf audit, is:

```lean
Erdos1052.NineOdd.three_mem_and_exponent_one :
  ∀ (a : ℕ) (P : Finset ℕ) (e : ℕ → ℕ),
    P.card = 9 →
    (∀ p ∈ P, Nat.Prime p) →
    (∀ p ∈ P, Odd p) →
    (∀ p ∈ P, 0 < e p) →
    11 ≤ a →
    (∃ p ∈ P, 32768 < p ^ e p) →
    (2 ^ a + 1) * ∏ p ∈ P, (p ^ e p + 1) =
      2 * (2 ^ a * ∏ p ∈ P, p ^ e p) →
    3 ∈ P ∧ e 3 = 1
```

Here `P` is the finite set of distinct actual odd prime bases, not a multiset of freely chosen prime powers. Each `e p` is positive on `P`; its values outside `P` are unrestricted. The large-component condition is about a prime-power **component**, not its underlying base. The identity is an ordinary equality in `ℕ`, not a congruence or truncated computational surrogate.

The intended objects, quantifiers, explicit hypotheses, and conclusion of the supplied uniform contract survived unchanged. In particular, there is no fixed core, no fixed value of `a`, no global base or exponent cap, and no envelope, closure, or valuation-budget premise in the principal theorem. These certificates are derived internally. The necessary condition is non-circular and unbounded.

## Mathematical source and unpaid source bridges

The implementation follows Sections 1–5 of the supplied reviewed argument:

- `/tmp/erdos-program-nine-odd-final-prose-01a125d8.md`
- SHA-256: `f8c7803a586628003e7e44533b7c76b000666ab12ed7dd4ec340e8782c5c6e54`
- Supplied review: `/tmp/erdos-program-nine-odd-final-prose-review-01a125d8.md` (reported PASS by the coordinator).

The source identifies Charles R. Wall, *New Unitary Perfect Numbers Have At Least Nine Odd Components*, Fibonacci Quarterly 26 (1988), 312–317, canonical URL <https://www.fq.math.ca/Scanned/26-4/wall.pdf>. Its introductory bounds cite earlier work. Those earlier proofs were not independently audited or formalized here; the supplied transcription also has corrupted symbols and the paper omits repetitive cases. No unchecked paper theorem is imported as a Lean axiom.

The two bounds remain **explicit sourced hypotheses**:

1. `11 ≤ a`;
2. `∃ p ∈ P, 32768 < p ^ e p`.

The bridge from an independently formalized unitary-perfect-number predicate to the displayed factorized identity, and the applicability/proofs of the two external bounds for a new exactly-nine candidate, are not established in this module. The theorem proves the assigned conditional implication; it does not absorb those upstream obligations.

## Proof outline and implementation correspondence

1. **Actual components.** Positive prime-power uniqueness proves `component_injOn`, hence the actual image `X = P.image (fun p => p ^ e p)` has cardinality nine. Products and sums transfer through this injection; distinct-base semantics are retained.
2. **Exact ratio and closure.** The full identity gives `componentRatio (2 ^ a) * ∏ x ∈ X, componentRatio x = 2`, where the rational ratio is `(x + 1) / x`. Primality makes the relevant denominator factors nonzero. `successor_prime_mem` derives odd-prime successor closure from the same identity.
3. **Unbounded envelopes.** `sorted_component_lower` transfers count bounds below a threshold to sorted actual entries. `sorted_last_lower` transfers the existential large-component bound to the last entry. Antitonicity of the positive ratio then gives the product upper bound. Repeated auxiliary envelope entries only relax the comparison class; actual components remain distinct.
4. **Finite interval classification, not global enumeration.** `odd_prime_power_lt_thirty_seven` classifies exactly the values below 37. Its local bounds on the base and exponent are consequences of that interval condition, not restrictions on the principal theorem. The finite checks use `decide`, not `native_decide`.
5. **Base three.** If base three is absent, closure and prime uniqueness force every component to be one modulo three. The envelope `[7,13,19,25,25,25,25,25,25]` has exact ratio below two at `a = 11`, contradicting the identity. This branch does not need the large-component bound.
6. **Exponent one or two.** If actual components three and nine are both absent, the envelope `[5,7,11,13,17,19,23,25,32769]` contradicts the ratio. Prime-power uniqueness therefore restricts the actual base-three exponent to one or two.
7. **Force actual five and seven in the exponent-two branch.** The corresponding omitted-component envelopes give actual exponent-one components five and seven, not merely their bases.
8. **Derive the three-adic budget.** `ordinary_valuation_budget` applies `padicValNat` to the full identity with explicit nonzero factors and prime guards. Transport to `X` gives total successor budget two when `e 3 = 2`. Numeric valuations are certified by divisibility and nondivisibility of successive powers via `valuation_eq_of_pow_dvd`, rather than an unchecked executable valuation.
9. **Exclude absent eleven.** Actual five consumes one unit; actual seventeen is impossible, and twenty-three and twenty-nine cannot both occur. Distinct bases also exclude further powers of three and five. The derived full envelope `[5,7,9,13,19,23,31,37,32769]` has ratio below two at `a = 11`, so actual eleven must occur.
10. **Exclude present eleven.** Five and eleven exhaust the two-unit budget. The binary successor is coprime to three, forcing even `a`, hence `12 ≤ a`. Every component other than nine is coprime to three; the remaining successor constraints give the final envelope `[5,7,9,11,13,19,31,37,32769]`. Its exact ratio is below two at `a = 12`, excluding exponent two. The principal theorem combines the branches to conclude `3 ∈ P ∧ e 3 = 1`.

All exact rational envelope inequalities are checked by Lean. The mathematical work is the derived domination and branch exclusion, not just evaluation of those products. Representation/API infrastructure consists of the actual-component image, sorted-finset transfer, product/sum transport, and guarded valuation lemmas.

## Scope, satisfiability, and downstream use

The complete exactly-nine class's joint satisfiability is **not exhibited and is unknown in this work**. This is an explicit limitation, not a claim that the complete hypotheses have a model. `P.card = 9` makes the intended finite domain nonempty and the exponent and prime hypotheses are not quantified only over an empty set. Nevertheless, nonemptiness of the support alone does not establish satisfiability of the full identity together with all bounds.

The checked `sixty_model` witnesses the ordinary identity, odd primality, and positive exponents for the unitary-perfect number 60 with odd components three and five. `repeated_envelope_model` witnesses the sorted-envelope infrastructure with repeated lower-bound entries. `two_budget_model` witnesses a joint two-unit successor-budget model with actual values five, seven, nine, and eleven. None is presented as a complete nine-odd witness.

This is a **necessary-condition theorem**, not global exclusion, existence, or contemporary novelty certification. Section 9 is an informal downstream consumer only: it can use actual `3¹` to obtain its one-unit three-adic budget and pursue further reductions. This module does not formalize Section 9, settle its no-actual-five branch, or certify a global nine-odd exclusion.

## Verification and cleanup evidence

Episode: `01a127d7-126c-7a54-9269-c14a7a27a755`.
Final source SHA-256 recorded at `2026-10-11T00:20:23Z`:
`e9976f06b8c922528ac79bdcd9665b69ae5e7b0b26b743d3af23d3cded9fcfcc`.

Incremental production commands were bounded narrow builds:

```sh
timeout --kill-after=2s 60s lake -q build +Erdos.Unitary1052NineOddReduction
```

Tasks `nine-build10`, `nine-build11`, and `nine-build12` returned successful completion notifications; `nine-build12` included the complete principal theorem. Earlier build failures were repaired locally (including valuation computability and membership elaboration). Full console logs for those earlier tasks were not separately preserved; they are not substituted for the preserved fresh closeout checks below.

The original audit output was found in `/tmp/nine-odd-audit-01a127d7.log`. Since that log alone did not preserve its command exit status, a fresh bounded audit was run:

```sh
timeout --kill-after=2s 60s lake env lean -j 1 -M 4000 Proofs/Scratch/NineOddAudit.lean
```

Fresh audit task: `nine-closeout-audit`.
Full preserved output: `/tmp/nine-odd-closeout-audit-01a127d7.log`.
Result: `AUDIT_EXIT_STATUS=0`. It printed the expanded signature above and:

```text
'Erdos1052.NineOdd.three_mem_and_exponent_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1052.NineOdd.two_budget_model' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1052.NineOdd.sixty_model' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only the owned temporary leaf `Proofs/Scratch/NineOddAudit.lean` was removed after the successful audit. Production contains no audit imports or `#check`/`#print` commands. A source scan at `2026-10-11T00:20:23Z` found no `sorry`, `axiom`, `native_decide`, `#check`, `#print`, `#eval`, `implemented_by`, `extern`, or `csimp` matches. No other scratch file was removed.

The final fresh production re-elaboration (not merely a cached Lake target) uses:

```sh
timeout --kill-after=2s 60s lake env lean -j 1 -M 4000 Proofs/Erdos/Unitary1052NineOddReduction.lean
```

Task: `nine-closeout-fresh-compile`.
Full output and explicit exit status: `/tmp/nine-odd-closeout-compile-01a127d7.log`.
Result: `FRESH_COMPILE_EXIT_STATUS=0`, with no compiler warnings or errors.
Started `2026-10-11T00:20:30Z`; completed `2026-10-11T00:20:46Z` (16 seconds by the recorded wall-clock timestamps).

```text
FRESH_COMPILE_START=2026-10-11T00:20:30Z
FRESH_COMPILE_EXIT_STATUS=0
2026-10-11T00:20:46Z
```

Closeout began with a recorded inspection at `2026-10-11T00:20:05Z`; these are observed timestamps, not an invented total campaign effort estimate.

The coordinator will independently audit the imported signature and axioms in its own campaign workspace. Compilation, this agent's axiom audit, semantic correspondence, and the unproved complete-class satisfiability question are distinct checks. No ledger, reference artifact, or manual revision operation was performed in closeout.
