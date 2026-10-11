# E-unitary exponent-12 obstruction — normalized theorem complete

**Status:** the full all-positive-`b` normalized contradiction is kernel-checked. The actual-number class theorem remains unpaid at its factorization bridge. The coordinator-owned `Proofs/Erdos/EUnitaryP1TwelveFamily.md` is not modified here; no independent review or adoption is claimed.

## Exact completed contract

Namespace `EUnitaryP1` exports:

```lean
theorem normalized_ne (b : ℕ) (S : Finset ℕ) (hb : 0 < b)
    (hS : ∀ q ∈ S, q.Prime ∧ q ≠ 2 ∧ q ≠ 3) :
    2061 * localA 3 b * (∏ q ∈ S, (q + 1)) ≠
      2 ^ 12 * 3 ^ (b - 1) * (∏ q ∈ S, q)
```

Objects, quantifiers, side conditions, and conclusion survive unchanged. No support-size, valuation, forced-base, capacity, or exponent-cap certificate is a premise of this theorem. The six-element budget is an internal consequence of the supposed identity, not a surrogate for it. This completes the assigned normalized implication available to the intended `sigmaEU_twelve_class_ne` consumer.

## Objects and boundary checks

- `exponentDivisors a = a.divisors.filter (fun d => Nat.Coprime d (a / d))` is exponential-unitary exponent support, not ordinary unitary divisibility of the number. Membership proves `0 < d` and `d ∣ a`.
- `localA p a = ∑ d ∈ exponentDivisors a, p^(d-1)` uses positive exponent divisors; its zero-exponent support is empty.
- `sigmaEU n` is zero by explicit convention at zero, otherwise the product over actual `n.primeFactors` of the corresponding sums at `n.factorization p`. It is not a ratio surrogate.

Ground-truth examples check zero/one exponent supports, the exponent-twelve factor, `sigmaEU 0`, `sigmaEU 1`, and `sigmaEU 4 = 6`. The prime-power characterization relates the definition to the actual function. An example jointly instantiates the intended class side conditions at empty support, `b=t=1`, with squarefreeness and coprimality. Empty support is allowed, while the ambient natural-number domains are nonempty. The final normalized theorem is also instantiated at `b=1`, empty support; thus its actual hypotheses are jointly satisfiable. Parity and tail hypotheses have concrete examples at `b=2` and `b=7`. Conditional helper lemmas that assume the impossible normalized identity are deliberately contradiction steps, not purported satisfiable perfect-number models.

Natural subtraction is guarded: the public theorem has positive `b`; residual `b-5` uses the internally proved `5 ≤ b`; the tail has `7 ≤ b`; each exponent divisor is positive. Rational ratio denominators are primes and hence positive. No new definitions or altered arithmetic conventions were introduced in the continuation.

## Checked argument

1. `local_sum_eq`, `sigmaEU_prime_pow`, and the exact local values establish the infrastructure: `localA 2 12 = 2061`, `localA 3 5 = 82`, `localA 3 6 = 256`.
2. The normalized identity forces `229,5,23 ∈ S` and `5 ≤ b`. Splitting off these bases yields, for `U = S \ {229,5,23}`,
   ```text
   localA 3 b * ∏q∈U (q+1) = 128 * 3^(b-5) * ∏q∈U q.
   ```
3. Existing boundary lemmas exclude `b<5`, `b=5`, and `b=6`. The five case uses the forced-41 chain; the six case uses an odd denominator.
4. `localA_three_even` pairs complementary exponent divisors by `d ↦ b/d` in `ZMod 2`. Coprimality excludes a fixed point when `1<b`. Every summand is one modulo two, so `2 ∣ localA 3 b`.
5. `normalized_residual_card_le` obtains one additional factor of two from each residual successor. Cancelling against the odd denominator gives `2^(U.card+1) ∣ 2^7`, hence `U.card ≤ 6`. No valuation oracle or size assumption is used.
6. `residual_ratio_le` proves the exact envelope
   ```text
   ∏q∈U (q+1)/q ≤ 2073600/1339481.
   ```
   Put `C=30/29` and divide each ratio by `C`. Outside `{7,11,13,17,19}`, the allowed primes are at least 29, so these adjusted factors are at most one. Inside that set they are at least one. Filtering and extending the finite product, followed by `U.card ≤ 6`, bounds it by the six-smallest-primes product (including 29). The elementary exclusions below 29 are proof-producing finite arithmetic, not a new range search.
7. `localA_three_tail_lt` proves, for `7 ≤ b`,
   ```text
   54 * localA 3 b < 55 * 3^(b-1).
   ```
   Every proper exponent divisor is at most `b/2`. Its map `d ↦ d−1` is injective into `range (b/2)`. A checked geometric-sum identity bounds the tail; `(b/2)+3 ≤ b−1` supplies the strict leading-term comparison.
8. `normalized_identity_false_of_seven_le` combines the residual identity, positive denominator, exact envelope, and strict tail bound. The final integer comparison is `54*128*1339481 > 4455*2073600`. `normalized_ne` combines this with the boundary cases and excludes every positive exponent.

## Exact unpaid bridge

For positive `b,t`, squarefree `t`, prime support excluding two and three, and `Nat.Coprime t (6 * ∏q∈S,q)`, still prove

```text
sigmaEU (t * 2^12 * 3^b * ∏q∈S,q^2)
  = t * (2*2061) * (3*localA 3 b) * ∏q∈S, q*(q+1).
```

Disjoint-support/factorization infrastructure and exponent-one stripping are needed, followed by cancellation of positive factors to obtain the normalized identity from `sigmaEU n = 2*n`. Only the individual prime-power characterization is finished. The intended actual-number theorem `EUnitaryP1.sigmaEU_twelve_class_ne` is not declared or proved. No placeholder or strengthened class theorem hides this gap.

## Verification and provenance

The immutable reviewed inputs were read and their SHA256 hashes matched `af07f08458abafa2e633b9fdd1490d8899d66a945885d73dedfaa132171ade12` and `351f636e74ab337856bb3599aa2b228a55d66351691a9d6f96e3c2c4067821f6`.

The narrow build is `timeout 60s lake -q build +Erdos.EUnitaryP1TwelveObstruction`. A separate disposable leaf imports the result, checks all 27 full public signatures, and prints their axiom dependencies; it is never imported into production. Every dependency report is exactly `{propext, Classical.choice, Quot.sound}`. Output is retained at `/tmp/eunitary-p1-continuation-audit-01a127d7.log`, a temporary receipt rather than a proof dependency. There are no `sorry`s, custom axioms, native decision procedures, or production inspection commands. Arithmetic uses kernel `decide`, proof-producing `norm_num`, and checked tactic proofs.

The finishing phase used seven bounded compiler task sequences: the combined parity/cardinality and envelope probe; one rejected tail probe; corrected helper build/tail probe; final-comparison build/probe; all-positive theorem build; separate signature/axiom audit; and a fresh terminal build/audit after the final non-vacuity example. Six passed; the rejected tail probe exposed a missing division simplification and unreduced injectivity hypothesis, both repaired locally before proceeding. Earlier continuation repairs addressed involution casts and residual-product rewriting. Successful quiet checks did not print wall times; runtime/model billing is unavailable. The original partial episode's ten build invocations remain historical evidence, not verification of the newly completed theorem. No workers, Sage experiment, mathematical range search, or cold finite computation ran.

Only this `.lean` and `.md` are deliverables. Disposable probe/audit leaves are removed after the terminal check. No umbrella, References, Ledger, publication, integration, adoption, or revision movement is performed. Elaboration, translation checks, non-vacuity witnesses, and axiom auditing are separate evidence; independent semantic review remains with the coordinator.
