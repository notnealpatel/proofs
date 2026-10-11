# E-unitary exponent-12 obstruction — actual class theorem complete

**Status:** both the full all-positive-`b` normalized contradiction and the actual-number class theorem are kernel-checked. The squarefree/factorization bridge is now proved from the actual `sigmaEU` definition; it is not an added premise. The coordinator-owned `Proofs/Erdos/EUnitaryP1TwelveFamily.md` is not modified here; no independent review or adoption of this new bridge candidate is claimed.

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

## Actual-number bridge and completed consumer

The new public consumer is:

```lean
theorem sigmaEU_twelve_class_ne (b t : ℕ) (S : Finset ℕ)
    (hb : 0 < b) (ht : 0 < t)
    (hS : ∀ q ∈ S, q.Prime ∧ q ≠ 2 ∧ q ≠ 3)
    (hsq : Squarefree t) (htc : Nat.Coprime t (6 * ∏ q ∈ S, q)) :
    sigmaEU (t * 2^12 * 3^b * ∏ q ∈ S, q^2) ≠
      2 * (t * 2^12 * 3^b * ∏ q ∈ S, q^2)
```

Its objects, universal quantifiers, hypotheses, and conclusion match the assigned family without strengthening. In particular, no nonempty-support condition is imposed; `S=∅`, `t=1`, and `b=1` remain allowed. Neither a factorized identity nor multiplicativity nor a certificate is assumed. There is no unpaid bridge in this consumer.

Six new public lemmas supply the bridge:

1. `sigmaEU_mul_of_coprime`: multiplicativity for positive coprime natural numbers. `Nat.Coprime.primeFactors_mul` and `disjoint_primeFactors` split the actual prime support. Support membership and `Nat.factorization_mul` establish that the exponent at a prime in one factor is unchanged by the other factor.
2. `sigmaEU_eq_self_of_squarefree`: for positive squarefree `t`, every exponent on `t.primeFactors` is exactly one, by its nonzero support membership and `Squarefree.natFactorization_le_one`. The local sum is the prime itself, and `Nat.prod_primeFactors_of_squarefree` reconstructs `t`.
3. `sigmaEU_prod_of_pairwise_coprime`: finite-product multiplicativity, by induction and `Nat.coprime_prod_right_iff`. Pairwise coprimality is a standard `Set.Pairwise` predicate on the coerced finite support.
4. `sigmaEU_prod_prime_sq`: distinct primes give pairwise coprime squares. The checked prime-power and exponent-two lemmas yield `∏q∈S,q*(q+1)`.
5. `sigmaEU_twelve_class_eq`: the original side conditions imply every required coprimality, using prime exclusions and the decomposition of `Nat.Coprime t (6 * ∏q∈S,q)`. Consequently,
   ```text
   sigmaEU (t * 2^12 * 3^b * ∏q∈S,q^2)
     = t * (2*2061) * (3*localA 3 b) * ∏q∈S,q*(q+1).
   ```
6. `sigmaEU_twelve_class_ne`: suppose the actual sum equals twice the number. Let `D=t*2*3*∏q∈S,q`; positivity follows from `ht` and primality. The preceding identity, finite-product arithmetic, and the guarded equality `3^b=3*3^(b-1)` give the normalized identity after cancelling `D`. The unchanged `normalized_ne` contradicts it.

Production examples check every new helper at concrete positive inputs, including the two-element coprime product `{2,3}`. Both the empty-support consumer at `b=t=1` and the nonempty-support consumer at `b=1,t=7,S={5}` are checked. A separate conjunction jointly instantiates all class premises at the latter model. The squarefree decoration is thus demonstrably permitted to be nontrivial, and the support is not forced to be empty.

The old 27 declarations and all their examples are preserved byte-for-byte relative to reviewed revision `8026571b734469b54513870b5d42bfdc3252c101`, ignoring only two additional imports (`Mathlib.Data.Nat.Squarefree` and `Mathlib.Data.Nat.GCD.BigOperators`). The new bridge is appended before the namespace end, in a separate mutable candidate; the immutable reviewed revision is not changed.

## Verification and provenance

The immutable reviewed inputs were read and their SHA256 hashes matched `af07f08458abafa2e633b9fdd1490d8899d66a945885d73dedfaa132171ade12` and `351f636e74ab337856bb3599aa2b228a55d66351691a9d6f96e3c2c4067821f6`.

The normalized theorem's narrow build is `timeout 60s lake -q build +Erdos.EUnitaryP1TwelveObstruction`. Its separate disposable leaf checked all 27 original full public signatures and printed their axiom dependencies; that historical receipt is retained at `/tmp/eunitary-p1-continuation-audit-01a127d7.log`. The new actual-bridge candidate receives the same narrow build and a fresh, separate audit of all 33 full public signatures and axiom lists; its receipt is `/tmp/eunitary-p1-actual-audit-01a127d7.log`. Every dependency report is exactly `{propext, Classical.choice, Quot.sound}`. Audits are temporary evidence, never production imports or proof dependencies. There are no `sorry`s, custom axioms, native decision procedures, or production inspection commands. Arithmetic uses kernel `decide`, proof-producing `norm_num`, and checked tactic proofs.

The normalized-theorem finishing phase used seven bounded compiler task sequences: the combined parity/cardinality and envelope probe; one rejected tail probe; corrected helper build/tail probe; final-comparison build/probe; all-positive theorem build; separate signature/axiom audit; and a fresh terminal build/audit after the final non-vacuity example. Six passed; the rejected tail probe exposed a missing division simplification and unreduced injectivity hypothesis, both repaired locally before proceeding. Earlier continuation repairs addressed involution casts and residual-product rewriting. Successful quiet checks did not print wall times; runtime/model billing is unavailable. The original partial episode's ten build invocations remain historical evidence, not verification of the newly completed theorem. No workers, Sage experiment, mathematical range search, or cold finite computation ran.

The actual-bridge episode used ten bounded compiler task sequences: the initial multiplicativity probe; squarefree/product probe; family factorization probe; consumer probe; corrected consumer probe; model probe; corrected model probe; production build; full audit; and terminal production build/audit. Seven passed. The three rejected probes exposed, respectively, the unavailable `Finset.Pairwise` spelling, the orientation of `Finset.prod_pow`, and finite coprimality/oddness goals left by `norm_num`; each was repaired locally and rechecked. No probe timeout or mathematical blocker occurred. The terminal receipt records measured build and audit wall times of 1.42 s and 2.38 s at `/tmp/eunitary-p1-actual-terminal-01a127d7.log`; those are cached finishing costs, not a claimed cold-build benchmark. No workers, Sage experiment, or mathematical range search ran in this episode.

Only this `.lean` and `.md` are deliverables. Disposable probe/audit leaves are removed after the terminal check. No umbrella, References, Ledger, publication, integration, adoption, or revision movement is performed. Elaboration, translation checks, non-vacuity witnesses, and axiom auditing are separate evidence; independent semantic review remains with the coordinator.
