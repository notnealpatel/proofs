/-!
# A323653: multiperfect-congruence residual

DOCUMENTATION ONLY: no imports, executable declarations or admissions.
The preserved passage is the complete A323653 residual from Formalize/INDEX.
Current evidence was read from Proofs/Enumerative/MultiperfectCongruence.lean,
whose source ledger records OEIS A323653 and Karttunen's 2021/2022 comments,
with companion functions A276086 (primorial-base exponent function) and
A003961 (prime shift). Write sigma(m) for the sum of positive divisors.
IsA323653 means that m and sigma(m) are both multiperfect. The congruence
families IsA351458 / IsA349745 carry 0 < k explicitly and compare
k*gcd(sigma(k),f(k)) with sigma(k)*gcd(k,f(k)); zero would satisfy the unguarded
identities only because Nat.divisors 0 is empty.

KarttunenConjecture1c quantifies m with 1 < m and IsA323653 m, requiring a
prime q not dividing m, every smaller prime dividing m, and sigma(m) = q*m;
it does not use totalized natural division. KarttunenConjecture3 asserts the
A007691/A351458 intersection equality, and KarttunenConjecture4 the A349745
inclusion. These named Props are statements, not full proofs. Production has
ground witnesses and conditional results, not the universal assertions or
finiteness. Those exact universal/distribution implications remain the blocker;
this module neither reproves the existing predicates nor admits their truth.

## Formalize/INDEX — complete A323653 residual (verbatim)

```text
- **A323653:** `Proofs/Enumerative/MultiperfectCongruence.lean` already defines `IsA351458`, `IsA349745`, `IsA323653`, and `KarttunenConjecture1c`, `KarttunenConjecture3`, and `KarttunenConjecture4`, with ground and conditional results. These propositions are not proofs. The least-nonfactor-prime assertion, finiteness, the A007691/A351458 intersection equality, and the A349745 inclusion remain open; do not reassign the existing predicate definitions.
```
-/
