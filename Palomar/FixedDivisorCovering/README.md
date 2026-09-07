# Fixed-divisor covering criterion for affine-exponential families

## Claim and scope

This candidate groups the reusable development in `Proofs/Erdos/Covering/FixedDivisor.lean` with its Sierpiński and Riesel applications. For a finite certificate `T : Finset (ℕ × ℕ × ℕ)` of triples `(a,d,p)`, the predicate `IsFixedDivisorSystemBase b A B T` records four conditions: every listed divisor satisfies `1 < p`; the classes `n ≡ a (mod d)` cover the exponents; `b^d ≡ 1 (mod p)`; and `p ∣ A b^a + B`. The resulting theorem says that every value `A b^n + B` has a divisor among `fixedDivisors T`. The compositeness corollaries additionally require an explicit bound `p ≤ M < N`; divisibility alone does not imply compositeness.

The development is deliberately over `ℤ`, so the same theorem handles `k·b^n+1`, `k·b^n-1`, and `m-b^n` without informal subtraction side conditions. The base-2 predicate is retained and connected by `isFixedDivisorSystem_iff_base_two`; the arbitrary-base criterion is not a second bespoke proof.

## Principal declarations and applications

The core API includes `residueClasses`, `fixedDivisors`, `isFixedDivisorSystemBase_iff`, `pow_intModEq_pow_mod`, `pow_intModEq_of_mod_eq`, `dvd_affine_pow_of_mod_eq`, and `IsFixedDivisorSystemBase.exists_mem_fixedDivisors_dvd`, together with `.composite` and `.not_prime`. Transport lemmas `.of_dvd_sub_const` and `.of_dvd_sub_coeff` turn one certificate into arithmetic progressions in the constant or coefficient. `.of_modEq_base` transports a certificate to bases congruent modulo every listed divisor.

`Sierpinski.lean` instantiates the framework with Selfridge’s seven-class certificate for `78557·2^n+1`, proving `isSierpinskiNumber_78557`, its coefficient progression, and infinitude. Its arbitrary-base layer proves `4` is a Sierpiński number in base `14`, with a two-class certificate, the associated progression, and infinitude. `Riesel.lean` similarly treats `509203·2^n−1`, its progression and infinitude, and the base-6 witness `84687`. The latter also formalizes the base transport statement for `6` whenever `b ≡ 34 (mod 35)`, yielding infinitely many suitable bases.

The base-14 case preserves an important erratum: `4·14^0+1=5` is prime. The declaration `not_composite_four_mul_fourteen_pow_zero_add_one` records why the base predicate starts at `n ≥ 1` and why the proper-divisor inequality in `.composite` is load-bearing. The draft also records a dated sign discrepancy in the cited Riesel base definition; the formalized predicate uses the mathematically consistent `gcd(k−1,b−1)=1` condition.

## Contribution and attribution

The concrete numbers are not claimed as new. Selfridge’s `78557` and Riesel’s `509203` predate this work; Cowles–Gamboa, “Verifying Sierpiński and Riesel Numbers in ACL2” (EPTCS 70, 2011; arXiv:1110.4671), machine-verified both. A bespoke Lean proof of `78557` also exists in `google-deepmind/formal-conjectures`. The proposed contribution is the coherent, reusable arbitrary-base certificate theorem and its transport API, from which the applications become instances. The bounded searches recorded in the source material found no matching general proof-assistant criterion, but that is not a priority or first-formalization claim.

## Evidence, limitations, and next obligations

Evidence recovered for this README is source inspection and the existing declarations/comments, not a fresh compilation, axiom audit, or independent proof review. No acceptance, global-priority, or human-approval claim is made. The source itself reports sorry-free declarations and kernel `decide` checks, but those reports remain unverified in this recovery.

Before any Palomar submission, a prover should compile the pinned modules, inspect principal declarations and axioms, check statement alignment (especially natural subtraction and the `n ≥ 1` conventions), and independently recheck the certificate tables and transport hypotheses. A package maintainer must then prepare the required small Challenge, Solution bridge, Comparator configuration, and `formalization.yaml` under the current registry policy. External source snapshots and dated erratum claims should be re-fetched before publication. Human review remains pending; no submission or publication is authorized by this README.
