# Gcd sunflower bound for an almost-prime layer

**Status: candidate for review; human review and fresh verification are pending.** This candidate is deliberately limited to the exact almost-prime layer theorem below. It is not a solution of the wider Erdős Problem #535, and no acceptance, priority, or approval is claimed.

## Exact result and formal interface

For `r,k : ℕ` with `2 ≤ r`, and a finite `A : Finset ℕ`, the principal theorem
`Erdos535.card_le_of_isAlmostPrime` states:

> if every `a ∈ A` satisfies `Nat.IsAlmostPrime k a` (in particular `a ≠ 0` and `Ω a = k`), and `A` is free of `r` elements whose pairwise gcds are all equal, then
> `A.card ≤ (r - 1)^k * k!`.

Here `EqualPairwiseGcd S` means that every two distinct pairs from `S` have the same `Nat.gcd`; `GcdPatternFree r A` means that no member of `A.powersetCard r` has this property. Thus the positivity and multiplicity-counted `Ω` hypotheses are part of the theorem, not implicit conventions.

The reduction uses `layerSet N a`, the finite set of prime powers `q ≤ N` such that `q` is a prime power and `q ∣ a`. The source proves `layerSet_inter`, namely `layerSet N a ∩ layerSet N b = layerSet N (Nat.gcd a b)`, and `card_layerSet`, which identifies its cardinality with `Ω a` when `a ≠ 0` and `a ≤ N`. `layerSet_injOn` supplies injectivity on `1 ≤ a ≤ N`. These declarations transfer an equal-gcd tuple to a sunflower and invoke the repository theorem `erdos_rado_sunflower_same_card`.

Related declarations are `gcdSunflowerNumber` (the supremum of achievable cardinalities), `gcdSunflowerNumber_le`, and `gcdSunflowerNumber_one`: the bound is sharp at `k = 1`, where the value is `r - 1`, witnessed by distinct primes. `fgcd` defines the finite-interval version of `f_r(N)`. The source also proves
`fgcd r N ≤ (log₂ N + 1) · (r - 1)^(log₂ N) · (log₂ N)!`, but explicitly records that this is weaker than the trivial `fgcd r N ≤ N` and does not estimate Problem #535 effectively.

## Contribution and attribution

The mathematical encoding is classical, not a new theorem. The recovered #535 source attributes the underlying argument to Erdős (1964), and records Erdős (1973) as the source of the stronger auxiliary formulation using `Ω` (prime factors with multiplicity). A later reply by Thomas Bloom explicitly says that the detailed encoding is the argument sketched by Erdős and that improved sunflower bounds can be inserted. Abbott–Hanson’s 1970 bound is relevant background for the broader problem, not a consequence of this file.

The credible contribution is a machine-checked Lean artifact for the gcd-to-prime-power-layer reduction, consuming a formal Erdős–Rado sunflower bound. A bounded prior-formalization search recovered the 2021 Isabelle/AFP formalization of the sunflower lemma and the repository’s corresponding Erdős–Rado development, but no earlier formalization of this specific gcd reduction. This supports only cautious “new artifact in this repository” wording, never a global-first claim.

## Scope limitations and evidence

This theorem is weaker than the corrected auxiliary statement discussed in the recovered #535 evidence: it drops that statement’s coprime-quotient side condition by forbidding *all* equal-pairwise-gcd tuples, and it proves the Erdős–Rado `(r - 1)^k k!` bound rather than the open `c_r^k` strengthening. The interval form therefore does not solve the open estimation problem. Rankin/smooth–rough estimates and the sharper `N`-asymptotics are absent.

Evidence recovered for this README is direct source inspection plus the saved campaign reports and policy notes. No Lean elaboration, build, test, Comparator run, or fresh axiom audit was performed in this recovery, by instruction; the source’s embedded examples and audit commands are not treated as independently verified results.

## Concrete next obligations

1. In the pinned package, a prover must compile the target and inspect the exact declarations and dependencies, then perform an independent allowed-axiom audit (including the imported Erdős–Rado theorem).
2. Prepare an independent, small Challenge statement for the exact layer theorem, a Solution bridge, an allowlisted Comparator configuration, and `formalization.yaml`; none is prepared here.
3. Confirm Challenge/Solution statement alignment and package compatibility, and document any reliance on classical choice or other configured axioms.
4. Resolve the full Er64/Er73 page-level citations, the incomplete Abbott–Hanson bibliography lead, and the scope of prior formalizations. Human mathematical review remains required before any submission decision.
