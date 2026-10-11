# Global divisor-terminal contraction: Lean handoff

## Exact checked unit

`Combinatorics.DivisorTerminalContraction` exports
`DivisorTerminalContraction.prod_lt_prod_terminals`:

For any nonempty `Q : Finset ℕ`, assume

* `∀ p ∈ Q, Odd p ∧ 3 ≤ p`;
* `∀ p₁ ∈ Q, ∀ p₂ ∈ Q, ∀ q ∈ Q,
  q ∣ p₁ + 1 → q ∣ p₂ + 1 → p₁ = p₂`.

With `terminals Q = Q.filter (fun p => ∀ q ∈ Q, ¬ q ∣ p + 1)`, it proves over ℝ

`(∏ p ∈ Q, (1 + 1 / (p : ℝ))) <
 ∏ p ∈ terminals Q, ((p : ℝ) + 1) / ((p : ℝ) - 1)`.

All objects, quantifiers, actual divisibility premises, collision uniqueness, and
strictness from the assigned contract are retained. No primality, congruence,
size cutoff, perfectness, or desired terminal count is assumed. Subtraction is
in ℝ after casting; `3 ≤ p` guards every denominator. There are no section
variables or extra instance parameters.

## Proof and nonvacuity

A private mapping lemma is composed with the actual divisor-edge wrapper. Put
`D = Q \ terminals Q`; choose one outgoing divisor `f p` for every `p ∈ D`.
Capacity gives injectivity on `D`; oddness gives `2 * f p ≤ p + 1`.
The image lies in `Q` and excludes its maximum. For
`F(p) = (p+1)/(p-1)` and `G(p) = p/(p-1)`, all factors are positive,
`G(p) > 1`, and `F(p) ≤ G(f p)` on `D`. Finite-product comparison over
the proper image, followed by cancellation of the positive product of `G`,
gives the stated strict bound. This is global for arbitrary finite supports;
there is no finite-to-infinite extrapolation or computational search.

Production examples prove `terminals {7} = {7}` and apply the public theorem to
`Q = {7}`, jointly instantiating nonemptiness, oddness, lower bounds, and
capacity. A disposable audit also proved `8/7 < 4/3` over ℝ. This singleton is
not a perfect-number witness. Empty `Q` is excluded; empty `D` and singleton
supports are covered by the same proper-image argument, without a nonempty
`D` assumption.

## Checks and scope boundaries

Checks used bounded `tool_task` jobs:

* `timeout 60s lake -q build +Combinatorics.DivisorTerminalContraction`;
* `timeout 60s lake env lean -j 1 -M 4000 Proofs/Scratch/DivisorTerminalAudit.lean`.

The complete production module and singleton example compile without `sorry`.
The disposable imported probe checked the full public signatures and reported
exactly `[propext, Classical.choice, Quot.sound]` for both public theorems.
No `axiom`, `native_decide`, custom trusted implementation, or production
`#check`/`#print` is used. The audit leaf is removed before handoff. Initial
global-build API failures were a missing explicit finset argument to
`Finset.le_max'` and the wrong cancellation lemma; both were repaired and
checked. Tactic warnings were removed, not suppressed.

The named consumer is the independently reviewed **global ≥6 terminal-leaf
argument**, Section 4 of the corrected prose report
`/tmp/erdos-program-eunitary-corrected-01a125d8.md` (SHA256
`83ad730fd3bee24e6faa2dd711f84fa2f535978783a198fa23ffa2ee4d749904`).
In that application `Q` is the odd support with exponent exactly two, and the
edge is `p → q` iff `q ∣ p+1`. Exact residual valuation capacity one makes
incoming collisions unique. This Lean theorem supplies the global terminal
product contraction, **not** the perfect-number necessity theorem itself.

Perfectness → valuation capacity, support closure, abundance demand, and
terminal maxima → ≥6 all remain **prose, not Lean-checked**. Distinct terminal
leaves can share nonsquare sinks; unrestricted outgoing/nonsquare sink capacity
remains a mathematical gap. P2 is not solved. There is no ordinary Erdős1052
transfer or novelty claim; the exact 1986 primary source remains unavailable
and numerical-method overlap with Kolenick (2007) is not resolved here.

Fresh exact-source independent semantic review and the coordinator-owned
imported signature/axiom audit and integration/adoption gates remain unpaid.
The local audit receipt above does not replace those gates. Only this `.lean`
file and companion `.md` are production deliverables; no umbrella imports,
References, ledger, or revision operations were changed.
