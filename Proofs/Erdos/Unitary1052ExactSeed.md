# Separately identified successor: exact small-seed exponent

Production module: `Proofs/Erdos/Unitary1052ExactSeed.lean`, importing the unchanged finalized transfer module. The transfer source SHA256 matches exact revision `20d93977ac7690b8f3c91b1f3cac7e75a00b82e2`: `eb83ee6313fc547a9a54737c55de03dae5c078398abc5bdf251fdfb7fd12da19`. No previous public statement or hypothesis changed.

New public symbols:
- `Erdos1052.component_exponent_eq_one_of_lower_bound`
- `Erdos1052.fixed_core_seed_exponent_eq_one`

Exact successor contract: retain every fixed-core component hypothesis and the exact canceled natural-number identity of `fixed_core_square_component_transfer`; require membership `i ∈ s`, `q i = 11 ∨ q i = 19`, and explicit analytic INPUT `P < 705`; conclude `c i = 1`. Thus the component's exponent `2*c i` is exactly two. The faithful consumer **derives** the lower bound from the retained transfer theorem; it does not assume transfer or the lower bound.

Proof: target congruence supplies mod four equal to three; component positivity supplies `0 < c i`. If c differs from one, `4 ≤ 2*c`. Verified `Nat.pow_le_pow_right` and `Nat.pow_le_pow_left` give `11^4 ≤ q^4 ≤ q^(2*c)`. Therefore `29282 ≤ 2*q^(2*c) ≤ P+1 ≤ 705`, a contradiction. The arithmetic helper uses q≥11, positive c, P<705, and the numerical lower bound. All objects/quantifiers and full fixed-core hypotheses survive unchanged in the consumer. No new definitions, representation changes, valuation claims, infrastructure, or delegation.

Nonvacuity/boundary evidence: a kernel-checked model jointly satisfies every helper hypothesis at q=11,c=1,P=241. A checked boundary example shows c=0 can satisfy the numerical bound but is explicitly excluded by positivity. Index membership and the inherited transfer's empty-index example exclude vacuous index selection. Full fixed-core identity satisfiability remains unestablished, as explicitly authorized; no model is fabricated.

`P < 705` is unpaid upstream analytic-envelope input. This successor does not prove that bound, any Euler envelope, the 100/99 input, P=73 bootstrap, companion forcing, or seed closure. The stronger exclusion of a 19-component under this same bound is not formalized here. Remaining integration: instantiate this consumer in exact-small-seed analysis and discharge/retain the upstream analytic input separately. Review and adoption remain parent-owned.

## Final checks

Both commands exited 0. Final production build had no warnings, errors, or stdout:

```sh
timeout --kill-after=2s 60s lake -q build +Erdos.Unitary1052ExactSeed
timeout --kill-after=2s 60s lake env lean -j 1 -M 4000 Proofs/Scratch/Unitary1052ExactSeedAudit.lean
```

The disposable audit imported only `Erdos.Unitary1052ExactSeed`, set `autoImplicit false`, checked the two power APIs and new full signatures, and printed axioms for both new and all three retained theorems. Audit removed after preserving stdout below. No scratch audit is imported by production; no sorry, custom axiom, native_decide, or external implementation is used. Helper axioms are a subset of the standard trio; consumer and retained theorem axioms are exactly the standard trio.

Actual implementation feedback: first narrow build reported two redundant `decide` steps after `rw` had already closed numeral-congruence goals. Removing those redundant steps produced the successful build and audit; no mathematical repair was needed.

```text
@Nat.pow_le_pow_right : ∀ {n : ℕ}, n > 0 → ∀ {i j : ℕ}, i ≤ j → n ^ i ≤ n ^ j
@Nat.pow_le_pow_left : ∀ {n m : ℕ}, n ≤ m → ∀ (i : ℕ), n ^ i ≤ m ^ i
Erdos1052.component_exponent_eq_one_of_lower_bound : ∀ (q c P : ℕ),
  11 ≤ q → 0 < c → P < 705 → 2 * q ^ (2 * c) ≤ P + 1 → c = 1
@Erdos1052.fixed_core_seed_exponent_eq_one : ∀ {ι : Type u_1} (s : Finset ι) (q c : ι → ℕ) (a p e P : ℕ) (i : ι),
  Even a →
    12 ≤ a →
      Nat.Prime p →
        13 < p →
          p % 24 = 1 →
            0 < e →
              Odd e →
                P = p ^ e →
                  (∀ j ∈ s, Nat.Prime (q j) ∧ Odd (q j) ∧ q j ≠ 3 ∧ q j ≠ 5 ∧ q j ≠ 7 ∧ q j ≠ 13 ∧ q j ≠ p ∧ 0 < c j) →
                    Set.InjOn q ↑s →
                      (2 ^ a + 1) * (P + 1) * ∏ j ∈ s, (q j ^ (2 * c j) + 1) =
                          2 ^ (a - 6) * 65 * P * ∏ j ∈ s, q j ^ (2 * c j) →
                        i ∈ s → q i = 11 ∨ q i = 19 → P < 705 → c i = 1
'Erdos1052.component_exponent_eq_one_of_lower_bound' depends on axioms: [propext, Quot.sound]
'Erdos1052.fixed_core_seed_exponent_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1052.not_dvd_sq_add_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1052.square_component_transfer' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1052.fixed_core_square_component_transfer' depends on axioms: [propext, Classical.choice, Quot.sound]

```
