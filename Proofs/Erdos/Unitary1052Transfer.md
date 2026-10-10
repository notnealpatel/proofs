# Selected contract (before Lean implementation)

Consumer contract, with `s : Finset ι`, `q c : ι → ℕ`, `i ∈ s`:
`Even a`, `12 ≤ a`, `Nat.Prime p`, `13 < p`, `p % 24 = 1`,
`0 < e`, `Odd e`, `P = p ^ e`,
`∀ j ∈ s, Nat.Prime (q j) ∧ Odd (q j) ∧ q j ≠ 3 ∧ q j ≠ 5 ∧ q j ≠ 7 ∧ q j ≠ 13 ∧ q j ≠ p ∧ 0 < c j`,
`Set.InjOn q (↑s : Set ι)`,
`(2^a+1)*(P+1)*(∏ j ∈ s, (q j^(2*c j)+1)) = 2^(a-6)*65*P*(∏ j ∈ s, q j^(2*c j))`,
and `q i % 4 = 3` imply
`q i^(2*c i) ∣ P+1 ∧ 2*q i^(2*c i) ∣ P+1 ∧ 2*q i^(2*c i) ≤ P+1`.

General transfer unit: replace RHS scalar `2^(a-6)*65*P` by arbitrary `R`; retain `Even a`, `Odd P`, `Nat.Prime (q i)`, `q i % 4 = 3`, and `i ∈ s`. Other components need not be prime. Exponents may be zero. This is a genuine generalization, not a transfer assumption. Prime nondivisibility of square-plus-one comes from `ZMod.mod_four_ne_three_of_sq_eq_neg_sq'`.

Source inspection: exact revisions 62dae66fcf92bdc82df1d8b10e161278c4351aa0 (`Argument.md`), 5c8a52bb4cb6081e3dbd9254d499e5a62e1b445e (`Argument-t5-successor.md`), c60ce391e271e9b612265c6f9de07bf00e29e6fa (`Argument-t5-successor.md`, applicability note) all available. No immutable input edited.

Nonvacuity limitation: no concrete full fixed-core canceled-identity model is known here. It would represent precisely an unresolved candidate. The general transfer unit will have a jointly satisfying nonempty, positive-exponent concrete example. The full-core hypotheses are preserved as the intended conditional consumer contract, not asserted to be jointly satisfiable.

## Checked output and translation evidence

Production file: `Proofs/Erdos/Unitary1052Transfer.lean`.

Public symbols:
- `Erdos1052.not_dvd_sq_add_one`
- `Erdos1052.square_component_transfer`
- `Erdos1052.fixed_core_square_component_transfer`

The full wrapper preserves the objects, quantifiers, full fixed-core assumptions, finite membership, exact natural-number identity, and all three requested conclusions. No transfer, coprimality, or valuation conclusion is assumed. Distinctness is expressed as `Set.InjOn q ↑s`; all exclusion and positive-exponent assumptions are retained. `12 ≤ a` guards the natural subtraction in the identity. The prime/mod-four argument is a genuine application of the Mathlib finite-field obstruction, via `ZMod`.

Unused assumptions in this weaker conclusion: the lower bound on a, primality/lower bound on p, positivity/oddness of e, distinctness, exclusions, other-component primality/oddness, and positive component exponents. They are not needed because the RHS scalar is arbitrary, every even power is a square, and membership supplies the indexed factor regardless of duplicates. `p % 24 = 1` alone supplies odd p, hence odd P for any e. Target oddness follows from its mod-four residue. These unused hypotheses are kept in the faithful wrapper, not deleted. Exact valuation would need more of them and is not claimed.

Nonvacuity: the generalized premises jointly hold in the checked model `ι = Fin 1`, `s = {0}`, `q = 11`, `c = 1`, `a = 12`, `P = 241`, `R = 999668`. A second checked model covers c = 0, Q = 1. A checked example rules out membership in an empty index finset. Full fixed-core identity satisfiability remains **unestablished**; this is a conditional theorem, not evidence that an unresolved candidate exists. No arbitrary instances on concrete arithmetic types are supplied.

Remaining consumer work: apply this wrapper at q_i = 11 or 19; combine with the separately established conditional bound P < 705 and positive c_i to obtain c_i = 1; then analyze the exact 11²/19² seed configurations. This module neither proves P < 705 nor an Euler-product/100/99 estimate, exact valuation, forced 61/181 companions, global classification, or seed closure. Independent review/adoption remains parent-owned.

### Final check receipts

Commands, both exit status 0; final production build had no warnings/errors/output:

```sh
timeout --kill-after=2s 60s lake -q build +Erdos.Unitary1052Transfer
timeout --kill-after=2s 60s lake env lean -j 1 -M 4000 Proofs/Scratch/Unitary1052Probe.lean
```

The temporary audit imported only `Erdos.Unitary1052Transfer`, set `autoImplicit false`, checked the APIs and all three full theorem signatures, and printed each theorem's axioms. It also checked 11 and 19 primality and mod-four residue with `decide`. The audit source was removed after recording this output; no production `#check`/`#print` commands or extra audit imports remain. No `sorry`, custom axiom, native decision procedure, or external implementation is used. Exact audit stdout follows:

```text
@ZMod.mod_four_ne_three_of_sq_eq_neg_sq' : ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {x y : ZMod p},
  y ≠ 0 → x ^ 2 = -y ^ 2 → p % 4 ≠ 3
@Nat.Prime.coprime_iff_not_dvd : ∀ {p n : ℕ}, Nat.Prime p → (p.Coprime n ↔ ¬p ∣ n)
@Nat.coprime_prod_right_iff : ∀ {ι : Type u_1} {x : ℕ} {t : Finset ι} {s : ι → ℕ},
  x.Coprime (∏ i ∈ t, s i) ↔ ∀ i ∈ t, x.Coprime (s i)
@Finset.dvd_prod_of_mem : ∀ {ι : Type u_1} {M : Type u_2} [inst : CommMonoid M] (f : ι → M) {a : ι} {s : Finset ι},
  a ∈ s → f a ∣ ∏ i ∈ s, f i
@Nat.Coprime.dvd_of_dvd_mul_left : ∀ {k m n : ℕ}, k.Coprime m → k ∣ m * n → k ∣ n
@Nat.Coprime.mul_dvd_of_dvd_of_dvd : ∀ {m n a : ℕ}, m.Coprime n → m ∣ a → n ∣ a → m * n ∣ a
@Nat.le_of_dvd : ∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
Erdos1052.not_dvd_sq_add_one : ∀ (q x : ℕ), Nat.Prime q → q % 4 = 3 → ¬q ∣ x ^ 2 + 1
@Erdos1052.square_component_transfer : ∀ {ι : Type u_1} (s : Finset ι) (q c : ι → ℕ) (a P R : ℕ),
  ∀ i ∈ s,
    Even a →
      Odd P →
        Nat.Prime (q i) →
          q i % 4 = 3 →
            (2 ^ a + 1) * (P + 1) * ∏ j ∈ s, (q j ^ (2 * c j) + 1) = R * ∏ j ∈ s, q j ^ (2 * c j) →
              q i ^ (2 * c i) ∣ P + 1 ∧ 2 * q i ^ (2 * c i) ∣ P + 1 ∧ 2 * q i ^ (2 * c i) ≤ P + 1
@Erdos1052.fixed_core_square_component_transfer : ∀ {ι : Type u_1} (s : Finset ι) (q c : ι → ℕ) (a p e P : ℕ) (i : ι),
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
                        i ∈ s →
                          q i % 4 = 3 →
                            q i ^ (2 * c i) ∣ P + 1 ∧ 2 * q i ^ (2 * c i) ∣ P + 1 ∧ 2 * q i ^ (2 * c i) ≤ P + 1
'Erdos1052.not_dvd_sq_add_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1052.square_component_transfer' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1052.fixed_core_square_component_transfer' depends on axioms: [propext, Classical.choice, Quot.sound]

```
