# Nine-odd small-witness interval kernel

## Result and scope

**Complete kernel implementation**, in
`Erdos1052.NineOdd.WitnessInterval.interval_kernel`.
The theorem concludes `False` under the exact strengthened interval contract.
Actual **19 and 25 remain explicit hypotheses**. It does not import or assume a
generic forcing theorem, any actual-109 exclusion, or any actual-373 exclusion.
The only import is `Erdos.Unitary1052NineOddReduction`.

The stronger interval result without the 19/25 hypotheses requires the separately
owned generic forcing result. It is not proved or claimed here. Neither a
supplier-gap corollary, elimination of the remaining witness regimes, whole B,
nor a global 1052 result is included.

## Exact public consumer contract

The public theorem has data `a : ℕ`, `P : Finset ℕ`, `e : ℕ → ℕ`, and `x : ℕ`.
Writing `X = P.image (fun p => p ^ e p)`, its hypotheses are exactly:

```lean
P.card = 9
∀ p ∈ P, p.Prime
∀ p ∈ P, Odd p
∀ p ∈ P, 0 < e p
11 ≤ a
Even a
(2 ^ a + 1) * (∏ y ∈ X, (y + 1)) = 2 ^ (a + 1) * ∏ y ∈ X, y
3 ∈ X
7 ∈ X
11 ∈ X
13 ∈ X
19 ∈ X
25 ∈ X
5 ∉ X
∃ y ∈ X, 32768 < y
x ∈ X
373 ≤ x
x < 32769
11 ∣ x + 1
```

Conclusion: `False`. The source spells out the image instead of adding `X` as a
free parameter. There is no exponent cap, prime-base range restriction, valuation
certificate, closure premise, unique-supplier hypothesis, or assumed residual
shortlist. `5 ∉ X` is retained in the signature even though this implementation
can prove the contradiction without using it.

## Frozen input evidence

The complete new prose, certificate transcript, independent PASS review, and
coordinator complete-literal receipt were read. The supplied mathematical
artifact hashes were verified:

- `/tmp/erdos-program-nine-odd-small-witness-interval-exclusion-01a127d7.md`:
  `9b93ffb1cd724637639264027105b22530afdbf8e5ee2dd097f3022521132ef1`;
- `/tmp/erdos-nine-small-witness-interval-certificates-01a127d7.txt`:
  `d9994d3d99b17149ea99b1d1542483c4b2d8f9413962dd9c924dbc13aa999a6e`.

No frozen artifact was modified. Witness373 production files were frozen and
were not imported or edited. Their observed hashes at this continuation were:

- `.lean`: `a969561b2482c90eabd7355803b370d77825927490acacaf32648f2648795797`;
- `.md`: `7a950a7d501b3768e187e597e85bb791dbf62c0cc6ebcc4f398dffdcd85d94bc`.

Only the new WitnessInterval `.lean` and this `.md` are production changes in
this continuation. No shared-file edits, children, or other mathematical fronts
were opened.

## Formal argument and representation infrastructure

The mathematical objects, quantifiers, hypotheses, and conclusion of the
strengthened kernel are unchanged. The source implements an equivalent sorted
count argument rather than naming the two residual components `r < p`.
This is representation infrastructure, not an additional mathematical premise.

1. `base_identity` transports the exact identity on actual values to the accepted
   prime-base identity using positive-prime-power injectivity. `component_card`
   gives `X.card = 9`. All actual components are positive.
2. `actual_prime` fixes a prime actual value's base and exponent one.
   `prime_budget` transports the ordinary valuation budget to actual values.
   `exhausted` proves that a divisible successor spends a one-unit budget and
   every other successor is prime to that prime. The final consumer derives
   all these budgets from the ordinary identity; it does not assume them.
3. `mod_three` uses actual 3 and successor 12 to show that every component other
   than 3 and 11 is one modulo three. The assertion is about the **value**, not
   just the base.
4. `small_prime_power` proves the value list
   `{7,13,19,25,31,37,43,49}` for positive odd prime powers congruent to one modulo
   three and below 61. Base `p < 61` and exponent `k < 4` are derived inside this
   lemma from the value bound. Its finite check covers only 61 times 4 local
   bounded pairs. No original exponent or base is globally capped.
5. `small_actual_values` excludes 49 by the already occupied base 7 (actual 7
   fixes exponent one), and excludes 43 by the eleven-budget exhausted by the
   separate witness `x`. Thus every actual value below 61 is among
   `{3,7,11,13,19,25,31,37}`.
6. If 31 or 37 is present, `not_ratio_of_small_residual` bounds the product from
   below by the product on the fixed six together with that prime. Every other
   positive component ratio and the binary ratio is at least one. The two
   fixed partial products are strictly above two, so the exact ratio identity
   is impossible. Strictly greater-than-one bounds on omitted factors are not
   needed: the partial products already give the strict contradiction.
7. Otherwise all actual values below 61 lie among the fixed six. For indices
   zero through six, the accepted sorted-component count lemma gives lower
   bounds `3,7,11,13,19,25,61`.
8. A large component `y ≥ 32769` is distinct from `x < 32769`. Both `x` and `y`
   are at least 373. `count_below_of_two_large` removes these two distinct
   members from the nine-element set and proves that at most seven values are
   below 373. This gives the eighth sorted lower bound 373; the largest-component
   lemma gives the ninth lower bound 32769. This precisely replaces the
   seven-fixed/two-residual allocation. It works even when both residual
   components are large, and never creates a slot from a base collision.
9. Even `a` with `11 ≤ a` gives `12 ≤ a`. The accepted sorted-envelope theorem
   applies to
   `[3,7,11,13,19,25,61,373,32769]` and binary exponent 12. Its exact rational
   product is strictly below two, contradicting the same exact identity.

The three rational gates are kernel-checked by `norm_num` in their respective
consumer proofs:

- upper: `28301731852/14166268083 < 2`, with gap
  `30804314/14166268083`;
- fixed six times `h(31)`: `65536/32395 > 2`, excess `746/32395`;
- fixed six times `h(37)`: `4096/2035 > 2`, excess `26/2035`.

Every component factor occurs once. The sorted proof allocates distinct slots
for the witness, a large actual value, and the remaining component lower bound;
no underlying-base largeness is inferred. Actual 25 occupies one set entry;
extracting its base 5 and exponent two separately is unnecessary for the count
argument. Injectivity still ensures the exact nine-value representation.

## Compilation, audit, and actual effort

Three successive bounded `tool_task` builds ran:

```text
timeout --kill-after=2s 60s lake -q build +Erdos.Unitary1052NineOddWitnessInterval
```

They checked the foundation, count/short-list layer, and complete consumer in
sequence. Each passed on its first attempt. The final task explicitly printed
`INTERVAL KERNEL PASSED`; there were no errors or `sorry` warnings. No speculative
untested final edit was made.

A separate fresh disposable leaf `/tmp/interval-audit-MfzZMjN.lean` imports the
built production module, prints the exact consumer and selected helper
signatures, and audits every one of its eleven public theorem declarations.
It runs with:

```text
timeout --kill-after=2s 60s lake env lean -j 1 -M 4000 /tmp/interval-audit-MfzZMjN.lean
```

The audit is not imported back into production. It passed and explicitly printed
`INTERVAL AUDIT PASSED`: each of the eleven theorem declarations, including the
complete consumer, reports exactly `[propext, Classical.choice, Quot.sound]`.
The printed full consumer signature matches the contract above and confirms
that actual 19/25 remain explicit and no extra section variables occur.
No independent exact-revision implementation review is claimed.
Actual effort is the three incremental builds and one imported audit just
listed; no wall-clock estimate is invented.

All public theorems have informal docstrings, `autoImplicit` is false, there are
no section variables, and there are no new definitions, axioms, `sorry`,
`native_decide`, unsafe implementation attributes, or production probes.

## Non-vacuity and remaining gates

The indexing domains are nonempty: `X.card = 9`, actual components are positive,
and the two distinct high entries are established from explicit membership,
not from empty quantification. Ratio denominators are positive in every bound.
The finite short-list proof derives positive exponent and local bounds before
its bounded check. Erasure cardinality is used only with explicit membership.

Concrete examples check the generic one-unit budget at `{11,7}`, the short-list
interface at `7^2`, the two-high-entry count interface on a nine-element set,
and the lower-product interface on the fixed six plus 31. A joint ordinary
identity model is provided at `a=2`, `P={3,5}`, all exponents one (the number 60).
**No model satisfying all strengthened kernel premises exists**, since the
kernel proves their inconsistency. Consequently no such satisfiability witness
is claimed; this is an intentional exclusion result, not an accidental
empty-domain statement or a construction theorem.

The implication now available to consumers is exactly: ordinary nine-odd model
plus explicit actual 19/25 and the interval witness hypotheses implies `False`.
The upstream forcing of 19/25 remains unpaid by this unit and separately owned.
The original UPN-to-identity bridge, prior branch memberships/evenness/large bound,
whole-B/global conclusions, and an independent implementation review remain
outside this producer's completion claim.
