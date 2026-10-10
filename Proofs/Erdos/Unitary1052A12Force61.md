# #1052: the actual 11-square seed forces a 61 slot

## Conditional scope and immutable source mapping

`Unitary1052A12Force61.lean` imports the paid
`Erdos.Unitary1052A12Support` dependency from base
`b769eb50442744bb0e0245f955d4d0c0bbe0b74c`. It does not modify or reprove
that dependency or the 81 tower obstruction.

The following immutable sources were directly inspected with
`jj --ignore-working-copy file show`:

- `62dae66fcf92bdc82df1d8b10e161278c4351aa0:Argument.md`, lines 200, 243,
  and 303–315. Components are distinct prime powers. The surviving core
  `3·5·7·13` has exponent one, the extra odd-exponent component is `P=p^e`,
  and the other components are actual prime powers `Q_j=q_j^(2c_j)`.
  Equation (5) is
  `(2^a+1)(P+1)∏(Q_j+1)=2^(a-6)·65·P·∏Q_j`.
  The source retains arbitrary positive odd `e`, `p≡1 (mod 24)`, and
  `s=a-7`. Thus the conditional `a=12` branch has five square slots.
- `00547c07d38bc425648cdf2d61accf01212e6e8b:Argument-11-seed-closure-budget.md`,
  lines 7–22, specializes to `11^2`, an assumed mandatory `61^(2c)`, and
  three residual square slots. This new module pays the previously missing
  forcing-61 implication from the exact identity with `11^2` and four
  unspecified residual square slots. It does not assume mandatory 61.

The conjecturist's supplied gate identified this implication, not a global
unitary-perfect-number theorem. No fixed-core applicability, applicability of
the 11 seed, global five-slot model, `a>10` bridge, or `P<705` premise is
assumed established. There is no `e=1` restriction and no abundance multiplier.

## Exact Lean contract and translation audit

All declarations are in namespace `Erdos1052`. Both branch theorems quantify
`p e r1 r2 r3 r4 d1 d2 d3 d4 : ℕ` and retain:

- `p.Prime`, `13 < p`, `p % 24 = 1`, `0 < e`, `Odd e`;
- `0 < d1`, `0 < d2`, `0 < d3`, `0 < d4`;
- `∀ r ∈ ({r1,r2,r3,r4} : Finset ℕ),
  r.Prime ∧ Odd r ∧ r ≠ 3 ∧ r ≠ 5 ∧ r ≠ 7 ∧ r ≠ 13`;
- `List.Pairwise (· ≠ ·) [p,11,r1,r2,r3,r4]`;
- the full, left-associated natural-number identity

```
(2^12+1)*(p^e+1)*(11^2+1)
  *(r1^(2*d1)+1)*(r2^(2*d2)+1)*(r3^(2*d3)+1)*(r4^(2*d4)+1)
= 2^6*65*p^e*11^2*r1^(2*d1)*r2^(2*d2)*r3^(2*d3)*r4^(2*d4).
```

Bundling the four individual component conditions by membership in the
four-element finset is equivalent to requiring each separately; membership
of each explicit slot is proved by simplification. It does not weaken the
pairwise-distinct list premise. No ordering, no residual `1 mod 4` condition,
and no extra valuation equations are introduced. The powers, positive
exponents, distinct prime components, congruence, identity, and requested
conclusions survive unchanged. There is no natural subtraction or division
in the new statements.

## Completed mathematical implication and direct consumer

1. `a12_not_sixty_one_dvd_odd_component` proves
   `p.Prime → p % 24 = 1 → ¬61 ∣ p^e` for arbitrary natural `e`.
   Prime-power divisibility would give `61∣p`, hence `p=61`, contradicting
   `61 % 24 = 13`.
2. `a12_eleven_seed_forces_sixty_one` proves
   `r1=61 ∨ r2=61 ∨ r3=61 ∨ r4=61` from the complete branch contract above.
   An explicit cofactor certifies that 61 divides the left side, using
   `11^2+1=2·61`. The identity transfers this divisibility to the right side.
   Prime divisibility splits the actual product. Checked small arithmetic
   excludes `2^6`, `65`, and `11^2`; the preceding helper excludes `p^e`.
   Divisibility of each remaining prime power forces its prime base to be 61.
   Positivity, oddness, exclusions, and distinctness not needed for this
   elementary step remain explicit source premises.
3. `a12_eleven_seed_forces_sixty_one_not_dvd_eighty_one` proves

   ```
   (r1=61 ∧ ¬81∣d1) ∨ (r2=61 ∧ ¬81∣d2) ∨
   (r3=61 ∧ ¬81∣d3) ∨ (r4=61 ∧ ¬81∣d4).
   ```

   It invokes the preceding forcing theorem and handles all four cases.
   In case `i`, the adopted consumer
   `a12_five_slot_not_dvd_eighty_one` receives `c=di` and the other three
   slots in their original order. The residual component conditions follow
   from the original membership premise. Explicit adjacent-swap `List.Perm`
   certificates and `Perm.pairwise_iff` transport the complete distinctness
   list. The full identity is passed directly in case 1 and transported by
   `convert hid using 1 <;> ring` in cases 2–4. All exponent positivity data
   are passed to the adopted consumer. Neither support nor a 61 recipient
   is assumed. The four-case representation bridge is complete, not unpaid.

## Satisfiability and domain evidence: precise limitation

The helper's hypotheses are jointly satisfied by `p=73` (for example `e=3`).
A checked example jointly instantiates all **nonidentity** branch premises
at `p=73,e=3`, `(r1,r2,r3,r4)=(17,19,23,61)`, and all `di=1`. This tests the
intended distinctness, core exclusions, positive square exponents, and an
odd exponent different from one. Natural-number quantified domains are
nonempty; the component set is explicitly inhabited and the example has
four distinct bases. No empty finite index type is used.

No model satisfying the full identity is exhibited or claimed. The checked
example is therefore not a joint satisfiability/non-vacuity certificate for
all hypotheses of the full branch theorem. Existence of that unresolved
branch is not furnished by the sources, and is not inferred from successful
elaboration. The deliverable is the requested conditional implication.

## Actual compiler and audit receipts

All execution used bounded `tool_task` calls. The exact narrow build command
was:

```
timeout --kill-after=2s 60s lake -q build +Erdos.Unitary1052A12Force61
```

- `force-first-check`: exit 0, no diagnostics, compiled the odd-component
  exclusion helper. This earliest actual receipt and the selected main
  contract were sent to the parent immediately.
- `force-main-check`: exit 0, no diagnostics, compiled forcing61.
- `consumer-first-check`: failed locally at fourth-case permutation syntax:
  an unparenthesized `.cons r2.cons r1` was parsed as a field of `r2`.
- `consumer-fixed-check`: exit 0, no diagnostics, compiled both full branch
  declarations and the source-data consistency example after local repair.

A disposable leaf `Proofs/Scratch/Force61Probe.lean` imported the compiled
module and ran `#check @...` and `#print axioms` on all three declarations:

```
timeout --kill-after=2s 60s lake env lean -j 1 -M 4000 Proofs/Scratch/Force61Probe.lean
```

`force61-axioms` exited 0. Full signatures match the contracts above; every
axiom report contains only `propext`, `Classical.choice`, `Quot.sound`.
The leaf is removed and never imported by production. A preliminary
permutation probe failed on unavailable `~` notation; production uses the
explicit `List.Perm` type and the compiler-verified swap direction instead.
No `sorry`, declared axioms, `native_decide`, external implementations, or
exploratory commands remain in production.

Required metadata tools were used: `/home/exedev/go/bin/erdos fetch 1052`
returned the canonical finiteness question, five known values, and null
comments; `/home/exedev/go/bin/oeis show A002827` returned those five values
and the note that a sixth is unknown. These metadata are not proof evidence.
API inspection used `leandoc` and compiler probes. No computational research,
c27m investigation, nested delegation, integration, publication, ledger
edits, References edits, or manual revision manipulation was performed.

The source-gated identity-to-forcing61 implication and its direct 81 consumer
are available. Upstream fixed-core/seed/five-slot applicability and full-model
existence remain outside this deliverable. Independent controller review and
integration/adoption gates remain for the orchestrator.
