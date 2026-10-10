# E2 — forced-61 cubic support obstruction

## Checked unit and scope

Production module: `Erdos.Unitary1052C81Support` at
`Proofs/Erdos/Unitary1052C81Support.lean`.

Source SHA256: `c079f679a112a043dd96ed9e068bd9f6f7ee8c493133919ada81aa214c95dd47`.

The selected universal claim is faithfully preserved: for every natural `c > 0`,
if the natural number `T_c = (61^(2*c)+1)/2` has at most four **distinct prime
divisors**, then `81` does not divide `c`. Support is the standard finite
`Nat.primeFactors`; cardinality is exclusively `Finset.card`. No invented support
predicate, extra factor witnesses in the hypotheses, or finite-c substitute is used.

Named consumer: E1's `a=12`, five-square-slot, actual `11^2` branch. The implication
from the full canceled identity to four-base support containment/cardinality
**remains UPSTREAM**. This unit neither formalizes that implication nor asserts
that the full identity has a model. It does not bound all `c`, discharge the
remaining closure layers, or formalize any valuation machinery.

Sources inspected: argument packet `00547c07d38bc425648cdf2d61accf01212e6e8b`
(`Argument-11-seed-closure-budget.md` and its producer/output), and the sole
prose review `ef51dd4ecfef64f51d0716eb0a1cceb2dfa174c1`
(`Review-11-seed-closure-budget.md`). The finite producer at `c=81` is only
preflight evidence; the Lean argument below is universal and does not use it.

## Structural proof and translation

If `c=81*m`, positivity gives `m>0`. Put `x=61^(2*m)`. Then `x>1`, `Odd x`, and
`x % 3 = 1`. For any iterate `y=x^(3^i)`, these three properties persist.
The natural quadratic factor `F(y)=y^2+1-y` is used as an expression rather than
as a new definition. The hypotheses prove `y ≤ y^2+1`, so the subtraction is
exact, and `1<y` proves `1<F(y)`.

The proof first establishes `(y+1)*F(y)=y^3+1`. **Oddness is explicitly required**
for the halved identity: it gives `2 ∣ y+1`, so natural division is exact.
Residue one modulo three alone is not used as a parity substitute.

A common prime of `y+1` and `F(y)` makes `y=-1` in `ZMod r`. Substitution into
the exact quadratic relation gives `3=0`; thus the prime is three. The residue
`y % 3 = 1` contradicts divisibility of `y+1` by three. Passing to the divisor
`(y+1)/2` shows that the new factor is coprime to the **entire preceding half
successor**, not just the immediately previous quadratic factor. Hence successive
factors introduce disjoint prime supports, which is the required pairwise
coprimality mechanism across all levels.

`Nat.Coprime.primeFactors_mul`, `Nat.Coprime.disjoint_primeFactors`, and
`Finset.card_union_of_disjoint` turn this into growth by at least one prime.
The initial half successor is greater than one, so has nonempty prime support.
Induction yields `k+1` distinct primes for `(x^(3^k)+1)/2`. At `k=4` this is five
primes for `T_c`; the exponent equality is proved, and contradicts support at most
four. No factorization or large finite computation is used.

No hypotheses, quantified objects, or conclusions were repaired or weakened.
New mathematical lemmas are the exact cubic factorization, coprimality, growth,
and tower induction; cast/division APIs are representation infrastructure only.

## Exact elaborated signatures

These are the imported-leaf `#check @...` outputs (parentheses added to disambiguate
the tower exponent without changing the type):

```lean
Erdos1052.cubic_successor_factorization : ∀ (y : ℕ),
  1 ≤ y → (y + 1) * (y ^ 2 + 1 - y) = y ^ 3 + 1
Erdos1052.coprime_successor_cubic_factor : ∀ (y : ℕ),
  y % 3 = 1 → (y + 1).Coprime (y ^ 2 + 1 - y)
Erdos1052.half_cubic_successor_factorization : ∀ (y : ℕ),
  1 ≤ y → Odd y → (y ^ 3 + 1) / 2 = (y + 1) / 2 * (y ^ 2 + 1 - y)
Erdos1052.primeFactors_half_cube_card_growth : ∀ (y : ℕ),
  1 < y → Odd y → y % 3 = 1 →
  ((y + 1) / 2).primeFactors.card + 1 ≤ ((y ^ 3 + 1) / 2).primeFactors.card
Erdos1052.primeFactors_half_cubic_tower_card_lower_bound : ∀ (x k : ℕ),
  1 < x → Odd x → x % 3 = 1 →
  k + 1 ≤ ((x ^ (3 ^ k) + 1) / 2).primeFactors.card
Erdos1052.not_dvd_eighty_one_of_primeFactors_card_le_four : ∀ (c : ℕ),
  0 < c → ((61 ^ (2 * c) + 1) / 2).primeFactors.card ≤ 4 → ¬81 ∣ c
```

## Satisfiability and boundaries

Production examples jointly instantiate the helper hypotheses at `y=7` and the
target's hypotheses at `c=1`: `T_1=1861`, proved prime by kernel-checked `norm_num`,
so its support has cardinality one. Every quantified domain is `ℕ`, not an empty
subtype; the tower index admits both zero and four. The base case `k=0` is proved,
not discarded. A separate example shows `c=0` has support cardinality zero but
`81 ∣ 0`, explaining why the target's positive-c hypothesis is essential.
There are no instance arguments on concrete arithmetic types that replace their
canonical structure. The local `Fact r.Prime` instance is obtained from an actual
prime hypothesis and used solely for the standard `ZMod r` structure.

## Build and separate audit receipts

All commands ran in the assigned workspace, using bounded background tasks.

Final production check:

```sh
set -o pipefail; timeout --kill-after=2s 60s lake -q build +Erdos.Unitary1052C81Support 2>&1 | tee /tmp/unitary1052-c81-completed-build.txt
```

**Exit 0; stdout/stderr empty.** The preceding growth-only build also exited zero.
The first final-target build failed only on two satisfiability examples: direct
`decide` did not reduce the prime-factor list/cardinality. Replacing that with the
prime-singleton API and `norm_num` fixed the examples; no theorem statement or
mathematical argument changed. The first local coprimality probe needed an explicit
`linear_combination` converting the cast equality `2=-1` to `3=0`; the repaired
probe compiled. These were elaboration/API repairs, not mathematical gaps.

Separate audit leaf imported only the production module, set `autoImplicit false`,
and issued `#check @...` and `#print axioms ...` for all six public declarations:

```sh
set -o pipefail; timeout --kill-after=2s 60s lake env lean -j 1 -M 4000 Proofs/Scratch/Unitary1052C81Audit.lean 2>&1 | tee /tmp/unitary1052-c81-audit.txt
```

**Exit 0.** Signature stdout is transcribed above. Axiom stdout:

```text
'Erdos1052.cubic_successor_factorization' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1052.coprime_successor_cubic_factor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1052.half_cubic_successor_factorization' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1052.primeFactors_half_cube_card_growth' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1052.primeFactors_half_cubic_tower_card_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1052.not_dvd_eighty_one_of_primeFactors_card_le_four' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Temporary probe/audit leaves are removed before handoff. Production contains no
`sorry`, custom axiom, `native_decide`, exploratory directives, or custom trusted
implementation. Compilation and this author audit do not replace the parent's
independent review of semantic fidelity and the external support implication.

## Effort and preserved inputs

Recorded E2 start: 2026-10-10 20:37:51 UTC. Final build and six-theorem audit had
completed by 20:41:55 UTC (4m04s since that start); receipt preparation and cleanup
followed. Five bounded compiler runs were used: two local probes, growth-only
build, initial target build, and repaired target build; the separate audit was
one additional run. No proof delegation or computation search was used.

Prior artifacts remain byte-identical:

- Transfer SHA256 `eb83ee6313fc547a9a54737c55de03dae5c078398abc5bdf251fdfb7fd12da19`.
- ExactSeed SHA256 `461d4bd5b098486b0793a019eb91a2f06f277c9f89d373d52f5fd1c014935179`.

Disposition: E2 checked unit complete, conditional on the explicit support premise.
Pause at this episode boundary; no adoption, successor work, monitoring-ledger
edit, or revision management is performed.
