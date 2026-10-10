# #1052: actual a=12 five-slot canceled identity → four-prime support

## Scope and immutable source mapping

This is a conditional branch theorem, not a global unitary-perfect-number result.
Sources were read with `jj --ignore-working-copy file show` at their exact revisions:

- `62dae66fcf92bdc82df1d8b10e161278c4351aa0:Argument.md`, final surviving
  `3·5·7·13` core section, identity (5):
  `(2^a+1)(P+1)∏(Q_j+1)=2^(a-6)·65·P·∏Q_j`.
  This section retains arbitrary positive odd `e` in `P=p^e`, distinct odd
  component primes, `p>13`, `p≡1 (mod 24)`, and square primes outside the core.
- `00547c07d38bc425648cdf2d61accf01212e6e8b:Argument-11-seed-closure-budget.md`,
  normalization (6), selects `a=12`, square slots `11^2`, `61^(2c)`, and
  three residual slots `q_j^(2d_j)`. Its four-recipient support projection is
  now derived here from the full canceled identity, not taken as a premise.

`Unitary1052A12Support.lean` directly substitutes these five slots into (5).
It does not formalize the normalization from (5) to (6): using the full
undivided identity avoids an unnecessary additional division bridge.
`P` is expanded to `p^e`; `a=12` turns `2^(a-6)` into `2^6`. There are no
abundance multipliers and no restriction `e=1` or conditional `P<705` input.

The actual branch consumers preserve:

- `p.Prime`, `13<p`, `p%24=1`, `0<e`, `Odd e`;
- `0<c` and `0<d1`, `0<d2`, `0<d3`;
- each residual base is prime and odd and is not `3,5,7,13`;
- `List.Pairwise (·≠·) [p,11,61,q1,q2,q3]`, representing actual pairwise
  distinctness of the extra odd components (no numerical ordering imposed);
- the exact natural-number identity

```
(2^12+1)*(p^e+1)*(11^2+1)*(61^(2*c)+1)
  *(q1^(2*d1)+1)*(q2^(2*d2)+1)*(q3^(2*d3)+1)
= 2^6*65*p^e*11^2*61^(2*c)
  *q1^(2*d1)*q2^(2*d2)*q3^(2*d3).
```

Some preserved source premises are not needed by the support proof. Their
underscore-prefixed names in the cardinality theorem document that fact without
removing them. E1's additional descriptions of exact seed valuations at `11`
and `2` are **not** assumed or proved in this module: they are unnecessary for
this implication from (5), which consequently also applies to any models with
those additional constraints. Residual primes are not required to be `1 mod 4`;
that would incorrectly exclude the contamination mechanism retained by the source.

## Checked argument and declarations

All declarations are in namespace `Erdos1052`.

1. `not_dvd_pow_successor_of_period`: a positive finite modular period whose
   residues avoid minus one excludes divisibility of a power successor.
2. `a12_fixed_odd_primes_not_dvd_successor`: excludes `5,11,13,61` from
   `61^(2c)+1`. The periods of `(61^2)` modulo `5,11,13` used are `1,5,3`.
   Period equations and all finite residue exclusions are kernel checked with
   `decide`. Modulo `61`, positive powers vanish and the `c=0` boundary is
   handled separately.
3. `a12_half_successor_exact_and_odd`: proves
   `2*((61^(2c)+1)/2)=61^(2c)+1` and excludes `2` from the natural half.
   Oddness of the numerator's power supplies exact divisibility by two;
   modulo four the power is one, excluding divisibility of the half by two.
4. `a12_half_successor_primeFactors_subset_of_dvd_rhs`: from divisibility of
   the numerator by the exact full RHS and primeness of `p,q1,q2,q3`, derives
   `((61^(2c)+1)/2).primeFactors ⊆ {p,q1,q2,q3}`. It splits divisibility of
   the RHS into its actual factors, including `65=5*13`, and removes the
   proved fixed-prime impossibilities. There is no assumed support containment.
5. `a12_five_slot_primeFactors_card_le_four`: the source-faithful full
   identity consumer. An explicit integer cofactor gives numerator divisibility
   on the LHS, the identity transfers it to the RHS, and the support subset
   gives cardinality at most four.
6. `a12_five_slot_not_dvd_eighty_one`: composes that bound with the unchanged
   accepted `not_dvd_eighty_one_of_primeFactors_card_le_four` in
   `Unitary1052C81Support.lean`, proving `¬81∣c` for the actual conditional branch.

Only fixed primes present on this RHS are excluded; exclusions of `3` and `7`
from the numerator are not necessary and were not added.

## Boundary and non-vacuity evidence

The source data excluding the full identity are jointly instantiated at
`p=73,e=3,c=d1=d2=d3=1,q1=17,q2=19,q3=23`, showing in particular that the
consumer does not restrict `e` to one. All index domains used are nonempty:
the finite periods have positive sizes `1,5,3`; the residual set and six-entry
pairwise-distinct list are concretely inhabited. A joint model for the weaker
RHS-divisibility helper is checked at `p=1861,e=c=1`, residual primes `17,19,23`
and residual exponents zero (permitted for that general helper only).
The exact-half boundary `c=0` is also checked; the actual final consumer
requires `0<c`, as does the accepted obstruction theorem.

No full-identity model or full-branch existence is claimed. Such a witness is
not supplied by the source and is not needed for the requested conditional
implication. Thus checked arithmetic/nonidentity premise satisfiability is not
a non-vacuity certificate for the entire unresolved full branch.

## Checks and remaining upstream obligations

Bounded narrow build:

```
timeout --kill-after=2s 60s lake -q build +Erdos.Unitary1052A12Support
```

Final build completed with exit zero, no warnings, errors, or `sorry`.
A separate disposable leaf audit checked the full consumer signatures and
printed axioms for all six declarations; only `propext`, `Classical.choice`,
`Quot.sound` occurred. The audit leaf is removed and is not imported by production.
No `native_decide`, axioms, external implementations, or exploratory commands
are present in production. An early broad-import probe exceeded its explicit
4000 MB ceiling and was replaced by the narrow dependency route; subsequent
helper and full-consumer builds were successful (recorded build times 2.2–2.5s
for intermediate versions). This is compiler execution evidence, not an estimate
of total worker effort.

The canonical fixed-core reduction, applicability of the actual seed, and any
upstream `a>10` argument remain unpaid here. No result for `c=27m` or other
stronger tower bound was pursued. The assigned identity-to-support bridge and
its composition with the existing 81 obstruction are closed conditionally.

Required metadata tools were used: `erdos fetch 1052` returned the canonical
finiteness question, five known values, and null comments; `oeis show A002827`
returned the same five unitary-perfect numbers and the note that a sixth is
unknown. These metadata are not theorem premises or proof evidence.
