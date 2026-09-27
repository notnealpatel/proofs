# Exact `b=128` reflection-transfer audit

## Scope and notation

This note records an exact transfer computation for the following candidate,
called **(O)** here.  If `A` is a scalar cap with
`A ⊂ [0,N²)`, `m = |A| > N`, define, for
`c ∈ [0,N²) \ A`,

```text
ν_A(c) = #{(x,y) ∈ A² : 2x - y = c}.
```

Thus `ν_A(c)` counts reflections of `y` through `x` landing at `c`.  Put

```text
M = ∑_{c ∈ [0,N²) \ A} ν_A(c),
E = ∑_{c ∈ [0,N²) \ A} ν_A(c)².
```

The candidate estimate is

```text
(O)  E ≤ M² r₃(N)^(8/3) / (N^(2/3)(m-N)²),
```

where `r₃(N)` is the largest cardinality of a 3-term-progression-free
subset of `[0,N)`.  The construction below verifies (O), with constant `1`,
for this family and for every `k ≥ 1`.

This is an exact computation/audit artifact.  It is not a proof of (O) for
arbitrary scalar caps, and it neither proves nor disproves Erdős 142.

## The digit family

Set

```text
b  = 128,
E₁ = {0,1,5,7,11,12,16,18,26,38,39,42,44,48,53,55,59,61},
E₂ = {17,18,21,23,34,36,42,46}.
```

For `k ≥ 1`, let `A_k` consist of the integers with `2k` base-`b` digits,
where the least-significant digit and every even-position digit lie in
`E₁`, while every odd-position digit lies in `E₂`:

```text
A_k = { ∑_{j=0}^{2k-1} a_j b^j :
        a_j ∈ E₁ for j even, a_j ∈ E₂ for j odd }.
```

Consequently

```text
N = b^k = 128^k,       m = |A_k| = (18·8)^k = 144^k > N.
```

The finite digit checks are as follows.  Neither `E₁` nor `E₂` contains a
nonconstant 3-term arithmetic progression.  Also, for each of these digit
sets, the relevant midpoint computations have no carry: the largest doubled
digit is at most `122` in `E₁` and at most `92` in `E₂`, both below `128`.
Thus a putative nonconstant progression in `A_k` would give a nonconstant
progression in at least one digit set.  Hence `A_k ⊂ [0,N²)` is a scalar cap.

Using only `E₁` in each of `k` base-`b` positions gives a 3-AP-free subset of
`[0,N)` of size `18^k`.  The same no-carry check therefore gives the exact
lower bound

```text
r₃(N) ≥ 18^k.
```

## Borrow transfer and the exact matrices

For a digit pair `(x,y)`, the reflected digit is obtained from
`2x-y`.  A borrow state is an element of `{0,-1}`.  If `β` is the incoming
borrow, the outgoing state `γ` and output digit `z` are defined by

```text
2x - y + β = z + bγ,       0 ≤ z < b,
β,γ ∈ {0,-1}.
```

The initial state is `0`.  The state `-1` records that the lower digits have
borrowed one unit from the current digit.  For `F ⊂ [0,b)`, define the exact
2-by-2 transfer matrix, with rows and columns ordered as `(0,-1)`, by

```text
(P_F)_{β,γ}
  = #{(x,y) ∈ F² : there is a z ∈ [0,b) with
                       2x-y+β = z+bγ}.
```

For the paired energy count, use two simultaneous reflected pairs.  The
paired state ordering is explicitly

```text
(0,0), (0,-1), (-1,0), (-1,-1),
```

where the first coordinate is the borrow for `(x,y)` and the second is the
borrow for `(x',y')`.  Define `Q_F` by

```text
(Q_F)_{(β,β'),(γ,γ')}
 = #{(x,y,x',y') ∈ F⁴ : there is a common z ∈ [0,b) such that
       2x-y+β   = z+bγ,
       2x'-y'+β' = z+bγ'}.
```

All entries below are direct finite integer counts from these definitions.
The least-significant digit is an `E₁` digit and the next digit is an `E₂`
digit, so one two-digit block uses `P₁P₂` and `Q₁Q₂`, where
`P_i=P_{E_i}` and `Q_i=Q_{E_i}`.

The single-pair matrices are

```text
P₁ = [[223, 101],
      [222, 102]],

P₂ = [[ 58,   6],
      [ 54,  10]],
```

and hence

```text
P = P₁P₂ = [[18388, 2348],
             [18384, 2352]].
```

Its characteristic polynomial and eigenvalues are

```text
χ_P(x) = x² - 20740x + 82944,
         eigenvalues: 20736, 4.
```

With the paired-state ordering displayed above, the energy matrices are

```text
Q₁ = [[551, 104, 104, 235],
      [423, 124, 123, 172],
      [423, 123, 124, 172],
      [550, 104, 104, 236]],

Q₂ = [[88, 0, 0,  6],
      [37, 0, 0,  0],
      [37, 0, 0,  0],
      [72, 0, 0, 22]],
```

so that

```text
Q = Q₁Q₂
  = [[73104,     0,     0, 8476],
     [58747,     0,     0, 6322],
     [58747,     0,     0, 6322],
     [73088,     0,     0, 8492]].
```

Its characteristic polynomial and eigenvalues are

```text
χ_Q(x) = x⁴ - 81596x³ + 1305280x²,
         eigenvalues: 81580, 16, 0, 0.
```

These matrices are also an independently auditable specification of the
finite computation: every entry is obtained by enumerating the displayed
finite digit sets and applying the displayed borrow equations.

## Exact mass and energy formulas

Let `\widetilde M` and `\widetilde E` include all reflected outputs in
`[0,N²)`, including outputs that lie back in `A_k`.  Starting in state `0`
and requiring final state `0` gives

```text
\widetilde M = (P^k)_{(0),(0)},
\widetilde E = (Q^k)_{(0,0),(0,0)}.
```

Exact diagonalization of the two displayed matrices gives

```text
\widetilde M
  = (4596/5183)·20736^k + (587/5183)·4^k,

\widetilde E
  = (18272/20391)·81580^k + (2119/20391)·16^k.
```

The cap condition explains the diagonal subtraction.  If `c ∈ A_k` and
`2x-y=c` with `x,y ∈ A_k`, then `(y,x,c)` is a 3-term progression in the
scalar cap.  Therefore cap-freeness forces `x=y=c`; every point of `A_k`
contributes exactly one diagonal reflection and there are no other
reflections landing in `A_k`.  Thus

```text
M = \widetilde M - 144^k,
E = \widetilde E - 144^k.
```

In particular,

```text
M = (4596/5183)·20736^k + (587/5183)·4^k - 144^k,
E = (18272/20391)·81580^k + (2119/20391)·16^k - 144^k.
```

## Bounds needed for (O)

First, since `20736=144²`,

```text
M - (4/5)·144^(2k)
 = (2248/25915)·20736^k - 144^k + (587/5183)·4^k.
```

For `k ≥ 1`, the first term is at least `144^k`, because
`2248·144 = 323712 > 25915`.  Hence

```text
M ≥ (4/5)·144^(2k).
```

For the energy, note that

```text
1 - 18272/20391 = 2119/20391,
```

and `16^k ≤ 81580^k`.  Therefore

```text
E ≤ \widetilde E ≤ 81580^k.
```

The preceding mass bound, `m-N ≤ m`, and `r₃(N) ≥ 18^k` give the following
lower bound for the right-hand side of (O):

```text
M² r₃(N)^(8/3) / (N^(2/3)(m-N)²)
 ≥ (16/25)·[144²·18^(8/3)/128^(2/3)]^k.
```

The exact cubed comparison used in the audit is

```text
81580³·128²
 = 8,895,513,891,831,808,000
 < 98,255,075,431,437,047,955,456
 = 144⁶·18⁸.
```

The prefactor is also sufficient already at `k=1`, as witnessed by the
exact integer comparison

```text
16³(144⁶·18⁸) - 25³(81580³·128²)
 = 402,313,796,562,606,276,425,547,776
 > 0.
```

Consequently

```text
81580^k
 ≤ (16/25)·[144²·18^(8/3)/128^(2/3)]^k
```

for every `k ≥ 1`.  Combining this with `E ≤ 81580^k` proves (O), with
constant `1`, for every member `A_k` of this explicitly defined family.

## Audit boundary

The conclusion is only a family result: every `k ≥ 1` in the displayed
`b=128` construction satisfies the proposed estimate.  The exact transfer
calculation does not establish candidate (O) for general scalar caps, and
it does not prove Erdős 142.
