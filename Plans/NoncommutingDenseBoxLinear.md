# Linear dense-box deficit via fixed-threshold rectangular halos

## Claim

Let `I1,I2,I3` be translated nonempty integer intervals, with cardinalities
`N1,N2,N3 >= 1`, and assume

```
M := max(N1,N2,N3) <= κ m,       m := min(N1,N2,N3),       κ >= 1.
```

Put `B = I1 × I2 × I3`, `V = N1 N2 N3`, and `h = |B \ A|` for
`A ⊆ B`. For

```
L0(x,y,z) = (y,-x,0),  L1(x,y,z) = (z,0,-x),  L2(x,y,z) = (0,z,-y),
M(A) = L0(A) + L1(A) + L2(A),
```
there is the explicit estimate

```
|M(B) \ M(A)| <= 7776 κ^5 h.                         (1)
```

Consequently,

```
|M(A)| >= 8|A| - (7776 κ^5 + 12 κ^2) (h + V^(2/3)).  (2)
```

The constants are intentionally crude. This is a dense comparable-box statement,
not an inverse theorem for arbitrary finite sets and not the separate #711 bridge.
The proof is a box adaptation of the adopted cube artifact
`873072cd65205aec2b2dd318e5a2c18c2d6633aa`,
`Plans/NoncommutingDenseCubeLinear.md`; the older comparable-box plan is
`00c77ea87467bed7c5c168d0bd45745431787e93`,
`Plans/NoncommutingDenseBox.md`.

## Fiber and projection holes

Define projection-hole sets by declaring a projected pair a hole when its
whole remaining-coordinate fiber in `B` is absent from `A`:

```
H0 ⊆ I2 × (-I1),   H1 ⊆ I3 × (-I1),   H2 ⊆ I3 × (-I2).
```

The fibers belonging to distinct holes in each `Hi` are disjoint. Therefore

```
|H0| <= h/N3,   |H1| <= h/N2,   |H2| <= h/N1,       (3)
```

and in particular `|Hi| <= h/m`. Here interval length always means
cardinality; a singleton has length one.

For an output `s=(s1,s2,s3)` in `M(B)`, use independent fiber variables
`(a,b,d)` and set

```
c = s1-a,  e = s2-b,  f = s3-d.
```
The admissible common fiber is

```
J1 = I2 ∩ (s1-I3),
J2 = (-I1) ∩ (s2-I3),
J3 = (-I1) ∩ (s3+I2).
```
If `s` is absent from `M(A)`, every triple in `J1 × J2 × J3` has at least
one of its three projected pairs in `H0,H1,H2`; otherwise the three
non-hole pairs have independent completions in `A` and produce `s`.
Averaging the covering indicators gives one rectangle of density at least
`1/3` in its corresponding projection set:

```
R0 = J1 × J2,
R1 = [I3 ∩ (s1-I2)] × [(-I1) ∩ (s3+I2)],
R2 = [I3 ∩ (s2+I1)] × [(-I2) ∩ (s3+I1)].
```

For `R1` and `R2`, the affine changes from common variables are bijections
(they reflect and/or translate one coordinate), so the rectangle densities
are exactly densities of `H1` and `H2`, respectively. No independence of
holes is being asserted.

## The unequal-side overlap lemma

This is the only new geometric input beyond the cube proof. Normalize two
translated intervals to `[0,u-1]` and `[0,v-1]`, with `u,v >= 1`, and write

```
J_s = [0,u-1] ∩ [s-v+1,s],       0 <= s <= u+v-2.
```
Let `l=max(0,s-v+1)`. Choose a retained or enlarged window and a marked
point `q` as follows:

* if `s <= u-1`, choose `q=s` and retain `J_s` (whose right endpoint is `s`);
* if `s > u-1` and `l>0`, choose `q=l` and retain `J_s` (whose left endpoint is `l`);
* if `s > u-1` and `l=0`, then necessarily `u <= s <= v-1`; choose `q=s` and
  replace `J_s=[0,u-1]` by `[0,s]` in the fixed expanded grid
  `[0,max(u,v)-1]`.

In the last case `v>u`, and

```
|[0,s]|/|J_s| = (s+1)/u <= v/u <= κ.                  (4)
```
In the other cases the ratio is one. The marked point lies in the retained
or enlarged window in every case.

For fixed `u,v`, each `q` has at most two source values `s`: at most one
from the prefix/plateau branch (`q=s`) and at most one from the suffix
branch (`q=s-v+1`). The plateau branch has `q>u-1`, so it is disjoint from
the prefix branch and cannot create a third preimage. This remains true at
`u=1`, `v=1`, and `u=v`; in particular `u=1` costs at most `v<=κ`, while
`v=1` has no enlargement. Reflections and translations merely reverse
which endpoint is marked and preserve the statement.

Apply this lemma separately to the two overlap coordinates of each `Ri`.
A density-`1/3` rectangle can therefore be enlarged by area at most
`κ^2`, while its hole set is extended by zero outside the original
projection grid. Thus the enlarged rectangle has hole density at least

```
α = 1/(3κ^2).                                         (5)
```
It is important that only the window is enlarged: no new holes are added.
The expanded grid is fixed for the interval pair under consideration.

## Fixed-threshold halo and counting

For a finite rectangular grid and `E` in it, let `Halo_α(E)` be the points
lying in a nonempty integer rectangle whose `E`-density is at least `α`.
The elementary two-stage one-dimensional weak estimate gives

```
|Halo_α(E)| <= 36 α^(-2) |E|.                         (6)
```
Indeed, with `g` the one-dimensional maximal average in the second
coordinate and `F={g>α/2}`, a rectangle of average at least `α` has
`F`-fraction at least `α/(2-α) >= α/2`; applying the one-dimensional
bound (constant at most `3/t`) twice yields the displayed `36/α^2`
form. This argument is applied to the zero extension on the fixed expanded
grid, so boundary enlargement introduces no unsupported holes.

With (5), (6) gives `|Halo_α(Hi)| <= 324κ^4 |Hi|`. The marked pair map has
multiplicity at most `2` in each coordinate, hence at most `4` in two
coordinates. For each attributed output pair, the unused output coordinate
has at most `2M-1 <= 2M` values. Therefore

```
|M(B) \ M(A)|
 <= 3 · 4 · (2M) · (324κ^4) · (h/m)
 <= 7776 κ^5 h,
```
which proves (1). The factor three is the union over the alternatives
`H0,H1,H2`; the factor four is only the two-coordinate corner
multiplicity. No additional reflection factor is charged.

## Ambient size and the consequence

The three coordinates of `M(B)` vary independently, so

```
|M(B)| = (N2+N3-1)(N1+N3-1)(N1+N2-1).                (7)
```
Writing each factor as the corresponding sum minus one and using
`Ni <= M <= κ V^(1/3)` gives the deliberately coarse bound

```
|M(B)| >= 8V - 12M^2 >= 8V - 12κ^2 V^(2/3).           (8)
```
Combining (1), `|A|=V-h`, and `M(A)⊆M(B)` yields

```
|M(A)| >= 8V - 12κ^2V^(2/3) - 7776κ^5h
        >= 8|A| - (7776κ^5+12κ^2)(h+V^(2/3)),
```
which is (2). The first displayed line is the sharper quantitative form.

## Boundary cases and status

For `h=0`, all projection-hole sets are empty and (1) says the deficit is
zero, as it should. For `A=∅`, `h=V`; the deficit estimate is harmless and
(2) is vacuous, so no density assumption has been smuggled into the claim.
For singleton sides, the overlap lemma and all fiber bounds use cardinality
one and remain valid. Translations and sign reflections preserve all
cardinalities and the endpoint multiplicity argument.

The plateau repair was adversarially checked in the cases `u=1`, `v=1`,
`u=v`, translated/reflected windows, and zero-supported holes. The check
found no counterexample, but it also identifies the exact conventions
needed for the proof: `u,v` are cardinalities, `u,v` stay fixed while
preimages are counted, and holes are zero-extended rather than enlarged.
This is a prose proof, not Lean-checked and not independently reviewed.
The load-bearing new lemma is the fixed-expanded-grid overlap construction;
the fiber, halo, and corner-count portions inherit the adopted cube
argument. No claim is made about general inverse statements or #711.
