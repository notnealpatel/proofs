# Linear dense-cube deficit via fixed-threshold rectangular halos

## Claim

Let `I1,I2,I3` be translated integer intervals, each of length `N >= 1`, and put
`B = I1 × I2 × I3`, `h = |B \ A|` for `A ⊆ B`. For

```
L0(x,y,z) = (y,-x,0),  L1(x,y,z) = (z,0,-x),  L2(x,y,z) = (0,z,-y),
M(A) = L0(A) + L1(A) + L2(A),
```

one has the absolute-constant estimate

```
|M(A)| >= 8|A| - 6480 (h + N^2).
```

The constant is deliberately nonoptimal. This is only a dense, equal-side cube theorem; it is not an inverse theorem for arbitrary finite sets.

## Fiber and projection-hole setup

Write a summand choice as

```
(a,b,0) + (c,0,d) + (0,e,f),
```
where the three displayed pairs come from `L0(A), L1(A), L2(A)`, respectively. Define projection-hole sets

```
H0 ⊆ I2 × (-I1),   H1 ⊆ I3 × (-I1),   H2 ⊆ I3 × (-I2)
```

by declaring a pair to be a hole when its whole remaining coordinate fiber in `B` is absent from `A`. Distinct projection holes have disjoint fibers, so

```
|Hi| <= h/N.                                             (1)
```

For an ambient output `s=(s1,s2,s3)`, use independent fiber coordinates `(a,b,d)`:

```
Js1 = I2 ∩ (s1 - I3),
Js2 = (-I1) ∩ (s2 - I3),
Js3 = (-I1) ∩ (s3 + I2).
```

The associated triple gives `c=s1-a`, `e=s2-b`, `f=s3-d`. If `s` is absent from `M(A)`, every triple in `Js1 × Js2 × Js3` has at least one of its three projected pairs in `H0,H1,H2`; otherwise the three non-hole pairs can be completed independently in `A` and produce `s`. Averaging this covering statement gives that at least one of the following rectangles has hole density at least `1/3`:

```
R0 = Js1 × Js2                         in I2 × (-I1),
R1 = [I3 ∩ (s1-I2)] × [(-I1) ∩ (s3+I2)] in I3 × (-I1),
R2 = [I3 ∩ (s2+I1)] × [(-I2) ∩ (s3+I1)] in I3 × (-I2).
```

For example, the density sum is at least one because the three missing-pair indicators cover the full fiber; hence one density is at least `1/3`. No independence of the hole sets is used.

For clarity, these are affine preimages in the actual projection coordinates, not the common fiber variables reused across projections. In the fiber parametrization `(a,b,d)`, the three projected pairs are exactly

```
P0 = (a,b),
P1 = (c,d) = (s1-a,d),
P2 = (e,f) = (s2-b,s3-d).
```

Thus the density of `H1` is evaluated on the `(c,d)` rectangle
`[I3 ∩ (s1-I2)] × [(-I1) ∩ (s3+I2)]`, and the density of `H2` is evaluated on the `(e,f)` rectangle
`[I3 ∩ (s2+I1)] × [(-I2) ∩ (s3+I1)]`. The maps `(a,d) ↦ (s1-a,d)` and `(b,d) ↦ (s2-b,s3-d)` are bijections onto these rectangles, so averaging the three indicator functions over the common `(a,b,d)` fiber gives precisely the three displayed rectangle densities. The reflected signs merely reverse prefix/suffix orientation; they do not alter the equal-length overlap or corner multiplicity assertions.

## Fixed-threshold rectangular halo lemma

For finite integer intervals `X,Y` and `E ⊆ X × Y`, let `H(E)` consist of points contained in some nonempty interval rectangle `I × J ⊆ X × Y` with

```
|E ∩ (I × J)| >= (1/3)|I × J|.
```

Then

```
|H(E)| <= 270 |E|.                                  (2)
```

Here is an elementary proof, included to avoid invoking the false uniform weak-(1,1) statement for the strong maximal operator. For a nonnegative function on a finite integer interval, the uncentered one-dimensional maximal operator satisfies

```
|{Mf >= alpha}| <= (3/alpha) sum f.                 (3)
```

Indeed, choose a witnessing interval for each point and greedily retain witnessing intervals in nonincreasing order of length. Retained intervals are disjoint; every discarded interval intersects a retained interval at least as long, and is contained in its threefold enlargement. Thus the covered set has size at most three times the sum of retained lengths, which is at most `(3/alpha) sum f`.

Let `g = M_y 1_E` and `F={g>1/6}`. If a rectangle through a point has average at least `1/3`, then its average is at most the average, in the first coordinate, of `g`; consequently the strong rectangular halo is contained in `{M_x g >= 1/3}`. On a witnessing x-interval, if `p` is the fraction of points in `F`, then

```
1/3 <= avg g <= p + (1-p)/6,
```

so `p >= 1/5`. Therefore

```
H(E) ⊆ {M_x 1_F >= 1/5}.
```

Applying (3) in the y-direction at threshold `1/6`, and then in the x-direction at threshold `1/5`, gives

```
|F| <= 18|E|,       |H(E)| <= 15|F| <= 270|E|.
```

The finite boundary causes no problem: all witnessing intervals are contained in the finite grid, while the enlargement used only for the upper bound may extend beyond it. The fixed threshold is essential; this does not claim a threshold-uniform strong weak-(1,1) estimate.

## Moving corners and output counting

If `P,Q` are equal-length integer intervals, the nonempty overlaps `P ∩ (t-Q)` as `t` runs through `P+Q` are proper prefixes, then the full interval once, then proper suffixes, with lengths

```
1,2,...,N-1,N,N-1,...,2,1.
```

Map each prefix to its right endpoint, each suffix to its left endpoint, and the unique full overlap to (say) its right endpoint. The chosen endpoint belongs to the overlap, and each source point has at most two preimages. The same statement holds with either interval reflected or with the sum written as a difference.

Thus for `R0`, the output pair `(s1,s2)` maps to a corner of `I2 × (-I1)` lying in `R0`, with multiplicity at most `4`. For `R1`, the output pair is `(s1,s3)` and the two overlap coordinates are `(c,d)=(s1-a,d)`; for `R2`, the output pair is `(s2,s3)` and the two overlap coordinates are `(e,f)=(s2-b,s3-d)`. Each is an equal-length prefix/suffix overlap after the indicated translation or reflection, so the same corner maps have multiplicity at most `4` in the actual `H1` or `H2` projection grid. If one of these rectangles has density at least `1/3`, its mapped corner lies in the corresponding halo. Consequently the number of absent-output pairs attributed to `Hi` is at most

```
4 |H(Hi)| <= 1080 |Hi|.                              (4)
```

For each such pair, the remaining output coordinate has at most `2N-1` values. Taking the union over the three alternatives and using (1), the number of absent outputs in the full ambient output box is at most

```
|M(B) \ M(A)|
 <= 1080(2N-1)(|H0|+|H1|+|H2|)
 <= 3240 (2N-1)h/N
 <= 6480h.                                           (5)
```

The ambient full-box sumset is exactly the product of the three pairwise interval sums, since the coordinates used by the three independent summands can be chosen independently. Hence

```
|M(B)| = (2N-1)^3 = 8N^3 - 12N^2 + 6N - 1.
```

Since `M(A) ⊆ M(B)`, (5) yields

```
|M(A)| >= 8N^3 - 12N^2 + 6N - 1 - 6480h.
```

Comparing with `8|A| = 8(N^3-h)` and discarding the favorable positive linear and constant terms gives the claimed bound with `C=6480`.

## Boundary checks and status

For `N=1`, each overlap is the unique full interval, so the corner map has multiplicity one and the argument remains valid. For `h=0`, all hole sets and the deficit vanish; the exact full-box value is `(2N-1)^3`. For `A=∅`, the requested inequality is trivial (and the counting bound remains harmless). Translations and reflected intervals only change the orientation of prefix/suffix overlaps, not the argument.

This is a prose proof based on the stated fiber formulas, not Lean-checked. The quantitative improvement is established for the verified dense equal-side cube class. It does not address arbitrary finite `A` outside a dense cube, the general inverse problem, or the separate #711 bridge.
