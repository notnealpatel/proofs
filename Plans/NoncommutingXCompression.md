# x-coordinate compression is not monotone for the Conlon--Lim sum

## Decisive result

The proposed inequality is false, for the operation with three independently chosen summands. Take
\[
 A=\{(0,0,0),(0,0,1),(1,0,0),(1,1,0)\}.
\]
The fibers over `(y,z)` have sizes 2 at `(0,0)`, and 1 at `(0,1)` and `(1,0)`. Hence
\[
 C_x(A)=\{(0,0,0),(1,0,0),(0,0,1),(0,1,0)\}.
\]
Only the singleton fiber at `(1,0)` moves: `(1,1,0)` is replaced by `(0,1,0)`.

For clarity, for points `p_i=(x_i,y_i,z_i)`, the independently chosen sum is
\[
 L_0(p_0)+L_1(p_1)+L_2(p_2)
 =(y_0+z_1,\,-x_0+z_2,\,-x_1-y_2).
\]
Enumerating this formula over all `4^3` triples gives the following exact sets:

```
M(A) = [
 (0,-1,-2),(0,-1,-1),(0,-1,0),(0,0,-2),(0,0,-1),(0,0,0),
 (0,1,-1),(0,1,0),(1,-1,-2),(1,-1,-1),(1,-1,0),(1,0,-1),
 (1,0,0),(1,1,0),(2,-1,-1),(2,-1,0),(2,0,0)]

M(Cx(A)) = [
 (0,-1,-2),(0,-1,-1),(0,-1,0),(0,0,-2),(0,0,-1),(0,0,0),
 (0,1,-1),(0,1,0),(1,-1,-1),(1,-1,0),(1,0,-2),(1,0,-1),
 (1,0,0),(1,1,-1),(1,1,0),(2,0,-1),(2,0,0),(2,1,0)]
```

Thus `|M(A)|=17` and `|M(Cx(A))|=18`. The removed points are
`(1,-1,-2),(2,-1,-1),(2,-1,0)`; the added points are
`(1,0,-2),(1,1,-1),(2,0,-1),(2,1,0)`.

## Structural explanation

Put `e_x=(1,0,0)`, `e_y=(0,1,0)`, and `e_z=(0,0,1)`. The moved point changes `L0(A)` from
\[
 \{0,-e_y,e_x-e_y\}\quad\text{to}\quad \{0,-e_y,e_x\}.
\]
The `L1` image also stays unchanged: for the old point `(1,1,0)`, `L1=-e_z`, while for the new point `(0,1,0)`, `L1=0`; both values already occur in the image from the other points. `L2` ignores `x` entirely. Set
\[
 B=L_1(A)+L_2(A)=\{0,e_x,-e_z\}+\{0,e_y,-e_z\},
 \qquad U=B\cup(B-e_y).
\]
Then
\[
 M(A)=U\cup(B+e_x-e_y),\qquad
 M(C_x(A))=U\cup(B+e_x).
\]
Exact finite counts are `|B|=8`, `|U|=13`, while
\[
 |(B+e_x-e_y)\cap U|=4,
 \qquad |(B+e_x)\cap U|=3.
\]
So the new translate has one fewer collision with the fixed union and contributes 5 rather than 4 new points. Independence of the three choices permits these Minkowski sums, but does not preserve overlap multiplicities; compression can reduce overlap.

The reproducible Sage witness and bounded early-stopped search are in `Plans/NoncommutingXCompression.sage`. The search examines candidates in `{0,1}^3` in mask order (at most 255 nonempty candidates) and stops at the first witness encountered; this is not a claim of exhaustive coverage or minimality. The exact command used was:

```
timeout --kill-after=2s 60s sage Plans/NoncommutingXCompression.sage
```

## Boundary cases and scope

- For `A=∅`, or whenever `Cx(A)=A`, equality is immediate.
- If all points lie in one x-level `x=c`, compression is translation by `(-c,0,0)`. Since each of `L0,L1,L2` then changes by a fixed translation, `M` is translated and cardinality is preserved. This includes singletons.
- The failure already occurs when only one singleton fiber moves, so it is not an artifact of complicated fiber interactions.

This closes only unconditional monotonicity for this specified x-compression and three-independent-image sum. It does not address other compression directions, inverse operations, or restricted classes of sets. In particular, it supplies no missing bridge from the comparable-box density estimate to a general dense-box theorem; that separate issue remains open.