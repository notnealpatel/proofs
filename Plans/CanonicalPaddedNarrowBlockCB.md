# Canonical padded narrow-block carry transfer

## Status and exact proposition

This note proves one canonical-CB proposition.  It does **not** prove the
arbitrary rational-law conjecture, the full `#711` gain, an inverse theorem,
or the scalar condition (SC).  The latter is false, as recorded in
`Plans/CanonicalBaseCarryTransfer.md` (the SC family below is recalled only as
an adversarial check).

Fix integers `r >= 2`, `k >= 1`, and `h >= 1`.  Let
`2 <= a_i` satisfy

```
2 max_i a_i - 1 <= r,
```

and let `U=(U_0,...,U_{k-1})` be an *arbitrarily correlated* random vector
supported on `prod_i {0,...,a_i-1}`.  Put

```
A = sum_{i<k} U_i r^i,       Z = A + r^k V,
```

where `V` is independent and uniform on `{0,...,r^h-1}`.  Let `U'`, `V'`,
and `Z'` be independent whole-copy variables, and set

```
delta = sum_i log a_i - H(U),
Delta = k log r - sum_i log a_i + delta.
```
Assume `delta <= 7k/192` and `Delta <= 7(k+h)/192`.  For
`g_Z(n)=H(Z-nZ')-H(Z)`, there is an absolute constant `C` such that every
nonzero `P in Z[T]`, of degree `d >= 0` and coefficient height
`S=sum_j |c_j| >= 1`, obeys

```
g_Z(P(r)) <= C (d+1+log(1+S)) max(g_Z(1),g_Z(r)).       (CB-narrow)
```

The constant is independent of `r,k,h`, all coefficient heights, and the
joint law of `U`.  In particular, no restriction such as
`r >= (1+S) max a_i` is imposed.

All logarithms are natural.  Entropies are finite because all variables here
have finite support.

## Formal polynomial input

Write `W(T)=sum_{i<k}U_iT^i`, and use an independent copy.  The three
quantities below are **formal coefficient-vector entropies**, not scalar
entropies:

```
G_1=H(W-W')-H(W),
G_T=H(W-TW')-H(W),
G_P=H(W-PW')-H(W).
```

The reviewed correlated-polynomial-box input at commit
`aabb4e8797e157b192395a143c0833519bdfa25a` gives

```
G_P <= [4d+1+(192/7) log(1+S)] max(G_1,G_T).       (1)
```

It applies because the lower digit alphabets have deficit `delta` and the
hypothesis is exactly `delta <= 7k/192`.  For `W-W'`, each coefficient range
has width at most `2 max a_i-2 <= r-1`; finite base-`r` evaluation is therefore
injective on the possible coefficient vectors, including negative
coefficients.  For `W-TW'`, the coefficient ranges have widths at most
`a_0-1`, `a_i+a_{i-1}-2 <= r-1` for `1<=i<k`, and
`a_{k-1}-1 <= r-1` at the terminal degree.  Successive reduction modulo `r`
proves injectivity in this case too.  Since evaluation of `W` is injective,

```
H(A)=H(W),
H(A-A')=H(W-W'),
H(A-rA')=H(W-TW').
```

Thus `G_1=H(A-A')-H(A)` and `G_T=H(A-rA')-H(A)`, but `G_P` is **not**
identified with `H(A-P(r)A')-H(A)`: arbitrary polynomial evaluation can
collide.  The scalar argument below uses only a deterministic evaluation
upper bound for `G_P`.

## Carry lemmas

Put `q=r^k`.  For any two possible lower digit-difference vectors, every
coefficient difference has a fixed interval of width at most `r-1`: for the
ordinary difference it is at most `2 max a_i-2`, and for the shifted
coefficient `U_i-U'_{i-1}` it is at most `a_i+a_{i-1}-2`.  Consequently the
base-`r` residue map is injective on these coefficient vectors.  Indeed,
congruence modulo `r` first forces equality of the zeroth coefficients, and
induction after subtracting and dividing by `r` forces equality at every
coordinate.  This remains true for negative coefficients; no positivity of a
coefficient is being used.

### The unshifted carry

Let `B=A-A'`.  Its possible values lie in an interval of width at most
`q-1`, so its residue `R_1=B mod q` determines `B` (including its possibly
negative quotient).  Since `V,V'` are independent of the lower block,

```
H(Z-Z') = H(B) + H(V-V'),
H(Z)     = H(A) + H(V).
```

Thus the identity, not merely an inequality,

```
g_Z(1) = G_1 + g_V(1) >= G_1                         (2)
```

holds.  The first entropy equality follows from the bijection
`(R_1,(B-R_1)/q,V-V') -> Z-Z'`; the second follows from the disjoint padded
intervals `A+qV`.

### The shifted carry and the terminal boundary

Write `D=A-rA'`.  Its low formal coefficients are

```
C_0=U_0,       C_i=U_i-U'_{i-1} (1<=i<k),
```

and the terminal coefficient is `-U'_{k-1}`.  Let `R=D mod q`.  The
coefficient injectivity just proved says that `R` determines the entire low
coefficient vector `C`, although it need not determine `U` or the terminal
coefficient.  Given `R`, the scalar quotient `Q=(D-R)/q` can have at most
`a_{k-1}` possibilities: once `C` and `U'_{k-1}` are fixed, the full formal
coefficient vector, hence `D`, is fixed.  Therefore

```
H(D) <= H(R) + log a_{k-1}.                            (3)
```

Now

```
Z-rZ' = R + q (Q + V-rV').                            (4)
```

The pair `(R,Q)` is a function of the lower copies and is independent of
`V,V'`.  Conditioning first on `R` and then on `Q` gives

```
H(Q+V-rV' | R) >= H(Q+V-rV' | R,Q) = H(V-rV').         (5)
```

This is the required conditional-entropy point: `Q` need not be a function
of `R`, and no such false recovery assertion is made.  Combining (3)--(5),
then subtracting `H(Z)=H(A)+H(V)`, gives

```
g_Z(r) >= G_T - log a_{k-1} + g_V(r).                 (6)
```

In particular, since `log a_{k-1} <= log r`, (6) and the canonical height
bound below imply `G_T <= 3K`, where
`K=max(g_Z(1),g_Z(r))`.

## Scalar height and the polynomial estimate

The canonical padded law has length `L=k+h` and deficit `Delta`.  The
canonical-base carry fact (the independently reviewed input at commit
`47c425bc238381a14ae87407655e145eb0d210f0`) gives

```
g_Z(r) >= log r - 7/192.                               (7)
```

For completeness, this follows from injectivity of
`(x,y) -> x-r^L y` on `[0,r^L)^2`, which gives `g_Z(r^L)=H(Z)`, the
submultiplicativity of dilate gains, and
`H(Z)=L log r-Delta`.  Since `r>=2`, (7) implies
`log r <= 2 g_Z(r)`.  With (6), `g_V(r)>=0`, and
`log a_{k-1}<=log r`, we obtain

```
G_T <= g_Z(r)+log r <= 3 g_Z(r) <= 3K.                 (8)
```

Together with (2), `max(G_1,G_T)<=3K`.

Let `n=P(r)`.  The explicit map

```
(A,A',V,V') -> (A-P(r)A') + q(V-nV')
```
(or just the entropy chain rule followed by conditioning) gives the
subadditive code bound

```
g_Z(n) <= G_P + g_V(n).                                (9)
```
Indeed the scalar first summand is a deterministic evaluation of the formal
vector `W-PW'`, so its entropy is at most `H(W-PW')`; no injectivity of
`W-P(r)W'` is asserted or needed.  If `n=0`, then `g_V(n)=0`.  If `n != 0`,
the interval support of `V-nV'` has at most `(1+|n|)r^h` points, hence

```
g_V(n) <= log(1+|n|).
```
Since `|n|<=S r^d`, this is at most
`d log r+log(1+S)`.  The height estimate (7) bounds the first term by
`2dK`.  Also `K >= g_Z(r) >= log 2-7/192=:c_0>0`, so
`log(1+S) <= c_0^{-1} log(1+S) K`.

Insert (1) and (8) into (9).  Absorbing the absolute constants and the
fixed `c_0^{-1}` proves `(CB-narrow)` for `n != 0`.  For `n=0`, (9) is
`g_Z(0)=0`, so the conclusion is immediate.  This also covers `d=0`,
coefficients of either sign, and degrees `d>=k`; only
`|P(r)|<=Sr^d` was used.

## Adversarial checks and nonvacuity

The terminal-boundary estimate is deliberately weaker than the tempting
statement that `R` recovers the lower copy.  It does not.  For example,
with `k=2`, `r=3`, `a_0=a_1=2`, two positive-probability pairs can have the
same low coefficient vector and the same terminal digit while different
`U`; the proof uses only (3), not false coordinate recovery.  It also works
for `k=1`: the low residue is `U_0`, and the sole lost terminal digit is
`U'_0`.

There are genuinely nonproduct admissible laws.  Take `a=2`, `r=4`,
and let `U` be uniform on the even-parity subset of `{0,1}^k`, with
`k=20`.  This is nonproduct and has `delta=log 2 <= 7k/192`.  Choose, for
example, `h=400`: then

```
Delta = k log 4 - (k log 2) + log 2 = (k+1) log 2,
7(k+h)/192 = 420*7/192 > (k+1) log 2,
```

so the padded deficit hypothesis also holds.  More generally one may take
any `a>=2`, `r=a^2`, `k>=ceil((192/7)log 2)`, and then choose `h` large
so that `k log a+log 2 <= 7(k+h)/192`.  Thus the proposition is not vacuous
and does not rely on product lower digits.

The known SC counterexample remains inside the present class: take
`r=a^2`, the first `k=a` digits iid uniform on `{0,...,a-1}`, and `h=M`
upper digits uniform with
`M=ceil((192/7)k log a)`.  Then
`Delta=k log a <= 7(k+M)/192`.  In this example the ordinary and shifted
lower coefficient-difference widths are respectively `2a-2` (and at most
`2a-2` for adjacent shifted coefficients), which is at most `r-1`; this is
the narrow-block condition, not the larger terminal scalar support width.
It has `g_Z(a) >= k log a` while the proposed SC right side would see only a
bounded multiple of the endpoint gains.  This does not contradict
`(CB-narrow)`: for the constant polynomial `P(T)=a`, the allowed
`log(1+S)` term is of order `log a` and pays for the example.

## Exact frontier

What is proved here is CB only for a narrow lower block whose every adjacent
coefficient-difference range fits inside one base interval, followed by an
independent uniform interval block.  The proof's two indispensable interfaces
are (i) residue uniqueness from the width condition and (ii) independence of
that lower block from the padded high block.

No unnamed reduction extends this to wide alphabets, arbitrary rational laws,
or cross-block dependence.  With wide alphabets, residues no longer recover
coefficient vectors and the terminal quotient can have many more than
`a_{k-1}` possibilities.  With cross-block dependence, (5) loses the
independence needed to retain `H(V-rV')`.  Establishing a transfer across
those boundaries is the exact missing step; this note supplies no promise
that such a transfer exists.

The source attribution for the formal estimate is the reviewed
`CorrelatedPolynomialBox` artifact above.  The scalar inequalities used in
(7)--(9) agree with Tao, arXiv:2511.15135, Proposition `dilate` (the supplied
source file `kakeya__1_.tex`): product subadditivity, the canonical height
argument, and finite-support entropy bounds.  These are prose-checked
inputs here, not Lean-certified or adopted theorems, and no novelty claim is
made.
