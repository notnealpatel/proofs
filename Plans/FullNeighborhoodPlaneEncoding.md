# Full-neighborhood affine-plane encoding: diagnostic for #711

## Grade and scope

**Grade: exact diagnostic, negative for this encoding.** The specified encoding is valid for every integer `d <= n`, every nonempty Hall subset `D ⊆ {1,...,n}`, every `m >= 0`, and every nonempty interval
$$
 I=\{m+1,\ldots,m+H\}.
$$
It uses the actual full neighborhoods, not selected equal-length progressions. The correlated-plane fiber inequality is true, but for this encoding its dependence correction cancels the plane entropies and mutual-information terms exactly. Thus it supplies no improvement beyond the direct support accounting. This is not a prime-only statement and makes no exponent claim.

All logarithms below have one fixed base. The assertions are finite entropy identities or elementary counting arguments, not Lean-checked statements.

## 1. Full neighborhoods and the stationary walk

For each `d in D`, let `N_d = I ∩ dZ`. Empty neighborhoods are omitted. When `N_d` is nonempty, let `a_d` be its first member and split the *entire* neighborhood into tagged parity classes
$$
 B_{(d,0)}=\{a_d+2jd:0\leq j<r_{d,0}\},
 \qquad
 B_{(d,1)}=\{a_d+(2j+1)d:0\leq j<r_{d,1}\}.
$$
Equivalently, the tag records the parity of the index in the displayed progression (and hence, after the fixed offset `a_d/d`, also determines the parity of `x/d`). Let `\mathcal L` be the nonempty tags, write
$$
 r_\ell=|B_\ell|,
 \qquad E=\sum_{\ell\in\mathcal L}r_\ell=\sum_{d\in D}|N_d|,
$$
and let
$$
 c(x)=|\{\ell:x\in B_\ell\}|=|\{d\in D:d\mid x\}|.
$$
The equality holds because the two parity tags for a fixed `d` partition `N_d`.

Assume first `E>0`. The stationary incidence walk is
$$
 \ell_0\sim r_{\ell_0}/E,\quad
 X_0\mid\ell_0\sim\operatorname{Unif}(B_{\ell_0}),\quad
 \ell_1\mid X_0\sim\operatorname{Unif}\{\ell:X_0\in B_\ell\},
$$
followed by `X_1` uniform in `B_{\ell_1}`, then `\ell_2` uniform through `X_1`, then `X_2` uniform in `B_{\ell_2}`. The exact probability of an admissible walk is
$$
 \Pr(W=w)=
 \frac1{E\,c(X_0)\,r_{\ell_1}\,c(X_1)\,r_{\ell_2}}. \tag{1}
$$
The initial factor `r_{\ell_0}` cancels against the first uniform-point factor. In particular, label coordinates have marginal `r_\ell/E` and point coordinates have marginal `c(x)/E`, but conditioning below does not preserve these marginals.

The exact unequal-degree entropy is therefore
$$
 H(W)=\log E
 +\frac2E\sum_xc(x)\log c(x)
 +\frac2E\sum_\ell r_\ell\log r_\ell. \tag{2}
$$
No common-degree formula is being used. Let `G` be exactly
$$
 \ell_0\ne\ell_1,\quad \ell_1\ne\ell_2,
 \quad X_0\ne X_1,\quad X_1\ne X_2,
$$
with no restriction on `\ell_0=\ell_2` or `X_0=X_2`. Put `g=Pr(G)`. If `g=0`, the conditional law given `G` is undefined and this diagnostic stops (the event must be handled separately). If `g>0`, (1) gives the exact conditional accounting
$$
\begin{aligned}
 H(W\mid G)= {}&\log(Eg)\\
 &+E\bigl[\log c(X_0)+\log r_{\ell_1}
       +\log c(X_1)+\log r_{\ell_2}\mid G\bigr]. \tag{3}
\end{aligned}
$$
This is the required variable-degree formula; stationarity cannot be substituted into the conditional expectations.

## 2. Good paths, full-neighborhood containment, and labels

Let `U=\bigcup_{d\in D}N_d`. On `G`, both consecutive point pairs lie in one parity class. Hence
$$
 M_1=(X_0+X_1)/2\in N_{d_1},
 \qquad M_2=(X_1+X_2)/2\in N_{d_2},
 \qquad X_1\in U.
$$
The midpoint is an integer multiple because the two quotient indices have the same parity; it lies in `I` because `I` is an interval and both endpoints lie in `I`. Writing `Y_i=X_i-m`, the output below therefore lies in
$$
 (2(U-m))\times(2(U-m))\times(U-m). \tag{4}
$$
This uses every point of each `N_d`; there is no truncation to an equal-length selected AP.

Set
$$
 \kappa=\max_{1\le t\le H}|\{d\in D:d\mid t\}|.
$$
For distinct `x,y` in `I`, a tagged parity class containing both requires
$$
 d\mid x,\qquad d\mid (y-x)/2,
$$
and the parity tag is then uniquely determined as
$$
 \epsilon=(x-a_d)/d\pmod 2.
$$
The parity of `x/d` alone is offset-dependent. Since `0<|y-x|/2<H`, there are at most `\kappa` possible divisors, including for composite `d`; no cancellation or primality assumption is used. Consequently, after the initial tag and the point triple are known, the remaining pair `(\ell_1,\ell_2)` has at most `\kappa^2` possibilities. Remote repetitions are allowed and do not affect this argument.

## 3. The specified affine-gauge encoding

Put
$$
 T=2d_0+\epsilon_0,\qquad B=2H+1,
$$
and define
$$
\begin{aligned}
 P&=(Y_0+BT,Y_1,0),\\
 Q&=(Y_1-BT,0,Y_2),\\
 R&=(0,Y_2,Y_1-Y_2).
\end{aligned} \tag{5}
$$
Then
$$
 S=P+Q+R=(Y_0+Y_1,Y_1+Y_2,Y_1). \tag{6}
$$
Since `1 <= Y_i <= H < B`, each coordinate involving `BT` has a unique decomposition with its residue in `{1,...,H}`. Thus:

* `P` recovers `(T,Y_0,Y_1)`;
* `Q` recovers `(T,Y_1,Y_2)`;
* `R` recovers `(Y_1,Y_2)`.

The map `T=2d_0+epsilon_0` is injective: its parity recovers `epsilon_0` and then `d_0`. Therefore `(P,Q,R)` and
$$
 Z=(T,Y_0,Y_1,Y_2)
$$
determine one another. More strongly, `S` itself determines the whole ordered point triple:
$$
 Y_1=S_3,\qquad Y_0=S_1-S_3,\qquad Y_2=S_2-S_3. \tag{7}
$$
The third/free point coordinate is essential; it has not been discarded.

The exact remaining-label decomposition, under the conditional law given `G`, is
$$
 H(W\mid G)=H(S\mid G)+H(T\mid S,G)+b,
 \qquad b=H(\ell_1,\ell_2\mid T,Y_0,Y_1,Y_2,G)\le2\log\kappa. \tag{8}
$$
This is the precise entropy/remaining-label accounting. The inequality is a support bound, not an assertion of uniformity.

## 4. Full correlated-plane inequality: exact cancellation

All quantities in this section are under the law conditional on `G`. Set
$$
 h=H(S),\quad a=H(T\mid S),
 \quad p=H(P),\ q=H(Q),\ r=H(R).
$$
Recoverability and (7) give only
$$
 H(P,Q,R)=h+a.
$$
The individual plane entropies must not be identified with `h+a`: `P` omits `Y_2`, while `Q` omits `Y_0`. What is exact is
$$
 H(P\mid S)=H(Q\mid S)=a,
 \qquad H(R\mid S)=0,
$$
and therefore
$$
 \operatorname{TC}(P,Q,R)=p+q+r-h-a,
$$
$$
 I(P;S)+I(Q;S)+I(R;S)=p+q+r-2a.
$$
Substitution into the supplied verified fiber inequality gives the **full RHS**
$$
\begin{aligned}
 &\frac12(p+q+r)-\operatorname{TC}(P,Q,R)
 +\frac12\{I(P;S)+I(Q;S)+I(R;S)\}\\
 &\quad=\frac12(p+q+r)-(p+q+r-h-a)
   +\frac12(p+q+r-2a)=h=H(S).
\end{aligned}
$$
Thus the full inequality is an equality for every conditional distribution supported on this encoding. The dependence penalty is not an unestimated small error: together with the mutual-information terms it cancels exactly.

If the mutual-information terms are dropped, the resulting bound is instead
$$
 H(S)\ge \frac12(p+q+r)-\operatorname{TC}(P,Q,R)
 =h+a-\frac12(p+q+r). \tag{14}
$$
This expression is not sign-definite and must not be called vacuous or negative. Equivalently, if `u=H(S\mid P)` and `v=H(S\mid Q)`, then the same RHS is
$$
 \frac12(u+v-r),
$$
using `H(S)=h`, `H(P\mid S)=H(Q\mid S)=a`, and `R` being determined by `S`. In either form, dropping MI supplies no new restriction beyond the identity. The direct exact accounting remains (8), with the residual `H(T\mid S,G)` and the nonuniform remaining-label entropy `b` retained.

The scoped obstruction is therefore precise: this pair-cover inequality imposes no additional restriction on the encoded law. It does not prove that all other entropy estimates fail, nor does it rule out a general exponent improvement from a genuinely different encoding.

## 5. Source audit, CRT compatibility, and limits

The supplied `EntropyWalk.md` at full revision
`b30fb4cfaf23039c2b80820fdcc894eedff888fc` is retained only as an earlier **selected common-AP baseline**. It is not a theorem about the present full, unequal-degree variable-neighborhood walk, so no source-level cubic estimate is inherited here.

The supplied `EntropyExcessCRT.md` at full revision
`672d5ebf503e293036ea21732e6f1c584cadab9a` is compatible with the present diagnosis: its actual full prime-neighborhood examples have `\kappa=1`, `R\to\infty` with `R=n^{o(1)}`, and `h/\log R\to1`. They refute a fixed-factor degree-entropy excess for all `R`; they do not refute a polynomial-`R` claim and do not license a prime-only conclusion.

The verified correlated-plane source is `Plans/NoncommutingFiberShearer.md` at full revision
`93729b6501d7559370aac679950c6c9effcc01a5`. The local primary source was checked at `/home/exedev/p/erdos711-restart-20261009/sources/ChenKorsky-2607.26450.tex`: its local progression-union estimate begins at Section 2 (the `local-cube-root` lemma, around line 121), while the prime CRT construction begins at Section 5 (around line 326). Those are source dependencies only; the stationary formulas and the cancellation above are new elementary calculations for the present encoding.

No global exponent conclusion follows. This note closes only the specified affine-gauge encoding: its full correlated-plane inequality is an identity for every conditional law, while its dropped-MI form is the exact expression (14), not a sign claim. A different encoding or arithmetic control remains open.

## 6. Structural obstruction to the proposed global spectral route

The previously suggested uniform global mixing hypothesis is impossible in general. Put
$$
 g_2=2^{\min_{d\in D}v_2(d)}.
$$
Every `d` is divisible by `g_2`, and in the present full-neighborhood construction every point of every nonempty `N_d` is a multiple of `g_2`. Moreover, each tagged parity class is wholly contained in exactly one of the two residue classes
$$
 0\pmod{2g_2}\quad\text{or}\quad g_2\pmod{2g_2},
$$
with the precise tag epsilon given by `(x-a_d)/d mod 2`; the parity of `x/d` alone is offset-dependent.

For the normalized label-chain kernel
$$
 K(\ell,\ell')=\frac1{r_\ell}
 \sum_{x\in B_\ell\cap B_{\ell'}}\frac1{c(x)},
$$
a transition cannot cross these two residue classes. If both residues occur among the nonempty labels, the chain has at least two closed components, so eigenvalue `1` has multiplicity at least two. Since this incidence up-down operator is reversible and positive semidefinite, its nontrivial eigenvalues satisfy
$$
 \sum_{j\ge2}\lambda_j^{2t}\ge1
$$
for every `t>=1`. Therefore a global `o(1)` spectral sum hypothesis cannot hold uniformly.

Componentwise mixing after splitting by residue is a possible change of load-bearing feature, but it has not been shown to pay the conditional residual label entropy `H(T\mid S,G)`. It is consequently left **UNESTABLISHED**, not offered as a delivered reopening mechanism. No midpoint-balance claim or raw-path repetition is being proposed.

## Consumer limits and boundary cases

* `D=empty` or `E=0`: there is no stationary incidence walk; Hall's empty condition is separate.
* `G` of probability zero: conditional entropies above are undefined and must not be assigned asymptotic meaning.
* The four exclusions defining `G` are exact; remote repeats remain allowed.
* The `\kappa` bound uses distinct adjacent points and the range `1 <= |X_i-X_{i-1}|/2 < H`; it is valid for composite divisors.
* The residual label law need not be uniform, so `2 log \kappa` is only a support upper bound.
* No prime restriction, polynomial-regime inference, exponent claim, or replacement of full neighborhoods by selected APs is used.

**Conclusion:** close the specified affine-gauge plane encoding. Its exact correlated entropy identity is a rigorous obstruction to extracting a dependence gain from this construction; any progress must alter the observable or impose genuinely new arithmetic mixing/control.
