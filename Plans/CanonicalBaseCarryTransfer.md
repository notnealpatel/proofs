# Canonical-base carry transfer: scalar status

## Question and exact scope

Fix integers `r >= 2` and `L >= 1`. Let `U` have an arbitrary joint law supported on
`{0,...,r-1}^L`; no digit independence is assumed. Put
$$
 Z=\sum_{i=0}^{L-1}U_i r^i,
 \qquad \Delta=L\log r-H(U),
$$
and assume `Delta <= 7L/192`. Let `Z'` be an independent *whole-vector* copy of
`Z`, and, for an integer `a`, set
$$
 g(a)=H(Z-aZ')-H(Z).
$$
The selected claim is that there is an absolute constant `C`, independent of
`r,L,U,d,S`, such that every nonzero `P in Z[T]` of degree `d`, with
`S=sum_j |c_j| >= 1`, satisfies
$$
 g(P(r))\le C\bigl[d+1+\log(1+S)\bigr]\max\{g(1),g(r)\}. \tag{CB}
$$
This note concerns only this canonical scalar box. It makes no inverse,
universal, rational-law, finite-field, #711, or novelty claim.

## Verified canonical facts

Canonical evaluation is a bijection from the digit box to
`{0,...,r^L-1}`. Consequently `Z-r^L Z'` is injective as a map from the pair
of interval-supported values: if `x-r^L y = x'-r^L y'`, with both first and
second coordinates in `[0,r^L-1]`, then `x=x'` and `y=y'`. Hence
$$
 g(r^L)=H(Z).
$$
The multiplicative inequality `g(ab) <= g(a)+g(b)` (for the same fixed `Z`)
then gives
$$
 g(r)\ge H(Z)/L=\log r-\Delta/L\ge\log r-7/192. \tag{1}
$$
This is a genuine scalar height lower bound; it is not a transfer of a formal
coefficient-vector gain.

The interval support also gives, for every nonzero integer `n`,
$$
 H(Z-nZ')\le \log((|n|+1)r^L),
 \quad\text{so}\quad
 g(n)\le \log(1+|n|)+\Delta. \tag{2}
$$
Formula (2) is insufficient for (CB): the allowed deficit is proportional to
`L`, whereas the desired right side has no standalone `L` term. In particular,
`Delta` cannot simply be paid from `g(1)`.

## Genuine attempt using the reviewed source calculus

For sparse Horner evaluation, write the nonzero terms of `P` in increasing
exponent order. The fixed-law inequalities
$$
 g(ab)\le g(a)+g(b),
\qquad
 g(a_1+\cdots+a_m)\le \sum_j g(a_j)+(m-1)g(1)
$$
give the rigorous bound
$$
 g(P(r))\le d\,g(r)+(k-1)g(1)+\sum_{c_j\ne0}g(c_j), \tag{3}
$$
where `k` is the number of nonzero coefficients (`1 <= k <= d+1`). The
exponents telescope in Horner, so (3) charges total degree only once.

The source integer estimate, as recorded in
`Plans/RationalPolynomialEntropy.md`, is
$$
 g(n)\le (4+10\lfloor\log_2|n|\rfloor)g(1)
$$
for a nonzero integer `n`. Tao's exact proposition is for one `Q`-valued
random variable and an independent copy (our finite canonical law is a
specialization); together with
`g(a^{-1})=g(a)` and the displayed sum/product rules, this is not an
independence assertion about digits or later SD variables. Applying it to (3)
proves
$$
 g(P(r))\le
 \left[d+5k-1+10\sum_{c_j\ne0}\lfloor\log_2|c_j|\rfloor\right]
 \max\{g(1),g(r)\}. \tag{4}
$$
This establishes (CB) for bounded coefficient magnitudes, but not uniformly:
for dense coefficients it can cost `k log(S/k)`, potentially of order
`d log(S/d)`, rather than `d+log(1+S)`. No batching inequality in the reviewed
source calculus removes this loss.

## Adversarial checks and what they do (and do not) show

An extensive deficit alone is not a counterexample. Fix the lowest `t` digits
and take the remaining digits independent uniform. Then
`Z=b+r^t X`, where `X` is uniform on an interval; `Delta=t log r`. Translation
and nonzero scaling preserve every `g(a)`, so this family has
`g_Z(n)=g_X(n)` and no `Delta` loss in the scalar gaps. It is admissible whenever
`t log r <= 7L/192` and demonstrates why (2) is crude, not why (CB) fails.

More general correlated laws or uniform sparse subsets are not reduced to this
arithmetic-progression model by the entropy hypothesis. No concrete law giving
an asymptotic violation of (CB) has been found. Conversely, high entropy alone
has not yielded the required per-scale control of dilate entropies.

## A concrete counterexample to the proposed scalar bridge (SC)

The stronger inequality (SC) is false, even for independent digits. Fix an integer
`a >= 2`, set `r=a^2` and `k=a`, and let the first `k` canonical digits be
iid uniform on `{0,...,a-1}`. Let the next `M` digits be iid uniform on
`{0,...,r-1}`, independently of the first block. Thus
$$
 Z=A+r^kV,
 \quad A=\sum_{i<k}U_i r^i,
 \quad V\sim\operatorname{Unif}\{0,\ldots,r^M-1\}.
$$
Choose
$$
 M=\left\lceil {192\over7}k\log a\right\rceil,
 \qquad L=k+M.
$$
Then
$$
H(Z)=k\log a+M\log r,
\qquad \Delta=k\log(r/a)=k\log a\le {7L\over192},
$$
so this is an admissible canonical law.

Put `B=A-aA'` and `R=B mod r^k`, with `R` in `{0,...,r^k-1}`. Each coefficient
`C_i=U_i-aU_i'` runs bijectively through
`{-a(a-1),...,a-1}`, a consecutive interval of width `a^2-1=r-1`. Adding
`b=a(a-1)` to each coefficient converts the formal base-`r` expansion to all
ordinary digit vectors:
$$
 B+b\sum_{i<k}r^i=\sum_{i<k}(C_i+b)r^i.
$$
Therefore `B` runs bijectively through an interval of width `r^k-1`; its
residue `R` determines `(A,A')`, and is uniform on all `r^k` residues. If
`Q=(B-R)/r^k`, then `Q` is a function of `R`, and
$$
 Z-aZ'=R+r^k(Q+V-aV').
$$
Residue/quotient decomposition is bijective, including negative quotients.
Since `(V,V')` is independent of `R`,
$$
 H(Z-aZ')=k\log r+H(V-aV')\ge k\log r+M\log r,
$$
where the last step is `H(V-aV') >= H(V-aV'|V')=H(V)`. Hence
$$
 g(a)\ge k\log a. \tag{5}
$$

For comparison, explicit coefficient codes give small reference gains. The
`k` low differences and the high difference imply
$$
 g(1)\le k\log(2a-1)+\log(2r^M-1)-H(Z)
 \le k\log(2-1/a)+\log2. \tag{6}
$$
For `r`, use
$$
 Z-rZ'=U_0+\sum_{i=1}^{k-1}(U_i-U'_{i-1})r^i
+r^k(V-rV'-U'_{k-1}).
$$
The displayed coefficients form an explicit code. The last has at most
`(r+1)(r^M-1)+a <= (r+1)r^M` possible values, so
$$
 g(r)\le (k-1)\log(2-1/a)+\log(r+1). \tag{7}
$$
No unique decoding is needed for these upper bounds. Thus, with `k=a` and
`r=a^2`, `max(g(1),g(r))=O(a)`, whereas (5) is `a log a`.

The proposed scalar inequality
$$
 g(n)\le A\left(1+{\log(1+|n|)\over\log r}\right)\max\{g(1),g(r)\}
$$
would have a bounded multiplier at `n=a`, since
`1+log(1+a)/log(a^2) <= 2`. Equations (5)--(7) therefore contradict it as
`a` tends to infinity. This is a genuine refutation of SC, not of CB.

Indeed, taking the constant polynomial `P(T)=a` gives `d=0`, `S=a`; the
factor `log(1+S)` in CB is of order `log a` and pays exactly for this example.
Thus this example does not refute CB; CB remains open in the stated
canonical class. The prior `Delta <= 1/8` fallback remains a separate stricter
intermediate and is not being promoted to a solution.

## Source and dependency audit

The correlated formal-box input in `Plans/CorrelatedPolynomialBox.md` proves a
coefficient-vector estimate for `W(T)` and an independent copy under arbitrary
digit correlations, but its scalar transfer requires a large base
`|r| >= (1+S) max_i(N_i-1)+1`; it therefore does not apply at canonical base
`N_i=r` with unrestricted coefficients. Its formal gains must not be renamed
as scalar gains. The present note uses only the canonical injectivity fact and
(1).

The primary source (Tao, arXiv:2511.15135, Proposition `dilate`, checked directly) states these inequalities for a single `Q`-valued random variable `X`, with `X'` an independent copy and `g(a)=H[X-aX']-H[X]` (in our application the law is finite, so all entropies are finite). It gives `g(0)=0`, `g(a^{-1})=g(a)` for nonzero `a`, the product and finite-sum inequalities above, and for nonzero integer `n`,
$$
 g(n)\le (4+10\lfloor\log_2|n|\rfloor)g(1).
$$
The source also has the separate sign comparison `g(-a) <= 3g(a)`; it is not needed here. These hypotheses do not impose digit independence. They likewise do not provide a canonical-box carry theorem, coefficient batching, or an inverse transfer to arbitrary rational laws. Therefore SC is **refuted by the above family**, while CB remains **unproved and unrefuted**. Further progress requires a different bridge or a direct proof of CB; nothing here implies that a universal conjecture is false.
