# Original half-interval: a variance-filtered fourth-moment bound

This is a restricted prose bound. Novelty is unverified. It is not a Lean
formalization. Review and adoption records are maintained separately from
these theorem-and-proof bytes.

## Definitions and exact theorem

Let $p$ be any odd prime, let $q$ be any integer with $1\le q\le p$, and
write $\mathbb F_p=\mathbb Z/p\mathbb Z$. Integers in the following sets
and expressions are reduced modulo $p$. Put

$$
h=\frac{p-1}{2},\qquad C=\{0,1,\ldots,h\}\subset\mathbb F_p,
\qquad m=|C|=\frac{p+1}{2},\qquad \rho=\frac mp.
$$

For $a\in\mathbb F_p^\times$ and $b\in\mathbb F_p$, define

$$
Y_a(b)=\sum_{j=0}^{q-1}1_C(aj+b),\qquad f_a(b)=Y_a(b)-\rho q,
$$

$$
S(a)=\frac1p\sum_{b\in\mathbb F_p}|f_a(b)|^2,
\qquad F_4(a)=\frac1p\sum_{b\in\mathbb F_p}|f_a(b)|^4.
$$

Define the nonzero-direction variance average and its retained set by

$$
\overline S=\frac1{p-1}\sum_{a\in\mathbb F_p^\times}S(a),
\qquad R=\{a\in\mathbb F_p^\times:S(a)\le2\overline S\}.
$$

For each positive integer $n$, let $H_n=\sum_{r=1}^n1/r$. All logarithms
below are natural. For a nonempty finite set $R$, write
$\mathbb E_R G=|R|^{-1}\sum_{a\in R}G(a)$.

**Theorem.** With exactly these definitions and quantifiers,

$$
\overline S=\frac{m(p-m)q(p-q)}{p^2(p-1)}
=\frac{(p+1)q(p-q)}{4p^2},\qquad |R|\ge\frac{p-1}{2}>0,
$$

and

$$
\boxed{\quad \mathbb E_R F_4\le q^2H_h^2
\le q^2(1+\log h)^2.\quad}
$$

In particular this proves the specified bound with fixed logarithmic
exponent $B=2$ when $q=\lceil p^{5/12}\rceil$, which lies in $[1,p]$.

## Proof

### 1. Exact variance average and the zero-variance case

For every nonzero $a$, averaging over $b$ gives $\mathbb E_bY_a=\rho q$.
For distinct $j,j'\in\{0,\ldots,q-1\}$, their difference is nonzero in
$\mathbb F_p$. The map

$$
(a,b)\longmapsto(aj+b,aj'+b)
$$

is a bijection from $\mathbb F_p^\times\times\mathbb F_p$ to ordered
pairs of distinct field elements. Consequently, with uniform averages,

$$
\mathbb E_{a\ne0,b}1_C(aj+b)1_C(aj'+b)
=\frac{m(m-1)}{p(p-1)}.
$$

The diagonal expectation is $\rho$. Expanding the centered square gives

$$
\overline S
=q\rho(1-\rho)
+q(q-1)\left(\frac{m(m-1)}{p(p-1)}-\rho^2\right)
=\frac{m(p-m)q(p-q)}{p^2(p-1)}.
$$

Substituting $m=(p+1)/2$ gives the stated formula. If $q<p$, then
$\overline S>0$. Nonnegativity and Markov's inequality imply that at
most half of the $p-1$ directions have $S(a)>2\overline S$, so
$|R|\ge(p-1)/2$. No probabilistic independence is involved.

If $q=p$, the points $aj+b$, $0\le j<p$, enumerate the field for every
nonzero $a$. Thus $Y_a(b)=m=\rho q$, $f_a(b)=0$, and
$S(a)=F_4(a)=0$. In this case $\overline S=0$ and
$R=\mathbb F_p^\times$, so the theorem holds directly. In particular
nonemptiness in the zero-variance case does not rely on dividing by
$\overline S$. Below one may assume $q<p$.

### 2. Normalized Fourier expansion and the interval bound

Set $e_p(t)=\exp(2\pi i t/p)$, and use the normalized Fourier transform
and unnormalized finite exponential sum

$$
\widehat{1_C}(k)=\frac1p\sum_{x\in\mathbb F_p}1_C(x)e_p(-kx),
\qquad D_q(t)=\sum_{j=0}^{q-1}e_p(tj).
$$

Fourier inversion has no prefactor with this convention. Since
$\widehat{1_C}(0)=\rho$ and $D_q(0)=q$, centering removes exactly the
zero mode and gives

$$
f_a(b)=\sum_{k\in\mathbb F_p^\times}
\widehat{1_C}(k)D_q(ak)e_p(kb).
$$

Represent each nonzero $k$ by its unique signed integer with
$1\le|k|\le h$. The geometric-sum formula for this specific interval gives

$$
|\widehat{1_C}(k)|
=\frac{|\sin(\pi km/p)|}{p|\sin(\pi k/p)|}
\le\frac1{2|k|}.
$$

Indeed, $0<\pi|k|/p<\pi/2$ and $\sin x\ge2x/\pi$ on
$[0,\pi/2]$, while the numerator is at most one. Hence

$$
L:=\sum_{k\ne0}|\widehat{1_C}(k)|\le H_h\le1+\log h.
$$

The last inequality follows from the integral comparison for the harmonic
sum, including $h=1$.

### 3. Exact quadratic affine-pair count, conditional on retention

For each fixed $k\ne0$, multiplication by $k$ permutes the nonzero
residues. Character orthogonality, and the fact that $j=j'$ is the only
congruence $j\equiv j'\pmod p$ among $0\le j,j'<q\le p$, give

$$
\sum_{t\in\mathbb F_p}|D_q(t)|^2
=\sum_{0\le j,j'<q}\sum_{t\in\mathbb F_p}e_p(t(j-j'))=pq.
$$

Removing $t=0$ subtracts $q^2$, so exactly

$$
\sum_{a\ne0}|D_q(ak)|^2=q(p-q).
$$

All summands are nonnegative. Although $R$ depends on the variances,
restriction to $R$ therefore gives the valid conditional estimate

$$
\mathbb E_R|D_q(ak)|^2
\le\frac{q(p-q)}{|R|}
\le\frac{2q(p-q)}{p-1}=:A.
$$

Only this quadratic sum is enlarged to all nonzero directions. No
unrestricted fourth-moment average is substituted for the retained one.

### 4. Conditional Cauchy--Schwarz and the full variance filter

For each direction put

$$
B_a=\sum_{k\ne0}|\widehat{1_C}(k)|\,|D_q(ak)|.
$$

The Fourier expansion gives $\|f_a\|_\infty\le B_a$, where the supremum
norm is the maximum over $b\in\mathbb F_p$. Cauchy--Schwarz in the uniform
average on $R$ gives, for any nonzero $k,\ell$,

$$
\mathbb E_R\bigl(|D_q(ak)|\,|D_q(a\ell)|\bigr)
\le\sqrt{\mathbb E_R|D_q(ak)|^2\,
              \mathbb E_R|D_q(a\ell)|^2}\le A.
$$

Expanding $B_a^2$ and applying this to every cross term gives

$$
\mathbb E_RB_a^2\le A L^2.
$$

Equivalently this is Minkowski's inequality in normalized $L^2(R)$.
It assumes neither frequency independence nor phase cancellation.

For every retained direction, keep the full defining variance inequality:

$$
F_4(a)\le\|f_a\|_\infty^2\frac1p\sum_b|f_a(b)|^2
\le B_a^2S(a)\le2\overline S B_a^2.
$$

Averaging, substituting the exact variance and quadratic-count constants,
and then using $L\le H_h$ yields

$$
\mathbb E_RF_4\le2\overline S A L^2
=\frac{p+1}{p-1}\frac{q^2(p-q)^2}{p^2}L^2
\le q^2H_h^2.
$$

For clarity, the last numerical coefficient satisfies, since $q\ge1$,

$$
\frac{p+1}{p-1}\frac{(p-q)^2}{p^2}
\le\frac{p+1}{p-1}\frac{(p-1)^2}{p^2}
=\frac{p^2-1}{p^2}<1.
$$

This completes the proof.

### 5. The other endpoint: $q=1$

When $q=1$, $Y_a(b)=1_C(b)$ is independent of $a$. Thus
$S(a)=\rho(1-\rho)=\overline S>0$, and all directions are retained.
The proof above applies without modification, with $D_1(t)=1$ and
$A=2$. The fourth moment is explicitly

$$
F_4(a)=\rho(1-\rho)^4+(1-\rho)\rho^4.
$$

Together with the separate $q=p$ case, both endpoints of the theorem's
quantified range have been addressed.

## Scope and the interval bottleneck

The load-bearing interval input is $L\le H_h$, obtained from the
geometric Fourier formula for $C=\{0,\ldots,(p-1)/2\}$. Exact quadratic
counting does not replace this input. This artifact asserts no uniform
arbitrary-$C$ dilation theorem, selected-minimum theorem, or inference
from a sampled interval class to arbitrary sets.

The result bounds a retained **mean**, not each retained direction. A
single large retained fourth moment in the separate enlarged-interval
family does not refute this theorem and must not be relabeled as an
original-half-interval or retained-mean counterexample. The two interval
families are not identified here.

There is no claimed improvement to the adjacent arbitrary-set problem or
to Erdős #711, no claim of literature priority, and no certification of a
broader interval or arbitrary-set theorem.

## Operation history and withdrawn necessity claim

The initial same-owner operation kept only coefficientwise consequences
of the variance filter and combined truncated one-frequency fourth
amplitudes with Hausdorff--Young/weighted Hölder. The owner reported the
weaker loss $O(q^{5/2}(\log p)^2)$ and claimed that removing it required a
coupled additive-four-frequency estimate. That necessity claim was
incorrect and has been explicitly withdrawn; neither that estimate nor
the initial operation is a dependency of the proof above.

Controller inspection supplied the correction: retain the full $S(a)$
filter in $F_4(a)\le S(a)\|f_a\|_\infty^2$, count **second** amplitudes
exactly, and apply conditional $L^2$ Cauchy--Schwarz/Minkowski. This removes
the earlier extra $q^{1/2}$ loss. The same mathematical owner checked the
correction with adversarial `tool_think` and direct algebra. That check
was actually performed, but it was not independent review.

The initial exploratory output was
`9b1ff0e7a4c7ab0abc2705d738f074c3db0b8f19`; the corrected same-owner output
was `fc4c163ec374faee1d6ad33e13663fea15a6b9eb`. Both were zero-diff
repository outputs. This standalone artifact freezes the corrected
argument without expanding its mathematical scope.
