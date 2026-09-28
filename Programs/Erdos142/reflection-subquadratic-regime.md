# Reflection mass/energy: the subquadratic regime

> **Status.** This note records a route closure for a restricted size regime,
> not a proof of the universal reflection estimate or of Erdős 142.  The
> finite universal mass/energy bounds used below are **kernel checked** in the
> existing Lean development.  The averaged fiber-overlap theorem below is an
> **independently audited accepted prose theorem**; its Lean formalization is
> in progress and is not claimed here.  The asymptotic consequence, the
> fixed-digit corollary, and the two-cluster consequence are accepted prose
> deductions using this theorem; none is claimed as a Lean theorem.

## Setup and the exact sufficient condition

Let $N\ge2$ and let $A\subseteq[0,N^2)$ be a scalar 3-AP-free cap, put
$m=|A|>N$, and write

$$
 r=r_3(N),
 \qquad
 F_N=\frac{r^{8/3}}{N^{2/3}}.
$$

For an in-range target $c\in[0,N^2)$, let

$$
 \nu(c)=\#\{(a,b)\in A^2:a\ne b,\ 2a-b=c\},
$$

and define the reflection mass and energy by

$$
 M=\sum_{0\le c<N^2}\nu(c),
 \qquad
 E=\sum_{0\le c<N^2}\nu(c)^2.
$$

The candidate estimate with constant $1$ is

$$
 \tag{O}
 E\le \frac{M^2r^{8/3}}{N^{2/3}(m-N)^2}
   =\frac{F_NM^2}{(m-N)^2}.
$$

The existing finite reflection bounds are

$$
 E\le(m-1)M,
 \qquad
 Q(m):=\left\lfloor\frac{(m-1)^2}{4}\right\rfloor\le M.
$$

Since $M>0$ in the present range, the first bound implies (O) whenever

$$
 F_NM\ge(m-1)(m-N)^2.
$$

Consequently, the exact sufficient condition supplied by these two universal
bounds is

$$
 \boxed{\quad
 F_NQ(m)\ge(m-1)(m-N)^2.
 \quad}
 \tag{SC}
$$
Indeed, (SC) and $M\ge Q(m)$ give the preceding inequality, and then
$E\le(m-1)M\le F_NM^2/(m-N)^2$.

## Independently audited averaged fiber-overlap theorem

Here are the exact conventions.  Let $A\subseteq[0,T)$ be a scalar
3-AP-free set, let $m=|A|$, and, for every integer $c\in[0,T)$, put

$$
 X_c=\{a\in A:a\ne c,\ 2a-c\in A\},
 \qquad n_c=|X_c|,
 \qquad M=\sum_{0\le c<T}n_c,
 \qquad E=\sum_{0\le c<T}n_c^2.
$$

For $c\ne d$, the map sending $a\in X_c\cap X_d$ to the ordered pair
$(2a-d,2a-c)$ injects this intersection into the fixed nonzero-difference
pairs in $A$.  Capness makes those pairs a matching, so
$|X_c\cap X_d|\le\lfloor m/2\rfloor$ and therefore

$$
 n_c+n_d\le B,
 \qquad B:=m+\left\lfloor\frac m2\right\rfloor.
$$

Also $n_c\le m-1$: if $c\in A$, capness makes $X_c$ empty; if
$c\notin A$ and $X_c=A$, the finite set $A$ would be closed under
$a\mapsto2a-c$, whose iterates $c+2^k(a-c)$ are unbounded unless $a=c$.
The already audited mass lower bound is

$$
 M\ge u,
 \qquad u:=\left\lfloor\frac{(m-1)^2}{4}\right\rfloor.
$$

Let $L=\max_c n_c$.  If $L\le B/2$, then
$E\le(B/2)M$.  If $L>B/2$, isolate a fiber of size $L$ and use the
pairwise bound on all other fibers:

$$
 E\le L^2+(B-L)(M-L)
  =\frac{BM}{2}+\left(L-\frac B2\right)(2L-M).
$$

For $m\ge9$, $u\ge2(m-1)\ge2L$, so the final term is nonpositive.  Thus the
independently audited averaged overlap estimate is

$$
 \boxed{\qquad E\le\frac B2M.\qquad}
 \tag{AO}
$$

For $T=N^2$, these are exactly the note's reflection multiplicities
$n_c=\nu(c)$.  Hence (AO) and $M\ge u$ give the exact sufficient condition
from this averaged theorem

$$
 \boxed{\qquad
 F_N\ge\frac{B(m-N)^2}{2u}
 \qquad}
 \tag{ASC}
$$
for (O), where $F_N=r_3(N)^{8/3}/N^{2/3}$.  This applies when
$m>N\ge2$ and $m\ge9$.

As a compact diagnostic, for
$A_m=\{2^j:0\le j<m\}=\{1,2,4,\ldots,2^{m-1}\}\subset[0,2^m)$ (an ambient interval
containing all nonnegative reflections),

$$
 M=\frac{(m-1)(m+2)}2,
 \qquad
 E=\frac{(m-1)(3m-2)}2.
$$

Here $n_0=m-1$, while every nonzero fiber is a singleton, so this example
refutes no averaged bound.

## A convenient subquadratic regime

For $N\ge2$ and $m>N$, one has

$$
 4u\ge(m-N)^2.
 \tag{1}
$$

Indeed $u=Q(m)$.  If $m$ is odd, then
$4u=(m-1)^2$; if $m$ is even, then $4u=m(m-2)$.  In either case
$4u\ge(m-2)^2\ge(m-N)^2$.

The earlier pointwise criterion still gives the convenient hypothesis
$m\le F_N/4$.  The averaged theorem improves this, for $m\ge9$, to

$$
 m\le\frac{F_N}{3}.
 \tag{2}
$$

Indeed $B\le3m/2$, so (1) gives

$$
 \frac{B(m-N)^2}{2u}\le2B\le3m\le F_N.
$$

Thus (2) implies (ASC).  This improves $F_N/4$ by only the constant factor
$4/3$; it does not close the high-density range or solve Erdős 142.

## Behrend consequence

Use the uniform Behrend lower bound in the form

$$
 r_3(N)\ge N\exp\!\bigl(-C\sqrt{\log N}\bigr)
$$

for an absolute $C$ and all sufficiently large $N$.  Then

$$
 F_N\ge N^2\exp\!\left(-\frac{8C}{3}\sqrt{\log N}\right).
$$

Set $C'=8C/3$ (or take any larger absolute constant).  For all large $N$,
every scalar cap in the range

$$
 N<m\le\frac13N^2\exp\!\bigl(-C'\sqrt{\log N}\bigr)
 \tag{3}
$$

satisfies $m\le F_N/3$, and therefore satisfies (O) with constant $1$.
The range in (3) is nonempty for all sufficiently large $N$.

## Fixed-digit corollary

Fix $b\ge2$.  Let $E_1,E_2\subseteq[0,b)$ be ordinary caps, let

$$
 2\max(E_i)<b\quad(i=1,2),
 \qquad
 s=|E_1||E_2|>b,
$$

and define the alternating $2k$-digit set

$$
 A_k=\left\{
 \sum_{j=0}^{2k-1}a_jb^j:
 a_{2j}\in E_1,\ a_{2j+1}\in E_2
 \right\}.
$$

With

$$
 N=b^k,
 \qquad
 m=|A_k|=s^k,
$$

no digit of $2y$ or of $x+z$ can carry: the displayed digit condition puts
both below $b$.  The ordinary cap property therefore makes $A_k$ a scalar
cap in $[0,b^{2k})=[0,N^2)$.  Also, each $|E_i|<b$, so $s<b^2$
automatically, while $s>b$ gives $m>N$ for every $k$.

For the same absolute $C'$ as above,

$$
 \frac{m}{N^2\exp(-C'\sqrt{\log N})}
 =\left(\frac{s}{b^2}\right)^k
   \exp\!\left(C'\sqrt{k\log b}\right)
 \longrightarrow0.
$$

Thus $m\le\frac13N^2\exp(-C'\sqrt{\log N})$ eventually, and (O) holds
with constant $1$ for every sufficiently large member of every fixed
$(b,E_1,E_2)$ carry-free alternating digit family.  This excludes those
fixed-parameter families as counterexamples to (O).  It does not address
variable alphabets or variable digit sets, prove (O) for general scalar caps,
or solve Erdős 142.

The fixed-digit conclusion is an accepted prose deduction using the
independently audited averaged theorem, not a Lean theorem.

## Optional sharper half-range check

For a cap contained in the half-range $A\subseteq[0,N^2/2)$, every unordered
pair $x<y$ contributes the in-range reflection $2y-x$, and scalar
3-AP-freeness puts that target outside $A$.  Hence the direct count gives

$$
 M\ge\frac{m(m-1)}2.
$$

Together with the universal pointwise multiplicity bound
$\nu(c)\le m-1$ and the trivial $M\le m(m-1)$, this gives

$$
 E\le(m-1)M\le m(m-1)^2\le m^3.
$$

The alternating fixed-digit family above is in this half-range, so these are
sharper family-level checks.  They are not needed: the averaged criterion
(ASC), and already its convenient consequence (2), suffices for the
fixed-digit conclusion.

## Previously recorded digit-sphere/two-cluster family

The averaged criterion (ASC) also closes the previously documented family-only
stress test.  Take $q=d$, $Q=4d$, let $B$ be the base-$Q$ encoding of a
largest sphere in $\{0,\ldots,d-1\}^d$, and write

$$
 b=|B|\le d^d,
 \qquad
 L=1+(d-1)\frac{Q^d-1}{Q-1},
 \qquad
 A=B\cup(T-1-B),
 \qquad
 T=3L-1,
 \qquad
 m=2b,
 \qquad
 N=\lceil\sqrt T\rceil.
$$

This is the scalar two-cluster cap already recorded in the ledger.  For
$d\ge2$,

$$
 T=2+3(d-1)\frac{Q^d-1}{Q-1},
 \qquad
 \frac{3}{16}Q^d\le T\le4Q^d,
$$

so $N^2\ge(3/16)(4d)^d$.  The sphere count used in the ledger also gives
$b\ge d^d/(d(d-1)^2+1)$, which implies $m>N$ eventually.  Since
$\log N\le d\log(4d)$ for all sufficiently large $d$, the Behrend bound
above gives

$$
 \frac{m}{F_N/4}
 \le \frac{8d^d}{N^2}\exp\!\bigl(C'\sqrt{\log N}\bigr)
 \le \frac{128}{3}\,4^{-d}
       \exp\!\bigl(C'\sqrt{d\log(4d)}\bigr)
 \longrightarrow0.
$$

Therefore $m\le F_N/4$ eventually, and hence also $m\le F_N/3$; the
averaged criterion (ASC) proves (O), with constant $1$, for this stress
family as well.  This is a family-only conclusion; it is not a statement
about arbitrary variable-alphabet constructions, general (O), or Erdős 142.

## Separate exact $b=128$ evidence

The exact artifact
[`reflection-transfer-b128.md`](reflection-transfer-b128.md) is stronger for
one particular fixed family: its exact borrow-transfer matrices verify (O),
with constant $1$, for the $b=128$ alternating family for every $k\ge1$.
That all-$k$ finite computation is separate from the eventual universal
criterion above.  It remains family-specific evidence and is not a proof of
(O) for arbitrary scalar caps or of Erdős 142.
