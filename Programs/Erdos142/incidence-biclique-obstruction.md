# Erdős 142 incidence-biclique obstruction

> **Status.** This is an independently audited finite/prose route closure, not a
> Lean formalization and not a solution of Erdős 142. The midpoint checks for
> the fixed digit sets are finite computation evidence. The incidence
> identities, biclique implications, and no-carry deduction below are
> elementary proofs once those finite set properties are recorded.

## Incidence notation and degree facts

Write $[0,L)=\{0,1,\ldots,L-1\}$, and let
$A\subseteq[0,L)$ be scalar 3AP-free: there are no distinct
$x,y,z\in A$ with $x+z=2y$. Put $m=|A|$ and define the bipartite incidence
relation

$$
I_A=\{(c,d):0\le c<L,\ d\ne0,\ c+d\in A,\ c+2d\in A\},
$$

where $d$ ranges over the nonzero integers. Rows are indexed by $c$ and
columns by $d$. Define the in-range reflection multiplicity

$$
\nu_A(c)=\#\{(a,b)\in A^2:a\ne b,\ 2a-b=c\}.
$$

For every row $c$, the change of variables

$$
 d\longmapsto(a,b)=(c+d,c+2d)
$$

is a bijection from the neighbors of $c$ in $I_A$ to the representations
counted by $\nu_A(c)$. Its inverse is $d=a-c=b-a$. Therefore

$$
\deg_{I_A}(c)=\nu_A(c).
$$

For a nonzero column $d$, put

$$
 r_A(d)=\#\{a\in A:a+d\in A\}.
$$

The substitution $a=c+d$ gives the exact column formula requested here:

$$
\deg_{I_A}(d)
 =\#\{a\in A:a+d\in A,\ 0\le a-d<L\}
 \le r_A(d)\le\left\lfloor\frac m2\right\rfloor.
$$

For the last inequality, let
$X_d=\{a\in A:a+d\in A\}$. Both $X_d$ and $X_d+d$ are subsets of $A$
and have cardinality $r_A(d)$. They are disjoint: an element in their
intersection would give $a,a+d,a+2d\in A$, a nontrivial 3AP. Thus
$2r_A(d)\le m$.

## What a biclique forces

Let $C\subseteq[0,L)$ and let $D$ be a set of nonzero integers. Suppose
$C\times D\subseteq I_A$; only the nonempty case is relevant below. Then
both $C$ and $D$ are scalar 3AP-free. Indeed, if $c_1,c_2,c_3\in C$ form a
nontrivial 3AP, fix $d\in D$; the three points $c_i+d$ form a nontrivial
3AP in $A$. Conversely, if $d_1,d_2,d_3\in D$ form one, fix $c\in C$;
the three points $c+d_i$ form one in $A$.

The two sides also obey the difference exclusion

$$
\bigl((C-C)\setminus\{0\}\bigr)\cap D=\varnothing.
$$

For if $d=x-y\in D$ with distinct $x,y\in C$, the edge $(y,d)$ puts
$y+d=x$ in $A$, while the edge $(x,d)$ puts $x+d$ and $x+2d$ in $A$.
Hence $x,x+d,x+2d$ is a nontrivial 3AP in $A$, a contradiction. These are
necessary consequences of a biclique, not a sufficient characterization.

## An exact scalable family

Set

$$
\begin{aligned}
b&=128,\\
E_1&=\{0,1,5,7,11,12,16,18,26,38,39,42,44,48,53,55,59,61\},\\
E_P&=\{17,18,21,23\},\\
E_2&=E_P\cup2E_P
   =\{17,18,21,23,34,36,42,46\}.
\end{aligned}
$$

An exact finite midpoint check enumerates the pairs of endpoints and certifies
that $E_1$ and $E_2$ are 3AP-free. The same check records

$$
E_1,E_2\subseteq[0,64),\qquad E_P\subseteq[1,32),
\qquad E_P\cap2E_P=\varnothing.
$$

This is computation evidence for these finite facts, not an asymptotic
claim. In particular, no unverified digit-set growth estimate is being used.

For $k\ge1$, use base-$b$ digits indexed from zero and define

$$
T_k=\left\{\sum_{i=0}^{k-1}
       \bigl(e_i b^{2i}+f_i b^{2i+1}\bigr):
       e_i\in E_1,\ f_i\in E_2\right\},
$$

$$
C_k=\left\{\sum_{i=0}^{k-1}e_i b^{2i}:e_i\in E_1\right\},
\qquad
P_k=\left\{\sum_{i=0}^{k-1}p_i b^{2i+1}:p_i\in E_P\right\}.
$$

Thus $C_k$ has even digits in $E_1$ and zero odd digits, while $P_k$ has
odd digits in $E_P$ and zero even digits.

Every digit in $T_k$ is below $64=b/2$, so $T_k\subseteq[0,b^{2k})$.
The no-carry argument makes $T_k$ a scalar 3AP-free set. Namely, if
$x,z,y\in T_k$ satisfy $x+z=2y$, then the digit sums on both sides are
carry-free: each digit of $x+z$ and of $2y$ is strictly below $b$. Base-$b
uniqueness therefore gives, at every even position, a midpoint relation in
$E_1$, and at every odd position one in $E_2$. Their 3AP-freeness forces the
three digits to agree at every position, so $x=y=z$.

Unique base-$b$ expansions give

$$
|T_k|=(18\cdot8)^k=144^k,
\qquad |C_k|=18^k,
\qquad |P_k|=4^k.
$$

There are no carries in either of the following additions. The even digits
of $C_k+P_k$ lie in $E_1$ and its odd digits lie in $E_P\subseteq E_2$;
the even digits of $C_k+2P_k$ lie in $E_1$ and its odd digits lie in
$2E_P\subseteq E_2$. Consequently,

$$
C_k+P_k\subseteq T_k,
\qquad
C_k+2P_k\subseteq T_k.
$$

Every element of $P_k$ is nonzero because all digits in $E_P$ are positive.
Thus, with

$$
N=b^k=128^k,
\qquad L=N^2=b^{2k},
\qquad m=|T_k|=144^k>N,
$$

all pairs $(c,d)\in C_k\times P_k$ are edges of $I_{T_k}$. Hence

$$
I_{T_k}\text{ contains }K_{18^k,4^k}.
$$

## Exact scope of the obstruction

As $k$ grows, both sides of these bicliques grow without bound. Therefore no
fixed $K_{s_0,t_0}$-free property can follow from scalar-cap structure, even
in the regime $m>N$. Likewise, no bound of the form
$|C||D|\le K$ for all such bicliques, with an absolute constant $K$, can
follow from that structure: here

$$
|C_k||P_k|=72^k\longrightarrow\infty.
$$

This is the exact conclusion of the incidence-biclique route closure. It does
not refute bounds depending on $m,L$, the candidate $(C)$, the candidate
$(O)$, or Erdős 142.

### Correction to the tempting union construction

The tempting family

$$
(C_k+P_k)\cup(C_k+2P_k)
$$

has $|C_k+P_k|=|C_k+2P_k|=72^k$. When the two sets are disjoint (as they
are here, since their odd digits lie respectively in the disjoint sets
$E_P$ and $2E_P$), its size is

$$
2\cdot72^k,
$$

not $144^k$. Thus it is not the dense scalable family for $k>1$; its ratio
to $|T_k|$ is $2^{1-k}$. Unsupported asymptotics for digit-set sizes are
discarded.
