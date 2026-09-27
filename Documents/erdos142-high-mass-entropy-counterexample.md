# A high-mass entropy counterexample

## Status and scope

This is a counterexample to a **campaign-internal conjectured lemma**: there is no absolute finite constant $C$ for which, eventually, every vector cap $A\subseteq[0,N-1]^2$ with $|A|\ge N\sqrt{r(N)}$ satisfies

$$
I(X;Y)\le C\bigl(d_X+d_Y+1\bigr).
$$

It is not an external theorem, and it makes no claim about the truth or falsity of Erdős 142 or of a P-shaped cardinality bound. Here $r(N)=r_3(N)$ is the largest size of a 3-AP-free subset of $[0,N-1]$, $\lambda(N)=\log(N/r(N))$, all logarithms are natural, and “vector cap” means a set containing no nonconstant coordinatewise three-term arithmetic progression. For uniform $(X,Y)$ on $A$, write $d_X=\log N-H(X)$ and $d_Y=\log N-H(Y)$.

The asymptotic lower bound used below is the accepted, kernel-checked Lean result `eventually_rothNumberNat_lower_bound` in `Proofs/Erdos/Erdos142/TorusAsymptoticLowerBound.lean`. The entropy and sampling argument that follows is a prose proof; it is not Lean-formalized.

## Construction and balance

Fix $N$, and take a **maximum-cardinality** 3-AP-free set $B\subseteq[0,N-1]$, so $|B|=r$. Each subset of $B\times B$ is a vector cap: in any coordinatewise three-term progression in such a subset, each coordinate progression lies in $B$ and hence must be constant. Thus both coordinates, and therefore the vector progression, are constant.

The cited Lean result says, for every fixed $\varepsilon>0$ and all sufficiently large $N$,

$$
N\exp\!\left(-\bigl(c+\varepsilon\bigr)\sqrt{\log N}\right)\le r(N),
$$

where $c$ is the fixed constant in that theorem. Taking one fixed $\varepsilon$ gives $\lambda=O(\sqrt{\log N})$. Also $r\le N$, so $\lambda\ge0$. In particular, eventually $\lambda\le\tfrac13\log N$, and hence $r=N e^{-\lambda}\ge N^{2/3}$.

Set

$$
m=\left\lceil N\sqrt r\right\rceil.
$$

For sufficiently large $N$, $N\sqrt r\le r^2$, since this is equivalent to $r\ge N^{2/3}$. The ceiling causes no difficulty: $r^2$ is an integer upper bound for the real number $N\sqrt r$, so $\lceil N\sqrt r\rceil\le r^2$. We can therefore choose an $m$-subset $A$ of $B\times B$.

Choose this subset uniformly at random. Each row and each column has a hypergeometric degree $D$ with mean $\mu=m/r\ge\sqrt N$ (using $r\le N$). Put

$$
\delta=\sqrt{\frac{6\log(4r)}{\mu}}.
$$

Since $r\le N$ and $\mu\ge\sqrt N$, we have $\delta=o(1)$. The hypergeometric Chernoff bound gives

$$
\Pr\bigl(|D-\mu|\ge\delta\mu\bigr)
\le 2\exp(-\delta^2\mu/3)=\frac{1}{8r^2}.
$$

A union bound over the $2r$ rows and columns bounds the probability of any failure by $1/(4r)<1$. Thus some deterministic choice of $A$ has every row and column degree at most $(1+\delta)\mu$.

## Entropy calculation

For this choice of $A$, each nonzero row marginal probability is at most $(1+\delta)/r$, and the same holds for each column marginal. Comparing either marginal with the uniform distribution on $B$ by relative entropy yields

$$
0\le \log r-H(X)\le\log(1+\delta)=o(1),
\qquad
0\le \log r-H(Y)\le\log(1+\delta)=o(1).
$$

Indeed, the relative entropy is the average of $\log(rp)$ under the marginal, and $rp\le1+\delta$. Write the two nonnegative entropy defects as $o(1)$ terms. Since $(X,Y)$ is uniform on $A$, $H(X,Y)=\log m$. Moreover, $m=\lceil N\sqrt r\rceil$ and $N\sqrt r\to\infty$, so

$$
\log m=\log N+\tfrac12\log r+o(1).
$$

Consequently,

$$
d_X+d_Y=2\lambda+o(1),
\qquad
I(X;Y)=H(X)+H(Y)-H(X,Y)
=\tfrac12\log N-\tfrac32\lambda+o(1).
$$

Because $\lambda=O(\sqrt{\log N})$, the mutual information is $\tfrac12\log N+O(\sqrt{\log N})$, while $d_X+d_Y+1=O(\sqrt{\log N})$ and is positive. Therefore

$$
\frac{I(X;Y)}{d_X+d_Y+1}\longrightarrow\infty.
$$

The constructed vector caps have $|A|=\lceil N\sqrt{r(N)}\rceil\ge N\sqrt{r(N)}$, so this disproves the stated campaign-internal high-mass entropy conjecture for every fixed $C$.

## Exact non-consequence and diagnostic

This family does **not** violate any fixed positive-$\eta$ P-shaped cardinality bound of the form in question. In fact, for each fixed $\eta>0$,

$$
\frac{m}{r^{1+\eta}N^{1-\eta}}
=(1+o(1))N^{-1/2}\exp\!\left((\eta+\tfrac12)\lambda\right)\longrightarrow0,
$$

by $\lambda=O(\sqrt{\log N})$. This is an explicit non-consequence, not a claim about the truth of that bound.

*Diagnostic (not a proved replacement theorem):* any repair of the internal entropy conjecture would need to exclude sub-products such as subsets of $B\times B$, or impose mass much nearer the row-cap maximum $Nr$.
