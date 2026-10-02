# Erdős–Gyárfás (Erdős 64): excess and closed bridge constraints

## Status and scope

This is a self-contained **informal** argument about a globally minimal
counterexample.  It makes no existence claim for such a counterexample and is
not a proof of the Erdős–Gyárfás conjecture (EGC).

Terminology follows `Documents/erdos64-vertex-split-obstruction.md`.  In
particular, retain its split warning: a new dyadic cycle can arise either from
alternative (I), an old near-dyadic cycle using the new split edge, or from
alternative (II), an edge-avoiding figure-eight made from two old cycles.
Nothing below silently discards (II).

Call a finite nonempty simple graph **dyadic-free** if it has no simple cycle
of length $2^k$ for $k\geq2$, and call such a graph of minimum degree at least $3$
a **CE**.  For a graph $X$ put
$$
\varepsilon(X)=\sum_{v\in V(X)}(d_X(v)-3)=2e(X)-3n(X)\geq 0.
$$
Assume a CE exists, and choose $G$ globally lexicographically minimal for
$(\varepsilon(G),n(G))$ among **all** CEs: no connectedness, cubicity,
bipartiteness, or fixed order is imposed in this choice.  This is not the
`Basic.IsMinimalCounterexample` invariant.

For prior-art delimitation, Guillaume Ducoffe and Bogdan Dumitru,
["Towards a more structured search for Erdős–Gyárfás counter-examples"](https://arxiv.org/abs/2609.28594), use lexicographic $(|V|,|E|)$ minimality.  Their Lemma 2.1 and Corollary 2.2 give a $2^k+1$ cycle through every edge and bridgelessness for that ordering; Theorem 2.5 gives a unique-balanced-bridge alternative for minimal cubic CEs, or within hereditary bridge-addable classes closed under disjoint unions.  These are not premises for the present $\varepsilon$-first proofs.  This paragraph makes no novelty or exhaustive prior-art claim; arbitrary contraction may increase $\varepsilon$, so those theorems are not being asserted for $\varepsilon$-minimality.

## 1. The chosen CE is connected

If $G$ had a proper component $C$, then $C$ would itself be a nonempty simple
minimum-degree-three dyadic-free graph.  Also
$\varepsilon(C)\leq\varepsilon(G)$, since the excesses of the components sum
to $\varepsilon(G)$ and are nonnegative.  The component has smaller order, so
it contradicts the global lexicographic choice.  Hence $G$ is connected.

## 2. Every bridge endpoint has degree three

Let $ab$ be a bridge, and let $A$ and $B$ be the vertex sets of the two
components of $G-ab$, with $a\in A$ and $b\in B$.  Define the internal
excesses
$$
\varepsilon_A=\sum_{v\in A}(d_{G[A]}(v)-3),\qquad
\varepsilon_B=\sum_{v\in B}(d_{G[B]}(v)-3).
$$
Only $a$ and $b$ regain the bridge edge, so
$$
\varepsilon(G)=\varepsilon_A+\varepsilon_B+2,
\qquad \varepsilon_A,\varepsilon_B\geq-1.
$$
If $d_G(a)\geq4$, then $G[A]$ has minimum degree at least $3$ and is
still dyadic-free.  Moreover
$\varepsilon_A=\varepsilon(G)-2-\varepsilon_B\leq\varepsilon(G)-1$,
contradicting global minimality.  The same argument at $b$ gives
$$
 d_G(a)=d_G(b)=3.
$$

## 3. No bridge endpoint has a high neighbor

Keep the notation above and suppose $x\in N_G(a)\setminus\{b\}$ has
$d_G(x)\geq4$.  Write the other neighbor of $a$ as $y$, so
$N_G(a)=\{b,x,y\}$.  The edge $by$ is absent: otherwise $abya$ would be a
cycle containing the bridge $ab$.  Form
$$
H=(G-a)+by.
$$
The degrees of $b$ and $y$ are restored, $x$ loses one degree but remains at
least $3$, and every other degree is unchanged.  Thus $H$ is simple and has
minimum degree at least $3$, with
$$
 n(H)=n(G)-1,\qquad e(H)=e(G)-2,\qquad
\varepsilon(H)=\varepsilon(G)-1.
$$
The new edge $by$ is a bridge of $H$: it joins $B$ to the component of
$A-a$ containing $y$; any other components of $A-a$ are irrelevant.  Every
cycle of $H$ is therefore an old cycle in $G$, so $H$ is dyadic-free.  This
contradicts global minimality, without any assumption that $A-a$ is connected
or $2$-connected.  The same holds on the other side.  Consequently every
neighbor of either bridge endpoint has degree exactly $3$.

## 4. Every bridge supplies two disjoint odd cycles

For the bridge $ab$, let $N_{G[A]}(a)=\{y,z\}$.  The two vertices $y,z$ have
degree three in $G$ by the preceding section.  If $yz$ is an edge, then
$ayza$ is an odd cycle.  Otherwise form
$$
H_A=G[A]-a+yz.
$$
This is simple and has minimum degree at least $3$: $y$ and $z$ lose the edge
to $a$ and regain one edge to each other.  It need not be connected; this is
harmless because the CE definition and the global choice impose no connectedness
requirement.  Also
$$
 n(H_A)=|A|-1,\qquad e(H_A)=e(G[A])-1,
\qquad \varepsilon(H_A)=\varepsilon_A+1\leq\varepsilon(G),
$$
where the last inequality uses $\varepsilon_B\geq-1$.  If $H_A$ were
dyadic-free, global minimality would be contradicted (strictly smaller excess,
or equal excess and smaller order).  Hence it has a $2^k$-cycle.  That cycle
must use the new edge $yz$, because $A-a$ is a subgraph of the dyadic-free
$G$.  Replacing $yz$ by $y-a-z$ gives a simple cycle in $G$ of length
$2^k+1$, hence an odd cycle through $a$.  The same construction on $B$ gives
an odd cycle through $b$.  They are vertex-disjoint because $A$ and $B$ are
disjoint.

Thus every bridge in $G$ yields two vertex-disjoint odd cycles.  No equal-half
or auxiliary parameter is used here.

## 5. Cutvertices and the main conditional corollary

There is no high cutvertex.  Indeed, let $v$ be a cutvertex with degree at
least four.  Every component of $G-v$ has at least two neighbors of $v$;
otherwise its unique attachment edge would be a bridge incident to the high
vertex $v$, contradicting Section 2.  Choose one component $C$ and replace
$v$ by adjacent copies $v_C,v_R$, attaching the neighbors in $C$ to $v_C$
and all other neighbors to $v_R$.  This new edge is a bridge, both new copies
have degree at least three, and
$$
 n\mapsto n+1,\qquad e\mapsto e+1,\qquad
\varepsilon\mapsto\varepsilon-1.
$$
Every old cycle lifts with the same length: a cycle through $v$ must use two
neighbors in one component of $G-v$.  The new graph is therefore a CE with
smaller excess, a contradiction.

A degree-three cutvertex has an incident bridge.  Its three incident edges
are distributed among at least two components of $G-v$, so one component has
exactly one attachment; that attachment edge is a bridge.

It follows that if the globally minimal CE has odd-cycle packing number at
most one, it has no bridge by Section 4, and then no cutvertex by the preceding
paragraphs.  Since it is connected (and a simple minimum-degree-three graph
has order at least four), it is $2$-connected.  This applies in particular if
it is bipartite, or if deleting one vertex makes it bipartite: in either case
there cannot be two vertex-disjoint odd cycles.

This conclusion does **not** minimize only inside a bipartite class.  The
surgeries above need not preserve bipartiteness.  It also does not assert that
every CE is $2$-connected, or that $\varepsilon(G)=0$.

## 6. A rooted transfer certificate (useful, but not bridge elimination)

For any bridge side $(A,a)$ and any high vertex $h\in A$, Section 3 gives
$ah\notin E(G)$.  Since $G$ is $C_4$-free, $a$ and $h$ have at most one common
neighbor.  Thus at least $d_A(h)-1\geq3$ neighbors $x$ of $h$ satisfy
$ax\notin E(G)$.  For any such $x$, form
$$
H=A-hx+ax.
$$
This is simple, nonempty, and has minimum degree at least three; it has the
same numbers of vertices and edges as $A$, hence
$\varepsilon(H)=\varepsilon_A\leq\varepsilon(G)-1$.  Global minimality forces
$H$ to contain a dyadic cycle.  That cycle must use the new edge $ax$, since
$H-ax=A-hx$ is a subgraph of the dyadic-free $A$.  Therefore $A-hx$ contains
a simple $a$--$x$ path of length $2^k-1$ for some $k\geq2$.

This argument does not need $A$ to be $2$-connected: a disconnected surgery
still qualifies for the global CE comparison.  It supplies no common exponent,
disjoint routing, or other linkage between different choices of $x$; therefore
it does not by itself eliminate bridges.

## 7. Optional $t=1$-type closure on one bridge half

Suppose one bridge half $A$ has port $a$ of internal degree $2$, exactly one
high vertex $h$ of degree $4$, and every other vertex of $A$ has degree $3.
By Section 3, $a$ and $h$ are nonadjacent.  Put
$$
D=N_A(a)\cup N_A(h).
$$
Since $G$ is $C_4$-free, the neighborhoods have at most one common vertex,
so $|D|=6$ or $5$.  Remove $a,h$ and add three carefully chosen nonedges $F$
on $D$.

If $|D|=6$, every vertex of $D$ loses one edge, and $A[D]$ has maximum
degree at most two.  Its complement has minimum degree at least three, hence
has a perfect matching $F$ (for six vertices this also follows directly by
augmenting any maximal matching).  If $|D|=5$, let $u$ be the common neighbor.
Then $u$ has degree at most one in $A[D]$, while the other four vertices have
degree at most two there.  If $u$ has no neighbor among those four, choose any
complement edge $cd$ among the four and join $u$ to the remaining two.  Such
an edge exists by the maximum-degree bound.  If $u$ has one neighbor $w$, then
$w$ has a complement neighbor $z$ among the four; use $wz$ and join $u$ to
the remaining two.  In both cases $F$ consists of three nonedges, with
$\deg_F(u)=2$ and every other vertex of $D$ having $F$-degree one.

Thus
$$
A_2=A-\{a,h\}+F
$$
is a nonempty simple cubic graph: in the six-vertex case each affected vertex
loses and gains one edge, and in the five-vertex case $u$ loses two and gains
two.  Hence $\varepsilon(A_2)=0<\varepsilon(G)$, since $G$ contains the high
vertex $h$.  Global minimality forces a dyadic cycle in $A_2$, and it must use
an edge of $F$, because $A_2-F=A-\{a,h\}$ is a subgraph of $A$.  Note that
$F$ is not a matching in the five-vertex case.  This is a closed local
certificate, not a cycle-preserving reduction or a bridge-elimination proof.

## Scope verdict

The only inherited inputs used here are the definitions and the global
lexicographic choice of $(\varepsilon,n)$.  The bridge, endpoint, neighbor,
odd-cycle, cutvertex, rooted-transfer, and optional $t=1$ statements above are
proved directly, including the cases where a surgery is disconnected.
There is no claim that a CE exists, no pole-to-minimality converse, and no
claim of a general EGC theorem.  For arbitrary vertex splits, both alternatives
(I) and (II) from the referenced document remain possible, including when the
split is not component-separated.  No literature novelty claim, experiment, or
external order bound is being asserted.
