# Expander amplification of a dyadic-cycle counterexample

## Status and scope

**Status.** Owner-checked structural result, independently reviewed at revision
`871ea0a80702695f7eeb13853f613a48606736c9` (review `tFLmIyL` PASS).  Only the
generic finite connected-fiber lemma below is now Lean-formalized as
`Erdos64.edgeExpands_of_fiberExpansion` in
`Proofs/Erdos/Erdos64/FiberExpansion.lean`, with proof revision
`7aec85b4cb636df6175a47c093610458735a3026`; both formal reviews and the owner
axiom audit now pass.  The whole amplification construction, its
cycle-localization arguments, the LPS existence input, and the equivalence
consequence remain informal and are not Lean-formalized.  This manuscript
makes no novelty claim.

This file records a counterexample-amplification result, not a modification of
the high-girth cycle manuscript.  In particular, it does not give a cubic
reduction and it does not impose a girth condition.

Call a finite simple graph **dyadic-free** if it has no cycle whose length is a
power of two.  Given a nonempty finite simple dyadic-free graph of minimum
degree at least three, take one connected component and denote it by $F$.  It
is again dyadic-free and has minimum degree at least three.  Write
$$
 m=|V(F)|,\qquad \Delta_F=\Delta(F).
$$
The construction below turns $F$ into arbitrarily large, connected,
bounded-degree, constant-vertex-expansion, dyadic-free graphs.

## 1. The construction

Start with the six-regular LPS Ramanujan graphs $X_N$ used in the standard
non-vacuity examples.  They have $N$ vertices, edge expansion at least
$\eta_X=1/2$, and maximum degree six.  Subdivide every edge of $X_N$ into a
path of length three, producing $H_N$.  Since $X_N$ has $3N$ edges,
$$
 |V(H_N)|=7N,
$$
and the $6N$ new subdivision vertices have degree two.  Every simple cycle in
$H_N$ is obtained from a simple cycle in $X_N$ by multiplying its length by
three.  Consequently $H_N$ has no dyadic cycle.

For every degree-two vertex $x$ of $H_N$, attach one fresh copy of $F$ by a
single bridge from $x$ to the chosen root of that copy.  Call the resulting
graph $G_N$.  Then
$$
 |V(G_N)|=(7+6m)N,
 \qquad
 \delta(G_N)\ge3,
 \qquad
 \Delta(G_N)\le D_F:=\max\{6,\Delta_F+1\}.
$$
The graph is connected because $X_N$ is connected and every attached copy is
joined by a bridge.  A bridge lies on no simple cycle.  Therefore every cycle
of $G_N$ lies either in $H_N$ or entirely in one attached copy of $F$.  The
first possibility is not dyadic, and the second is not dyadic by hypothesis on
$F$.  Thus every $G_N$ is dyadic-free.

The girth condition is deliberately absent.  Indeed, $F$ has a cycle because
it has minimum degree at least three, and each copy survives in $G_N$, so
$$
 \operatorname{girth}(G_N)\le\operatorname{girth}(F).
$$
The family is nevertheless an expander family, as shown next.

## 2. Connected-fiber expansion lemma

Let $Y$ be a finite simple base graph with edge expansion at least $\eta>0$ and
maximum degree at most $d$, and let $G$ be a finite simple graph whose vertex
set is partitioned into nonempty induced connected fibers $K_v$ indexed by
$v\in V(Y)$, each of size at most $s$, where $s\ge1$.  Equivalently, the
partition is given by a surjective projection $\pi:V(G)\to V(Y)$ with
$K_v=\pi^{-1}(v)$.  For every base edge $uv\in E(Y)$, require at least one
cross-edge of $G$ between $K_u$ and $K_v$; additional edges of $G$, including
additional cross-edges, are allowed.  No regularity or upper bound inside a
fiber is needed for the cut estimate.  Then $G$ has edge expansion at least
$$
 \eta_G\ge\frac{\eta}{s(\eta+d+1)}.
 \tag{F.1}
$$

To verify this, take a vertex set $A$ in the new graph with
$|A|=a\le|V|/2$.  Classify fibers as full, empty, or partial, and let $p$ be
the number of partial fibers.  Since each fiber has size at most $s$, the
number of full fibers and the number of empty fibers are each at least
$a/s-p$.  Every partial connected fiber contributes at least one internal cut
edge, so the cut has size at least $p$.

Let $U$ be the set of base vertices whose fibers are full.  Base expansion
provides at least $\eta|U|$ edges leaving $U$.  At most $dp$ of those edges can
land in partial fibers, so at least
$$
 \eta(a/s-p)-dp=\eta a/s-(\eta+d)p
$$
base edges run from a full fiber to an empty fiber.  Their cross-edges also
cross the cut.  Hence the cut size is at least
$$
 \max\{p,\ \eta a/s-(\eta+d)p\}
 \ge\frac{\eta a}{s(\eta+d+1)}.
$$
Dividing by $a$ proves (F.1).  This is the only amplification lemma needed
here.

## 3. Expansion of the two-stage construction

View $H_N$ as a fiber replacement over $X_N$.  Over each original vertex put
the seven-vertex star consisting of that vertex and its six incident
subdivision endpoints.  Each base edge has exactly one cross-edge joining the
appropriate endpoints of the two stars.  Applying (F.1) with
$s=7$, $d=6$, and $\eta=1/2$ gives
$$
 \eta_H\ge\frac{1/2}{7(1/2+6+1)}=\frac1{105}.
 \tag{F.2}
$$

Now view $G_N$ as a fiber replacement over $H_N$.  A fiber over an unmodified
vertex is a singleton.  A fiber over a former degree-two subdivision vertex is
that vertex together with its attached copy of $F$, joined internally by the
bridge.  Every fiber is connected and has size at most $m+1$.  There is one
cross-edge for each edge of $H_N$, and $\Delta(H_N)\le6$.  Applying (F.1)
again with $s=m+1$, $d=6$, and $\eta=1/105$ gives
$$
 \eta_G\ge
 \frac{1/105}{(m+1)(1/105+6+1)}
 =\frac1{736(m+1)}.
 \tag{F.3}
$$
Since the maximum degree of $G_N$ is at most $D_F$, its external vertex
expansion is at least
$$
 h_F=\frac1{736(m+1)D_F}>0.
 \tag{F.4}
$$
This constant depends only on the fixed counterexample $F$, not on $N$.
The LPS family has $N\to\infty$, so $(G_N)$ is an arbitrarily large family of
simple connected minimum-degree-three $h_F$-vertex-expanders, with fixed finite
maximum degree $D_F$, and no dyadic cycle.

## 4. Consequence for the finite and asymptotic statements

If the finite Erdős--Gyárfás assertion fails, choose a finite simple
minimum-degree-three dyadic-free counterexample $F$.  Sections 1--3 then give
arbitrarily large dyadic-free $h_F$-expanders with minimum degree at least three,
without any girth hypothesis and with a fixed maximum-degree bound $D_F$.
Conversely, any finite expander counterexample is already a finite
Erdős--Gyárfás counterexample.  Therefore the full finite assertion is
equivalent to the following asymptotic form:

> For every fixed $h>0$, all sufficiently large finite simple graphs with
> minimum degree at least three that are $h$-vertex-expanders contain a dyadic
> cycle.

It is also enough to require this asymptotic statement in the bounded-degree
subclass, for every fixed pair $(h,D)$: a hypothetical finite counterexample
would produce the fixed parameters $(h_F,D_F)$ in (F.4).  This is a reviewed
counterexample amplification, not an induced-subgraph extraction or a cubic
reduction.

The high-girth theorem in `Documents/high-girth-expander-cycles.md` cannot by
itself settle this girth-free equivalence.  The amplified graphs contain copies
of $F$, and their girth is bounded above by $\operatorname{girth}(F)$, so they
are outside the high-girth regime.  No claim here changes the status of that
separate theorem.

## 5. Boundary: the girth-free full-interval conclusion is false

The fiber and cycle-localization lemmas do not require $F$ itself to be
dyadic-free.  Dyadic-freeness was used only in §1 and §4 to amplify a finite
counterexample.  Taking $F=K_{3,3}$ instead gives a rigorous boundary example
for the stronger girth-free program.

Use a six-regular **bipartite** LPS base $X_N$.  Here $m=6$ and
$\Delta_F=3$, so the same construction gives a simple bipartite graph $G_N$
with
$$
 |V(G_N)|=(7+6\cdot6)N=43N,
 \qquad \delta(G_N)\ge3,
 \qquad \Delta(G_N)\le6,
 \qquad h(G_N)\ge\frac1{736\cdot7\cdot6}=\frac1{30912}.
 \tag{B.1}
$$
Every bridge lies on no simple cycle.  A cycle inside a $K_{3,3}$ copy has
length $4$ or $6$, while every cycle inside the three-subdivided bipartite
base has length a multiple of $6$.  Therefore
$$
 \mathcal C(G_N)\subseteq\{4\}\cup6\mathbb N,
$$
where $\mathcal C(G_N)$ denotes the set of cycle lengths; the graph contains a
$4$-cycle, but it has no dyadic cycle of length at least $8$.

Thus, for every fixed $0<h\le1/30912$, there is an infinite family of simple
bipartite minimum-degree-three $h$-expanders for which the full even interval
conclusion, and even the conclusion supplying all sufficiently large dyadic
lengths, fails without a girth hypothesis.  This is a rigorously derived
boundary of the program, not a conjecture.  A future girth-free statement can
only aim here at existence of **some** dyadic cycle, allowing a small cycle such
as $C_4$; this example does not disprove the Erdős--Gyárfás conjecture.


## Sources and verification boundary

The base graphs are the six-regular LPS Ramanujan families; the relevant source
is A. Lubotzky, R. Phillips, and P. Sarnak, *Ramanujan graphs*, Combinatorica 8
(1988), §2, Proposition 3.3, Theorem 3.4, and the following nonbipartiteness
discussion.  The fiber calculation is the independently reviewed kernel
identified above.  This manuscript remains informal apart from the generic
finite connected-fiber lemma formalized above, and makes no novelty claim.
