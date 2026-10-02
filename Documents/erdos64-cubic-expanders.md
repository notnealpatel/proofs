# Cubic expanders: a class-specific cycle-length draft

## Status, conventions, and scope

**Status.** This is a complete informal composition draft, awaiting an independent
end-to-end review.  Its ingredients have been reviewed separately, but the
composition below has not yet been checked as one proof.  In particular, this
file is not a Lean formalization. Separate Lean modules formalize the finite
variational cut kernel and a degree-free floor-to-ceil expansion conversion
under the explicit order bound $4h+4\le hn$. The latter uses the sufficient
uniform threshold $n\ge4+4/h$, not the sharper odd-order threshold below.
The locality, blocks, degree-free floor-pruning process, cycles, rank-three
linkage, packing, and assembly in this file remain informal.

Fix a real number $0<h\le 1$.  All logarithms in this file are natural
logarithms, written $\ln$ when a base conversion matters.  The exception is
explicit: every invocation of the reviewed Friedman--Krivelevich (FK) container
is made with the corrected base-$2$ convention of
[`fk-rooted-container-conditional.md`](fk-rooted-container-conditional.md), so
its quantities $(\log_2 M)^6$, $c\log_2 M$, and the associated radius bounds are
really base $2$.  Likewise, the reviewed strong-reservoir assembly is cited
under its corrected base-$2$ convention.  The fixed powers of logarithms below
are unaffected except for constants; we do not identify $(\ln M)^6$ with
$(\log_2 M)^6$.

For a graph $G$, write $N_G(X)$ for the closed neighborhood of $X$, and call
$G$ an $h$-vertex-expander when
$$
 |N_G(X)\setminus X|\ge h|X|
 \qquad\text{for every }X\subseteq V(G),\quad |X|\le |V(G)|/2.
$$
All graphs are finite and simple.  A cubic graph is $3$-regular, and
3-vertex-connected has its usual meaning.  An induced cycle $C$ is
**nonseparating** if $G-C$ is connected.

The candidate theorem is the following restricted-class statement.

> **Theorem candidate.** For every fixed $0<h\le 1$, there are constants
> $B_h>0$, $\rho_h>0$, and $n_0(h)$ such that every simple cubic,
> 3-vertex-connected, $h$-vertex-expander $G$ on $n\ge n_0(h)$ vertices
> contains a cycle of every even integer length in
> $$
> [B_h(\ln n)^4,\,\rho_h n].
> $$
> If $G$ is nonbipartite, it contains a cycle of every integer length in the
> same interval.

Consequently, for sufficiently large $n$, $G$ contains a dyadic cycle: an
integer power of $2$ lies in the displayed interval, and that power is even.
This is **not** a reduction of the general Erdős--Gyárfás cycle problem to
cubic 3-connected graphs.  The general problem remains unresolved.  No claim
is made here for general graphs, for arbitrary cubic graphs, or for a parameter
$q$ growing with $n$.

The composition uses the following individually reviewed inputs.

* The localized pruning and local block manuscript is
  [`erdos64-localized-pruning.md`](erdos64-localized-pruning.md), read here at
  exact revision `afa1bd18188a65afc32c838cafe0d6a81bfbade9`.  Its localized
  block kernel was reviewed at `2f28bf74035892fae57482ac11847e25b5160f4c`,
  canonical monotonicity at `e2691e9e8a568b82ae3d66e60ef489d205708260`, and
  buffered core packing at `644c5e2b0cc654d31127602f968799b8ec0b2b8d`.
* The robust rank-three linkage lemma used below was independently reviewed
  VALID at `b198ef762edd9092d2772674c20e8be2fcfb9292`.
* The joint buffer hierarchy, conditional on that robust lemma, was reviewed
  at `776858cf86f02f0efb541e2d9b08b8a29b4a0013`.
* The conditional common-expander assembly was reviewed at
  `c8f977a69154d9d939905323df726559c541b138`.  Its corrected convention uses
  base-$2$ logarithms for the FK input, including the return boundary
  $(\log_2 M)^6$.
* The odd peripheral-cycle lemma needed in the nonbipartite case was reviewed
  at `ed2a016fb2d3e898b4487e35e6b051d1e56d96b3`.  Its full proof is included
  here because that derived lemma is not yet in the companion repository.
* The supported fixed-arm container is the conditional theorem in
  `fk-rooted-container-conditional.md`, based on Friedman--Krivelevich,
  arXiv:1912.11011.  It is used only after the common strong gadget has been
  assembled.

The revisions and reviews above concern inputs separately.  They do not certify
this end-to-end theorem.

## 1. The pruning and block package used by the composition

We use the following consequences of the localized-pruning manuscript.  They
are recorded here to make clear exactly which hypotheses are needed later.

Let $A\subseteq V(G)$ satisfy
$$
 |A|\le \frac{h^2n}{144}.
$$
Choose the canonical maximum-cardinality minimizer $D(A)$ of
$$
 f(D)=e(D,V(G)\setminus D)-\frac h2|D|
$$
among the feasible sets $D\supseteq A$ with $|D|\le n/2$, and put
$H(A)=G-D(A)$.  For the empty seed use $D(\varnothing)=\varnothing$.
The reviewed pruning proof gives
$$
 |D(A)|\le \frac{6|A|}{h},
 \qquad H(A)\text{ is an }\frac h6\text{-vertex-expander}.
 \tag{1.1}
$$
It also gives locality.  Every vertex of $D(A)$ is within
$$
 \rho(A):=
 \left\lceil
 \frac{\ln(6|A|/h)}{\ln(1+h/12)}
 \right\rceil+1
 \tag{1.2}
$$
of $A$, with the empty-seed case understood separately.  This includes
vertices at internal distance inside $D(A)$, not only vertices adjacent to the
original seed.  If $A_1\subseteq A_2$, canonical monotonicity gives
$$
 D(A_1)\subseteq D(A_2),
 \qquad H(A_2)\subseteq H(A_1).
 \tag{1.3}
$$
The same proof gives the component bound: every component $K$ of $G[D(A)]$
meets $A$, and
$$
 |K|\le \frac{6|K\cap A|}{h}.
 \tag{1.4}
$$
When the connected pieces of $A$ are farther apart than the corresponding
locality radii, there is exactly one deleted component around each piece.

The local 2-connected-block conclusion will be used in the following form.  If
$H(A)$ has more than $1+18/h$ vertices, there is an induced 2-connected block
$Q(A)\subseteq H(A)$ such that
$$
 Q(A)\text{ is an }\frac h{18}\text{-vertex-expander},
 \tag{1.5}
$$
and every component of $H(A)-Q(A)$ has size at most $6/h$ and touches the
pruned region.  Thus, if $A$ is localized near a collection of protected
sets, the discarded part is within
$$
 \rho(A)+\left\lceil\frac6h\right\rceil
 \tag{1.6}
$$
of those sets.  The budget $n-|D(A)|>1+18/h$ is kept explicitly whenever
this block conclusion is invoked.  For the polylogarithmic seeds below, all
these inequalities hold for sufficiently large $n$ depending only on $h$ and
the fixed number of gadgets.

The variational identities behind (1.1) are the cut kernels that have been
separately formalized.  No formal result about (1.2), the block $Q(A)$, or any
cycle is being asserted here.

## 2. Robust three-target linkage

We next state and prove the rank-three input used to turn each protected core
into a strong gadget.  The proof is included in full because it is the bridge
between the individually reviewed pruning facts and the final composition.

### Robust linkage lemma

First fix a length constant $\mathsf C>0$.  For each fixed pair $(h,\mathsf C)$
there are constants $\kappa_{h,\mathsf C}>0$, $K_{h,\mathsf C}\ge 6/h$,
and a threshold such that the following holds for all sufficiently large $n$.
Let $G$ be a simple cubic 3-connected $h$-vertex-expander.  Let $C$ be an
induced nonseparating cycle with
$$
 c=|C|\le \mathsf C\ln n.
$$
Let $B_1,B_2,B_3$ be pairwise disjoint connected vertex sets, each of size in
$$
 [\tau,K_{h,\mathsf C}\tau],
 \qquad \tau:=\lceil(\ln n)^{12}\rceil.
$$
Let $F$ be any set of vertices of fixed polylogarithmic size, disjoint from
these four protected sets.  Assume that every pair among
$C,B_1,B_2,B_3$, and each one of these sets with $F$, has distance greater than
$$
 \Delta:=\kappa_{h,\mathsf C}\bigl[
 \ln(2+|F|+\tau)+\ln(2+c)
 \bigr].
 \tag{2.1}
$$
For $F=\varnothing$, the distance-to-$F$ condition is vacuous.  The constants
$\kappa_{h,\mathsf C}$ and $K_{h,\mathsf C}$, as well as the implied leg-length
constant below, do not depend on the fixed exponent in the polylogarithmic
bound for $F$.  That exponent affects only how large $n$ must be for the
budgets and distance inequalities to hold.

In the application below, the core-packing and odd-core lemmas first supply a
fixed constant $\mathsf C=C_{\mathrm{core}}(h)$ with
$|C|\le C_{\mathrm{core}}(h)\ln n$.  We then apply this lemma with
$\mathsf C=C_{\mathrm{core}}(h)$ and abbreviate
$\kappa_{h,\mathsf C}$ and $K_{h,\mathsf C}$ by $\kappa_h$ and $K_h$.
Thus all constants used in the final theorem depend only on $h$.

Then there are vertices $a,b\in C$ and two vertex-disjoint paths from $a$ and
$b$ to two distinct target sets among $B_1,B_2,B_3$ with the following
properties:

1. the two paths have total support of at most $K_{h,\mathsf C}(\ln n)^4$ vertices;
2. except for their own initial vertices on $C$, they avoid all of $C$;
3. except for their last vertices, they avoid all three target sets, and their
   last vertices lie in distinct target sets; and
4. if $c$ is odd, $a,b$ split $C$ into arcs whose lengths differ by $1$; if
   $c$ is even, they split $C$ into arcs whose lengths differ by $2$.

No hypothesis about an $H$-boundary of $C$ or of the $B_i$ is part of this
lemma.  The boundary is supplied separately by the joint packing construction.

### Proof of the robust linkage lemma

Set
$$
 \alpha:=\frac h6,
 \qquad H_0:=H(F)=G-D(F).
$$
The seed-size hypotheses needed for this pruning, and for the later auxiliary
prunings, are imposed explicitly.  In particular, for one or two target sets,
respectively,
$$
 |F|+K_{h,\mathsf C}\tau\le \frac{h^2n}{144},
 \qquad
 |F|+2K_{h,\mathsf C}\tau\le \frac{h^2n}{144}.       \tag{2.2}
$$
The first inequality covers $F\cup B_i$ and the second covers
$F\cup B_i\cup B_j$; the same bounds cover the corresponding block calls.
Since $F$ has a fixed polylogarithmic exponent and
$\tau=(\ln n)^{12+o(1)}$, both inequalities, as well as the required
$n-|D|>1+18/h$ block budgets, hold automatically for all sufficiently large
$n$.  We also enlarge the threshold so that every resulting pruned graph has
more than $1+18/h$ vertices.

Choose $\kappa_{h,\mathsf C}$ and the order threshold so that, for every
auxiliary seed $A\in\{F,F\cup B_i,F\cup B_i\cup B_j\}$ with $i\ne j$
where relevant, and every remaining protected set $X$ (the core $C$ or a
target $B_k$ not included in $A$),
$$
 \operatorname{dist}(X,A)>\Delta>
 \rho(A)+\left\lceil\frac6h\right\rceil.
$$
The first inequality follows from the pairwise separation hypotheses.
The fixed factor $K_{h,\mathsf C}$ in the seed-size estimates contributes
only a fixed additive constant to the logarithmic locality bound and is
absorbed into the order threshold. For $A=\varnothing$, use
$D(A)=\varnothing$, $\rho(A)=0$, and distance to the empty set equal to
infinity; the block may be taken to be $G$ itself. Every vertex of $G-Q(A)$
lies within the displayed locality radius of $A$, so the whole set $X$
lies in $Q(A)$ whenever that block is used. In particular, $D(A)$ avoids
all the remaining protected sets. For one- or two-target seeds this says
nothing about targets already included in $A$.

By locality, $H_0$ contains all of $C,B_1,B_2,B_3$.  Indeed, a protected
vertex put into $D(F)$ would be within $\rho(F)$ of $F$, contradicting (2.1)
once $\kappa_{h,\mathsf C}$ is chosen larger than the constants in (1.2).  The graph
$H_0$ is an $\alpha$-vertex-expander.

#### Connectivity after deleting the core

We first show that
$$
 H_0-C\text{ is connected}.                         \tag{2.3}
$$
A useful elementary fact is that deleting $k$ vertices from an
$\alpha$-expander leaves at most one giant component, and the union of all
other components has size at most $k/\alpha$, provided the host is large
relative to $k/\alpha$.  For a nongiant component $K$, its external
neighborhood in the host lies in the deleted set, so vertex expansion gives
$\alpha|K|\le k$.  The existence of a giant follows by applying the same
observation to a component of size at most half the host; for our application
we may take the host large enough that it cannot be covered by several such
small components.

Apply this with $k=c$.  If $K$ is a nongiant component of $H_0-C$, then
$|K|\le c/\alpha$.  While a ball in $H_0$ starting at a vertex of $K$ avoids
$C$, it remains in $K$ and grows by a factor at least $1+\alpha$.  Therefore
every vertex of $K$ is within
$$
 R:=\left\lceil
 \frac{\ln(c/\alpha)}{\ln(1+\alpha)}
 \right\rceil+1
 \tag{2.4}
$$
of $C$.  If $K$ had an edge to $D(F)$, locality would imply
$$
 \operatorname{dist}(C,F)\le R+1+\rho(F),
$$
contrary to (2.1), after increasing $\kappa_{h,\mathsf C}$.  Thus $K$ has no edge to
$D(F)$.  It would then be a component of $G-C$, contrary to the assumed
nonseparation of $C$.  This proves (2.3).  The distance assumption also shows
that every outside neighbor of a vertex of $C$ lies in $H_0$.

We will also use the following deletion-expansion fact.  If $J$ is a
$\beta$-vertex-expander and $X$ has $k$ vertices, then every connected
component $L$ of $J-X$ is a
$$
 \frac{\beta}{2\max(1,k)}\text{-vertex-expander}.     \tag{2.5}
$$
For a set $S\subseteq L$ of size at most $|L|/2$, expansion in $J$ gives at
least $\beta|S|-k$ neighbors outside $S$; at most $k$ of these are in $X$.
If $|S|\ge 2k/\beta$, this is at least $\beta|S|/2$.  If $|S|$ is smaller,
connectedness gives at least one neighbor, which is at least
$\beta|S|/(2\max(1,k))$.  This proves (2.5), and the usual ball-growth
argument gives diameter
$$
 O_\beta(k\ln n)                                      \tag{2.6}
$$
for every nontrivial component.

#### The directed network and rank three

Form a unit-capacity directed network from $H_0$ as follows.  Its vertices are
all vertices of $C$, all ordinary vertices of $H_0-C$, and three absorbing
vertices $t_1,t_2,t_3$, where the whole interior of each $B_i$ is collapsed to
$t_i$.  Delete edges with both ends on $C$; orient each edge leaving $C$ from
$C$ to the ordinary side, and replace every edge from an ordinary vertex into
$B_i$ by an edge into $t_i$.  All ordinary edges are bidirected.  A directed
path stops at its first target node.  Every vertex-capacity is one, including
sources and target nodes; no cut is permitted to split the interior of a
collapsed target, so there are no individual target-vertex cuts after the
collapse.

Before cuts, $H_0-C$ is connected by (2.3), and every vertex of the induced
cycle $C$ has its third edge outside $C$ in $H_0$.  Thus the source vertices
have no loops and every source has an outgoing edge.  We claim only the
existence assertion needed for directed Menger: after deletion of any set
$X$ of at most two ordinary network vertices (ordinary vertices may include
vertices of $C$, but $X$ excludes all $B_i$ interiors), some surviving source
has a directed path to a surviving target.  This is deliberately weaker than
claiming that every surviving source reaches a target.

For $|X|\le2$ without target deletion, apply the giant-component argument in
$H(F)-X$.  The union of nongiant components has size at most $|X|/\alpha$.
Every intact target $B_i$ has size at least $\tau$, so it lies in the giant
component for large $n$.  If the giant contained no surviving source, every
source would lie in a nongiant component, and the expansion/locality estimate
used in (2.4), together with the 3-connectivity edge out of that component,
would put all of $C$ within $2/\alpha+\rho(F)+O(1)$ of $F$, contrary to (2.1).
Hence a surviving source and an intact target lie in the same giant.  Take an
undirected path in that component, stop at its first surviving target, and
start at the last vertex of $C$ before that stop.  The segment from that last
$C$ vertex to the target is directed: only its first edge leaves $C$, and all
later ordinary edges are bidirected.

If two target sets $B_i,B_j$ are removed, use the canonical survivor for the
seed $F\cup B_i\cup B_j$.  It is nested inside $H(F)$ by (1.3), contains $C$
and the remaining target $B_k$, and supplies the same undirected avoiding path
from some surviving source to $B_k$.  If one target node $t_i$ and at most one ordinary vertex $v$ are removed, use the local block $Q(F\cup B_i)$, which is
2-connected, nested inside $H(F)$, contains $C$ and the other targets, and
remains connected after $v$ is removed when $v$ is present.  Again take an undirected path, stop at
the first surviving target, and start at the last $C$ vertex before the stop.
The preceding cases establish the required source-to-target existence after
every cut of size at most two.  They do not assert a separate path for every
source, and the fresh target graphs are only linkage proof devices.

Unit-capacity directed set-to-set Menger now gives rank at least three for the
source-to-target network: if a source set could have rank at most two, a cut of
at most two would separate that set from all surviving target nodes.  In
particular, the source pair selected below has two vertex-disjoint paths to
distinct target nodes.  This use of Menger is on the collapsed-target network,
not on individual target vertices.

#### Choosing the near-half pair

Write the vertices of $C$ cyclically.  If $c$ is odd, set
$$
 d=\frac{c-1}{2};
$$
if $c$ is even, set
$$
 d=\frac c2-1.
$$
Then
$$
 \gcd(c,d)\le 2.                                    \tag{2.7}
$$
Consider the rank-three gammoid restricted to the source vertices on $C$.
It has no loops.  If every pair $\{x,x+d\}$ were dependent, each such pair
would be parallel.  Parallelism propagates along the orbits of addition by
$d$ on the cyclic group of order $c$.  There are at most
$\gcd(c,d)\le2$ orbits, so the matroid would have rank at most two, a
contradiction.  Thus some pair $\{a,b\}$ is independent.  Its two arcs on
$C$ have gap $1$ in the odd case and gap $2$ in the even case, and it has two
vertex-disjoint target paths.

It remains to make the two paths short without changing the selected sources.
By the rank-three conclusion choose an independent pair $\{a,b\}$ and retain
its two vertex-disjoint paths to distinct targets.  Their two arcs on $C$ have
gap $1$ when $c$ is odd and gap $2$ when $c$ is even.

#### Shortening a fixed pair

Let $P_0$ be one of these existing paths, shortened only at its first target;
then $|P_0|=O_h(c\ln n)$.  For every ordinary vertex $v$ on $P_0$, the
existing two-path linkage from the fixed vertices $a,b$ has one path avoiding
$v$, since its paths are disjoint.  Use that fixed-pair witness, rather than
selecting a new core source.  After the same source's unique outside edge, the
witness lies in a component of $H_0-(C\cup\{v\})$.  Applying (2.5) with the
$c+1$ deleted vertices gives weak expansion at least
$$
 \frac{\alpha}{2(c+1)},
$$
and hence diameter $O_h(c\ln n)$.  Replace the relevant outside portion by
a short path from that same source's available outside neighbor, stop at the
first surviving target, and do not walk through an absorbing target.

There is one further witness when the terminal target on $P_0$ itself must be
avoided.  For that target $B_i$, prune with $F\cup B_i$.  The resulting block
$Q(F\cup B_i)$ is 2-connected and nested in $H(F)$.  Its deletion argument
uses the original connected graph $G-C$: the first repeating
$H(F\cup B_i)-C$ giant/nongiant/locality argument shows that this block with
$C$ removed is connected.  More explicitly, every component of
$H(F\cup B_i)-Q(F\cup B_i)$ has a unique attachment in the block, and it
cannot bridge distinct components of $Q(F\cup B_i)-C$ because $C$ is contained
in the block.  Each component after deleting $C$ therefore has weak expansion
at least
$$
 \frac{\beta}{2c}=\frac{\alpha}{6c},\qquad \beta:=h/18=\alpha/3.
$$
A short fixed-source path from the available outside neighbor of $a$ or $b$
then reaches a first target while avoiding the whole bag $B_i$.

Take the union of $P_0$, all ordinary-vertex fixed-pair witnesses, and the
whole-bag terminal witness.  There are $O_{h,\mathsf C}(c\ln n)$ ordinary
vertices on $P_0$, and each witness has $O_{h,\mathsf C}(c\ln n)$ vertices.
Thus the union has size
$$
 O_h\bigl(c^2(\ln n)^2\bigr)
 \le O_h\bigl(\mathsf C^2(\ln n)^4\bigr).       \tag{2.8}
$$
After $\mathsf C=C_{\mathrm{core}}(h)$ this is $K_h(\ln n)^4$ with $K_h$
depending only on $h$.  The union has no one-vertex separator between the
fixed source pair and two distinct target nodes: if a vertex lies on $P_0$,
the corresponding fixed-pair avoiding witness survives, while if it lies off
$P_0$, $P_0$ survives.  Directed unit-capacity Menger therefore gives two
vertex-disjoint paths from the **fixed** vertices $a,b$ to distinct sinks.

Finally uncollapse each target node at the actual first-entry vertex of its
path.  This preserves simplicity, disjointness, length bounds, and support.
The resulting legs avoid $F$, all other vertices of $C$, and all unowned target
sets.  This proves the robust linkage lemma. $\square$

## 3. An odd peripheral core in the nonbipartite case

The nonbipartite case needs one odd core.  We use the following derived lemma,
whose proof is included rather than attributed to a relative Tutte theorem.

### Odd peripheral lemma

Let $G$ be cubic and 3-vertex-connected, and let $H\subseteq V(G)$ be
nonempty and connected.  If $G-H$ contains an odd cycle, then $G$ contains an
induced odd cycle $C$ disjoint from $H$ such that $G-C$ is connected.

### Proof

Among all induced odd cycles outside $H$, choose $C$ so that the component $B$ of $G-C$ containing $H$ is as large as possible.  Such a cycle exists by
starting with an odd cycle in $G-H$ and taking an induced odd subcycle.

Suppose another component $D$ of $G-C$ exists.  It is bipartite: otherwise an
induced odd cycle in $D$ could replace $C$, while the old $C$ would remain a
connected bridge from $H$ to the old component $B$, strictly enlarging the
component containing $H$.

For every component of $G-C$, let its attachment set be its neighbors on $C$.
Because $G$ is cubic and $C$ is induced, every vertex of $C$ has exactly one
edge leaving $C$.  Thus the attachment sets $S_B,S_D$ (and those of any other
components) are disjoint and partition $V(C)$.  Each attachment set has at
least three vertices by 3-connectivity: one or two attachment vertices could
otherwise be deleted to separate that component.  In particular
$|S_B|,|S_D|\ge3$.

Extend the bipartite graph $D$ by adding one leaf at each vertex in $S_D$,
representing its attachment edge to $C$.  List $S_D$ cyclically on $C$ and,
for each consecutive pair, take a shortest path through $D$ between the
corresponding attachment vertices.  Because the extended graph is bipartite,
the sum of the parities of these paths around the cyclic list is even.  The
corresponding $C$-arcs have total length $|C|$, which is odd.  Hence some
consecutive pair gives an odd union of its $C$-arc and its $D$-path.  The
shortest path is induced, and its interior has no $D$-attachment; $C$ is
chordless.  Taking an induced odd cycle inside this union therefore gives an
induced odd cycle with an open $C$-arc $I$ and no $D$-attachment in the
interior of $I$.

Maximality of $B$ forces all of $S_B$ to lie on the open arc $I$.  Indeed, if a
$B$-attachment were outside $I$, the induced odd cycle omits that attachment
while the edge into $B$ keeps $B$ in the component containing $H$, so that
component would enlarge.  Consequently, when the first and last vertices of
$S_B$ on $I$ are chosen, the complementary $C$-arc between these consecutive
$S_B$ attachments contains all of $S_D$.  Thus $D$ lies in one gap between
consecutive $B$-attachments.  The same argument, component by component,
assigns every component other than $B$ to one such $B$-gap.

Let $W$ be the interior of one nonempty $B$-gap together with all non-$B$ components assigned to that gap.  Its boundary is contained in the two
endpoint attachment vertices on $C$, and those endpoints are not in $B$.
The component $B$ is nonempty outside $W$, so these two vertices form a
2-vertex cut, contradicting 3-connectivity.  Therefore no component $D$
exists, and $G-C$ is connected.  The cycle is induced and odd by construction.

We also need a length estimate.  A shortest odd cycle $C_0$ is isometric in
the following weak sense: a shortcut between two of its vertices shorter than
both corresponding arcs, followed by the parity choice of one of the two
arcs, would produce a shorter odd cycle (and an induced odd subcycle if the
shortcut meets the cycle internally).  Choosing two vertices at nearly
opposite positions gives
$$
 |C_0|\le 2\operatorname{diam}(G)+1.                 \tag{3.1}
$$
An $h$-vertex-expander has diameter $O_h(\ln n)$ by ball growth, so
$|C_0|=O_h(\ln n)$.  Let $J$ be the giant component of $G-C_0$.  For
$n>4|C_0|/h$, expansion gives
$$
 |G-J|\le \left(1+\frac1h\right)|C_0|.              \tag{3.2}
$$
The connected set $J$ is a protected set, and $G-J$ contains the odd cycle
$C_0$.  Applying the odd peripheral lemma with protected set $J$ gives an
induced odd nonseparating cycle outside $J$ of length $O_h(\ln n)$.  This is
the odd core used below.  The argument is derived here; it is not an
attribution of a relative odd-cycle or relative $0$-mod-$4$ theorem.

## 4. Joint buffered packing and the parameter hierarchy

We now describe how the cores and reservoirs are prepared simultaneously.  The
point of this section is to make the dependence of all buffer parameters
explicit.  The number of gadgets is fixed before any buffer is chosen.

Set
$$
 q:=\left\lceil\frac{2448}{h}\right\rceil.          \tag{4.1}
$$
Choose this $q$ before any buffers or cores are packed.  Because $q$ is fixed
after $h$, the buffered packing and odd-core construction supply a fixed
constant $\mathsf C=C_{\mathrm{core}}(h)$ and a threshold such that every core
used below satisfies $|C_i|\le\mathsf C\ln n$.  The robust-linkage constant is
chosen after this fixed $\mathsf C$ and depends only on $h$; the exponent of a
polylogarithmic forbidden set affects only the final threshold.

In the bipartite case, apply the reviewed buffered-core packing to obtain
induced peripheral cycles $C_1,\ldots,C_q$ of size $O_h(\ln n)$, pairwise
separated by any prescribed fixed multiple of $\ln\ln n$, with both individual
and joint complements connected.  In the nonbipartite case, first take the
short odd peripheral core $C_1$ from Section 3 and then run the buffered
packing iteration $q-1$ times starting from $R=C_1$.  Since $G-C_1$ is
connected, the same construction applies.

Choose $3q$ connected BFS seed sets $S_{i,j}$, $1\le i\le q$ and
$1\le j\le3$, each of size exactly
$$
 \tau:=\lceil(\ln n)^{12}\rceil.                      \tag{4.2}
$$
Their intrinsic BFS radius is $O(\ln\ln n)$.  All cores and seeds can be
mutually far by $L\ln\ln n$ for any fixed $L$ chosen after $h,q$; cubic balls
satisfy
$$
 2^{b\ln\ln n}=(\ln n)^{b\ln2}.                     \tag{4.3}
$$
Thus every forbidden volume is polylogarithmic and $o(n)$.

Apply canonical pruning once to the union of all cores and all seed sets.  For
large $n$ this gives one core bag $D_{C_i}$ and one reservoir bag $D_{i,j}$
for each $(i,j)$.  Put
$$
 H_0:=G-D,\qquad
 D:=\bigcup_iD_{C_i}\ \cup\ \bigcup_{i,j}D_{i,j}.
$$
Then $H_0$ is a floor-half $h/6$-vertex-expander, the bags are outside $H_0$,
and
$$
 \tau\le |D_{i,j}|\le\frac{6\tau}{h}.                \tag{4.4}
$$
Each reservoir bag supplies at least $h\tau$ contacts with $H_0$, while the
core bags have size $O_h(\ln n)$ and every reservoir bag has intrinsic diameter
$O_h(\ln\ln n)$.

### Fresh linkage hosts and backward buffers

Choose positive constants $b_q,b_{q-1},\ldots,b_1$ backwards, with
$$
 b_{i-1}>4\kappa_h(15+b_i)+10\qquad(2\le i\le q),
 \tag{4.5}
$$
and choose $L$ larger than all
$b_i+2\kappa_h(15+b_i)+10$.  These constants may be huge because
$q=\lceil2448/h\rceil$, but depend only on $h$.

At stage $i$, let $W_{<i}$ be the vertices used by earlier legs.  Define in
the original graph the fresh forbidden set
$$
 F_i:=W_{<i}\ \cup\!
 \bigcup_{\text{bags }E\text{ belonging to gadgets }r\ne i}
 N_G^{\lceil b_i\ln\ln n\rceil}(E).                 \tag{4.6}
$$
The robust-linkage lemma is applied with this fresh $F_i$ and with the current
core and three current reservoir bags.  The resulting canonical survivors
$H(F_i)$ and local blocks are proof devices only: no survivor graph is carried
from one stage to another, and no historical nesting relation is
asserted or needed.  Locality and the backward inequalities ensure that the
current protected sets are outside $D(F_i)$ and satisfy (2.1).  Since there
are fixed many bags and each earlier leg has size $O_h((\ln n)^4)$,
$$
 |F_i|=O_{h,q}\bigl((\ln n)^{12+b_i\ln2}+(\ln n)^4\bigr).     \tag{4.7}
$$
The exponent changes only the threshold.

Apply the robust lemma in this fresh original-graph setting.  It gives two
clean legs from fixed near-half core vertices to two distinct reservoir bags,
avoiding every other bag and all earlier legs, with total support
$O_h((\ln n)^4)$.  The third bag is slack for the rank-three proof.  This
stage-by-stage use never prunes a fresh leg or its target bag and never relies
on historical pruning.

### One final pruning of the fixed initial host

After all $q$ stages, let
$$
 Z:=V(H_0)\cap\bigcup_{i=1}^q(\text{vertices of the actual two legs for }i).
$$
This is the total actual leg set intersected with the fixed initial host; it
is not a union of any $F_i$, $D(F_i)$, fresh target bag, or connector set.  Put
$$
 f:=|Z|=O_{h,q}((\ln n)^4).
$$
For large $n$, explicitly
$$
 f\le\frac{(h/6)^2|H_0|}{16}.                         \tag{4.8}
$$
Apply the degree-free floor-pruning lemma from §0 of the FK companion once to
$H_0$ with seed $Z$.  It removes a set $R$ with
$|R|\le2f/(h/6)$ and total loss
$|Z\cup R|\le3f/(h/6)=O_{h,q}((\ln n)^4)$, leaving the fixed common host
$$
 H_1:=H_0-(Z\cup R),\qquad
 H_1\text{ floor-half }\frac h{12}\text{-expanding},
 \qquad |H_1|=n-O_{h,q}((\ln n)^{12}).              \tag{4.9}
$$
This is the only final pruning.  In particular, the $H_1$ loss is not charged
against the fresh $F_i$ or against any $D(F_i)$.

Every selected reservoir bag is kept in its entirety outside $H_1$.  Root its
explicit BFS spanning tree at the actual leg endpoint in that bag, using the
same vertex set for every boundary contact.  Its radius is at most its
intrinsic diameter, hence $O_h(\ln\ln n)$.  The tree meets its own leg only at
that root, avoids every other bag and leg, and is clean against both alternative
core arcs.  Later connectors may use the appropriate intermediate reservoir
trees; endpoint trees are not silently enlarged.  The remaining contacts after
$Z\cup R$ still number
$$
 h\tau-O_{h,q}((\ln n)^4)>2(\log_2|H_1|)^6                 \tag{4.10}
$$
for large $n$.  Thus the selected trees have the required base-$2$ return
boundary and eventually radius at most a fixed multiple of $\log_2|H_1|$.

## 5. Assembly through one common expander

We now invoke the conditional common-host assembly lemma from
[`erdos64-strong-reservoir-assembly.md`](erdos64-strong-reservoir-assembly.md),
reviewed at `c8f977a69154d9d939905323df726559c541b138`.  Its input is the fixed
initial host $H_1$, which is floor-half
$$
 \beta:=\frac h{12}
$$
expanding.  The assembly's one accumulated connector pruning leaves a
floor-half $\beta/2$ host and the floor-to-ceil bridge makes the final FK host
ceil-half
$$
 \frac\beta4=\frac h{48}\,.
$$
Consequently the fixed-arm width is
$$
 A=\frac{204}{\beta}=\frac{2448}{h},                 \tag{5.1}
$$
and the choice $q=\lceil2448/h\rceil$ made before the buffers is sufficient.
The associated FK density constant is written
$$
 \rho_h:=\frac12\rho(h/48)>0,                       \tag{5.2}
$$
where the factor $1/2$ absorbs $|H_1|\ge n/2$ and all fixed boundary losses.

Use the clean legs and the explicitly rooted reservoir trees to connect the
return reservoir of gadget $i$ to the entry reservoir of gadget $i+1$ by short
paths in the original floor-$\beta$ host $H_1$.  At each step the assembly
returns to this original host and applies its degree-free floor-pruning lemma
against the total actual connector seed so far, including zero-length
connector endpoints.  It never iteratively halves a previously pruned host.
The connector paths and tree paths are mutually disjoint except at intended
endpoints, and the resulting outside path $Q$ contains one chosen long core
arc from every gadget.  Its length is
$$
 |Q|=O_{h,q}((\ln n)^4).                              \tag{5.3}
$$

All $H_1$-vertices used by these connectors form the final accumulated seed in
the assembly lemma.  Its floor-pruning loss is $O_{h,q}(\log_2 n)$, while the
reservoir boundaries in (4.10) remain above the required
$(\log_2 M^*)^6$.  The resulting host $H^*$ has order $M^*=n-o(n)$, and the
floor-to-ceil bridge is applied only after this one final accumulated pruning.
Apply $F'$ to $H^*$ with ceil-half parameter $h/48$.  Its target window has the
form
$$
 [|Q|-1+c\log_2 M^*,\ |Q|-1+\rho(h/48)M^*],
 \tag{5.4}
$$
with $c=3K+O_h(1)$ and fixed tree-radius constant $K$.  Since $M^*\ge n/2$
for large $n$, shrinking the upper endpoint gives the claimed $\rho_h n$.
The lower endpoint and all fixed integer adjustments are absorbed into
$B_h(\ln n)^4$.

Let $\delta_i$ be the difference between the long and short arcs of gadget $i$.
The robust linkage gives $\delta_i=2$ for an even core and $\delta_i=1$ for an
odd core.  Replacing any chosen subset of long arcs by its short arc preserves
simplicity because both alternatives are supported by the same clean gadget
and every other support is disjoint.  In the bipartite case all $\delta_i=2$,
so every even correction through the width is available.  In the
nonbipartite case the first odd peripheral core supplies one $\delta_i=1$ and
all other gaps lie in $\{1,2\}$; their subset sums contain every integer from
zero through their total, which is at least $q\ge A$.  Therefore every integer
in the target window (and every even integer in the bipartite window) is
obtained.  This is conditional on the stated $F'$ and assembly inputs and
makes no unrestricted EGC claim.

## 6. Dyadic consequence and explicit boundary bookkeeping

Because $(\ln n)^4=o(n)$, for large enough $n$ the interval
$$
 [B_h(\ln n)^4,\rho_h n]
$$
has multiplicative width greater than $2$.  It therefore contains a power of
$2$.  For all sufficiently large $n$ that power is at least $2$, hence even,
and the theorem supplies a cycle of exactly that dyadic length.

The two boundary scales used in the composition are deliberately different:
$$
 \tau=\lceil(\ln n)^{12}\rceil,
 \qquad
 (\log_2 M^*)^6=O((\ln n)^6).
$$
The first is the natural-logarithm reservoir size used in the buffer proof; the
second is the base-$2$ return-boundary requirement of the FK black box.  The
estimate
$$
 h\tau-O_{h,q}((\ln n)^4)>2(\log_2|H_1|)^6
$$
for large $n$ is the exact comparison needed.  Similarly, the reservoir and
connector radii are $O(\ln\ln n)$, while the FK tree allowance is measured in
$\log_2 M^*$; eventually $O(\ln\ln n)\le \log_2 M^*$.

## 7. Verification boundary and provenance

The localized pruning manuscript supplies the canonical minimizers, their
locality and monotonicity, the local 2-connected block, and buffered peripheral
core packing.  The robust lemma in Section 2 supplies the rank-three network,
the near-half pair, and the fixed-pair short-linkage witnesses.  The parameter
hierarchy in Section 4 is the separately reviewed joint-buffer input, with the
fresh-forbidden-set and backward-constant details written out here to expose
its logarithmic budgets.  The strong assembly manuscript supplies only the
conditional common-host assembly; it does not itself construct these gadgets.
The FK manuscript supplies only the supported cycle theorem under its container
hypotheses, with base-$2$ logarithms as stated above.

The Alon--Hoory--Linial Moore-bound input and the related pruning discussion are
covered in the companion manuscripts.  Bondy--Vince, *Cycles in a Graph Whose
Lengths Differ by One or Two* (1998), is relevant background for bridge and
cycle-length ideas, but the odd relative lemma here is derived and is not
attributed to a verbatim theorem there.  A bounded inspection of
Ducoffe--Dumitru, arXiv:2609.28594, records the general Erdős--Gyárfás problem
as open and did not find this restricted expander composition; that inspection
is not a novelty proof.  No novelty or unrestricted Erdős--Gyárfás claim is
made in this draft.

The remaining required action is an independent end-to-end review of the
composition, including the interface between the robust linkage, the fresh
buffer hierarchy, the final pruning, and the corrected base-$2$ FK boundary.
Until that review, the theorem above is a draft candidate rather than an
accepted theorem.
