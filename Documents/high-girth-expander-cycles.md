# High-girth expanders contain all long cycles, with the bipartite parity restriction

## Status, scope, and conventions

**Status.** Informal generalized assembly; final manuscript review pending.

It uses the independently reviewed deletion and sparse-adjuster kernel together
with the cited AHL/FK inputs.  It is not Lean-formalized, novelty is not
established, and it is not an unrestricted Erdős--Gyárfás claim.  The degree
hypothesis is minimum degree, not maximum degree: no cubic reduction is being
asserted.

All graphs are finite and simple.  If $X$ is a graph and $S$ is a vertex set,
write $N_X(S)$ for the external vertex neighborhood $N_X(S)\setminus S$.
Thus an $h$-vertex-expander on $n$ vertices satisfies
$$
 |N_X(S)|\ge h|S|\qquad(0<|S|\le n/2).
$$
Logarithms are base two unless a subscript is displayed.  Constants are
increased harmlessly to absorb floors, ceilings, and changes of logarithm
base.

## 1. The generalized theorem

**Theorem (informal degree-free/parity generalization).**  For every fixed
$0<h\le1$ there are constants
$$
 C(h)>0,\qquad B(h)>0,\qquad \rho(h)>0,\qquad n_0(h)
$$
such that the following holds.  Let $G$ be a finite simple graph on
$n\ge n_0(h)$ vertices with minimum degree at least three, let $G$ be an
$h$-vertex-expander, and suppose
$$
 \operatorname{girth}(G)\ge C(h)\log\log n.
$$
If $G$ is nonbipartite, then for every integer $T$ with
$$
 B(h)\log n\le T\le \rho(h)n
$$
there is a simple cycle of length exactly $T$.  If $G$ is bipartite, the same
conclusion holds for every even integer $T$ in that interval.

Consequently, in either case all dyadic lengths $2^k$ in a possibly shortened
interval $[B(h)\log n,\rho(h)n]$ occur.  In the bipartite case these dyadic
lengths are, of course, even.  The shortening only ensures that the first
power of two above the lower endpoint remains below the upper endpoint.

The proof has three inputs.  The deletion-expansion input $E$ below uses the
average-degree Moore bound of Alon, Hoory, and Linial.  The sparse-adjuster
packing input $P$ is the independently reviewed degree-free kernel described
in §3.  The rooted container input $F$ is the conditional companion in
`Documents/fk-rooted-container-conditional.md`, based on the
Friedman--Krivelevich framework and source revision
`724c14d8259403ad831c3f0dbcf90aee04326c0d`, with the greedy quantifier
clarification recorded there.  The construction below supplies the container
before applying $F$ and preserves its exact support and interface.

## 2. Deletion preserves expansion without a maximum-degree bound (`E`)

Let $G$ be an $h$-vertex-expander of girth $g$, let $Z$ have size $m$, and put
$J=G-Z$.  Assume that $J$ has minimum degree at least two and that its
vertices of degree two form an independent set $B$.  If
$$
 \left(\frac98\right)^{\lfloor(g-1)/2\rfloor}>\frac{3m}{h},
 \tag{E.1}
$$
then $J$ is a $\kappa$-vertex-expander, where
$$
 \kappa:=\min\{h/2,1/16\}.
 \tag{E.2}
$$
The expansion parameter is that of the original $G$; it is not divided again
at every later packing stage.

Let $S\subseteq V(J)$ be nonempty with $s=|S|\le |V(J)|/2$.  If
$s\ge2m/h$, then expansion in the original graph and deletion of at most $m$
vertices give
$$
 |N_J(S)|\ge hs-m\ge hs/2\ge\kappa s.
 \tag{E.3}
$$
Suppose now that $s<2m/h$.  Write $T=N_J(S)$ and assume for contradiction that
$|T|<s/16$.  Then $U=S\cup T$ has
$$
 |U|<17s/16<3m/h.
$$
The AHL average-degree Moore bound, together with (E.1), gives
$$
 e_J(U)<17|U|/16<289s/256.
 \tag{E.4}
$$
The same consequence applies to the induced graph on $R$ whenever $R$ is
nonempty, because $|R|<3m/h$; hence
$e_J(R)<17|R|/16$.  Indeed, otherwise the induced graph on $U$ (or on $R$)
would have average degree at least $17/8$ and girth at least $g$, while AHL
would force more than $3m/h$ vertices.

Let $I$ be the isolated vertices of $J[S]$ and let $R=S\setminus I$.  Put
$t=|R\cap B|$, $s_3=|R\setminus B|$, and let $D$ be the sum of ambient
$J$-degrees of vertices in $R\setminus B$.  Since $B$ is independent, every
neighbor in $S$ of a vertex of $R\cap B$ lies in $R\setminus B$; nonisolation
therefore gives $D\ge t$ (the other ambient edge may leave $S$).  Also
$D\ge3s_3$.  Thus
$4D\ge t+9s_3$, and
$$
 \sum_{v\in R}d_J(v)=2t+D\ge\frac94|R|.
 \tag{E.5}
$$
For the separate whole-graph degree count, take $t=|B|$,
$s_3=|V(J)\setminus B|$, and let $D$ be the degree sum on
$V(J)\setminus B$.  Then both edges at every vertex of $B$ are counted in $D$,
so $D\ge2t$, while $D\ge3s_3$.  Hence $5D\ge2t+12s_3$, and the average
degree of $J$ is at least $12/5$.

The induced graph $J[R]$ has girth at least $g$.  Since $e_J(R)<17|R|/16$,
$$
 e_J(U)\ge\sum_{v\in R}d_J(v)-e_J(R)+2|I|
 >\frac{19}{16}|R|+2|I|\ge\frac{304s}{256},
 \tag{E.6}
$$
when $R$ is nonempty.  This contradicts (E.4), since
$304/256>289/256$.  If $R$ is empty, every vertex of $S$ has at least two
edges to $T$, so $e_J(U)\ge2s>289s/256$, the same contradiction.  Hence
$|N_J(S)|\ge s/16$, proving $E$.

This argument uses AHL as an average-degree theorem and makes no conversion
from an edge cut using a maximum degree.  The source is N. Alon, S. Hoory, and
N. Linial, *The Moore bound for irregular graphs*, Graphs and Combinatorics 18
(2002), 53--57, Theorem 1,
<https://web.math.princeton.edu/~nalon/PDFS/ahl1.pdf>.  For a polylogarithmic
deleted set, (E.1) follows from a sufficiently large constant multiplying
$\log\log n$ in the girth assumption.

## 3. The sparse degree-free adjuster kernel (`P`)

Fix an integer $q\ge1$ independently of $n$, and set
$$
 p_i=10+3(q-i),\qquad
 r_i=\left\lceil p_i\log\log n\right\rceil,\qquad r_{\max}=r_1,
$$
$$
 S_0=400\,4^q(r_{\max}+1),\qquad R_i=S_0/4^i,
 \qquad S_i=4R_i.
 \tag{P.1}
$$
Roundings are absorbed into the leading constants.  Initially $B$ is empty.
At stage $i$, the current graph $J$ has minimum degree at least two, its
degree-two set $B$ is independent, and distinct vertices of $B$ are at distance
at least $S_i$.

If $t$ vertices have degree two, $s_3$ vertices have degree at least three, and
$D$ is the degree sum on the latter, then $D\ge2t$ and $D\ge3s_3$.  Hence
$5D\ge2t+12s_3$, and
$$
 2t+D\ge\frac{12}{5}(t+s_3).
 \tag{P.2}
$$
Thus every current graph has average degree at least $12/5$, without any upper
degree assumption.

### 3.1 Isometric cycles and the buffer geometry

A shortest odd cycle $C$ is isometric even when shorter even cycles exist.  If a
path $P$ between two vertices of $C$ is shorter than the shorter $C$-arc, then
joining $P$ to either arc gives two closed walks, both shorter than $C$ and of
opposite parity.  The odd one contains a shorter odd cycle, a contradiction.
Internal intersections of $P$ with $C$ do not matter: this is a closed-walk
argument.  An ordinary shortest cycle is isometric as well, by the standard
shortcut proof: choose a shortest counterexample path and use consecutive
intersections with $C$ to obtain a cycle shorter than the supposedly shortest
one.

More generally, let $Z$ be a connected chosen subgraph containing an isometric
cycle $C$, and suppose every $z\in Z$ has intrinsic distance at most $R$ from
$C$.  For $z,z'\in Z$,
$$
 d_Z(z,z')\le d_J(z,z')+4R.
 \tag{P.3}
$$
Project to $C$, use shortest paths to the projections, and use the isometry of
$C$ for the intervening cycle arc.  If the ambient girth satisfies
$g>4R+4$, an outside vertex cannot have two neighbors in $Z$.  If two outside
$Z$-neighbors are joined by a shortest remaining path of length $L$, the two
routes through $Z$ and outside $Z$ give a cycle of length at most
$$
 2L+4R+4,
 \tag{P.4}
$$
so $L\ge g/2-2R-2$.  When the two contacts share a vertex, the corresponding
cycle has length $L+2$.  These statements remain valid when $Z$ is the chosen
subgraph rather than an induced subgraph: extra edges can only improve the
relevant distances.

At stage $i$, choose an ordinary shortest cycle in the current graph, except
that for the first cycle in a nonbipartite $G$ choose a shortest odd cycle.  The
latter exists and has length $O_h(\log n)$: an $h$-expander has logarithmic
diameter, and a BFS same-level edge supplies an odd cycle of length at most
$2\operatorname{diam}(G)+1$.  In the bipartite case the chosen cycle is even.
Every later ordinary shortest cycle has length $O(\log n)$ by the
average-degree $12/5$ AHL bound.  Write its length as $c$, and call it $C_i$.
All these cycles are isometric and satisfy $c\ge g$.

Set $r=r_i$.  Mark a cycle vertex bad when its distance from the old defect set
$B$ is at most $r+1$; equivalently, its radius-$(r+1)$ neighborhood meets $B$.
The reviewed bad-port counting estimate is unchanged:
$$
 \left(\frac{c}{S_i-2(r+1)}+1\right)(4(r+1)+1)<c/4.
 \tag{P.5}
$$
Thus two good ports $a,b$ can be chosen.  The two routes through the
core have lengths
$$
 c/2+1,\ c/2+3\quad\text{if $c$ is even},
 \qquad
 (c+3)/2,\ (c+5)/2\quad\text{if $c$ is odd}.
$$
For an even cycle use the shift
$c/2-1$ and for an odd cycle use $(c-1)/2$.  Both port distances are at
least $c/2-1$; the needed condition is $c>4r+8$, not the false even-cycle
lower bound $(c-1)/2$.  The choice $g\ge10S_0$ ensures this.

Let $u$ and $v$ be the off-cycle neighbors at the two ports.  In $J-C_i$,
the radius-$r$ BFS balls rooted at $u$ and $v$ are trees, since the girth is
larger than $2r+1$.  They have no additional contacts with $C_i$: an outside
path from a port to $C_i$ of length at most $r+2$, combined with isometry,
would give a cycle of length at most $2r+4$, while a return to the same port
other than the edge through $u$ gives one of length at most $r+2$.
Because the ports are more than $r+1$ from $B$, every vertex in these balls has
current degree at least three.  After removing the cycle root, every node at
depth less than $r$ therefore has at least two children.  Select exactly two
children at every level and call the resulting full binary subtrees $F_u,F_v$.
Each has
$$
 |F_u|=|F_v|=2^{r+1}-1.
$$
These are selected subtrees, not the entire potentially unbounded-degree
balls: internal nodes may have unselected children.  A cross-edge or unwanted
intersection between the two trees would give an $a$--$b$ shortcut of length
at most $2r+3$, contradicting the isometric distance between the ports.

The core is $C_i$ together with the designated off-cycle edges $ua$ and $vb$
and roots $u,v$.  The trees $F_u,F_v$ are associated reservoirs, not core
interiors; their only permitted core intersections are at the designated roots,
and distinct gadgets are disjoint.  Put
$$
 Z_0=C_i\cup F_u\cup F_v.
 \tag{P.6}
$$
Every point of $Z_0$ is within $r+1$ of $C_i$.  The number of outward edges from
each reservoir is at least
$$
 3|F_u|-2(|F_u|-1)-1=|F_u|+1=2^{r+1},
 \tag{P.7}
$$
and likewise for $F_v$.  The subtraction accounts for the designated edge to
the cycle.  The outward neighbors are all distinct and lie outside $Z_0$; the
estimate is not based only on leaves.  Leaves have at least two outward edges,
while unselected children of internal nodes simply contribute to the same
degree count.

### 3.2 Saturation and boundary preservation

Saturate $Z_0$ by shortest paths from every old defect in $B$ within distance
$R_i$, stopping at the first hit on $Z_0$.  The old $4R_i$ separation makes
these paths disjoint outside $Z_0$ and their attachments $2R_i$-separated.  At
most
$$
 c/(2R_i)+3
 \tag{P.8}
$$
paths are needed, with the additive constant covering the two selected trees.
If $Z_i$ is the resulting deletion set, then
$$
 |Z_i|\le1.5c+2^{r+2}-2+3R_i.
 \tag{P.9}
$$
Every point of $Z_i$ lies within
$$
 \gamma_i=r+1+R_i
 \tag{P.10}
$$
of $C_i$.  Apply the geometry fact with $\gamma_i$, and with the ambient
girth $g$ rather than the cycle length $c$.  An outside vertex loses at most
one neighbor.  New-new defect distances are at least
$$
 g/2-2\gamma_i-2\ge R_i.
 \tag{P.11}
$$
An old surviving defect loses no neighbor: a contact with $Z_0$ would have
absorbed it, while a contact with a saturation path would put it within
$R_i+1<4R_i$ of another old defect.  The same separation gives old-new distance
at least $R_i$.  Remaining vertices have minimum degree at least two; vertices
of degree at least four that lose one neighbor still have degree at least three,
and a new degree-two defect is a degree-three vertex that lost one neighbor.
The old defects remain mutually $4R_i$-separated, so the full defect set is
$R_i$-separated, which is the next-stage requirement because
$S_{i+1}=R_i$.

The boundary estimate has two explicit cases.  For one saturation path and one
fixed reservoir $F$, if two outside contacts $x,x'$ meet neighbors
$z,z'\in F$, the tree path between $z,z'$ (which may run through internal
nodes) and the buffer segment give a cycle of length at most
$2r+R_i+2<g$.  Thus at most one boundary vertex is lost per reservoir by a
single buffer.  If a buffer contacts both $F_u$ and $F_v$, concatenate
$a-u$, the tree path to $z$, the edge to $x$, the buffer segment, the edge from
$x'$ to $z'$, the tree path to $v$, and $v-b$.  This is a walk of length at most
$$
 R_i+2r_i+4.
 \tag{P.12}
$$
It need not be simple: its closed-walk decomposition still contradicts the
isometric distance between $a$ and $b$, because
$$
 d_{C_i}(a,b)\ge c/2-1\ge5S_0-1,
$$
whereas $R_i+2r_i+4\le101S_0/400<5S_0-1$ from
$S_0\ge1600(r_{\max}+1)$.  Hence at most one contact occurs even in the union
of the two reservoir boundaries.  This stronger cross-reservoir check also
covers internal-node contacts.

The selected gadget loses $O_{h,q}(\log n/\log\log n)$ boundary vertices by
these cases, and later stages lose only
$O(\log^{p_i-3}n)$ more.  Therefore the final boundary of a stage-$i$
reservoir is at least
$$
 \log^{p_i}n\ge\log^8 n.
 \tag{P.13}
$$
Doing this for $i=1,\ldots,q$ gives pairwise disjoint adjusters.  Their total
deleted set has size
$$
 m=O_{h,q}(\log^{p_1}n).
 \tag{P.14}
$$
Choose $g\ge10S_0$ and the coefficient of $\log\log n$ large enough that
(E.1) holds against the **original** expansion $h$.  Applying $E$ after the
final deletion leaves a $\kappa$-expander, with
$\kappa=\min\{h/2,1/16\}$.  The kernel is independently reviewed; it is an
informal supplied argument, not a Lean artifact or a novelty claim.

## 4. The rooted container input (`F`)

We use the companion manuscript with its parameter order unchanged.  It takes
an induced $\alpha$-expander $H'$ of order $M$, two vertex-disjoint rooted trees
$T_1,T_2$ outside $H'$ with roots $a,b$, and an outside $a$--$b$ path $Q_0$
whose interior avoids both trees.  The tree radii and $|Q_0|$ are at most
$K\log M$.  With
$$
 X_i=N_G(V(T_i))\cap V(H'),
$$
the entry condition is $X_1\ne\varnothing$ and the return condition is
$|X_2|\ge\log^6 M$.

The corrected companion conclusion supplies constants
$$
 A(\alpha)=51/\alpha,\qquad c=3K+O_\alpha(1),\qquad
 \rho(\alpha)=2^{-O(\log(1/\alpha)/\alpha)},
$$
with $A$ independent of $K$, such that every integer
$\ell\in[c\log M,\rho(\alpha)M]$ has a simple cycle supported in
$$
 V(H')\cup V(T_1)\cup V(T_2)\cup V(Q_0),
 \tag{F.1}
$$
of length in $[\ell,\ell+A]$.  Its interface says that the cycle is a
prescribed outside path through $T_1,a,Q_0,b,T_2$, plus a simple path in $H'$;
therefore $Q_0$ can be replaced by any compatible outside alternative.  The
container is conditional in the companion itself, while §5 below constructs
it before $F$ is invoked, so no extra unproved container hypothesis remains in
the assembled argument.  The exact support and parameter order are retained.
The source framework is Friedman--Krivelevich, arXiv:1912.11011, §§2.1 and
2.3, including Lemmas 2.1--2.7.

## 5. Composition and the parity finish

Fix $h$, put $\kappa=\min\{h/2,1/16\}$ and $\alpha=\kappa/2$, and set
$A=51/\alpha$.  Before running the packing construction choose
$$
 q=\lceil A\rceil.
 \tag{C.1}
$$
The same $q$ is used in both parity cases; it depends only on $h$, not on $K$.

Use the reservoir boundaries to join successive adjusters through the retained
$\kappa$-expander by disjoint shortest connectors.  The greedy ball-growth
argument is unchanged: after $O_{h,q}(\log n)$ previously used vertices, each
unused boundary still has size at least a fixed fraction of $\log^8 n$, so two
balls meet.  A common endpoint is allowed as a zero-length connector.  The
connector paths, the endpoint trees, and the subsequent pruning are chosen so
that every connector is used once and the endpoint trees remain disjoint.
The expander-pruning step removes only $O_{h,q}(\log n)$ further vertices and
leaves an induced $\alpha$-expander $H'$ of order
$$
 M=n-O_{h,q}(\log^{p_1}n).
 \tag{C.2}
$$
The endpoint reservoir boundaries still exceed $\log^6 M$ for large $n$.
Thus the hypotheses of $F$ hold in the displayed order, with
$K=K(h,q)$ fixed before the final constants are selected.

The $q$ adjusters give an outside path family.  Let $d_i=1$ when $C_i$ is
odd and $d_i=2$ when $C_i$ is even.  The short and long routes in the $i$th
core differ by $d_i$.  In a nonbipartite graph the first cycle was chosen odd,
so $d_1=1$ and every later $d_i$ lies in $\{1,2\}$.  If
$$
 w=d_1+\cdots+d_q,
$$
then $q\le w\le2q$, and subset sums of the $d_i$ fill every integer in
$[0,w]$: start with the first $1$, and add each next $1$ or $2$, whose size is
at most one more than the interval already filled.  The resulting alternatives are denoted $Q_t$, where $t$ is their total
increment; they are simple, have lengths $|Q_0|+t$, and satisfy the
support/interface requirements of $F$.

In a bipartite graph every $d_i=2$.  The alternatives have all increments in
$\{0,2,4,\ldots,2q\}$, so they fill exactly the even subset sums in
$[0,2q]$.  This is the only parity restriction.

Let $T$ be an allowed target length and, in the nonbipartite case, set
$w=\sum d_i$; in the bipartite case set $w=2q$.  Apply $F$ with
$$
 \ell=T-w.
$$
Since $q\ge A$, the returned cycle length $L$ satisfies
$$
 T-w\le L\le T-w+A\le T.
 \tag{C.3}
$$
In the nonbipartite case $T-L$ lies in $[w-A,w]\subseteq[0,w]$ and is a
subset sum, so replacing $Q_0$ by $Q_{T-L}$ gives length $T$.  In the
bipartite case $T$ and $L$ are even, and $T-L$ is an attainable even subset
sum in $[0,2q]$, so replacing by $Q_{T-L}$ gives the same conclusion.  The explicit support statement
(F.1) and its interface ensure that the replacement remains a simple cycle.

Because $M=n-o(n)$ and $w=O_h(1)$, choose $B(h)$ large enough for the lower
endpoint of $F$ and choose $\rho(h)$ small enough for its upper endpoint.  The
fixed losses and the thresholds in $E$, the packing, pruning, and $F$ are then
absorbed into one $n_0(h)$.  This proves the theorem in both parity cases.

## 6. Dyadic corollary

The least power of two at least $B(h)\log n$ is at most
$2B(h)\log n$, which is below $\rho(h)n$ for large $n$.  Apply the theorem to
it and to every other dyadic integer in the target interval.  In the bipartite
case retain the even dyadic lengths, which are all dyadic lengths here.

## Appendix: non-vacuity

The hypotheses are nonempty without any star replacement.  Use the
Lubotzky--Phillips--Sarnak constructions with $p=5$.  For primes $q$ congruent
to $13$ or $17$ modulo $20$, the PGL$_2$ family is simple, bipartite, and
six-regular, with
$$
 N=q(q^2-1),\qquad
 \operatorname{girth}\ge4\log_5q-\log_5 4.
 \tag{A.1}
$$
For primes $q$ congruent to $1$ or $9$ modulo $20$, the PSL$_2$ family is
simple, nonbipartite, and six-regular, with
$$
 N=q(q^2-1)/2,\qquad
 \operatorname{girth}\ge2\log_5q.
 \tag{A.2}
$$
For large $q$ the six generators are distinct and nonidentity, and Dirichlet's
theorem supplies infinitely many primes in each indicated class.  The
Ramanujan bound $2\sqrt5$ gives edge expansion at least
$3-\sqrt5$, hence vertex expansion greater than $1/8$ after division by six.
Thus both parity types supply infinitely many examples for every fixed
$h\le1/8$, and their girth is of order $\log n$.

The source is A. Lubotzky, R. Phillips, and P. Sarnak, *Ramanujan graphs*,
Combinatorica 8 (1988), 261--277, §2, Proposition 3.3, Theorem 3.4, and the
following nonbipartiteness argument:
<http://math1.math.huji.ac.il/~alexlub/PAPERS/ramanujan%20graphs/ramanujanGraphs.pdf>.
This appendix only checks non-vacuity; it is not a proof of the theorem and
makes no unrestricted Erdős--Gyárfás claim.

## Verification boundary

The degree-free deletion argument and the selected-tree/saturation geometry
are informal uses of the cited AHL input and the supplied kernel.  The focused
generalization review passed at revision
`762dfe10e8d48c9bb2d76f4f7aac346670e2e228`; it specifically checked the
average-degree deletion argument, isometric odd-cycle step, parity finish,
selected reservoirs, saturation, and the same-reservoir and cross-reservoir
boundary cases.  The sparse kernel is independently reviewed, but this newly
written generalized manuscript still awaits final exposition audit.

The rooted companion `F` remains conditional on its explicitly stated
container hypotheses and passed its correction review at revision
`8ba7f02a063c3e814eccc412df2b559c5fb89ae6`.  The argument is informal, not
Lean-formalized; it makes no novelty claim and is not an unrestricted EGC
claim.  No `References` or ledger files are changed.
