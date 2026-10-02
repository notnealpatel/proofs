# Localized pruning and jointly nonseparating cycles in cubic expanders

## Status, conventions, and scope

**Status.** This is an informal, independently reviewed manuscript.  The
localized-pruning and local-2-connected-block kernel was independently reviewed
PASS at revision `2f28bf74035892fae57482ac11847e25b5160f4c`, and the fixed-
parameter core-packing kernel at revision
`e9badd16a700d46cb80e5187395ea2dafdd117cf`.  The buffered-core corollary below
was independently reviewed PASS at revision
`644c5e2b0cc654d31127602f968799b8ec0b2b8d`.  No novelty claim is made.

All graphs in this manuscript are finite and simple.  Unless a base is shown,
all logarithms are natural.  If $G$ has vertex set $V$, write
$N_G(A)$ for the closed neighborhood of $A$, and call
$N_G(A)\setminus A$ the external neighborhood.  A graph is an
$h$-vertex-expander if
$$
 |N_G(A)\setminus A|\ge h|A|
 \qquad (A\subseteq V, |A|\le |V|/2).
$$
For disjoint vertex sets $A,B$, $e(A,B)$ is the number of edges with one end
in each set; an edge is counted once.  We abbreviate
$e(A,V\setminus A)$ to the edge boundary of $A$.

An induced cycle $C$ is **nonseparating** when $G-C$ is connected.  The
results below concern local cores and local connected reservoirs.  They do not
provide a common supported connector carrying all cycle alternatives, and they
do not prove the rank-$3$ protected-gap-$2$ or reservoir applications that are
under separate investigation.  A separate manuscript,
[`erdos64-strong-reservoir-assembly.md`](erdos64-strong-reservoir-assembly.md),
records a conditional assembly lemma, but does not provide the strong gadgets
needed for its hypotheses.  There is no parity prescription for the packed
cycles, no dyadic consequence, no Erdős--Gyárfás solution, and no
 general-to-cubic-3-connected reduction here.  A separate Lean worker is
implementing only variational cut inequalities; this manuscript makes no claim
that cycles, blocks, or distances have been formalized.

## 1. Localized pruning

We first give the pruning statement in a form that will be used later.  Let
$G$ be cubic on $n$ vertices and let $0<h\le1$ be such that $G$ is an
$h$-vertex-expander.  Let $D_0\ne\varnothing$, put $r=|D_0|$, and assume
$$
 r\le \frac{h^2n}{144}.
 \tag{1.1}
$$
Among all sets $D\supseteq D_0$ with $|D|\le n/2$, choose one minimizing
$$
 f(D):=e(D,V\setminus D)-\frac h2|D|.
 \tag{1.2}
$$
Such a set exists because $D_0$ is feasible: $r\le n/144<n/2$.

The vertex-expansion hypothesis implies the edge-expansion inequality
$$
 e(A,V\setminus A)\ge h|A|\qquad (|A|\le n/2),
 \tag{1.3}
$$
 since every external neighbor of $A$ is incident with at least one boundary
edge.  Consequently
$$
 f(D)\ge \frac h2|D|,
 \qquad
 f(D)\le f(D_0)\le 3r.
 \tag{1.4}
$$
The last inequality uses cubicity and the fact that the second term in
$f(D_0)$ is nonpositive.  If $d=|D|$, (1.4) gives
$$
 d\le \frac{6r}{h}\le \frac{hn}{24}.
 \tag{1.5}
$$

Put $H=G-D$.  We claim that $H$ has edge expansion at least $h/2$.  Let
$A\subseteq V(H)$, write $a=|A|$, and assume $a\le |H|/2$.  The exact
addition identity is
$$
 f(D\cup A)-f(D)
 =e_H(A,H\setminus A)-e(A,D)-\frac h2a.
 \tag{1.6}
$$
If $d+a\le n/2$, minimality of $D$ makes the left side nonnegative, and
therefore
$$
 e_H(A,H\setminus A)\ge \frac h2a.
 \tag{1.7}
$$
Otherwise $a>n/2-d$.  By (1.3),
$$
 e_H(A,H\setminus A)\ge ha-e(A,D)\ge ha-3d.
 \tag{1.8}
$$
Now (1.5) gives $3d\le hn/8$, while
$a>n/2-d\ge 11n/24$; hence $3d<ha/2$.  Equation (1.7) follows in this
case as well.  Since every external vertex of $A$ in $H$ accounts for at
most three edges of this cut, $H$ is an $(h/6)$-vertex-expander.

There is also expansion inside the pruned set away from the prescribed seed.
For $A\subseteq D\setminus D_0$, removal of $A$ is feasible, and the exact
removal identity is
$$
 f(D-A)-f(D)
 =e(A,D\setminus A)-e(A,H)+\frac h2|A|.
 \tag{1.9}
$$
Minimality says that this is nonnegative.  Combining (1.9) with (1.3),
which applies because $|A|\le d\le n/2$, gives
$$
 e(A,D\setminus A)\ge e(A,H)-\frac h2|A|,
 \qquad
 e(A,H)+e(A,D\setminus A)\ge h|A|,
$$
and therefore
$$
 e(A,D\setminus A)\ge \frac h4|A|.
 \tag{1.10}
$$
Thus the internal external-neighborhood of $A$ in $G[D]$ has size at least
$h|A|/12$, because $G$ is cubic.

For completeness, we record the localization and component conclusions.
If $K$ is a component of $G[D]$, set
$$
 D'=(D\setminus K)\cup(K\cap D_0).
$$
There are no edges between $K$ and $D\setminus K$, so the cut functional is
additive over this replacement.  Minimality gives
$$
 f(K)\le f(K\cap D_0)\le 3|K\cap D_0|.
$$
On the other hand, (1.3) and $|K|\le d$ give $f(K)\ge h|K|/2$.
Hence
$$
 |K|\le \frac{6}{h}|K\cap D_0|.                    
 \tag{1.11}
$$
In particular, every component of $G[D]$ meets $D_0$; (1.11) does not say
that a component contains all of $D_0$.

While a ball in $G[D]$ avoids $D_0$, (1.10) makes its size grow by the factor
$1+h/12$ at each step.  It follows that every vertex of $D$ is within
$$
 \rho=\left\lceil
 \frac{\log(6r/h)}{\log(1+h/12)}
 \right\rceil+1
 \tag{1.12}
$$
of $D_0$.  Indeed, a ball that avoided $D_0$ for that many steps would have
more than $6r/h\ge d$ vertices, contradicting (1.5).

If $D_0$ is a union of connected seed sets whose pairwise graph distances are
larger than $2\rho+1$, their closed $\rho$-neighborhoods have no edges between
them.  Every component of $G[D]$ lies in the union of these neighborhoods and
meets $D_0$, while each seed set is connected and is itself contained in one
component of $G[D]$.  Thus $D$ has exactly one component meeting each seed set
and has no other component.  When $D_0=\varnothing$, use $D=\varnothing$ and
$H=G$ separately; no logarithm such as (1.12) is needed.

### Canonical monotone pruning choice

The following addendum was independently reviewed PASS at revision
`e2691e9e8a568b82ae3d66e60ef489d205708260`.  For every seed
$F\subseteq V(G)$ with
$$
 |F|\le \frac{h^2n}{144},
 \tag{1.13}
$$
consider the feasible sets $D\supseteq F$, $|D|\le n/2$, and minimize the same
potential $f(D)$ from (1.2).  Define $D(F)$ to be a minimum-potential feasible
set of maximum cardinality, and put $H(F)=G-D(F)$.  Then this choice is unique,
and for seeds $F_1\subseteq F_2$,
$$
 D(F_1)\subseteq D(F_2),
 \qquad H(F_2)\subseteq H(F_1).
 \tag{1.14}
$$

Indeed, the edge-cut function is submodular, and the cardinality term is
modular, so $f$ is submodular:
$$
 f(X\cap Y)+f(X\cup Y)\le f(X)+f(Y).                 
 \tag{1.15}
$$
Every minimizer for one of these seeds has size at most $hn/24$ by (1.5).
Thus, for minimizers $D_1,D_2$ associated to $F_1,F_2$, respectively,
$$
 |D_1\cup D_2|\le \frac{hn}{12}\le\frac n2.          
 \tag{1.16}
$$
The intersection contains $F_1$ and is feasible for the $F_1$ problem; the
union contains $F_2$ and is feasible for the $F_2$ problem.  Minimality of the
two potentials together with (1.15) therefore forces the union to be a
minimum-potential feasible set for $F_2$.  If $D_2=D(F_2)$ is the
maximum-cardinality minimizer, then $D_1\cup D_2=D_2$, proving the first
inclusion in (1.14).  The second is its complement formulation.

Taking $F_1=F_2$ shows uniqueness: the union of any two maximum-cardinality
minimizers is again a minimizer, so maximal cardinality forces that union to
be each of them.  The same argument with $D_1$ any minimizer for $F_1$ and
$D_2=D(F_2)$ shows that every $F_1$-minimizer is contained in the canonical
$F_2$-minimizer.  For the empty seed, $D(\varnothing)=\varnothing$ is the
unique minimizer because (1.4) gives $f(D)\ge(h/2)|D|$.

Each $D(F)$ is an ordinary minimizer from Section 1, so all of the locality,
component, and expansion bounds already proved there remain unchanged.  This
addendum supplies no rank-$3$ claim.

## 2. Transfer to a local 2-connected block

We next isolate the block argument.  Suppose that $G$ is cubic and
3-connected, $R'\subseteq V(G)$, and
$$
 H=G-R',\qquad M=|V(H)|,
$$
where $H$ is an $\alpha$-vertex-expander and
$$
 M>1+\frac3\alpha.                                  
 \tag{2.1}
$$
The expansion assumption makes $H$ connected: a component of size at most
$M/2$ would have no external neighbor.

Form the weighted block-cut tree of $H$.  A cut-vertex node has weight $1$;
a block node has weight equal to the number of vertices of that block that are
not cut vertices.  The weights sum to $M$.  A weighted centroid of this tree
has every branch of weight at most $M/2$.

A centroid cannot be a cut-vertex node.  Such a node has at most three actual
$H-v$ branches, because $H$ has maximum degree three.  Each branch $W$ has
external neighborhood just $\{v\}$ in $H$, so vertex expansion gives
$|W|\le1/\alpha$.  The centroid weight estimate would then imply
$$
 M\le1+\frac3\alpha,
$$
contrary to (2.1).  Let $B$ be a centroid block.

Every component $W$ of $H-B$ is contained in one weighted-tree branch, and
therefore has size at most $M/2$.  It has a unique attachment vertex
$v_W\in V(B)$.  The original graph $G$ is 3-connected, so $W$ has at least
two distinct neighbors in $R'$.  Otherwise its only neighbor in $H$ outside
$W$ is $v_W$, and deleting $v_W$ together with its one $R'$-neighbor would
separate $W$ from the rest of $H$ (with the zero-neighbor case even easier).
The rest of $H$ is nonempty in this centroid situation.  Since each vertex of
$R'$ has degree at most three,
$$
 \#\{W:W\text{ is a component of }H-B\}\le\frac{3|R'|}{2}. 
 \tag{2.2}
$$
It follows that
$$
 |G-B|\le |R'|+\frac1\alpha\cdot\frac{3|R'|}{2}
 =|R'|\left(1+\frac{3}{2\alpha}\right).             
 \tag{2.3}
$$

When $|B|\ge3$, the block is an induced 2-connected subgraph.  It also
inherits vertex expansion, with a loss of at most a factor three.  To see
this, let $A\subseteq V(B)$ with $|A|\le |B-A|$.  For every component $W$ of
$H-B$, assign all of $W$ to the side containing its unique attachment
$v_W$.  This lifts $A$ and $B-A$ to a partition $A^+$ and $B^+$ of $V(H)$,
with
$$
 |A^+|\ge|A|,
 \qquad |B^+|\ge|B-A|.
$$
The edges crossing the lifted partition are exactly the edges crossing
$A$ in $B$.  Applying the edge-expansion consequence of $H$ gives
$$
 e_B(A,B-A)=e_H(A^+,B^+)
 \ge \alpha\min(|A^+|,|B^+|)
 \ge\alpha|A|.
$$
At most three crossing edges can be incident with any external vertex of $A$
in $B$, so $|N_B(A)\setminus A|\ge\frac\alpha3|A|$.  Thus $B$ is an
$(\alpha/3)$-vertex-expander.

Here is the local form used below.  Apply the preceding block transfer with
$R'=D$ and $\alpha=h/6$ to the output of Section 1.  In addition to (1.1), assume
explicitly that
$$
 n-d>1+\frac{18}{h}.                              
 \tag{2.4}
$$
Then $H=G-D$ has more than $1+18/h$ vertices, and there is an induced
2-connected block $B\subseteq G-D$ satisfying
$$
 |G-B|\le d\left(1+\frac9h\right)
 \le \frac{6r}{h}\left(1+\frac9h\right)
 \le \frac{(h+9)n}{24}\le\frac{5n}{12},             
 \tag{2.5}
$$
so $|B|\ge7n/12$.  Moreover $B$ is an $(h/18)$-vertex-expander.
Every component $W$ of $H-B$ has size at most $6/h$ and touches $D$, by the
3-connectivity argument above.  Combining a path in $W$ to such a neighbor
with (1.12), every vertex of $G-B$ is within
$$
 \rho+\left\lceil\frac6h\right\rceil
 \tag{2.6}
$$
of $D_0$.  If $D_0=\varnothing$, take $B=G$; for a 3-connected
$h$-expander this is an induced 2-connected $(h/18)$-expander and no size
condition such as (2.4) is needed.

## 3. A relative 2-connected-cycle lemma

Let $J$ be 2-connected, and let $K\subseteq V(J)$ be nonempty and connected.
Assume that $K$ contains every vertex of $J$ of degree less than three and that
$J-K$ contains a cycle.  Then $J$ has an induced cycle $C$ such that
$J-C$ is connected.

Choose an induced cycle outside $K$ for which the component $U$ of $J-C$
containing $K$ is as large as possible.  Such a cycle exists by taking a
shortest cycle in $J-K$.  Suppose that another component $W$ of $J-C$ exists.
Every component of $J-C$ has at least two attachments to $C$: zero attachments
would disconnect it, and one attachment would make that attachment vertex a
cut vertex of $J$.  Let $S_U$ and $S_W$ denote the attachment sets.

Take any two distinct attachments $a,b\in S_W$.  If
$z\in S_U\setminus\{a,b\}$, take an $a$--$b$ path whose internal vertices
lie in $W$, and take the $a$--$b$ arc of $C$ that avoids $z$.  In the
vertex-induced subgraph on the union of these two paths, choose an induced
cycle $C'$.  It lies outside $K$ and avoids $U$ and $z$.  The old component
$U$ remains in the component containing $K$ after $C'$ is deleted, and the
edge from $z$ to $U$ joins $z$ to that component.  Thus that component is
strictly larger than $U$, contradicting the choice of $C$.

We have proved $S_U\subseteq\{a,b\}$ for every pair of attachments from
$S_W$.  Since both attachment sets have size at least two, it follows that
$$
 S_U=S_W=\{a,b\}.                                  
 \tag{3.1}
$$
The same argument applies to every component other than $U$, so all components
have the same two attachments.  Any remaining vertex of $C$ then has no
neighbor off $C$.  Since $C$ is induced, that vertex has degree exactly two
in $J$, contrary to the assumption that every degree-less-than-three vertex
lies in $K$ and $C\cap K=\varnothing$.  Hence there is no other component and
$J-C$ is connected.  This is a direct relative proof, not an invocation of a
separate relative Tutte theorem.

## 4. Fixed-$q$ core packing

Fix $0<h\le1$ and a positive integer $q$.  For all sufficiently large $n$
(depending on $h$ and $q$), a cubic 3-connected $h$-expander $G$ admits
induced cycles $C_1,\ldots,C_q$ with the following properties:

* each $|C_i|=O_h(\log n)$;
* the cycles are pairwise anticomplete;
* each $G-C_i$ is connected; and
* $G-\bigcup_{i=1}^q C_i$ is connected.

The constants here are for fixed $q$; no bound uniform in a growing $q$ is
claimed.

We construct the cycles successively.  Suppose that
$R=C_1\cup\cdots\cup C_j$ has already been constructed, with $j<q$.
Then $|R|=O_h(q\log n)$.  For large $n$, use Section 1 with $D_0=R$ if
$R\ne\varnothing$, followed by the local conclusion of Section 2.  We
obtain an induced 2-connected subgraph
$$
 B\subseteq G-R,
 \qquad \beta:=h/18,
 \qquad |G-B|=O_h(|R|),                         
 \tag{4.1}
$$
where the implicit constants are independent of $n$.  The empty-$R$ case uses
$B=G$ and the weaker but still valid expansion parameter $\beta=h/18$.

We now find a short cycle in a protected part of $B$.  Let
$$
 D_B=\{v\in V(B):\deg_B(v)=2\}
$$
be the defect set.  Since $G$ is cubic and $B$ is induced,
$$
 |D_B|\le 3|G-B|.                                  
 \tag{4.2}
$$
Choose a root in $B$, and join it and every vertex of $D_B$ by shortest paths
in $B$.  The diameter of $B$ is $O_h(\log n)$: balls grow by a factor at
least $1+\beta$ until they exceed half of $B$, and two such balls meet.
The union of these paths is a connected set $K$ with
$$
 |K|=O_h((|R|+1)\log n).                            
 \tag{4.3}
$$

Set
$$
 L=2\left\lceil\log_{3/2}n\right\rceil+2.          
 \tag{4.4}
$$
Enlarge $K$ along edges of $B$ only if necessary until
$|K|>L/\beta$.  Since $|R|$ is polylogarithmic for fixed $q$, we may take $n$
large enough that this connected set still satisfies $|K|\le|B|/7$; we also
record the useful large-$n$ inequality $|B|>4L/\beta$.  Every vertex outside
$K$ has degree exactly three in $B$.  Therefore
$$
 \frac{1}{|B-K|}\sum_{v\in B-K}\deg_{B-K}(v)
 \ge 3-\frac{3|K|}{|B|-|K|}\ge\frac52.             
 \tag{4.5}
$$

We use the following corollary of the average-degree Moore bound.  It is obtained
by inverting Theorem 1 of Alon--Hoory--Linial, rather than quoting that theorem
verbatim: a finite graph of average degree at least
$5/2$ contains a cycle of length at most
$2\lceil\log_{3/2}N\rceil+2$, where $N$ is its number of vertices.  If
necessary, strip vertices of degree zero or one before applying the theorem.
Thus $B-K$ contains a cycle $C_0$ with
$$
 |C_0|\le L.                                       
 \tag{4.6}
$$
This invocation is not reproved here.

Let $U$ be a largest component of $B-C_0$.  We claim that
$|U|>|B|/2$.  If every component had size at most $|B|/2$, greedily taking
components would produce a union $S$ with
$|B|/4\le|S|\le|B|/2$.  Its external neighborhood lies in $C_0$, so has size
at most $|C_0|\le L$, whereas expansion gives at least
$\beta|B|/4>L$, a contradiction.  The union of all the non-giant components
has size at most $|C_0|/\beta$: it has no neighbors in $U$, and its external
neighborhood is contained in $C_0$.  Consequently
$$
 |B-U|\le |C_0|+\frac{|C_0|}{\beta}
 \le\left(1+\frac1\beta\right)L.                  
 \tag{4.7}
$$
Since $K>|C_0|/\beta$, connectedness of $K$ forces $K\subseteq U$.

The set $B-U$ contains the cycle $C_0$ and is disjoint from $K$.  Apply the
proof of Section 3 with the candidate cycles restricted to $B-U$: choose an
induced candidate maximizing the component containing $K$.  The rerouting in
that proof stays in $B-U$, because every other component is disjoint from the
protected component containing $U$.  It follows that there is an induced cycle
$C\subseteq B-U$ for which $B-C$ is connected.  Its length is bounded simply
by the size of $B-U$, so
$$
 |C|\le\left(1+\frac1\beta\right)L=O_h(\log n).     
 \tag{4.8}
$$
Moreover $C\cap K=\varnothing$.  Since $K$ contains all degree-two vertices
of $B$, every vertex of $C$ has degree three in $B$.  Cubicity of $G$ then
implies that no vertex of $C$ has an edge to $G-B$, including to $R$.

It remains to check the two connectivity assertions.  By induction,
$G-R$ is connected.  Every component outside $B$ in $G-R$ attaches to $B$;
it cannot attach only to $C$, because there are no edges from $C$ to $G-B$.
It therefore attaches to the connected graph $B-C$, proving
$$
 G-R-C\text{ is connected}.                        
 \tag{4.9}
$$
The same argument in the original connected graph $G$ proves that $G-C$ is
connected.  The absence of edges from $C$ to $R$ proves anticompleteness to
all previous cycles.  This completes the induction for fixed $q$.

## 5. Buffered-core corollary

The following strengthened separation statement is also an informal,
independently reviewed result; its independent PASS review is recorded above.
Fix $a>0$, in addition to fixed $h$ and $q$.  For all sufficiently large $n$
with $n_0=n_0(h,q,a)$, the preceding construction can be arranged so that
$$
 \operatorname{dist}_G(C_i,C_j)>a\log\log n
 \qquad(i\ne j),                                  
 \tag{5.1}
$$
and all the other conclusions of Section 4 remain valid.  The cycle-length
constant depends only on $h$ (while the threshold $n_0$ may depend on
$h,q,a$).

Here is the buffered construction.  At a stage with previous union $R$, put
$$
 s=\left\lceil a\log\log n\right\rceil,
 \qquad F=N_G^s(R),                                 
 \tag{5.2}
$$
where $N_G^s$ is the closed radius-$s$ neighborhood.  A cubic graph satisfies
$$
 |F|\le 3\cdot 2^s|R|=\operatorname{polylog}(n)       
 \tag{5.3}
$$
for fixed $a,q,h$.  Thus $F$ is $o(n)$ and satisfies the smallness hypotheses
of Sections 1 and 2 for large $n$.  Use $F$ as the forbidden seed set in the
local pruning and block-transfer arguments.  They produce
$$
 B\subseteq G-F\subseteq G-R,
 \qquad |G-B|=O_h(|F|),                              
 \tag{5.4}
$$
and the defect hull used in Section 4 is still polylogarithmic and hence
o(n).  The same AHL step and the same protected-cycle argument give an
induced cycle of length $O_h(\log n)$, with the length constant depending only
on $h$.  Since the cycle lies outside $F$, it has distance greater than $s$
from every previous cycle, proving (5.1).

The graph $G-F$ need not be connected, and no such assertion is used.  The
joint deletion step instead uses the inductively maintained connectivity of
$G-R$: every component outside $B$ in $G-R$ attaches to $B-C$, because the
new cycle has degree three inside $B$ and hence no edge to $G-B$.  This proves
the buffered version with the same individual and joint nonseparation
properties.

## Related work and verification boundary

A bounded canonical literature check, not a complete survey, distinguishes the
local statement here from known trimming paradigms.  Saranurak--Wang,
arXiv:1812.08958, Overview Theorem (trimming) and Introduction Theorem
(pruning) give global volume/boundary and conductance guarantees; its Overview
trimming Proposition `certify` gives an interface-local volume charge.  Those
statements do not supply the graph-distance-$D_0$ locality or the per-component
bound $6|K\cap D_0|/h$ proved in Section 1.  We use the standard
trimming/min-cut paradigm as related context, not as an attribution of the
stronger statement here and not as a novelty claim.  The bounded check was
recorded in output `489c52ba54fb0d489e53153efbed3c6b27f642cf`.

Henning--Joos--Löwenstein--Sasse, *Induced Cycles in Graphs*,
arXiv:1406.0606, Theorems `general_bd` and `cubic_bd`, give induced
2-regular subgraphs of order greater than $n/4$ in the indicated settings.
They do not give the short cycles with jointly connected complement constructed
here.  This check does not purport to be a complete literature survey.

The short-cycle input is A. Alon, G. Hoory, and N. Linial, *The Moore bound
for irregular graphs*, Graphs and Combinatorics 18 (2002), with source at
<https://web.math.princeton.edu/~nalon/PDFS/ahl1.pdf>.  The pruning discussion
has related Friedman--Krivelevich context, but the proof in this manuscript is
self-contained and is not attributed to an FK theorem.  The review records
above concern the stated mathematical kernels; all cycle, block, and distance
arguments remain informal.
