# Conditional strong-reservoir assembly for packed cycle gadgets

## Status and conditional scope

**Status.** This is an informal conditional result, independently reviewed PASS at
revision `c8f977a69154d9d939905323df726559c541b138`.  It makes no Lean claim,
no novelty claim, and no Erdős--Gyárfás claim.  Every conclusion below is
conditional on the common strong-gadget hypotheses in Section 2; this manuscript
does not construct those gadgets.

All graphs are finite and simple.  Ambient expansion in this manuscript uses
the **floor-half** convention: a floor-$\gamma$ host of order $M$ expands every
set of size at most $\lfloor M/2\rfloor$.  Logs in this document are base two,
matching the supported $F'$ theorem, unless another base is displayed.
The exact internal conditional fixed-arm adaptation $F'$ used as a black box is Section 1 of
[`fk-rooted-container-conditional.md`](fk-rooted-container-conditional.md); its host
parameter is explicitly **ceil-half**.  The localized-pruning manuscript
[`erdos64-localized-pruning.md`](erdos64-localized-pruning.md) is related partial
input only; it does not prove all hypotheses below.

## 1. Fixed-arm extension

We use $F'$ in the following notation.  Let $H$ have
order $M$ and be a **ceil-half $\alpha$-expander**.  Outside $H$ are endpoint-rooted
trees of radius at most $K\log M$, with a clean outside path $Q_0$ between their
roots whose interior avoids $H$ and the endpoint trees.  The entry boundary in
$H$ is nonempty, the return boundary has at least
$(\log M)^6$ vertices, and $Q_0$ has length at most $K\log M$.  The adaptation
produces cycles supported only on $H$, the two trees, and $Q_0$, retaining
$Q_0$, with width
$$
 A=\frac{51}{\alpha},
 \tag{1.1}
$$
independent of $K$, for every integer target in
$$
 [c\log M,\rho M],\qquad c=3K+O_\alpha(1),
 \tag{1.2}
$$
where $\rho>0$ depends only on $\alpha$.  Its cycle has the stated
interface: the outside arm is a simple path, and the remainder is a simple
$H$-path between its two endpoints.

Here is the fixed-arm extension needed for assembly.  Let $Q_0$ instead be any
simple $a$--$b$ path of length $L$, with its interior disjoint from $H$ and from
the endpoint trees.  In the auxiliary graph retain $H$ and the endpoint trees,
choose the required tree-to-$H$ contact edges, omit the internal vertices of
$Q_0$, and use one artificial edge $ab$ in their place.  If $ab$ is already an
edge, retain and designate that edge; never add a parallel edge.

Apply $F'$ to the auxiliary graph at target
$$
 \ell'=\ell-(L-1).
 \tag{1.3}
$$
The resulting simple cycle uses the designated $ab$ edge.  Replace that edge by
$Q_0$.  The replacement preserves simplicity and support, retains the whole
arm, and adds exactly $L-1$ edges.  Hence the resulting cycle has width $A$ and
is available for every integer
$$
 \ell\in[L-1+c\log M,\ L-1+\rho M].              
 \tag{1.4}
$$
The same replacement works for any compatible alternative $a$--$b$ path $Q_j$
whose interior avoids $H$ and both endpoint trees: use the corresponding
artificial edge in the auxiliary graph, then lift it by $Q_j$.

This lemma does not allow arbitrary-radius trees or a uniform-in-$R$ variant.
The endpoint trees retain their fixed $O(\log M)$ radius.  A radius
$O(\log\log M)$ is allowed by choosing a fixed $K$ and taking $M$ large
enough.

## 2. Conditional common-$H$ strong-gadget assembly

Fix $q\ge1$ and $0<\beta\le1$.  Let $H$ be an induced floor-half
$\beta$-vertex-expander of
order $M$.  Assume that outside $H$ there are $q$ vertex-disjoint gadget
supports, indexed by $i=1,\ldots,q$, as follows.

* Gadget $i$ has a core with endpoints $a_i,b_i$.  It supplies two simple
  $a_i$--$b_i$ paths, called its long and short core arcs, with disjoint
  interiors and gap $\delta_i\in\{1,2\}$ between their lengths.
* There are two clean vertex-disjoint legs from $a_i,b_i$ to the roots of
  disjoint reservoir trees $L_i,R_i$.  Each leg meets only its own core root
  and its own reservoir tree, at the relevant endpoints, and avoids every
  other core, tree, and leg.
* All supports are disjoint across gadgets.  Both core arcs avoid all other
  gadget support and meet their own legs only at $a_i,b_i$.  Each reservoir tree has
  radius at most $K\log M$ for one fixed $K$, and has at least
  $2(\log M)^6$ distinct neighbors in $H$.

The total core-and-leg support is polylogarithmic in $M$, with constants fixed
(including $q$).  The reservoir trees may also be assumed polylogarithmic in
size, although this is not needed for the deletion estimates.  These are input
hypotheses, not a construction theorem.

We first connect $R_i$ to $L_{i+1}$ for $1\le i<q$.  At stage $i$, return to the **original** floor-$\beta$ host $H$ and apply the
degree-free floor-pruning lemma of §0 against the total actual connector seed
$F_i$ of previously used $H$-vertices, including vertices of zero-length
connectors.  Since each of the fixed $q-1$ connectors has length
$O_\beta(\log M)$ and only a fixed number of them is used,
$$
 f_i:=|F_i|\le C_{q,\beta}\log M
 \quad\text{and hence}\quad
 f_i\le\frac{\beta^2M}{16}
$$
for all sufficiently large $M$.  The lemma supplies a subgraph $H_i$ that is
floor-half $\beta/2$-expanding and loses at most
$$
 \frac{3f_i}{\beta}
 \tag{2.1}
$$
vertices.  This is one pruning with the accumulated seed, not iterative
halving of an already pruned host.  Since the reservoir boundaries have size
at least $2(\log M)^6$ and the total loss is $O_{q,\beta}(\log M)$, suitable
contacts remain, and
$$
 \operatorname{diam}(H_i)=O_\beta(\log M).
 \tag{2.2}
$$

The full connecting piece from the root of $R_i$ to the root of $L_{i+1}$ is
formed from the root-to-contact tree path in $R_i$, its contact edge, $S_i$,
the other contact edge, and the contact-to-root tree path in $L_{i+1}$.  The
clean-support hypotheses and the successive pruning make these pieces mutually
disjoint except at their intended endpoints.

Concatenate the reverse of the first leg, the long core arc of gadget $1$, its
return leg, the connecting piece to gadget $2$, and so on, ending at the root
of $R_q$.  This gives a simple path $Q$ from the root of $L_1$ to the root of
$R_q$ that contains every baseline long core arc.  Write
$$
 L=|Q|=O_{q,\beta,K}(\operatorname{polylog} M).       
 \tag{2.3}
$$
The endpoint trees $L_1,R_q$ meet $Q$ only at their roots; intermediate
reservoir trees may be traversed by the connecting pieces.

Now perform one final pruning in the original floor-$\beta$ host $H$, against
$$
 F=V(H)\cap V(Q),\qquad f:=|F|\le C_{q,\beta}\log M.
$$
The bound is from the fixed number of actual connector vertices, not from an
unquantified polylogarithmic support estimate.  For large $M$,
$f\le\beta^2M/16$, so the floor-pruning lemma gives $H^*\subseteq H-F$ that
is floor-half $\beta/2$-expanding and has order
$$
 M^*=M-O_{q,\beta}(\log M).                           \tag{2.4}
$$
All $H$-vertices of $Q$ lie in $F$, so the two endpoint trees are outside
$H^*$.  Their surviving $H^*$-boundaries still have at least
$(\log M^*)^6$ vertices for large $M^*$.  By the floor-to-ceil bridge in §0,
$H^*$ is a ceil-half $(\beta/4)$-expander once the explicit bridge threshold is
met.  Apply $F'$ with expander parameter $\alpha=\beta/4$.  Its width is
$$
 A=\frac{204}{\beta},                               \tag{2.5}
$$
independent of $q$, and the exact target window is
$$
 [L-1+c\log M^*,\ L-1+\rho(\beta/4)M^*],             \tag{2.6}
$$
with $c=3K+O_{\beta}(1)$ and integer endpoint adjustments understood.  It is
nonempty for large $M$ because
$L=O_{q,\beta,K}(\operatorname{polylog} M)=o(M)$.

The cycle supplied by the extension contains the baseline long arc of every
core.  For any subset $I\subseteq\{1,\ldots,q\}$, replace the long arc in
core $i$ by its short arc for $i\in I$.  All unused arc interiors avoid every
other support, so each replacement remains a simple cycle in the same support,
and its length is
$$
 |C_I|=|C_{\varnothing}|-\sum_{i\in I}\delta_i.       
 \tag{2.7}
$$
This is the conditional common-$H$ assembly lemma.

## 3. Arithmetic corollary and boundary

Choose $q\ge\lceil A\rceil$ before choosing the gadgets.  The choice depends
only on $\beta$, and no claim is made with $q$ growing.  In a bipartite ambient
graph, if the input gadgets have $\delta_i=2$ for every $i$, the baseline is
even.  For any even target in the window, choose an even baseline in
$[\ell,\ell+A]$; its even difference from $\ell$ is at most $A\le2q$ and is
realized by swapping core arcs.

If at least one $\delta_i$ equals $1$, the multiset of gaps from
$\{1,2\}$ has subset sums containing every integer from $0$ through
$\sum_i\delta_i$.  Since this sum is at least $q\ge A$, every integer
correction up to the width is available.  In the bipartite case, evenness of a
core does not by itself imply an arbitrary prescribed arc gap of two; the
condition $\delta_i=2$ is an explicit input requirement (as it would be for a
near-half construction that supplies such gaps).

All thresholds may depend on the fixed parameters $q,\beta,K$ and the gadget
constants.  There is no $q$-growing bound and no assertion that the expander
parameter is halved once per gadget.  The output is conditional on the common
strong-gadget hypotheses.  Neither this manuscript nor the localized-pruning
manuscript constructs those hypotheses, and no unconditional conclusion about
Erdős 64 follows.
