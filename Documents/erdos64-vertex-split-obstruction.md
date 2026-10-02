# Erdos 64: a vertex-split obstruction

## Status and scope

**Status.** This is a complete informal argument for the conditional completion,
terminal obstruction, and equivalences below.  The full conditional completion
and the equivalences are not Lean-formalized.

**Formal boundary.** The module
`Proofs/Erdos/Erdos64/VertexSplitObstruction.lean` contains a compiled finite
certificate. It formalizes only the seven-vertex core:
`core_not_hasPowerOfTwoCycle`, degree, minimum-degree, and noncounterexample
facts, normalization `splitPart_complete`, and `all_splitCore` with actual
simple $C_8$/$C_4$ witnesses for the three normalized partitions. It does not
formalize a general graph-splitting operator, bridge completion, the sequence
invariant, or the logical equivalences.

An independently audited mathematical argument for the finite seven-vertex core
has provenance hash `a4edc2b5e48a217ad51d1e5ab782c017c57815a4`; the prior conditional,
invariant, and equivalence audit has hash
`a8d6b3ff78df0c9e7cec6162abaae15205e441da`.  These hashes are audit provenance,
not published sources.  A finite computational check is only supplementary
evidence; the mathematical proof below is primary.

There is no novelty claim here, and this is not an unconditional counterexample
to EGC.  The conclusion is a conditional obstruction to a particular reduction
method.  Call a graph **dyadic-free** if it has no simple cycle of length $2^k$
for any $k\ge2$.  Here EGC denotes the assertion that every finite nonempty
simple graph of minimum degree at least $3$ has such a cycle.

## The locked seven-vertex core

Let $H$ have vertex set
$$
\{0,1,2,3,4,5,6\}
$$
and edges consisting of the path
$$
1-2-3-4-5-6
$$
and the four spokes
$$
0\mathord\sim1,\quad 0\mathord\sim2,\quad
0\mathord\sim5,\quad 0\mathord\sim6.
$$
Thus $H$ has $n=7$ and $e=9$, with
$$
d(0)=4,\qquad d(2)=d(5)=3,\qquad
 d(1)=d(3)=d(4)=d(6)=2.
$$

Since $H-0$ is a path, every simple cycle uses $0$ and exactly two spokes.
If the spoke endpoints are $a,b\in\{1,2,5,6\}$, its length is $|a-b|+2$.
The six endpoint pairs give the multiset
$$
3,\ 3,\ 5,\ 6,\ 6,\ 7.
$$
None is a power of $2$ with exponent at least $2$, and there cannot be a longer
cycle because $H$ has only seven vertices.  Hence $H$ is dyadic-free.

The graph $H$ is also $2$-connected.  Deleting $0$ leaves the path.
Deleting an interior path vertex leaves two path pieces, each containing a
neighbor of $0$ (the endpoint cases are immediate); the pieces are therefore
rejoined through $0$.  This core is not an EGC counterexample: its minimum
degree is only $2$.

Consider a balanced $2+2$ split of $0$, meaning that its four neighbors are
divided into two sides of size two.  The side containing $1$ is one of
$$
\{1,2\},\qquad \{1,5\},\qquad \{1,6\}.
$$
In the first case, the old $7$-cycle using spokes $1$ and $6$ becomes an
$8$-cycle after the split.  In the other two cases, the old $3$-cycle using
spokes $1$ and $2$ becomes a $4$-cycle.  Thus every balanced split at $0$ is
unsafe.

## The operation and its safety condition

An **admissible minimum-degree-preserving vertex split** is exactly the
following operation.  Choose a vertex $v$ with degree at least $4$, replace
it by adjacent fresh vertices $u,w$, and choose a partition
$$
N(v)=A\mathbin{\dot\cup}B,\qquad |A|,|B|\ge2.
$$
Join $u$ to the vertices in $A$, join $w$ to the vertices in $B$, and make
no other change.  In particular, the edge $uw$ is present and all old edges
not incident with $v$ remain present.

On a finite simple connected graph of minimum degree at least $3$, this
operation preserves finiteness, simplicity, connectedness, and minimum degree
at least $3$.  A split is **safe** when its result is still dyadic-free.  Only
these admissible splits may be used in a sequence: there are no edge or vertex
deletions, contractions, subgraph selections, or global replacements.  The
word balanced is used only for a degree-four vertex, where it means a $2+2$
partition; no equal-size partition is imposed at larger degrees.

## Conditional completion by bridges

Assume now that EGC is false.  Choose a finite simple dyadic-free graph of
minimum degree at least $3$ witnessing this failure, and take a connected
component if necessary.  Call the resulting nonempty connected graph $F$.
Choose an arbitrary root in each of four disjoint fresh copies of $F$.  Attach
these copies to $H$ by one new edge each at
$$
1,\qquad 3,\qquad 4,\qquad 6.
$$
Call the resulting graph $G$.  The copies must be distinct; this is not one
copy of $F$ with four attachments.

Each new attachment edge is a bridge.  Consequently every simple cycle of $G$
is wholly in $H$ or wholly in one copy of $F$, so $G$ is dyadic-free.  It is
finite, simple, and connected, and it has minimum degree at least $3$: the four
degree-two vertices of $H$ used above gain one edge, while all other vertices
already had degree at least three.  In particular, the original nonzero
vertices of $H$ now have degree $3$, whereas $0$ still has degree $4$.

Consider any sequence of safe admissible splits starting from $G$.  None of
the original nonzero vertices of $H$ can be selected, since they have degree
$3$.  A split outside $H$ preserves every internal edge of $H$ and the degree
of every original vertex of $H$.  This remains true when an attachment endpoint
itself is split: the one external edge is merely assigned to one of the two
new vertices.  Therefore those original nonzero vertices remain ineligible
forever.

The original vertex $0$ cannot be safely split either.  All core edges and
their spoke cycles remain fixed under splits outside $H$; the $C_3$ and $C_7$
in the case analysis above therefore continue to supply the witnesses.  If
$0$ is split, the three possible sides containing $1$ give respectively an
$C_8$, a $C_4$, or a $C_4$, as just proved.  Hence every possible split at
$0$ is unsafe at every stage.  This does **not** assert that the initial $G$
has no safe moves outside $H$.

It follows that $0$ remains degree $4$ under every safe sequence.  No safe
sequence from $G$ can end in a cubic graph.

## Termination and the terminal obstruction

For a finite minimum-degree-three graph define its excess by
$$
\varepsilon(G)=\sum_{x\in V(G)}(d(x)-3)=2e-3n\ge0.
$$
An admissible split changes $(n,e)$ to $(n+1,e+1)$, so it changes excess by
$$
\varepsilon\longmapsto\varepsilon+2-3=\varepsilon-1.
$$
Moreover, $\varepsilon(G)=0$ exactly when $G$ is cubic.  Thus every safe
sequence has length at most its initial excess.  Extending a safe sequence
until no safe split remains produces a maximal sequence, and it terminates.
For the graph $G$ above, every such terminal descendant still has the
original degree-four vertex $0$.  It is therefore noncubic and has no safe
admissible split.  This is the promised terminal obstruction.

## Exact universal principles

Let $\mathcal D$ be the class of all finite nonempty connected simple
dyadic-free graphs of minimum degree at least $3$.  Consider these three
principles, all quantified over exactly $\mathcal D$:

* $P_{\mathrm{complete}}$: every graph in $\mathcal D$ admits a finite safe
  admissible-split sequence ending cubic, with a zero-step sequence allowed.
* $P_{\mathrm{step}}$: every noncubic graph in $\mathcal D$ admits at least
  one safe admissible split.
* $P_{\mathrm{local4}}$: every degree-four vertex in every graph in
  $\mathcal D$ admits a safe balanced $2+2$ split.

First,
$$
P_{\mathrm{step}}\Longrightarrow P_{\mathrm{complete}}
$$
by induction on $\varepsilon$: repeatedly take a safe step while the graph
is noncubic.  The operation preserves membership in $\mathcal D$ and lowers
excess by one, so the process reaches excess zero.  Conversely,
$P_{\mathrm{complete}}\Longrightarrow P_{\mathrm{step}}$ because a
noncubic graph cannot be the endpoint of a zero-step completion; its first
step is safe.

If EGC holds, then $\mathcal D$ is empty, so all three universal principles
hold vacuously.  If EGC is false, the bridge-filled graph $G$ belongs to
$\mathcal D$.  The locked vertex $0$ shows that $P_{\mathrm{complete}}$
and $P_{\mathrm{local4}}$ fail, while the maximal-safe descendant above
shows that $P_{\mathrm{step}}$ fails.  Therefore
$$
\boxed{\mathrm{EGC}\Longleftrightarrow P_{\mathrm{complete}}
\Longleftrightarrow P_{\mathrm{step}}
\Longleftrightarrow P_{\mathrm{local4}}.}
$$

This is a conditional method obstruction and an exact equivalence, not a
proof that EGC is false.  In particular, a universal safe-splitting
reduction is not an independent weaker lemma: over this class it is
logically equivalent to EGC.  The argument does not claim that other
reductions are impossible.  The completed $G$ has bridges and contains the
proper counterexample subgraphs $F$, so it does not rule out a specialized
split chosen after selecting a suitably minimal counterexample, a theorem
restricted to $2$-connected minimum-degree-three graphs, or arbitrary graph
operations beyond the admissible splits defined here.
