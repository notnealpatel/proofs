/-!
# Excess-first bridge surgery program (prose archive)

All arguments below are internal informal local proofs, NOT Lean-checked.
No counterexample is asserted to exist and no theorem declaration is added.
This is the sole owner of the excess/order bridge kernel formerly recorded in
`erdos64-excess-bridge-constraints`; general split safety is owned by
`Sorry.Erdos.Erdos64.ExpanderCycleProgram`, section Split obstruction.

## Contract and comparison class

A CE is a finite NONEMPTY simple graph with minimum degree at least 3 and
no simple cycle of length 2^k, k≥2. Put ε(X)=Σ_v(d_X(v)−3)=2e(X)−3n(X).
Assuming the CE class nonempty, choose G globally lexicographically minimal
for (ε,n) among ALL CEs, without a connectedness, bipartite or cubic
restriction. This is not `Erdos64.IsMinimalCounterexample`: `Basic.lean`
uses (n,e). Guillaume Ducoffe–Bogdan Dumitru, *Towards a more structured
search for Erdős–Gyárfás counter-examples*, arXiv:2609.28594, Lemma 2.1,
Corollary 2.2 and Theorem 2.5 concern (n,e) minimality and their indicated
cubic/hereditary bridge-addable settings, not premises for these proofs.
No novelty or literature-exhaustiveness claim is made.

## Endpoints and their neighbors

Every proper component is a CE with ε(component)≤ε(G) and smaller order,
since component excesses are nonnegative and sum to ε(G). Thus G is connected.
For a bridge ab, write A,B for its sides, a∈A,b∈B, and let
ε_A=Σ_{v∈A}(d_{G[A]}(v)−3), similarly ε_B. Then ε_A,ε_B≥−1 and
ε(G)=ε_A+ε_B+2. If d_G(a)≥4, the induced side A is a CE and
ε_A≤ε(G)−1, impossible; likewise d_G(b)=3.

If x∈N(a)\{b} is high (degree≥4), write N(a)={b,x,y}. The edge by is
absent because ab is a bridge. H=(G−a)+by is simple and restores the
degrees of b,y, while x loses one but remains degree≥3. Its order is n−1,
its size is e−2 and its excess is ε−1. The new edge is a bridge joining B
to the component of A−a containing y. Other components of A−a need not be
connected to it: disconnected CEs are eligible comparisons. Every cycle
is old, so H is a CE, contradiction. Hence all neighbors of either bridge
endpoint have degree exactly 3.

## Odd cycles and cutvertices

Let N_{G[A]}(a)={y,z}. If yz is an edge, ayza is an odd cycle. Otherwise
H_A=G[A]−a+yz is simple, nonempty and minimum-degree-three, with
n(H_A)=|A|−1, e(H_A)=e(G[A])−1 and ε(H_A)=ε_A+1≤ε(G).
If dyadic-free it contradicts global minimality (smaller excess or equal
excess and smaller order). Therefore a dyadic cycle uses yz; replacing
that edge by y−a−z gives a simple (2^k+1)-cycle through a. The same on B
gives two vertex-disjoint odd cycles. No common k or equal-half condition
is obtained.

A high cutvertex v cannot occur: every component of G−v has at least two
neighbors at v, since a single attachment would be a bridge at a high
endpoint. Split v into adjacent copies for one component and its complement.
Both copies have degree≥3; the new edge is a bridge and (n,e,ε) changes
to (n+1,e+1,ε−1). Every old cycle through v uses two neighbors in ONE
component and lifts with unchanged length. Thus the split is a CE of
smaller excess. A degree-three cutvertex has an incident bridge, by
pigeonholing its three edges among at least two components. Consequently
odd-cycle packing number≤1 implies G has neither bridges nor cutvertices,
hence is 2-connected (n≥4). Bipartite and one-vertex-deletion-bipartite G
satisfy that packing restriction. This is global minimality, NOT minimality
inside the bipartite class; the surgeries need not preserve bipartiteness.
It proves neither that every CE is 2-connected nor that ε(G)=0.

## Rooted transfer certificate

For a bridge side (A,a) and a high vertex h∈A, ah is absent by the neighbor
result. Dyadic-freeness gives C₄-freeness, so a,h have at most one common
neighbor. At least d_A(h)−1≥3 neighbors x of h satisfy ax absent.
H=A−hx+ax is simple, nonempty, minimum-degree-three, with the same n,e as
A and ε(H)=ε_A≤ε(G)−1. Minimality forces a dyadic cycle using ax;
therefore A−hx contains a simple a–x path of length 2^k−1, k≥2.
No 2-connectivity is needed, and no equal exponent, disjoint routing or
linkage across different x follows. This is not bridge elimination.

## Actual unpaid bridge and reopening condition

The general split criterion includes both an edge-using old near-dyadic
cycle and an edge-avoiding figure-eight; these proofs avoid both dangers
only at component-separated/bridge surgeries. Nothing above discards case
II for arbitrary splits. Current production has CE vocabulary and other
order-first reductions, but not this excess-first global minimality or
these surgery implications. Reopen with formal surgery/cycle-transport
objects and the exact global comparison, or with an additional linkage
argument that genuinely converts the rooted certificates to bridge
elimination. No existence model for a CE is supplied or required as an
unconditional conclusion: the whole program is conditional on EGC failure.
-/

set_option autoImplicit false
