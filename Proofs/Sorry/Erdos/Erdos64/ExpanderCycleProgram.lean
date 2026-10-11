/-!
# Expander cycle program: consolidated unformalized kernels

This is a docstring-only archive, NOT a Lean-checked proof. Internal prose
arguments are distinguished below from external AHL/FK/LPS inputs and from
unproved conditional gadget hypotheses. No EGC solution, novelty claim or
unrestricted cubic reduction is asserted. Graphs are finite and simple;
dyadic means a simple cycle of length 2^k with k≥2. Vertex expansion is
external-neighborhood expansion on sets of size≤floor(n/2), unless marked
ceil-half. Natural logs are ln; all FK, common-host and high-girth logs are
base 2. Constants depend on the fixed displayed parameters, never on n.

Section ownership (each dependency is retained once): Local pruning/packing
owns the canonical/block kernels of `erdos64-localized-pruning`; Cubic
linkage/odd core/composition owns the unique `erdos64-cubic-expanders`
argument; F′ owns `fk-rooted-container-conditional`; Common host owns
`erdos64-strong-reservoir-assembly`; E/P/high-girth owns
`high-girth-expander-cycles`; Amplification owns
`erdos64-expander-amplification`; Split obstruction owns
`erdos64-vertex-split-obstruction`. Excess-first bridge surgery instead
belongs to `Sorry.Erdos.Erdos64.ExcessBridgeSurgeryProgram`.

## Current formal boundary

`Erdos64.exists_localPruningSet` in `LocalPruning.lean` supplies finite
max-degree-three EDGE cut minimization (seed≤h²n/144, |D|≤6|seed|/h,
remaining edge expansion h/2, internal added-part edge boundary h/4).
It does not supply canonical choice, vertex locality, blocks or cycles.
`ExpansionConvention.lean` supplies floor-to-ceil half-constant conversion
under 4h+4≤hn, not the sharper parity-specific prose threshold below.
`FiberExpansion.lean` proves `edgeExpands_of_fiberExpansion`, not graph
construction, LPS or cycle localization. `VertexSplitObstruction.lean`
checks only the seven-vertex core and the three split witnesses, not the
general operator, completion or equivalences. No current theorem represents
robust linkage, peripheral packing, F′, common-host assembly or either
cycle-interval consumer. These named helpers are dependencies, not proofs
of the unformalized implications archived here.

## Local pruning, canonicality and expanding block (shared owner)

Let G be cubic and h-vertex-expanding, 0<h≤1. For nonempty seed A of size
r≤h²n/144 minimize f(D)=e(D,V\D)−h|D|/2 over A⊆D, |D|≤n/2.
Vertex expansion implies edge boundary≥h|D|, so h|D|/2≤f(D)≤f(A)≤3r,
giving d=|D|≤6r/h≤hn/24. For S⊆H=G−D, s≤|H|/2,
  f(D∪S)−f(D)=e_H(S,H\S)−e(S,D)−hs/2.
If d+s≤n/2, minimality gives edge expansion h/2. Otherwise
s>n/2−d≥11n/24 and e_H(S,H\S)≥hs−3d, with 3d≤hn/8<hs/2.
Divide the cut by maximum degree 3 to get vertex expansion h/6.
For S⊆D\A, removal is feasible and
  f(D−S)−f(D)=e(S,D\S)−e(S,H)+h|S|/2≥0.
Combine with e(S,H)+e(S,D\S)≥h|S| to get
 e(S,D\S)≥h|S|/4, hence internal vertex boundary≥h|S|/12.

For a component K of G[D], replacement by K∩A and cut additivity give
f(K)≤3|K∩A| and f(K)≥h|K|/2. Thus |K|≤6|K∩A|/h and every K meets A.
Internal balls avoiding A grow by 1+h/12, so every deleted vertex has
internal distance to A at most
  ρ(A)=⌈ln(6|A|/h)/ln(1+h/12)⌉+1.
Connected seed pieces separated by more than 2ρ+1 have exactly one deleted
component per piece. For A=∅ use D=∅, H=G and ρ=0 separately.
Choose the maximum-cardinality minimizer D(A). Cut submodularity and the
modularity of |D| make f submodular. Any two minimizers have union size
≤hn/12≤n/2. For A₁⊆A₂ their intersection/union are feasible for the two
problems; submodularity forces the union to minimize the A₂ problem.
Maximum cardinality gives D(A₁)⊆D(A₂); with equal seeds it gives uniqueness.
No historical pruning choice is used later in place of this canonical one.

For cubic 3-connected G, H=G−R′ an α-expander of order M>1+3/α,
take a weighted centroid of the block-cut tree (cut nodes weight 1,
block nodes weight their noncut vertices). A cut-node centroid would have
at most three branches each of size≤1/α, contradicting M>1+3/α.
The centroid block B has every outside component W of size≤1/α with one
attachment in B and at least TWO distinct neighbors in R′, by original
3-connectivity. Thus #W≤3|R′|/2 and |G−B|≤|R′|(1+3/(2α)).
Lift a partition of B by assigning W to its attachment side: crossing edges
are unchanged, and H expansion gives e_B(S,B\S)≥α|S| for |S|≤|B|/2.
Dividing by 3 gives B expansion α/3. In the pruning application, impose
n−d>1+18/h; the block Q(A) is induced 2-connected, expands by h/18,
|G−Q|≤d(1+9/h)≤5n/12, hence |Q|≥7n/12. Every H−Q component has
size≤6/h and touches D, so G−Q lies within ρ(A)+⌈6/h⌉ of A.
For the empty seed take Q=G without this order budget.

## Relative peripheral cycles and buffered packing

Relative lemma: J 2-connected, K nonempty connected containing all vertices
of degree<3, and J−K containing a cycle, imply an induced cycle C outside
K with J−C connected. Choose C maximizing the component U containing K.
For any other component W and two attachments a,b to C, if U has an
attachment z outside {a,b}, reroute via a W-path and the C-arc avoiding z,
then take an induced cycle. It avoids U,z and enlarges U, contradiction.
Since both attachment sets have size≥2, all other components and U must
have the same attachment set {a,b}. Every remaining C vertex then has degree
2, contrary to K containing all defects. This is a direct internal proof,
not an attributed relative Tutte theorem.

Fix q≥1, h, and optionally a>0 BEFORE n. Iteratively let R be the previous
cycle union, with G−R connected. For buffered packing seed F=N_G^s(R),
s=⌈a ln ln n⌉; cubic balls give |F|≤3·2^s|R|=polylog(n)=o(n).
Use the local block above, B⊆G−F, β=h/18, |G−B|=O_h(|F|).
Its degree-2 defect set has size≤3|G−B|. Join all defects to a root by
shortest B-paths (diameter O_h(ln n)) to form connected K, enlarge it so
|K|>L/β where L=2⌈log_(3/2)n⌉+2, and require |K|≤|B|/7,
|B|>4L/β. Outside K all B-degrees are 3, so B−K has average degree≥5/2.
External AHL (Alon–Hoory–Linial, *The Moore bound for irregular graphs*,
Graphs and Combinatorics 18 (2002), Theorem 1) gives a cycle C₀ of length≤L
(strip degrees 0/1 if needed). The giant U of B−C₀ has size>|B|/2:
otherwise a union of components of size between |B|/4 and |B|/2 contradicts
β expansion. The nongiant union has size≤|C₀|/β, so
|B−U|≤(1+1/β)L. Connected K lies in U since |K|>|C₀|/β.
Run the relative maximization restricted to candidates in B−U; rerouting
stays there. It yields induced C of length≤(1+1/β)L with B−C connected.
C avoids defects, hence has degree 3 inside B and no edge to G−B.
Every component outside B in G−R therefore attaches to B−C. This proves
G−R−C connected, also G−C connected, and distance(C,R)>s.
Thus fixed q peripheral cores are mutually separated by a ln ln n, with
individual and joint connected complements, lengths O_h(ln n). The length
constant depends only on h; thresholds may depend on q,a. No parity is
prescribed here and no growing-q claim is made.

## Cubic robust rank-three linkage (internal, still unformalized)

Fix h∈(0,1], a length constant 𝒞>0. There exist κ_(h,𝒞)>0 and
K_(h,𝒞)≥6/h such that, for sufficiently large n, a cubic 3-connected
h-expander G with induced nonseparating core C, c=|C|≤𝒞 ln n,
and three connected disjoint bags B₁,B₂,B₃ of sizes in [τ,Kτ],
τ=⌈(ln n)^12⌉, admits two disjoint legs from a near-half pair a,b∈C to
DISTINCT bags. F is any fixed-polylog-size forbidden set disjoint from all
four protected sets. All protected pairs and protected-to-F distances must
exceed Δ=κ[ln(2+|F|+τ)+ln(2+c)] (empty F distance condition vacuous).
The constants are independent of the fixed exponent of the F size bound;
that exponent changes only the n threshold. Legs have total support≤K(ln n)^4,
avoid F, avoid C except their sources, avoid all bags except their own
first-entry terminal vertices, and split C into arcs with gap 1 if c odd,
2 if c even. No boundary-contact hypothesis is hidden in this lemma.

Here is the retained causal chain. Let α=h/6, H₀=H(F). Impose
|F|+Kτ≤h²n/144 and |F|+2Kτ≤h²n/144 and all block budgets
n−|D|>1+18/h. Increase κ and the threshold so every remaining protected
set is farther than ρ(A)+⌈6/h⌉ from each auxiliary seed
A=F,F∪B_i,F∪B_i∪B_j. The canonical/block owner then keeps them in Q(A)
and gives nested survivors inside H₀.

H₀−C is connected. Deleting k vertices from a large α-expander has one
giant and a nongiant union of size≤k/α (use expansion on component unions,
not merely the individual-component bound). A nongiant K after C deletion
is within R=⌈ln(c/α)/ln(1+α)⌉+1 of C by ball growth. If K met D(F) by
an edge, locality would put dist(C,F)≤R+1+ρ(F), contradiction. Without
such an edge K is a component of G−C, contrary to nonseparation. Outside
neighbors of C also survive by locality. More generally every connected
component of a β-expander minus k vertices has expansion
β/(2 max(1,k)): large S use β|S|−k≥β|S|/2, smaller nontrivial S use one
neighbor by connectivity. Its diameter is O_β(max(1,k) ln n).

Form a directed unit-VERTEX-capacity network: delete internal C-edges,
orient C-to-outside edges outward, bidirect ordinary edges, collapse each
whole bag to one absorbing sink t_i. Paths stop at FIRST target; cuts may
remove a sink but may not split its bag interior. Every C source has an
outgoing edge (cubic induced C), and H₀−C is connected, hence no loops.
After deletion of any≤2 network vertices some surviving source reaches a
surviving sink. With no sink deleted, giant-component expansion plus original
3-connectivity/locality supplies a surviving C source in the giant containing
the large intact bags; a trapped source component would have size≤2/α
and an edge to D(F), violating separation. With two sinks deleted, Q(F∪B_i∪B_j)
contains C and the third bag and is connected. With one sink and one ordinary
vertex deleted, 2-connectivity of Q(F∪B_i) gives an avoiding connection.
Take an undirected connection, truncate at first surviving bag and begin at
its LAST C vertex: the segment is directed. This proves set-to-set rank≥3,
not that every source reaches every sink after every deletion.

On the source gammoid choose d=(c−1)/2 for odd c, d=c/2−1 for even c.
Since gcd(c,d)≤2, if every pair {x,x+d} were dependent, looplessness would
make them parallel; propagation around the≤2 addition orbits would force
rank≤2. Thus some such fixed pair a,b has disjoint paths to distinct sinks,
with the stated arc gap.

Shortening MUST preserve that pair. First take one fixed-pair path P₀,
replace its outside portion by a shortest path in the appropriate component
of H₀−C (weak expansion α/(2c)), then truncate at first target. This gives
|P₀|=O_h(c ln n). Truncation ALONE does not give this bound.
For each ordinary vertex v on P₀, the original two-path fixed-pair witness
has a path avoiding v. After its source's unique outside edge it lies in a
component of H₀−(C∪{v}); replace there using weak expansion α/(2(c+1)),
then first-target truncate. This keeps the SAME surviving source and gives
O_h(c ln n) support per witness. For the terminal sink B_i of P₀, use
Q(F∪B_i)⊆H₀. Repeat giant/locality/nonseparation to see
H(F∪B_i)−C connected; components outside its block have unique attachment
and cannot join distinct components after C deletion. Thus Q(F∪B_i)−C
is connected, with weak expansion (h/18)/(2c)=α/(6c), and gives a short
fixed-source path avoiding the ENTIRE terminal bag.

The union of P₀, all its ordinary-deletion witnesses and the whole-bag
witness has size O_h(c²(ln n)²)≤O_(h,𝒞)((ln n)^4).
Every single vertex deletion leaves a path from the fixed source SET {a,b}
to the sinks: off P₀ use P₀; on P₀ use its avoiding witness (including source
and sink deletions). Hence there is no cut of size≤1. Directed Menger gives
two undeleted vertex-disjoint paths, necessarily from both a,b to distinct
sinks. The fixed-pair Menger objection is WITHDRAWN: one surviving path
after each≤1 deletion is sufficient, not insufficient. Uncollapse at actual
first-entry vertices to obtain clean legs. All of this remains unformalized,
not refuted; it depends on the stated network, locality and connectivity
claims, not merely on truncation or an unqualified Menger invocation.

## Odd peripheral core and cubic composition

Internal odd relative lemma: cubic 3-connected G, H nonempty connected,
G−H containing an odd cycle, imply an induced odd nonseparating cycle
outside H. Choose induced odd C maximizing component B of G−C containing
H. Any other component D is bipartite, otherwise choose an induced odd
cycle in D and enlarge B through the old C. Cubicity makes attachment sets
of different components disjoint and partition C; 3-connectivity makes each
size≥3. Add attachment leaves to D. Shortest paths through this bipartite
extension between consecutive D-attachments have total parity even, whereas
the corresponding C-arcs sum to odd |C|. Some arc/path union is odd;
take an induced odd subcycle. Maximality forces all B-attachments onto its
open C-arc. Consequently D lies in one gap between consecutive
B-attachments; similarly every non-B component is assigned to a gap.
A nonempty gap interior plus its assigned components has boundary in its
two endpoints, a forbidden 2-cut. Thus no D exists.
A shortest odd cycle C₀ has |C₀|≤2 diam(G)+1=O_h(ln n): a shortcut shorter
than both arcs produces a shorter odd closed walk/cycle by parity.
For n>4|C₀|/h, the giant J of G−C₀ has
|G−J|≤(1+1/h)|C₀|. Apply the odd relative lemma protecting J to obtain
a short induced odd peripheral core outside J.

Fix q=⌈2448/h⌉ before buffers. Obtain q cores (first odd in the
nonbipartite case), |C_i|≤𝒞 ln n with fixed 𝒞=C_core(h), and 3q
connected BFS seeds of size τ and radius O_h(ln ln n), mutually separated
by L ln ln n. Prune their union ONCE to fixed host H₀ of expansion h/6.
Each core bag is O_h(ln n), each reservoir bag has τ≤size≤6τ/h,
intrinsic diameter O_h(ln ln n), and at least hτ distinct contacts with H₀.
For linkage stages choose b_q,…,b₁ backwards with
b_(i−1)>4κ_h(15+b_i)+10 and L>b_i+2κ_h(15+b_i)+10 for all i.
At stage i use F_i=earlier leg vertices ∪ radius-⌈b_i ln ln n⌉
neighborhoods of all bags belonging to OTHER gadgets, in the original G.
Then |F_i|=O_(h,q)((ln n)^(12+b_i ln2)+(ln n)^4).
Fresh canonical survivors are proof devices only, not carried between stages.
Robust linkage gives clean near-half legs avoiding all prior legs and other
bags; the third bag is rank-three slack.

Let Z be the actual leg vertices in the FIXED H₀ (not any F_i or D(F_i)).
f=|Z|=O_(h,q)((ln n)^4)≤(h/6)²|H₀|/16 eventually. Degree-free floor
pruning below removes≤3f/(h/6), leaving common host H₁ of expansion h/12,
order n−O_(h,q)((ln n)^12). Keep every chosen reservoir bag intact outside
H₁, root its BFS spanning tree at the actual leg endpoint, so radius is
O_h(ln ln n) and every surviving contact uses that same tree. Contacts≥
hτ−O_(h,q)((ln n)^4)>2(log₂|H₁|)^6. These trees and both core alternatives
are clean, so Common host applies with β=h/12. It yields ceil host h/48,
width A=2448/h, outside arm length O_(h,q)((ln n)^4), and target window
[|Q|−1+c log₂ M*, |Q|−1+ρ(h/48)M*]. Set ρ_h=ρ(h/48)/2 and absorb
lower losses in B_h(ln n)^4. Subset-sum gap corrections give every even
length in [B_h(ln n)^4,ρ_h n], and every integer there if nonbipartite.
A multiplicative width>2 eventually supplies a dyadic cycle. This is an
informal restricted theorem for simple CUBIC 3-VERTEX-CONNECTED h-expanders,
not all cubic graphs or general EGC. The robust and container implications
still require formalization; no new universal safe-split lemma is assumed.

## Degree-free floor pruning and the floor-to-ceil bridge

For floor-half α-expander G of order M>0, 0<α≤1, seed F of size
f≤α²M/16, iteratively remove nonempty bad half-sets S from G−(F∪R),
where |N_H(S)|<α|S|/2. Keep R disjoint from F. Original expansion gives
|S|<2(f+|R|)/α. The union R satisfies |N_G(R)|≤f+α|R|/2, since an
external neighbor outside F was present when its adjacent removed set was
removed. Original expansion on R (NOT F∪R) yields |R|≤2f/α.
The induction is legitimate: |R|+|S|≤4f/α+4f/α²≤8f/α²≤M/2.
At termination total loss≤3f/α<M, leaving nonempty floor α/2 host.
If f=0 no bad set exists. No degree bound or seed neighborhood is used.
For odd M=2m+1, a new ceil-half set S has size m+1; erase v∈S to get
|N(S)|≥γm−1≥γ(m+1)/2 if m≥1+2/γ.
Thus floor γ implies ceil γ/2 at odd threshold
M≥2⌈1+2/γ⌉+1; for even M no threshold or loss is needed.

## Rooted supported FK adaptation F′ (sole owner)

External source: Michael Friedman–Michael Krivelevich, arXiv:1912.11011,
§2.1 Lemmas 2.1–2.6, §2.2 Lemma 2.7, §2.3 proof of Theorem 1.
The following is an INTERNAL adaptation, not their verbatim Theorem 1.
Let 0<α≤1, K>0, H=G[U] ceil-half α-expanding, |U|=M. Outside U are
disjoint rooted trees T₁,T₂ (roots a,b), radius≤K log₂ M, and simple
outside a–b path Q₀ of length≤K log₂ M meeting the trees only at a,b.
X_i=N_G(T_i)∩U must satisfy X₁ nonempty and |X₂|≥(log₂ M)^6.
Then for all sufficiently large M=M₀(α,K) and every integer
ℓ∈[c log₂ M,ρM], a simple cycle retains Q₀, has length in [ℓ,ℓ+A],
A=51/α independent of K,M, c=3K+O_α(1),
ρ=2^(−O(log(1/α)/α)). Support is ONLY U,T₁,T₂,Q₀; its interface is
one simple outside path y→T₁→a→Q₀→b→T₂→x₀ plus a simple H-path
x₀→y. Any compatible alternative outside arm replaces Q₀, preserving
simplicity and adding precisely its length difference. Container existence
is an input here, not a conclusion.

Greedy packing input (internal proof): for A,B⊆H, D₀=min(|A|,|B|)≥1,
|F|≤αD₀/20, and both remaining target sets of size≥D₀/2, balls of sizes
between D₀/2 and half |H−F| grow by 1+0.9α. With
r=⌈log(2M/D₀)/log(1+0.9α)⌉ and L=2r+1 they meet, giving a path of
length≤L. Iterating p=⌊αD₀/(20(L+1))⌋ times with ALL path vertices in
F gives p disjoint short paths and keeps the bound. The slack p≥
αD₀/(40(L+1))≥2 needs αD₀/(20(L+1))≥4; arbitrary D₀ does not get
this just from large M. Here D₀≥(log₂ M)^6/2 does.

Retained F′ derivation and support checks: FK Lemma 2.7 at y∈X₁ gives
rooted T′ with levels L₁={y},…,L_k₂, k₀≤C₀ log₂ M,
k₁−k₀≤C₁, k₂−k₁≤C₂, degrees in the last window≤Δ,
U₂⊆T′_[k₁,k₂] an (M/10,α/5)-expander of size≥M/10, where
Δ=⌈1600/α^5⌉, C₀=15/α, C₁=201/α^5, C₂=17/α.
Pack from X₂\{y} to U₂ with the greedy lemma; truncate each at first U₂
entry v_x (a singleton if x∈U₂), then drop the at most one path through y.
Remaining set S has |S|≥p/2. On each disjoint Q_x choose b_x∈Q_x∩T′
maximizing subtree size. Some level has≥|S|/k₂ such b_x; its disjoint
subtrees give an x₀ with |T′_b_x₀|≤2Mk₂/p. Hence
Y=∪_{u∈Q_x₀∩T′}T′_u has |Y|≤(L+1)|T′_b_x₀|
=O(M log³ M/(α^4D₀))=O(M/(α^4 log³ M)). This is a union bound,
not a false claim that all these subtrees nest.

A level-k₁ subtree is bad if it meets Y. Each has size≤
C₃=Δ^(C₂+1)=2^(O(log(1/α)/α)); union A_B of bad subtrees has size≤C₃|Y|.
Let v₀=v_x₀, K₀ its component in H[U₂]. It is an (M/10,α/5)-expander,
|K₀|>M/10. Apply FK deletion Lemma 2.2 to A_B∩K₀ (not A_B itself),
with |A_B∩K₀|≤α²M/2000, to obtain U₃⊆K₀\A_B,
|U₃|≥(1−3α/40)|K₀| and (M/10,α/10)-expansion.
Let D be the union of good level-k₁ subtrees meeting U₃; D∩Y=∅.
Shortest v₀–(D∩K₀) path Q′ meets D only at its endpoint u₀ and has
length≤350 log₂ M/α by FK Lemma 2.1. Contract clusters T′_w∩U₃;
FK Lemmas 2.4/2.5 give a path from u₀'s contracted cluster of length
ℓ′=⌈(α/(10C₃))⌊M/(10C₃)⌋⌉≥αM/(100C₃²)−α/(10C₃).
Unfold each visited cluster using at most two edge representatives joined
by its tree path (length≤2C₂). In the first cluster join u₀ even if it
lies outside U₃. This yields a SIMPLE path P in D starting at u₀,
|P|≥ℓ′, each cluster one contiguous block of≤2C₂+1 vertices.

The outside interface W has length≤3K log₂ M+2. Q=W+Q_x₀+Q′ is simple:
first-U₂ truncation gives Q_x₀∩Q′={v₀}; dropping y avoids other interface
intersection, including the allowed singleton x₀=v₀. Also Q∩D={u₀},
so Q∩P={u₀}. Let m=|Q| and d=ℓ−m−k₁≥0, choosing c large enough.
With ρ=α/(400C₃²), ensure d+2C₂+2≤|P|. Walk d steps along P, then
to the first vertex z′ outside that vertex's cluster, and close along T′
to y. Length is (ℓ−k₁)+s+depth(z′), with 1≤s≤2C₂+1,
k₁−1≤depth(z′)≤k₁+C₂−1, hence [ℓ,ℓ+3C₂]. The closing root path
avoids Y (otherwise its good subtree would lie in Y), misses W, and meets
only the PREFIX of P at z′ because the block at z′ begins there. It misses
Q′ because Q′∩D={u₀} in the distinct initial cluster. This audits simplicity
and the exact outside interface. These are adaptation repairs, not an
assertion that canonical FK Theorem 1 has an error. Their source-level
container has linear return |X₂|≥α^4M/200, not this polylog bound;
greedy packing plus the full-level elimination count justify the changed
hypothesis here. No claim that these repairs are Lean-checked is made.

For bipartite G and fixed r≥⌈A/2⌉ compatible arms Q_j of lengths
|Q₀|+2j, j=0,…,r, apply F′ at ℓ=2^k−2r. Returned length is even and
≤2^k, so its difference is an available 2j. This gives each dyadic target
in [2c log₂ M,ρM] eventually, with exact compatible support.

## Common-host strong-reservoir assembly (conditional gadget input)

Fix q≥1 and 0<β≤1, induced floor-half β-expander H of order M.
Outside H assume q DISJOINT gadget supports, each a core with two simple
a_i–b_i arcs of disjoint interiors and length gap δ_i∈{1,2}, two clean
disjoint legs to disjoint reservoir trees L_i,R_i, radius≤K log₂ M for
one fixed K, each with≥2(log₂ M)^6 distinct H-neighbors. Legs meet only
their own core roots/tree roots, both alternatives avoid all other support.
Total core/leg support is polylog(M), with q,K and all constants fixed.
Reservoir size may be polylog but is not required for the deletion budget.
These are hypotheses, NOT produced by this section.

Long-arm extension: if a simple compatible outside arm Q₀ has any length
L, omit its internal vertices and use one designated artificial edge ab
(or the existing ab edge, never a parallel edge). F′ applied at
ℓ′=ℓ−(L−1), then replacing ab by Q₀, gives width 51/α on
[L−1+c log₂ M,L−1+ρM]. Endpoint trees still have fixed logarithmic radius;
this does not license arbitrary-radius or uniform-in-radius trees.

Connect R_i to L_(i+1) successively. At every stage RETURN to the original
H and floor-prune the ACCUMULATED actual connector seed, including
zero-length connector vertices. Its size f_i≤C_(q,β)log₂ M≤β²M/16.
Loss≤3f_i/β leaves floor β/2 host of diameter O_β(log₂ M); contacts
survive since boundary≥2(log₂ M)^6 and loss is only logarithmic.
Use the root-to-contact tree paths, contact edges and short host connector.
These connecting pieces are disjoint by prior seed deletion and clean
supports. Concatenating baseline long core arcs yields a SIMPLE path Q
from L₁ root to R_q root, |Q|=L=O_(q,β,K)(polylog M). Endpoint trees meet
Q only at roots; intermediate trees may be traversed.
Final pruning AGAIN in original H uses F=V(H)∩V(Q) with
|F|≤C_(q,β)log₂ M (actual connectors, NOT total polylog support).
It leaves H* of order M*=M−O_(q,β)(log₂ M), floor β/2 expansion,
then ceil β/4 by the explicit bridge. Endpoint boundaries≥(log₂ M*)^6
remain. Long-arm F′ has A=204/β independent of q and exact window
[L−1+c log₂ M*,L−1+ρ(β/4)M*], c=3K+O_β(1).
Replacing any subset I of baseline long core arcs by short ones preserves
simplicity and gives |C_I|=|C_∅|−Σ_{i∈I}δ_i.
For q≥⌈A⌉ chosen first, all δ_i=2 in a bipartite input supply every even
correction up to A; even cores alone do not prescribe gap 2, which is an
explicit hypothesis. If any δ_i=1, subset sums of these 1/2 gaps fill
[0,Σδ_i], hence every integer correction. All thresholds depend on fixed
q,β,K; never halve host expansion once per gadget or let q grow.

## High-girth degree-free deletion E

For h-expander G of girth g, delete Z of size m. Suppose J=G−Z has
minimum degree≥2 and independent degree-two set B. If
(9/8)^⌊(g−1)/2⌋>3m/h, then J expands by κ=min(h/2,1/16).
For s=|S|≤|J|/2 with s≥2m/h use |N_J(S)|≥hs−m≥hs/2.
For s<2m/h assume T=N_J(S) has |T|<s/16, U=S∪T,
|U|<17s/16<3m/h. AHL at average degree 17/8 implies
 e_J(U)<17|U|/16<289s/256,
and the same bound on any nonempty R⊆S. Let I be isolated vertices of
J[S], R=S\I, t=|R∩B|, s₃=|R\B|, D=sum of J-degrees on R\B.
Independence/nonisolation give D≥t, and degree≥3 gives D≥3s₃;
4D≥t+9s₃ so 2t+D≥9|R|/4. Therefore
 e_J(U)≥Σ_{v∈R}d_J(v)−e_J(R)+2|I|
 >19|R|/16+2|I|≥304s/256,
contradiction. If R empty, e_J(U)≥2s is enough. No maximum degree is used.
For the whole-graph count D≥2t and D≥3s₃ give average degree≥12/5.
For m=0 only the large-set branch is needed; no empty-set Moore invocation.

## Sparse adjusters P (degree-free, fixed q)

Fix q before n. Put p_i=10+3(q−i), r_i=⌈p_i log₂ log₂ n⌉,
r_max=r₁, S₀=400·4^q(r_max+1), R_i=S₀/4^i, S_i=4R_i.
Roundings are absorbed in the stated leading constants. Initially B=∅;
at stage i, min degree≥2 and degree-two vertices are S_i-separated.
The whole-graph count in E gives average degree≥12/5, so AHL gives an
ordinary shortest cycle C_i of length c=O(log₂ n). For the first cycle in
nonbipartite G choose a shortest ODD cycle instead; expansion/diameter gives
c≤2diam(G)+1=O_h(log₂ n). Both kinds are isometric: a shortcut shorter
than the shorter arc gives shorter closed walks of opposite parity in the
odd case, hence a shorter odd cycle. Internal intersections do not spoil
this closed-walk argument.

If chosen connected Z contains an isometric C and all points are within
intrinsic distance R of C, d_Z(z,z′)≤d_J(z,z′)+4R. When g>4R+4 an
outside vertex cannot have two Z-neighbors; a shortest remaining path of
length L between two outside contacts yields a cycle of length≤2L+4R+4,
so L≥g/2−2R−2 (shared contact uses length L+2). Extra induced edges
only improve distances; selected subgraphs suffice.

Set r=r_i and mark C vertices within r+1 of old B as bad. The separated
bad-port estimate is
 (c/(S_i−2(r+1))+1)(4(r+1)+1)<c/4.
Choose two good near-half ports with shift c/2−1 for even c, (c−1)/2
for odd c, distance at least c/2−1. The core routes, including off-cycle
edges, have lengths c/2+1,c/2+3 for even c and (c+3)/2,(c+5)/2 for odd c.
The needed condition is c>4r+8 (NOT the false even lower bound (c−1)/2);
g≥10S₀ ensures it. In J−C, radius-r balls at their outside neighbors u,v
are disjoint trees with no extra C contacts by girth/isometry, all degree≥3
since ports avoid B. Select EXACTLY two children per node, yielding full
binary reservoirs F_u,F_v of size 2^(r+1)−1, not unbounded-degree balls.
Each has≥3|F|−2(|F|−1)−1=2^(r+1) outward edges, all to distinct vertices
outside Z₀=C∪F_u∪F_v; unselected internal children count too.

Saturate Z₀ by shortest paths from old defects within distance R_i,
stopping at first hit. Old 4R_i separation gives disjoint paths and
2R_i-separated attachments, at most c/(2R_i)+3 paths.
Deletion set Z_i has |Z_i|≤1.5c+2^(r+2)−2+3R_i and every point is
within γ_i=r+1+R_i of C. Geometry then gives outside degree loss≤1,
new-new defect distance≥g/2−2γ_i−2≥R_i. Old surviving defects have no
contact (otherwise absorbed or too close to another old defect); old-new
distance≥R_i too. Thus min degree≥2 and next defect separation R_i=S_(i+1).
For a single buffer and reservoir, two lost boundary contacts would give
a cycle≤2r+R_i+2<g. If it contacts BOTH reservoirs, tree/buffer routes
give a walk≤R_i+2r_i+4≤101S₀/400<5S₀−1≤d_C(a,b), contradicting
isometry even if the walk is not simple. Hence at most ONE boundary contact
is lost per buffer across the two reservoirs together. This includes
internal-node contacts. Current-stage loss is O_(h,q)(log n/log log n);
later stages lose O(log^(p_i−3)n), so final contacts≥log^(p_i)n≥log^8 n.
Total deletion m=O_(h,q)(log^(p₁)n). Choose girth coefficient large enough
for g≥10S₀ and E's inequality against ORIGINAL h. Final host has κ expansion,
not an expansion parameter repeatedly divided during packing.

## High-girth consumer and satisfiability

For every fixed 0<h≤1 there exist C(h),B(h),ρ(h)>0,n₀(h) such that simple
minimum-degree-three h-expanders on n≥n₀ with girth≥C(h)log₂ log₂ n
have every integer cycle length in [B(h)log₂ n,ρ(h)n] if nonbipartite,
and every EVEN integer there if bipartite. This is the informal E/P/F′
composition, not a general girth-free claim. Set κ=min(h/2,1/16),
α=κ/4,A=204/κ,q=⌈A⌉ before P. Connect the selected gadgets in the
original E/P host, pruning accumulated actual connector vertices only,
O_(h,q)(log n). Final floor κ/2 then ceil κ/4 host has
M=n−O_(h,q)(log^(p₁)n); reservoir contacts>log^6 M and fixed log-radius
bounds provide F′'s actual container. Outside alternatives have increments
subset sums of d_i=1 for odd C_i, 2 for even C_i. First odd core ensures
all increments [0,w] if nonbipartite; bipartite increments are 0,2,…,2q.
For target T apply F′ at ℓ=T−w, w=Σd_i (2q if bipartite).
Returned L lies [T−w,T−w+A]⊆[T−w,T]. Correct by the compatible arm
with increment T−L. Parity is automatic in the bipartite case. M=n−o(n),
w=O_h(1) allow the target endpoints above. The least dyadic≥B log n is
≤2B log n<ρn eventually, and all dyadic targets in the interval occur.
The original generalized exposition still awaited a final exposition audit;
this archival compilation cannot replace it.

External LPS provides nonempty high-girth model families: Lubotzky–Phillips–
Sarnak, *Ramanujan graphs*, Combinatorica 8 (1988), §2, Proposition 3.3,
Theorem 3.4 and nonbipartiteness discussion. With p=5, primes q≡13,17
mod 20 give bipartite PGL₂ order q(q²−1), girth≥4log₅q−log₅4;
q≡1,9 mod 20 give nonbipartite PSL₂ order q(q²−1)/2, girth≥2log₅q.
For large q the six generators are distinct/nonidentity; Dirichlet supplies
infinitely many q in these classes. Ramanujan 2√5 gives edge expansion
≥3−√5 and vertex expansion>(1/8) after division by six. Both parity types
therefore inhabit the assumptions for every fixed h≤1/8. These are external
existence inputs, not Lean constructions or evidence for EGC failure.

## Fiber amplification and girth-free interval boundary

Assume a finite nonempty dyadic-free min-degree-three graph exists, and
choose connected component F, m=|F|, Δ_F=max degree. External six-regular
LPS base X_N has N vertices, edge expansion≥1/2, N→∞. Subdivide each edge
into a path of length THREE, forming H_N on 7N vertices with 6N degree-two
vertices; every cycle length is three times an old base cycle, hence not
dyadic. Attach one fresh F copy by a single bridge at EACH degree-two
vertex. Result G_N is connected, order (7+6m)N, minimum degree≥3,
maximum degree≤D_F=max(6,Δ_F+1), and every cycle lies in H_N or one copy F.
Thus it is dyadic-free and girth(G_N)≤girth(F), deliberately NOT high-girth.

Use the formal fiber helper with connected induced fibers of size≤s,
base maximum degree≤d, every base edge witnessed by a cross edge, and base
edge expansion η>0: output edge expansion η/[s(η+d+1)]. Extra edges are
allowed. The source's cut proof applies η|U| to the full-fiber set without
checking that it is a base half-set. Use the formal helper's min-form cut
bound η·min(|full|,|empty|) instead: both counts are≥a/s−p for a new
half-set of size a and p partial fibers. Thus cut≥p and
cut≥ηa/s−(η+d)p, giving the same constant. This explicitly repairs the
source argument, not the construction or the formal helper.
First fibers are seven-vertex stars over X_N, one cross edge per
base edge: s=7,d=6,η=1/2 give η_H≥1/105. Second fibers over H_N are
singletons or a subdivision vertex plus its F copy: s=m+1,d=6,η=1/105
give η_G≥1/[736(m+1)]. Divide by D_F for vertex expansion
h_F=1/[736(m+1)D_F]>0. The generic cut inequality is formal, but both
constructions, cycle localization and external base-family use are prose.
This proves informally the equivalence of finite EGC with: for every fixed
h>0, all sufficiently large min-degree-three h-expanders have SOME dyadic
cycle. Requiring a fixed maximum degree D as well for every fixed (h,D)
suffices. This is amplification, not induced extraction or cubic reduction.

For bipartite X_N and F=K₃,₃, the same construction is bipartite with
order 43N, minimum degree≥3, maximum degree≤6, vertex expansion≥1/30912.
Bridge localization gives cycle lengths⊆{4}∪6ℕ: K₃,₃ has only 4/6 and
three-subdivided bipartite base lengths are multiples of 6. It has C₄ but
NO dyadic cycle of length≥8. Hence for every fixed 0<h≤1/30912, full even
intervals and all large dyadic lengths fail without girth. It does NOT refute
EGC; only existence of some dyadic cycle remains a possible girth-free aim.

## Split obstruction: universal method, not an EGC counterexample

An admissible split replaces a degree≥4 vertex v by adjacent fresh u,w,
partitioning N(v)=A ⊔ B with |A|,|B|≥2. No other graph operation is allowed.
It preserves finite simple connected min-degree-three graphs and changes
(n,e,ε) to (n+1,e+1,ε−1), ε=2e−3n≥0. Safe means dyadic-free result;
ε=0 iff cubic, so every safe sequence has length≤initial ε.

Use the retained formal seven-vertex core H with hub 0, rim path 1–…–6,
spokes to 1,2,5,6. Its min degree is 2, hence not a CE. Its three balanced
hub partitions (side containing 1 is {1,2},{1,5},{1,6}) have C₈,C₄,C₄
witnesses respectively. Assuming EGC false choose a connected CE F and
attach FOUR DISTINCT copies by bridges at 1,3,4,6 of H. Every cycle stays
in H or a copy, and the completed G has min degree≥3 with all original
nonzero core vertices degree 3, hub degree 4. Splits outside H preserve
all core edges and core degrees, including when an external attachment
endpoint splits. Thus nonzero core vertices are forever ineligible; hub
witnesses are forever locked, so hub cannot safely split. No safe sequence
ends cubic, though initial G may have safe moves elsewhere. Extend until
no safe move remains; excess termination gives a noncubic terminal graph.

On EXACT class 𝒟 of finite nonempty connected simple dyadic-free graphs of
min degree≥3, the principles “every member safely splits to cubic” (zero
steps allowed), “every noncubic member has a safe step”, and “every degree-4
vertex has a safe balanced split” are each equivalent to EGC. Step implies
completion by excess induction, completion implies step by its first move.
EGC makes 𝒟 empty; if EGC false the bridge completion defeats completion
and local4, and its maximal descendant defeats step. This is a conditional
universal-method obstruction, not impossibility of other reductions or of
special minimal/2-connected reductions; G contains proper CE copies F.

Exact split cycle criterion for dyadic-free X: X′ has a 2^k-cycle iff
(I) X has a (2^k−1)-cycle through v with its two v-neighbors in opposite
parts, OR (II) two old simple cycles meeting exactly at v have lengths
r,s≥3, r+s=2^k, with both neighbor pairs crossing. A new cycle must use
both copies. If it uses uw contract it to get I; otherwise identifying
u,w gives the figure-eight II. Each portion length≥3 since the partition
has no common neighbor. Conversely expand I through uw, or open each
cycle of II into disjoint u–w paths and join them, avoiding uw.
The graph R_v on N(v) of near-dyadic cycle pairs only forces its connected
components to remain within parts; this condition is NECESSARY, not sufficient.

Pure-II family: j≥4, N=2^(j+1)−8, rim C_N with hub neighbors 0,4,8,2^j.
Rim gaps 4,4,2^j−8,2^j−8 are multiples of 4, so every hub cycle has
length 2 mod 4; rim length lies strictly between 2^j and 2^(j+1).
Thus B_j is dyadic-free, bipartite and 2-connected, hub degree 4, its four
neighbors degree 3, other rim vertices degree 2. R_v=∅ since all cycles
even. Pairings M₁={(0,4),(8,2^j)}, M₂={(4,8),(2^j,0)} give cycles meeting
only at hub with lengths 6 and 2^j−6. For partition {0,4}|{8,2^j}, M₂
crosses; for {4,8}|{2^j,0}, M₁ crosses; for {0,8}|{4,2^j}, both cross.
Every balanced hub split therefore creates C_(2^j) AVOIDING the split
edge. Min degree 2 prevents this family from being a CE or an excess-minimal
CE model. Bipartiteness, 2-connectivity, empty R_v and cubic hub-neighbors
alone cannot justify split safety.

## Concrete reopening conditions

For either interval consumer, formalize the exact locality/block/packing,
rank-three plus fixed-pair diameter replacement, and F′ support interfaces;
finite edge inequalities alone leave those bridges unpaid. For common-host
assembly outside the supplied cubic/high-girth constructions, produce the
stated disjoint strong gadgets rather than assume them away. For a girth-free
route aim only at SOME dyadic cycle and confront amplification, not the false
full-interval goal. For a split route retain both I and II or restrict to a
class where one is genuinely excluded. The external AHL, FK and LPS source
hypotheses and the fixed-q quantifier order must survive any formal statement.
Compilation of this module checks only comment syntax, none of these claims.
-/

set_option autoImplicit false
