import Combinatorics.CanonicalPairCarry

/-!
# Canonical-base carry transfer: scalar route archive

This archive records the scalar canonical-box route from
`Plans/CanonicalBaseCarryTransfer.md` (provenance note `8541812...`). Novelty
has not been verified. It is not a proof of either entropy assertion below.
Production does not import this archive.

## Exact open target CB

Let integers r ≥ 2 and L ≥ 1 be fixed. Let U have an arbitrary joint law on
{0,…,r−1}^L, with no independence hypothesis between its digits. Set
Z = ∑_{i<L} U_i r^i and Δ = L log r − H(U), and assume Δ ≤ 7L/192.
Let Z′ be an independent copy of the WHOLE vector evaluation Z. For integer n,
write g(n) = H(Z−nZ′)−H(Z). CB asks for an absolute C, independent of the
parameters and law, such that every nonzero integer polynomial P of degree d
and coefficient mass S = ∑ |c_j| ≥ 1 satisfies

  g(P(r)) ≤ C [d+1+log(1+S)] max(g(1),g(r)).

CB is open and unrefuted in this class. The stronger scalar bridge SC,

  g(n) ≤ A [1+log(1+|n|)/log r] max(g(1),g(r)),

with absolute A, is refuted by the family below. This does NOT refute CB.
Neither target is stated as a Lean theorem here, because its probabilistic
objects and requisite entropy bridges have not been formalized.

## Source calculus and why it stops

Historical plan-level provenance for the integer estimate is
`Plans/RationalPolynomialEntropy.md`; the correlated coefficient-box input is
recorded in `Plans/CorrelatedPolynomialBox.md`. These are source pointers,
not imported proofs or scalar CB results.

Tao, arXiv:2511.15135, Proposition `dilate`, supplies fixed-law product and
finite-sum inequalities and the integer estimate
  g(n) ≤ (4+10 floor(log₂ |n|)) g(1)  (n ≠ 0).
These are source results, not Lean-checked assertions in this archive. They
refer to one rational-valued law and an independent copy, not independent
digits or later auxiliary variables. Sparse Horner evaluation yields
  g(P(r)) ≤ d g(r)+(k−1)g(1)+∑_{c_j≠0}g(c_j),
where k counts nonzero coefficients. Dense coefficients can then cost
k log(S/k), of order d log(S/d), rather than d+log(1+S). No batching mechanism
in the reviewed calculus removes this loss.

Canonical evaluation gives g(r^L)=H(Z); the product inequality therefore gives
  g(r) ≥ log r−Δ/L ≥ log r−7/192.
The crude interval-support bound g(n) ≤ log(1+|n|)+Δ for n ≠ 0 does not
remove the L-sized deficit. Correlated formal coefficient-box estimates
require |r| ≥ (1+S) max_i(N_i−1)+1, a large evaluation base relative to
coefficient sizes, and therefore do not transfer at canonical base N_i=r with
unrestricted coefficients. Their formal gains are not scalar g.

## SC counterexample and the checked combinatorial unit

Take a ≥ 2, r=a², k=a, M=ceil((192/7) k log a), L=k+M. Use k independent
uniform digits in {0,…,a−1}, then M independent uniform digits in
{0,…,r−1}, with all blocks independent. Write Z=A+r^k V. Its deficit is
Δ=k log a ≤ 7L/192. For an independent whole-vector copy let B=A−aA′.
Put b=a(a−1). The coefficient u−av+b=u+a(a−1−v) bijects the pair digit
box with {0,…,r−1}. Thus B+b∑_{i<k}r^i is ordinary base-r evaluation.

The imported production module proves precisely this finite encoding unit:
pair vectors biject with r^k ordinary digits/values, the signed block has a
translated consecutive interval as its exact range, and its nonnegative
integer remainder modulo r^k is bijective (hence determines the low pair).
It includes a=1 and k=0, so the modulus is always positive for a ≥ 1;
the empty block has its single residue modulo one. This is a complete
combinatorial input to the named SC consumer, not the full entropy proof.

For the family, R=B mod r^k is uniform on all r^k residues and determines
both low vectors. Q=(B−R)/r^k is a function of R. Then
  Z−aZ′=R+r^k(Q+V−aV′).
Independence of the high block gives
  H(Z−aZ′)=k log r+H(V−aV′) ≥ k log r+M log r,
so g(a) ≥ k log a. Explicit (not necessarily uniquely decodable) coefficient
codes give
  g(1) ≤ k log(2−1/a)+log 2,
  g(r) ≤ (k−1)log(2−1/a)+log(r+1).
With k=a these reference gains are O(a), while g(a) ≥ a log a. The SC
multiplier at n=a is at most 2, so SC fails asymptotically. The constant
polynomial P=a in CB has d=0 and S=a; its log(1+S) pays for this example.
The source's earlier Δ ≤ 1/8 small-deficit fallback remains a separate
intermediate restriction; it is not promoted here to a solution of CB.

Uniform pushforward, entropy identities, conditional entropy bounds,
independence, ceiling estimates, these coding bounds, and the asymptotic
contradiction remain UNFORMALIZED here. No entropy assertion follows merely
from the existence of the imported Lean equivalence without those bridges.

## Reopening condition

A concrete equivalent CB batching target is an absolute K such that, for
signed binary layers ε_ij ∈ {−1,0,1},
  g(∑_{i≤m}∑_{j≤t} ε_ij r^i 2^j)
    ≤ K(m+t+1) max(g(1),g(r)).
The expected implications use binary coefficient expansion and
S ≤ (m+1)2^(t+1); they are not Lean-checked here. No proof of the signed-layer
estimate is available. Reopen CB on a new justified batching estimate or a
direct canonical carry argument, not by assuming SC or renaming formal
coefficient gains. The present unit only removes the finite low-pair encoding
obligation from a future SC entropy formalization. Coordinator review, a
separate axiom audit, and the retirement gate remain required before removal
of the original plan; this archive itself does not authorize such removal.
## High-mass balanced-subset obstruction (independent entropy route)

This is an internal counterexample to the proposed uniform assertion:
there exists absolute finite C such that, for all sufficiently large N,
every vector cap A ⊆ [0,N)² of mass at least N√r obeys
I(X;Y) ≤ C(d_X+d_Y+1), where r=r₃(N), (X,Y) is uniform on A,
d_X=ln N−H(X), d_Y=ln N−H(Y), and entropy uses natural logarithms.
A vector cap excludes every nonconstant coordinatewise 3-AP. This is NOT
a counterexample to CB, to the scalar-cap Fourier candidate, or to global P.

Take a maximum ordinary cap B ⊆ [0,N), |B|=r. Every subset of B×B is a
vector cap: each coordinate progression in B is constant. The existing
`Erdos142.eventually_rothNumberNat_lower_bound` in
`Erdos.Erdos142.TorusAsymptoticLowerBound` gives, for each fixed ε>0,
r ≥ N exp(−(torusLeadingConstant+ε)√ln N) eventually. Thus
λ=ln(N/r)=O(√ln N), 0≤λ, and eventually r≥N^(2/3). Let
m=⌈N√r⌉≤r² (the integer r² bounds the real quantity before the ceiling).
Uniformly sample an m-subset of B×B. Each row/column degree D is
hypergeometric with mean μ=m/r≥√N. Set
δ=√(6 ln(4r)/μ)=o(1), eventually 0<δ<1. The hypergeometric Chernoff
input gives Pr(|D−μ|≥δμ)≤2 exp(−δ²μ/3)=1/(8r²).
The union bound over 2r fibers is at most 1/(4r)<1, so some deterministic
m-subset has every fiber degree at most (1+δ)μ.

Its marginal probabilities are at most (1+δ)/r. Relative entropy against
the uniform law on B is the average of ln(rp), so
0≤ln r−H(X), ln r−H(Y)≤ln(1+δ)=o(1).
The whole-pair entropy is ln m=ln N+(ln r)/2+o(1). Consequently
  d_X+d_Y=2λ+o(1),
  I(X;Y)=(ln N)/2−3λ/2+o(1),
and I/(d_X+d_Y+1)→∞. This defeats every fixed C at the stated mass.
For each fixed η>0, however,
  m/(r^(1+η)N^(1−η))=(1+o(1))N^(−1/2)exp((η+1/2)λ)→0;
there is no P-shaped cardinality counterexample here.

The maximum-cap and lower-bound inputs are current mathematical objects;
only the lower-bound theorem is represented by the cited Lean module.
Sampling, Chernoff concentration, deterministic extraction, entropy and all
asymptotic bridges above remain prose, not kernel-checked. The construction
is internal (no external priority claim). Reopen this entropy route only with
a hypothesis excluding such sparse subproducts, or a precisely stronger
mass condition near Nr and a new justified estimate; balanced marginals and
mass N√r alone cannot supply it.
-/

set_option autoImplicit false
