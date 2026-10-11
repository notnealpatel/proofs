/-!
# Prime-power canonical polynomial phase sparsity: synthesized archive

## Status and provenance

This archive records a restricted finite sieve argument, not a proof of Erdős #711,
an all-moduli density theorem, or an exponent improvement. The input is
`Plans/Erdos711PrimePowerPhaseSparsity.md`, with assessment provenance at source
revision `8541812...`. Its “AUTHOR-validated” language is historical assessment
prose, not original-author certification or a Lean certificate. Novelty has not
been checked. The assessment accepts the exact finite canonical-phase collision
sieve; independent coordinator review, a fresh audit, and retirement of the plan
are separate gates. This archive consolidates the substantive source contract
while keeping unformalized premises and source checks explicit.

The standalone production module
`Combinatorics.PrimePowerPolynomialRoots` establishes only the root-lifting unit:
for a natural prime p, e ≥ 1, and an integer polynomial P whose reduction modulo p
is nonzero of natural degree at most d, the number of n in Fin(p^e) with
P(n) = 0 modulo p^e is at most d p^(e-1). Reduction sends every such root to a
prime-field root; the quotient coordinate has p^(e-1) possibilities. No Hensel
nonsingularity assumption is used. The zero reduction is deliberately excluded;
constant nonzero reductions have no roots. Exponent zero is excluded: modulo 1
there is one residue root even for a constant polynomial, incompatible with d=0.
This archive has no formal target theorem and imports no proof-bearing module.

## Exact finite contract and conclusion (mathematics, not Lean declarations)

Fix integers k ≥ 2, L ≥ 3, M ≥ 2 and positive v,W. Let P ∈ ℤ[T] have degree at
most k, without coefficient-height restrictions, and let D be a nonempty finite
set of DISTINCT integers in [v,v+W). Write Q=|D|. For each d, b_d is the unique
representative in {1,...,M} congruent to P(d) modulo M. Assume
M+(L-1)W < v and an actual integer m ≥ 0 with m ≡ -b_d (mod d) for every d∈D.
Set N_d={m+b_d+j d : 0 ≤ j < L}. These are the full canonical neighborhoods,
not arbitrary subsets of them. The displayed phase linkage and band condition
are essential; arbitrary phases or cross-band collisions are not covered.

Let rad(M) be the product of its distinct prime divisors, ω(M) their number,
E(M)=M/rad(M), and a1 the coefficient of T in P. Put
R=∏{q prime : q|M, k<q, deg(P mod q)≤1}, including zero and constant reductions
in this low-degree case. Let G count j∈{1,...,L-1} with gcd(j+a1,R)=1. Define
S_M=∑_{e|M} φ(e)/e = ∏_{q^a||M}(1+a(1-1/q)) and
H_t=∑_{j=1}^t 1/j. With real-valued error
Err=(W+M) k^ω(M) E(M) S_M H_(L-1), the finite claim is

  |⋃_{d∈D} N_d| ≥ QG - Err.

Also G ≥ (L-1)φ(R)/R - 2^ω(R), and R=1 gives G=L-1 exactly. Thus the additional
strict Hall deficiency premise |⋃ N_d|<Q implies Q(G-1)<Err. Deficiency is not
asserted to hold for every family.

## Collision consumer and mathematical proof dependencies

For a fixed positive j and positive Δ with d,d+Δ∈D, a collision gives
jΔ=b_d-b_(d+Δ), hence Δ<M/j; there are no collisions when M/j≤Δ.
Let g=gcd(Δ,M), h=M/g, and form the INTEGRAL polynomial
F_Δ(T)=(P(T+Δ)-P(T))/Δ. Integral divisibility of every coefficient must be proved
before reduction. The collision implies h | F_Δ(d)+j by integer gcd cancellation,
not inversion of Δ modulo M. A prime dividing Δ can remain in h: M=q^3, Δ=q
leaves h=q^2. A nonsquarefree CRT argument must retain those powers.

For q|h with q≤k, even the zero polynomial has at most q≤k prime-field roots.
For k<q and deg(P mod q)=r≥2, F_Δ mod q has degree r-1≤k-1 and leading
coefficient r c_r ≠ 0. This holds EVEN when q|Δ: division was integral before
reduction. For low-degree reductions F_Δ≡a1 modulo q; good j makes a1+j nonzero,
so there are no roots (including constant and zero reductions of P).
The production lifting theorem applies to the nonzero reduced polynomial
F_Δ+C j and supplies at most (r-1)q^(a-1) roots modulo q^a. In the small-prime
zero case use the trivial q^a bound, equivalently q prime residues each with
q^(a-1) possible lifts, rather than applying the nonzero-polynomial theorem.

CRT and prime-power factor comparisons then yield at most k^ω(M)E(M) residue
classes modulo h. Each class has at most W/h+1 candidates in the interval.
Thus fixed-Δ collision count is at most
(W+M) gcd(Δ,M)/M · k^ω(M)E(M), and is zero for Δ≥M/j.
Using gcd(Δ,M)=∑_{e|gcd(Δ,M)}φ(e), counting positive multiples gives, for real A≥0,
∑_{1≤Δ<A}gcd(Δ,M)≤A S_M. Therefore band j has at most
(W+M)k^ω(M)E(M)S_M/j collisions. A fiber of size t loses t-1 distinct values
and contributes choose(t,2) pairs. Bands T_j={b_d+j d:d∈D} are disjoint under
the strict band inequality, so summing the good positive bands proves the finite
union estimate. Translation by m preserves cardinality. Realization of m is an
explicit premise; it is not supplied by a fictitious unrestricted CRT assertion.
Shifted inclusion-exclusion gives the asserted G estimate and endpoint error.

## Corrected uniform consequence

For fixed k, additionally assume M≤W≤n, E(M)≤n^ρ, L≥n^ε with ρ<ε, and v≤n
(or instead explicitly L≤n). Then L≤n follows from the band inequality if v≤n:
W≥1, M≥2 and (L-1)W+M<v ensure L<v≤n. The source's phrase “all steps are at
most n” intended this extra scale control, but it is NOT part of the displayed
finite contract. Without it there is no stated uniform O(log n) bound for H_(L-1).
With it elementary estimates uniformly in the coefficients give
k^ω(M)E(M)S_M H_(L-1)≤n^(ρ+o(1)) and G≥n^(ε-o(1)). Under the indispensable
Hall deficiency premise this yields Q/W≤n^(ρ-ε+o(1)). For E(M)=n^o(1) it gives
decay in this model; for unrestricted moduli it gives no universal density decay.
No arbitrary-integer Hall reduction is supplied.

## Derived nonsquarefree source check, not a literal cited theorem

The source cites Chen--Korsky Section 5 in
`/home/exedev/p/erdos711-restart-20261009/sources/ChenKorsky-2607.26450.tex`:
compression at lines 330–350 and prime-rich construction at lines 354–429.
The historical squarefree plan is at revision
`861e46dfa2b892d6b19863951664520ed2b73105`; its quadratic CRT note is at
`672d5ebf503e293036ea21732e6f1c584cadab9a`. These are provenance pointers,
not independently checked source files in this task. Historical squarefree
prose audits do not certify the repeated-prime extension or this adaptation.

The squarefree predecessor reported two independent prose audits accepting its
local bad-prime sieve and checking affine, constant, small-prime, q|Δ,
CRT-lifting, endpoint, inclusion-exclusion and asymptotic cases. This is a
historical reported audit record, not a Lean certificate or a new source audit.
One objection exposed the need for the explicit linkage b_d=P(d) modulo M;
the other proposed cross-j collisions using parameters that violated
M+(L-1)W<v. With that retained band condition the T_j are disjoint, so the
proposed counterexample did not apply. Both representation risks remain
explicit in the finite contract above. These audits covered the squarefree
predecessor only, not the repeated-prime extension or derived nonsquarefree
construction.

For P=T^2, take the source product Q0 of the first s odd primes (including 3)
and replace the modulus by M=3Q0=9∏_{q|Q0,q>3}q. Completing the square shows
four values of d^2+j d modulo 9, versus two modulo 3. CRT changes compression
from δ=A/2^s to δ_new=2A/(3·2^s), where A=∏_{q|Q0}(1+1/q). The source prime
block, K and interval length W are retained. The claimed adaptation uses
M=3Q0=o(W), primes at scale n coprime to M, eventual source band inequalities,
and the source actual CRT realization of m. The actual union upper bound is
|T|≤3K^2Wδ_new<Q, two thirds of the previously strict bound. It is a derived
adaptation, NOT literally a Chen--Korsky theorem and NOT just relabeling a witness.
Here E(M)=3, R=1, G=K-1, and
S_M=(7/3)∏_{q|Q0,q>3}(2-1/q); the former squarefree factor at 3 was 5/3.

For compatibility, K^2≤2^s/(16A log n), Q≤W and W+M≥W imply that
Err=(W+M)2^s·3 S_M H_(K-1) satisfies
Err/Q≥48 A S_M K^2 log n H_(K-1), eventually exceeding G-1=K-2.
The conservative finite sieve does not rule out this deficient construction.
Its genuine union count, band estimates and CRT realization remain required;
the error comparison is no substitute for them.

## Remaining formal and mathematical gates

Only the named prime-power root-count implication is assigned to production.
Still unformalized are integral finite differences and their degrees even at
q|Δ; canonical-phase collision cancellation; the small-prime zero-polynomial
branch; retained prime-power CRT and E(M) comparison; interval residue counts;
the gcd/totient sum and S_M product; fiber-loss and disjoint-band union counts;
shifted inclusion-exclusion; Hall arithmetic; all uniform asymptotic estimates;
and the full nonsquarefree sourced construction with its actual realization.
These are not new axioms or assumed Lean certificates. The finite argument is
assessment mathematics, while the lifting unit is a separately checkable theorem.
No theorem here connects general #711 Hall subsets to this canonical polynomial
model. That global bridge, all-moduli density, novelty and exponent gains remain
unpaid. Coordinator review and fresh independent audits are still required before
any source retirement; compiling this documentation does not discharge them.
## Separate full-neighborhood affine-gauge diagnostic (prose only)

This closes only one encoding, not global #711 or the canonical-phase sieve.
Fix n≥1, nonempty D⊆{1,…,n}, m≥0 and an interval I={m+1,…,m+H}, H≥1.
For each d omit empty N_d=I∩dℤ; if a_d is its first point, split the entire N_d
into nonempty tags B_(d,ε)={a_d+(2j+ε)d:j≥0}∩I, ε∈{0,1}.
Let r_ℓ=|B_ℓ|, E=Σ_ℓ r_ℓ>0 and c(x)=|{ℓ:x∈B_ℓ}|.
Start ℓ₀ with probability r_ℓ₀/E, then alternately choose X₀ uniformly in
B_ℓ₀, ℓ₁ uniformly among tags through X₀, X₁ uniformly in B_ℓ₁, ℓ₂ uniformly
through X₁, and X₂ uniformly in B_ℓ₂. Condition on the event G given by
ℓ₀≠ℓ₁, ℓ₁≠ℓ₂, X₀≠X₁, X₁≠X₂, assuming Pr(G)>0; remote repeats are allowed.

Put Y_i=X_i-m, T=2d₀+ε₀ and B=2H+1. The specified encoding is
P=(Y₀+BT,Y₁,0), Q=(Y₁-BT,0,Y₂), R=(0,Y₂,Y₁-Y₂), with
S=P+Q+R=(Y₀+Y₁,Y₁+Y₂,Y₁). Since 1≤Y_i≤H<B, P recovers (T,Y₀,Y₁),
Q recovers (T,Y₁,Y₂), and R recovers (Y₁,Y₂); T recovers the initial tag.
Conversely S recovers Y₁=S₃, Y₀=S₁-S₃, Y₂=S₂-S₃, so (P,Q,R) and
(T,Y₀,Y₁,Y₂) determine each other. With one fixed logarithm base, all following
entropies are conditional on G. Write h=H(S), a=H(T|S), p=H(P), q=H(Q), r=H(R).
Recoverability gives H(P,Q,R)=h+a, H(P|S)=H(Q|S)=a and H(R|S)=0, not separate
identities H(P)=H(Q)=h+a. Thus TC(P,Q,R)=p+q+r-h-a and
I(P;S)+I(Q;S)+I(R;S)=p+q+r-2a. The supplied correlated-plane fiber RHS is

  ½(p+q+r) - TC(P,Q,R) + ½(I(P;S)+I(Q;S)+I(R;S))
  = ½(p+q+r) - (p+q+r-h-a) + ½(p+q+r-2a) = h = H(S).

It cancels for every conditional law on this encoding. Dropping MI gives only
H(S)≥h+a-½(p+q+r)=½(u+v-r), where u=H(S|P), v=H(S|Q) (equation (14) of the
calculation); this is not a new sign restriction. Exact path accounting is
H(W|G)=H(S|G)+H(T|S,G)+b, where W=(ℓ₀,X₀,ℓ₁,X₁,ℓ₂,X₂) and
b=H(ℓ₁,ℓ₂|T,Y₀,Y₁,Y₂,G)≤2 log κ, κ=max_{1≤t≤H}|{d∈D:d|t}|.
This is a support bound, not conditional uniformity. The calculation uses the
correlated-plane inequality, not a selected-common-AP stationary formula;
Chen–Korsky, arXiv:2607.26450, Section 2 (local progression unions) and Section 5
(prime CRT constructions) provide the original external progression-union
context, not a machine check of these elementary entropy identities.

There is also a precise disconnected-label warning. Set g₂=2^(min_{d∈D}v₂(d)).
Every tagged class lies wholly in residue 0 or g₂ modulo 2g₂; the tag is
ε=(x-a_d)/d mod 2, not unconditionally the parity of x/d. The normalized kernel
K(ℓ,ℓ′)=(1/r_ℓ)Σ_{x∈B_ℓ∩B_ℓ′}1/c(x) cannot cross these residues.
If both occur among nonempty labels, there are at least two closed components:
eigenvalue 1 has multiplicity at least two. For this reversible positive
semidefinite incidence up-down operator, Σ_{j≥2}λ_j^(2t)≥1 for every t≥1;
a uniform global o(1) spectral-sum premise therefore fails. Componentwise
mixing has not been shown to pay H(T|S,G). A different observable or new
arithmetic control is needed for this route, not a global #711 refutation.
-/

set_option autoImplicit false
