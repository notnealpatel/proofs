/-!
# Erdős 142 research kernels (prose archive, not proofs)

Let r(N)=r₃(N), the maximum size of an ordinary nonconstant-3AP-free subset
of [0,N). Translation identifies the papers' [1,N] with Lean
`rothNumberNat N`. For N≥3 put λ(N)=ln(N/r(N))>0 and
X(N)=λ(N²)−2λ(N), the sign used by `squareScaleDefect`.
P is the still-open all-scale assertion: some C>0, η∈(0,√2−1],N₀ satisfy
r(N²)≤C r(N)^(1+η)N^(1−η) for EVERY integer N≥N₀.
All asymptotic limits below are on positive/nonempty tails; ln is natural,
log₂ is explicitly marked. Vector caps exclude nonconstant coordinatewise
3-APs and are not automatically scalar caps under x+Ny.

Ownership: Weighted telescope owns `erdos142-loglog-dense-square-scales`
and is shared by Critical gain (`erdos142-critical-gain-density`). EHPS
refinement owns `erdos142-ehps-chebyshev-refinement`; Lacunary owns
`erdos142-lacunary-scalar-obstruction`; Fourier owns
`erdos142-unequal-fiber-fourier`; the shared b128 digit definition serves
Incidence (`incidence-biclique-obstruction`) and Reflection
(`reflection-transfer-b128`); TE owns `transverse-energy-TE`.
Every argument here is unformalized prose unless a CURRENT Lean boundary
is explicitly named. Internal derivations claim no external novelty.
The independent high-mass entropy obstruction is owned by
`Sorry.Combinatorics.CanonicalBaseCarryTransfer`, not reproduced here.
None of these internal obstructions is a counterexample to global P.

## Weighted telescope and ambient integer good scales

External quantitative input: Rushil Raghavan, *Improved Bounds for
3-Progressions*, arXiv:2603.27045v3 (15 May 2026), Theorem 1.4, a preprint,
gives eventually λ(N)≥c(ln N)^(1/6)/(ln ln N)^(1/6), c>0. Thus
 ln λ(N)≥(ln ln N)/6−(ln ln ln N)/6+O(1).
The loglog loss is REQUIRED: this is not a pure c(ln N)^(1/6) input;
the theorem, not its stale abstract, is the provenance. Qualitative Roth
λ→∞ and the accepted square/product bounds are additional inputs;
Behrend/EHPS gives the upper λ(N)=O(√ln N), not an asymptotic formula.

For n≥3 set w_n=ln ln(n+1)−ln ln n>0,
C_n=log₂(λ(n²)/λ(n)). The retained identity is
 S(M)=Σ_{3≤n≤M}w_n C_n=ln λ(M+1)+o(ln ln M).
To derive it let h=ln2,n(x)=⌊exp(exp x)⌋,a(x)=λ(n(x)),b(x)=a(x)+2h,
L(x)=ln b(x). With n=n(x),m=n(x+h), eventually n²≤m<2n²;
monotonicity and two-interval restriction give r(n²)≤r(m)≤2r(n²),
hence |λ(m)−λ(n²)|≤h. The accepted square inequality
r(n)²≤2r(n²) gives a(x+h)≤2a(x)+2h, so b(x+h)≤2b(x).
Also r(n²)≤nr(n) gives λ(n²)≥λ(n), thus 0≤C_n≤1+o(1).
Since λ→∞ the additive shifts/rounding give, tail-uniformly,
 C_(n(x))−[L(x+h)−L(x)]/h=o(1).
L(x)≥x/6−(ln x)/6+O(1). If T=ln ln(M+1),R₀=ln ln3,
n(x)=n on [ln ln n,ln ln(n+1)), so integrating the comparison yields
 S(M)=(1/h)∫_T^(T+h)L(y)dy+o(T),
with the fixed initial window absorbed. For N=M+1 and N≤m≤N²,
interval restriction r(m)≤⌈m/N⌉r(N), r(N²)≤⌈N²/m⌉r(m)
and ⌈t⌉≤2t for t≥1 give
 λ(N)−h≤λ(m)≤λ(N²)+h≤2λ(N)+2h.
Consequently L(y)=ln λ(N)+O(1) uniformly on the endpoint window.
Its length h CANCELS the factor 1/h, proving the exact natural-log identity.
Neither a factor 1/ln2 nor monotonicity of λ on arbitrary arguments is used.

It follows that liminf S(M)/(ln ln M)≥1/6 and limsup≤1/2.
For fixed 1<q<2^(1/6), let α=log₂q and G_q={n≥3:C_n≥α}.
Splitting the mean at G_q with tail bound 1+o(1) gives
 liminf [Σ_{3≤n≤M,n∈G_q}w_n]/(ln ln M)
 ≥δ(q)=(1/6−log₂q)/(1−log₂q)>0.
Exactly on these scales r(n²)≤r(n)^q n^(2−q), hence
X(n)≥−(2−q)λ(n), i.e. P with C=1 and η=q−1 on a weighted-density
set only. At q=1 all square scales are good (density 1, not just 1/6);
at q=2^(1/6) the bound becomes zero. The model λ≈a√ln N has eventual
goodness below √2, but the accepted envelope does not assert this model.
λ=ln ln N (r=N/ln N) is inconsistent with the Raghavan lower bound.

CURRENT boundary: `SquareScaleNegativeDensity.lean` concerns cardinal density
in index k of a fixed tower M^(2^k), not these integer w-weighted scales.
No ambient weighted integral/telescope or external Raghavan theorem is
formalized by it. Reopen with abstract positive-sequence weighted-prefix
lemmas, rounding and endpoint estimates; a discrepancy of order ln ln M
between S(M) and lnλ(M+1) would falsify this kernel. The proof needs only
accumulated o(ln ln M) errors, not an unsupported bounded-error claim.

## Critical gain transfer and all-real local windows

Put m_n=r(n)²→∞ (arbitrarily large finite caps follow from powers of two).
Choose n₀ with λ(n),λ(n²),λ(m_n)>0 for n≥n₀, and define
K_n=log₂(λ(m_n)/λ(n)). Accepted prose contraction input:
 |λ(m_n)−λ(n²)|=O(√λ(n)).
Write d_n for this difference. Since λ(n²)≥λ(n)→∞,
|d_n|/λ(n²)≤B/√λ(n)→0; then λ(m_n)>0 on a tail and
 K_n−C_n=log₂(1+d_n/λ(n²))=o(1)
uniformly, using |log₂(1+t)|=O(|t|) for |t|≤1/2. K_n can be slightly
NEGATIVE; positivity of the logarithm's argument is not K_n≥0.

To transfer weighted sums, for ε>0 fix J such that |K_n−C_n|≤ε for n≥J.
The finite prefix is constant and the tail difference is≤
εΣ_{J≤n≤M}w_n=ε(ln ln(M+1)+O_J(1)). Take M→∞ FIRST and ε→0 second.
Thus Σ_{n₀≤n≤M}w_n K_n=ln λ(M+1)+o(ln ln M).
For fixed q in the same interval, E_q={K_n≥log₂q} has lower weighted
density≥δ(q): K_n≤1+ε_J on a fixed tail gives the literally valid split
 mean≤α(1−p_M)+(1+ε_J)p_M+O_J(1)/W_M,
W_M=ln ln M+O(1), then M→∞ followed by J→∞. No lower bound on K is
needed. Limit q↓1 tends to 1/6 but q=1 is NOT asserted good at every
critical scale. Endpoint q=2^(1/6) is excluded.

For fixed ρ>3 and sufficiently large REAL T, define u(T) the least n≥3
with ln ln n≥T, v(T) the greatest n≥3 with ln ln n≤ρT. These exist with
u≤v, positive W_T=Σ_(u≤n≤v)w_n=(ρ−1)T+o(T). The local recurrence
for C is an accepted PROSE premise, not a Lean theorem:
 liminf_(all real T→∞) Σ_(u≤n≤v)w_n C_n/W_T≥A,
 A=(ρ/6−1/2)/(ρ−1)>0.
Uniform K−C=o(1) transfers that mean. For fixed 0<c<A, the same upper-tail
split yields lower local relative weight of {K_n≥c} at least
(A−c)/(1−c)>0. Every sufficiently large real-T window contains such an
index; it is not merely a subsequence of integer windows, nor all indices.

Finite comparison λ(n²)≥λ(m_n)−ln2 on a scale K_n≥c gives, q=2^c,
 r(n²)≤2r(n)^q n^(2−q),
 X(n)≥−(2−q)λ(n)−ln2.
This exact log2 loss is retained, and η=q−1 is admissible on the above
good scales. It is far weaker than near-zero X≥−o(√ln n) and proves no
eventual P. Models λ=C√ln N or the exact Raghavan-shaped expression give
C_n,K_n→1/2 or 1/6 respectively under the transfer error, not facts about r.
`CriticalContractionTransfer.lean` checks directed FINITE inequalities
λ(a)−λ(x)≤ln2 for 1≤a≤x, and
λ(x)−λ(a)≤λ(b)+2ln2 for 1≤a,1≤b,x≤2ab. It does not check the
O(√λ), weighted or all-real-window bridges. Reopen with these exact
abstract analytic premises and weighted transfer; do not absorb the local
recurrence or external lower envelope into a load-bearing assumption-free
claim. Failure at the stated orders falsifies one of those premises.

## EHPS Chebyshev/pigeonhole lower-prefactor refinement

External input: Elsholtz–Hunter–Proske–Sauermann, *Improving Behrend's
construction*, arXiv:2406.12290v1, Propositions 2.1 (torus slice), 2.2 (block), and
§3 direct-embedding remark. For even n≥4, measurable T⊆[0,1)² has
μ(T)≥7/24−1/n, and measurable f:T→[0,100n²] satisfies
 f(u)+f(w)−2f(v)≥‖u−w‖₂²
for u,v,w∈T with u+w≡2v modulo 1, coordinatewise. These geometric
hypotheses are needed, not just this range. In m=n/2 independent T-blocks let F=sum f. Conditional variance
≤m(100n²)²/4 by the bounded-range variance inequality. Chebyshev gives
≥3/4 of T^m in a central interval of length 200n²√m. Partition it into
bins of width δ²/2, δ∈(0,1); at most 402n²√m δ^(−2) bins meet it.
Since μ(T^m)≥.01(7/24)^m, a measurable bin S has
 μ(S)≥10^(−5)δ² n^(−5/2)(7/24)^m.
For x,y,z∈S with x+z≡2y modulo 1, summing the block inequality gives
Σ_i(x_i−z_i)²≤F(x)+F(z)−2F(y)<δ²: the three F-values lie in one
half-open bin of width δ²/2. Thus all endpoint coordinate differences are
STRICTLY <δ. This replaces the
source's whole-range n^(−3) pigeonholing by n^(−5/2), not its theorem
hypotheses or leading exponential constant.

Direct embedding is credited by EHPS §2 to Green–Wolf, *A Note on
Elkin’s Improvement of Behrend’s Construction* (2010). Let c=ln(24/7), L=ln N≥4c,
n=2⌈√(L/c)⌉ even and δ=N^(−1/n)/4. A random torus direction b avoids
all nonzero integer differences d with |d|≤N−1 from [−δ,δ]^n modulo 1:
union probability≤N(2δ)^n=2^(−n)<1. For a fixed avoiding b, average a
random translate a gives ≥Nμ(S) integer orbit points a+jb in S. Any
nonconstant integer 3-AP in these indices is a modular midpoint triple;
the strict closeness conclusion contradicts the avoidance for its nonzero endpoint
difference j−ℓ, not necessarily its AP step j−k. Thus these indices form an ordinary cap. Parameter substitution gives
 r(N)≥κ N exp(−2√(c ln N))(ln N)^(−5/4),
 κ=10^(−5)(7/24)c^(5/4)/(16·3^(5/2))>0.
Indeed n≤3√(L/c), nc/2+2L/n≤2√(cL)+c and δ² contributes 1/16.
This is an internal refinement DERIVED from Prop 2.2, not the published
EHPS prefactor or a formal theorem. It excludes proposed upper asymptotics
with the same leading exponential and factor (ln N)^(−β) for β>5/4,
by the divergent ratio (ln N)^(β−5/4); it does not solve #142.
`TorusBuildingBlock.lean` verifies finite modified geometric/polynomial
inequalities (enlarged facet and different coefficients), not conditional
measure/variance. `TorusAsymptoticLowerBound.lean` verifies only the accepted
arbitrary-positive-slack eventual leading-exponent lower bound. Reopen
with the precise source measurable block, conditional probability/binning
and random-direction/translate construction; none follows from compiling
these existing finite modules.

## Lacunary synthetic scalar obstruction

This is a model of accepted scalar inequalities, NOT the actual Roth number.
Fix a=1/6, 1<p<5 and T₀>max(1,2^(1/(p−1))); recursively T_(k+1)=T_k^p.
For s≥0 let ℓ_T(s)=(1−a)T^a+aT^(a−1)s,
f(s)=inf_k ℓ_(T_k)(s), F(s)=f(s)−f(0).
Adjacent tangents meet at
 S_k=5T_k r_k^5/(1+r_k+r_k²+r_k³+r_k⁴),
 r_k=(T_(k+1)/T_k)^(1/6)>1.
Thus T_k r_k≤S_k≤5T_k r_k and S_(k+1)/S_k>2 with the chosen T₀.
Decreasing slopes/increasing intercepts and ordered intersections ensure
NO skipped tangents: f=ℓ_(T_k) on [S_(k−1),S_k], with initial line for
s≤S₀. This yields increasing concave F with F(0)=0, slopes<1, hence
subadditive F(s+t)≤F(s)+F(t), and
 s^(1/6)−f(0)≤F(s)≤C√s.
The lower bound is concavity's tangent inequality. For the upper bound on
one active interval, ℓ_T(s)/√s= (5/6)T^(1/6)/√s+(1/6)T^(−5/6)√s
has maximum at an endpoint. At S_k use S_k≤5T_k^((p+5)/6) to bound its
slope term by O(T_k^((p−5)/12)); at S_(k−1)≥T_(k−1)^((p+5)/6)
the intercept term is≤(5/6)T_(k−1)^((p−5)/12). The other terms are
bounded because S_(k−1)≤T_k≤S_k. Here p<5 is essential.
At S=S_k, both S and 2S precede S_(k+1); the next tangent's slope
contributes only a vanishing fraction, so F(2S)/F(S)→1.

Set R(N)=N exp(−F(ln N)) for real N≥1. Then R is increasing (slope F<1),
1≤R(N)≤N, R(N)/N→0 and lnR(N)/ln N→1. Concavity/subadditivity give
 R(N)²≤R(N²)≤N R(N),
 R(N)R(M)≤R(NM)≤R(N(2M−1)) for N,M≥1.
For integer N_k=⌊exp S_k⌋, |lnN_k−S_k|≤2exp(−S_k) eventually; F is
Lipschitz (constant≤1), so F(2lnN_k)/F(lnN_k)→1 still.
For EVERY fixed C,η>0 the logarithm of
R(N_k²)/(C R(N_k)^(1+η)N_k^(1−η)) is
(1+η)F(lnN_k)−F(2lnN_k)−ln C→∞. Hence all such P bounds fail for R,
despite the scalar envelopes, monotonicity, product and square inequalities.
This pinpoints missing square-scale REGULARITY, not a counterexample to P
for r. `StretchedExponentialObstruction.lean` and
`NormalizedDeficitEnvelope.lean` use the actual upper envelope to rule out
larger exponents/limit constants; they do not define this model. Reopen
with structural information forbidding lacunary changes of active tangent;
scalar envelope/product inequalities alone cannot prove eventual P.

## Carry-sensitive unequal-fiber Fourier identity

For N≥1 let A⊆[0,N²) be a SCALAR cap, m=|A|, r=r(N),
B_y={x∈[0,N):x+Ny∈A}, d_y=|B_y|, with zero extension outside y∈[0,N).
Define φ_y=1_(B_y), Q=4N, e_Q(t)=exp(2πit/Q) and
φ̂_y(r)=Σ_x φ_y(x)e_Q(−rx). Frequency r in this section is a residue;
when r(N) is needed use the explicit function to avoid confusion.
Let γ_t(y,q)=1_[0,N)(y−q)1_[0,N)(y+q−t), t∈{−1,0,1}.
The exact progression count is T=Σ_(frequency r)C_r with
 C_r=Q^(−1)Σ_(t=−1,0,1)e_Q(tNr)Σ_(y,q)γ_t(y,q)
       φ̂_(y−q)(r) φ̂_y(−2r) φ̂_(y+q−t)(r).
Here y runs [0,N), q over all integers (finite by γ). The low residual
L=x₀+x₂−2x₁ and high residual H=y₀+y₂−2y₁ satisfy L+NH=0;
write L=tN and y₀=y−q,y₂=y+q−t. Since
|L−tN|≤3N−2<Q, Fourier orthogonality detects L=tN WITHOUT aliasing.
Only t=−1,0,1 can occur. The positive e_Q(tNr) phase matches the stated
negative transform convention. Scalar AP-freeness gives T=m (diagonals).
Rows/columns are ordinary caps, but neither fiber caps nor vector AP-freeness
alone gives this mixed identity.

Zero mode M₀=C₀≥Q^(−1)Σ_y d_y³≥m³/(4N³).
Put K=N^(2/3)r(N)^(4/3), R=Σ_(r≠0)C_r=m−M₀,
S=Σ_(r≠0)|C_r|. Let μ(t) count the weighted low residuals with ALL γ
conditions: C_r=μ̂(r)/Q and μ(0)=m. Then ν=μ−mδ₀≥0.
More precisely F_r=C_r−m/Q=ν̂(r)/Q, D=F₀=M₀−m/Q≥0.
Nonzero integer defects may alias each other modulo Q, but never into zero;
ν is defined after grouping them. Positivity gives |F_r|≤D, |C_r|≤M₀ and
PSD of the circulant (F_(j−k)): its quadratic form is
Q^(−1)Σ_(u≠0)ν(u)|Σ_k z_k e_Q(ku)|²≥0.
Parseval gives Σ_r|F_r|²=Q^(−1)Σ_(u≠0)ν(u)², while Σ_rF_r=0, hence
Σ_(r≠0)F_r=−D and Σ_(r≠0)|F_r|²≥D²/(Q−1).
These are LOWER collision/variation controls, not the needed upper bound.
The same-row diagonal blocks
 λ_row=Σ_(y,x∈B_y)(Σ_(a,c∈B_y)δ_(a+c−2x)−δ₀)
are nonnegative, λ_row≤ν, have mass T₃−m, T₃=Σd_y³, and their nonzero
integer support embeds injectively modulo Q. η_row=ν−λ_row≥0 has mass
QM₀−T₃. If P_r=Σ_y φ̂_y(r)²φ̂_y(−2r), then
 C_r=(P_r+η̂_row(r))/Q,
 S≤(Q−1)(QM₀−T₃)/Q+Q^(−1)Σ_(r≠0)|P_r|.
This defect decomposition retains distributional mixed-fiber information;
merely R=m−M₀ is tautological.

For a row B of size d and additive energy E₊(B)=#{a+b=c+d′ in B⁴},
Parseval gives Σ_r|φ̂(r)|⁴=Q E₊(B), since pair sums do not wrap.
The map r↦−2r is two-to-one onto even frequencies, but
Σ_(s even)|φ̂(s)|²=Qd/2: write s=2k and orthogonality modulo 2N,
where |a−b|<N<2N excludes aliases. Thus
Σ_r|φ̂(−2r)|²=Qd, NOT 2Qd. Cauchy gives
Σ_r|φ̂(r)|²|φ̂(−2r)|≤Q√(d E₊(B)). Consequently
 U_E=(Q−1)(QM₀−T₃)/Q+Σ_y√(d_y E₊(B_y)),
 U₂=(Q−1)(QM₀−T₃)/Q+A₂, A₂=Σ_y d_y²,
are valid upper bounds on S, using E₊(B)≤d³.
For a cap, each positive-difference graph is a matching: two adjacent
edges would form a 3-AP. Its multiplicity r_B(h)≤⌊d/2⌋ and
Σ_(h>0)r_B(h)=d(d−1)/2. The energy identity gives
 E₊(B)=d²+2Σ_(h>0)r_B(h)²≤d²+⌊d/2⌋d(d−1).
Set g(d)=d√(d+⌊d/2⌋(d−1)) and
 U_cap=(Q−1)(QM₀−T₃)/Q+Σ_y g(d_y).
Then S≤U_cap. In high mass m≥K, r(N)≤N gives m³/K²≥m,
T₃≤r(N)A₂≤NA₂. Exact subtraction from Θ below yields
 U₂−Θ=(Q−2)(M₀−T₃/Q)+(A₂−T₃/Q)+(m³/K²−m)
 ≥3A₂/4>0,
 U_cap−Θ=(Q−2)(M₀−T₃/Q)+(Σ_y g(d_y)−T₃/Q)+(m³/K²−m)
 ≥(1/√2−1/4)A₂>0,
since g(d)≥d²/√2 for d≥1 and d_y³/Q≤d_y²/4.
These LOOSE upper bounds do not prove Θ; their positive gaps are NOT
actual scalar-cap counterexamples. Cross-row phases and the coupling of
P_r to η_row have not yet been used before taking absolute values.

The open candidate, for N≥3 and m≥K, is
 S≤Θ:=M₀+m−m³/K².
Since S≥|m−M₀|≥M₀−m WITHOUT needing M₀≥m, the candidate implies
m³/K²≤2m, hence m≤√2 K, the η=1/3 P-shaped bound (constant √2).
A signed variant Σ_(r≠0)C_r=m−M₀ gives no information. At N=1,A={0},
all C_r=1/4, M₀=1/4,S=3/4 exceed Θ=1/4; N≥3 excludes this endpoint.
At N=3,A={0,3}, C_r=(1+2cos(πr/2))/6, M₀=1/2,S=5/2=M₀+m,
but m=2<K. Neither refutes the high-mass candidate. A half-digit relation
has m≤r(⌈N/2⌉)²≤r(N)²<K for N≥3. At m≥K projections each have
size≥m/r(N)>r(N); rows/columns of size≥m/(2N) carry >m/2 of the mass
and number >m/(2r(N)). Also m/M₀≤4N³/m²≤4N^(5/3)/r(N)^(8/3)=o(1)
by Behrend; hence R/M₀=−1+o(1), S≥(1−o(1))M₀. This high-mass
cancellation necessity is not an upper bound on S. The
retained `Programs/Erdos142/verify_unequal_fiber_relaxation.sage` supplies
N=16, m=102, r(16)=8 with cap rows/columns and full projections, yet scalar
A contains {0,9,18}; it has M₀=48183/32 and T=1564≠m. Thus it refutes
a FIBER-ONLY relaxation, not the scalar-cap statement. Reopen only by
exploiting the true mixed-fiber ν distribution/T=m, not row energies or
signed equality alone. No current Lean theorem covers this Fourier kernel.

## Shared b=128 digit specification

Set b=128,
E₁={0,1,5,7,11,12,16,18,26,38,39,42,44,48,53,55,59,61},
E_P={17,18,21,23}, E₂=E_P∪2E_P={17,18,21,23,34,36,42,46}.
For k≥1 define A_k=Σ_(j=0,…,2k−1)a_j b^j, with EVEN positions E₁,
ODD positions E₂ (least significant E₁). The finite no-nonconstant-midpoint
checks on E₁,E₂ are computational provenance, not Lean proofs. All doubled
digits are≤122 or≤92<b, so midpoint carries are absent. Thus A_k is an
ordinary scalar cap in [0,N²), N=b^k, m=144^k>N; E₁-only k digits give
r(N)≥18^k. This definition is the sole shared owner; reflection/incidence
below use the same family, not two unrelated models.

## Incidence/biclique obstruction

For C_k using E₁ at even positions and zeros at odd, and P_k using E_P at
odd and zeros at even, |C_k|=18^k, |P_k|=4^k. There are NO mixed-position
carries and C_k+P_k,C_k+2P_k⊆A_k. Therefore incidence
𝓘={(c,p):c+p∈A_k,c+2p∈A_k} contains the COMPLETE biclique C_k×P_k.
Both sides grow, so no fixed K_(s,t)-free premise or absolute bound
|C||P|≤constant can follow merely from these cap conditions. Equally,
reflection targets c=2(c+p)−(c+2p) have at least |P_k| incidences.
But the union (C_k+P_k)∪(C_k+2P_k) has ONLY 2·72^k elements, not
144^k; it need not be all A_k. No size-dependent incidence bound or P-shaped
upper bound is refuted. Current `HalfDigitRelationCap.lean` proves every
relation in a half-digit product maps to a scalar cap, but does not construct
this biclique. `ReflectionPopularTargets.lean` gives an AP-sensitive
three-target positional inequality and rich-target AP-freeness, not an
absolute product cap. Reopen with a quantitative size-dependent incidence
statement that survives these growing complete subgraphs.

## Reflection borrow transfer: exact family audit for candidate O

For general scalar cap A⊆[0,N²), m>N, let ν_A(c)=#{(x,y)∈A²:2x−y=c}
for c∈[0,N²)\A, M=Σ_cν_A(c), E=Σ_cν_A(c)². The OPEN estimate O is
 E≤M²r(N)^(8/3)/[N^(2/3)(m−N)²].
Here m>N is the denominator guard. For the shared A_k it holds with
constant 1 for EVERY k≥1, by the following exact internal finite counts.
For F⊆[0,b), states β,γ∈{0,−1} obey
 2x−y+β=z+bγ, 0≤z<b.
Define (P_F)_(β,γ) as the number of (x,y)∈F² obeying that equation;
state order (0,−1). Q_F counts two such pairs with common z and states
ordered (0,0),(0,−1),(−1,0),(−1,−1). Initial state is zero, final state
zero enforces output in range. Digit-block order is P₁P₂,Q₁Q₂, not reversed.

P₁=[[223,101],[222,102]], P₂=[[58,6],[54,10]],
P=[[18388,2348],[18384,2352]],
χ_P(t)=t²−20740t+82944, eigenvalues 20736,4.
Q₁=[[551,104,104,235],[423,124,123,172],
    [423,123,124,172],[550,104,104,236]],
Q₂=[[88,0,0,6],[37,0,0,0],[37,0,0,0],[72,0,0,22]],
Q=[[73104,0,0,8476],[58747,0,0,6322],
   [58747,0,0,6322],[73088,0,0,8492]],
χ_Q(t)=t⁴−81596t³+1305280t², eigenvalues 81580,16,0,0.
All entries are exact enumeration of the displayed digit equations. The
matrices/specification survive as independently auditable computation input;
no retained Sage script or current Lean module checks this b128 computation.

Starting/final-zero formulas and diagonalization give
 M̃=(P^k)_(0,0)=(4596·20736^k+587·4^k)/5183,
 Ẽ=(Q^k)_((0,0),(0,0))=(18272·81580^k+2119·16^k)/20391.
Since A_k is a scalar cap, every reflection landing inside A_k has x=y=c.
Thus M=M̃−144^k,E=Ẽ−144^k (not just mass subtraction).
As 20736=144²,
 M−(4/5)144^(2k)=(2248/25915)20736^k−144^k+(587/5183)4^k≥0,
because 2248·144=323712>25915. Also E≤Ẽ≤81580^k.
Using m−N≤m and r(N)≥18^k, the RHS of O is at least
 (16/25)[144²18^(8/3)/128^(2/3)]^k.
The exact comparisons are
 81580³128²=8,895,513,891,831,808,000
 <98,255,075,431,437,047,955,456=144⁶18⁸,
 16³(144⁶18⁸)−25³(81580³128²)
 =402,313,796,562,606,276,425,547,776>0.
The second handles the prefactor at k=1, and the first propagates it for all
k≥1. These show E≤RHS of O on THIS FAMILY ONLY; bicliques do not invalidate
O here. `ReflectionCarryEnergy.lean` is instead an exact finite localization
by the sum of THREE nonnegative low digits with carries 0,1,2, plus a
1/(3N) lower slice bound. It is not this two-state borrow upper-energy
calculation. `ReflectionEnergyCriterion.lean` derives a general sufficient
criterion/cardinality range, not O for arbitrary caps. Reopen by kernel
checking these finite matrices or by a new general energy estimate; do not
promote all-k family diagonalization to arbitrary A or to P.

## Transverse energy TE: open target and normalization

For vector cap S⊆[0,N)², N≥3, m=|S|, α=r(N)/N, put
r_S(u)=#{(a,b)∈S²:a−b=u},
E(S)=Σ_u r_S(u)² and E_⊥(S)=Σ_(u₁≠0,u₂≠0)r_S(u)².
Equivalently E_⊥ counts (a,b,c,d)∈S⁴ with a+b=c+d, a₁≠c₁ and
a₂≠c₂: use u=a−c=d−b and the two ordered pairs (a,c),(d,b).
The candidate is ABSOLUTE constants η>0,C>0,N₀ such that for all N≥N₀
and ALL such vector caps,
 E_⊥(S)≤C α^(1+η)m³+C r(N)m².                         (TE)
η is independent of N and S. The SECOND term is indispensable.
Difference support has at most (2N−1)²<4N² elements; Cauchy gives
E(S)≥m⁴/(4N²). Every row/column is a cap and has≤r(N) points;
the horizontal/vertical energy bound is≤2r(N)m² (double-counting the
origin is harmless). Thus TE implies
 m⁴/(4N²)≤C α^(1+η)m³+(C+2)r(N)m².
The empty cap has zero energy and satisfies TE trivially. For m>0 the
positive quadratic root is
2CN²α^(1+η)+2N√(C²α^(2+2η)N²+(C+2)r(N)), giving
 m≤(4C+o(1))N²α^(1+η),
using the Behrend lower bound α=N^(−o(1)) so
r(N)/(N²α^(2+2η))=N^(−1)α^(−1−2η)→0.
Equivalently the harmless root error is o(N²α^(1+η)); TE would provide
a P-shaped upper bound for r(N²) via its digit vector image. It remains
unproved and is not replaced by the lower energy identity.

First-term-only TE is FALSE: choose maximum cap A⊆[0,N),
S=A×{0,1}, m=2r. Then
 E_⊥(S)=2(E(A)−r²), E(A)≥r⁴/(2N),
so E_⊥≥r²(αr−2); normalized by m³ this is Ω(α), not
O(α^(1+η)). This product is a vector cap. The full TE's r m² term
correctly covers it, so this is not a counterexample to TE or P.

Fixed-alphabet no-go: fix base b≥3 and nonempty half-digit caps
D,E⊆{0,…,⌊(b−1)/2⌋}, sizes t,u; if t=1 or u=1 then E_⊥=0.
Otherwise t,u≥2; for d≥1 let A=D^d,B=E^d mean base-b
product digit sets in [0,b^d), and S=A×B, N=b^d. Signed digit differences
have magnitude≤(b−1)/2. Their expansions are unique: subtract two
representations, whose digit differences have absolute values<b, reduce
modulo b to force the lowest digit zero, divide by b and iterate (also for
negative digits). Therefore
 E(A)=E(D)^d,E(B)=E(E)^d,
 E_⊥(S)=(E(D)^d−t^(2d))(E(E)^d−u^(2d)).
For finite integer D of size t≥2, E(D)<t³: equality would force every
triple's fourth element back in D, contradicting a maximum/minimum triple.
Let q_D=E(D)/t³<1,q_E=E(E)/u³<1. Then
 E_⊥(S)/m³≤(q_Dq_E)^d,
and (q_Dq_E)^d/α(b^d)^(1+η)→0 for every fixed η>0 by Behrend
α(b^d)=b^(−o(d)). Thus these FIXED alphabets cannot refute the first TE
term asymptotically, a fortiori not TE. Base/alphabet depending on d,
nonproduct caps and finite-size evidence are not covered. In particular the
proposed per-digit test 2α(D)≤1, with
α(D)=ln(t³/E(D))/ln(b/t), uses the false actual-density substitution
α(b^d)=(t/b)^d. For D={0,1}, b=4, this digit exponent is
ln(4/3)/ln2≈.415<1/2, but the fixed-alphabet no-go still applies.
Fidelity note: the retired source prints |S|³=t^(6d)u^(6d) at one point;
its own |S|=t^d u^d and following normalization require t^(3d)u^(3d),
used here. This is an explicitly flagged algebraic typo, not a new theorem.
Likewise α=N^(−o(1)) requires BEHREND's lower bound; Roth alone only gives
α→0. Later source paragraphs had the correct combined attribution.

For maximum A⊆[0,N), S=A×A gives EXACT
 E_⊥(S)=(E(A)−r²)²,m=r².
The exact TE product stress inequality is
(E(A)−r²)²≤Cα^(1+η)r⁶+Cr⁵. It is equivalent to eventual uniform control
 E(A)−r²≪r³α^((1+η)/2)
over ALL maximum caps (the r⁵ TE remainder is asymptotically absorbed by
Behrend). This is not an equivalence for arbitrary vector subsets of A×A.
For example a two-point diagonal vector cap has transverse energy 2,
not the value 4 from the unsupported product formula; Cartesian structure
is necessary. The uniform maximum-cap energy bridge remains open.

External inverse theorem: Pohoata–Roche-Newton, *Higher energies and sumsets*,
arXiv:1905.08457, Theorem 6.1 (attributed there to Sanders), says that
E(A)≥δ|A|³ for A⊆ℤ implies at least exp(−Cδ^(−c))|A|² three-term APs.
Encode the grid by (x,y)↦x+My with M>2N: the bounded coordinate-sum
residuals have magnitude<M, so scalar 2-sum equalities force equality in
both coordinates. This is a Freiman 2-isomorphism, preserving energy/APs,
not merely an injection. A vector cap has only m trivial APs, so the theorem
gives E_⊥≤E≪m³/(ln m)^(1/c) (on a growing m tail). This logarithmic
saving is insufficient to guarantee the α^(1+η) factor: in the Behrend-shaped
regime that factor is exp(−Θ(√ln N)), smaller than every inverse log power.
No assertion of that regime as an actual r asymptotic is made.
Current reflection/half-digit modules prove neither TE, the product stress
bridge nor this quantitative inverse step. Reopen with precisely an α-power
transverse-energy gain beyond r m², or a growing-structure countermodel
satisfying every vector-cap constraint. Generic inverse-theorem or
random-model wishlists are not retained.

## Archival verification boundary

Only compilation of comment syntax is claimed by this file. No executable
definitions, declarations or axioms encode these kernels. The accepted
lower envelope, finite contraction, digit image and carry identities retain
their exact narrower scope. Quantifiers over all scales, fixed alphabets,
external preprints and internal computational certificates must remain
separate in any future formalization. In particular the finite Sage Fourier
relaxation, the b128 all-k audit and scalar lacunary model resolve none of P,
general O, high-mass Fourier S≤Θ or full TE.
-/

set_option autoImplicit false
