# Erdős 142 research ledger

This is the long-lived ledger for the automated research campaign begun on
2026-09-26.  It records the current posture, evidence level, live leads, and
closed routes.  It is not a proof of an asymptotic formula.

## Evidence levels

Entries use the following labels.

- **Kernel checked:** a sorry-free Lean artifact compiled in the stated
  revision, with an explicit axiom audit.
- **Accepted prose deduction:** a reviewed mathematical argument in the
  accepted repository, but not a kernel-checked theorem.
- **External theorem:** a claim read from a pinned primary source; it is not
  thereby formalized in Lean.
- **Exploratory or conditional:** a computation, conjecture, model, or
  implication with an unproved premise.

Finite computation is evidence only.  A scalar comparison function is not a
model realized by progression-free sets.  A failed route does not disprove the
square-scale target.

## Problem and fixed conventions

For three-term progressions,

$$
r(N)=\max\{|A|:A\subseteq[1,N]\text{ has no nontrivial 3-AP}\},
\qquad
\lambda(N)=\log\frac{N}{r(N)},
$$

$$
D(N)=\frac{\lambda(N)}{\sqrt{\log N}},
\qquad
X(N)=\lambda(N^2)-2\lambda(N)
    =\log\frac{r(N)^2}{r(N^2)}.
$$

The signs in these definitions are fixed.  The principal repository-specific
route target is an eventual inequality

$$
r(N^2)\le C r(N)^{1+\eta}N^{1-\eta},
\qquad 0<\eta\le\sqrt2-1.
$$

The cleaner asymptotic target is

$$
X(N)=o(\sqrt{\log N}),
$$

which is equivalent in the accepted development to $D(N)\to0$.  Neither is
known.  The canonical Erdős problem asks for an asymptotic formula, so even
this limit would be only progress toward the problem.

## Accepted starting frontier

The campaign started from accepted revision
`d923d18ffb4f0bbd066adcbbbedf39d14cfccd2d`, an adopted descendant of the
handoff revision `71ea6ec436ecff75aa10d431635086a8f7ca3195`.

- **Kernel checked:** the repository proves an explicit finite Roth theorem,
  the torus lower construction and its $\lambda(N)=O(\sqrt{\log N})$
  consequence, scale regularity below the critical dilation, the square-scale
  criterion, and the finite critical-contraction transfer.
- **Accepted prose deduction:** critical-contraction regularity transfers the
  best current square gains to a positive log-log weighted density of scales,
  but not to all sufficiently large scales.
- **External theorem:** Raghavan, arXiv:2603.27045v3, Theorem 1.4, gives
  $\lambda(N)\gg(\log N/\log\log N)^{1/6}$ for all sufficiently large $N$.
- **Accepted obstruction:** the lacunary scalar comparison function satisfies
  the currently used scalar constraints while defeating every fixed positive
  gain.  Additive structure is indispensable.

The canonical problem statement was also checked with the local `erdos`
corpus: problem 142 asks for an asymptotic formula for $r_k(N)$ and remains far
out of reach even for $k=3$.

## 2026-09-27 restart and coalesced handoffs

The current campaign restarted from accepted revision
`2a98a02afeedb182fd48a60c69685d17e217b001`.  Four predecessor handoffs were
coalesced: the primary campaign state, the primary-source/literature audit,
the finite reflection and half-digit lane, and the conditional quantitative
square-defect lane.  They agree that no eventual P inequality, proof of
$D(N)\to0$, positive square-defect excursion theorem, two-sided oscillation,
or asymptotic formula has been obtained.

**Kernel checked and accepted after the older ledger frontier.**  Revision
`ff87c9506a1e1129f0fa1d02dc8ba7d806cab1bf` adds
`Proofs/Erdos/Erdos142/HalfDigitRelationCap.lean`.  If
$H=\lceil N/2\rceil$, $B\subset[0,H)$ and $C\subset[0,N)$ are 3-AP-free,
then the scalar base-$N$ image of every relation $G\subset B\times C$ is
3-AP-free.  In particular,
$$
r(N^2)\ge r(H)r(N)\ge \tfrac12r(N)^2.
$$
The theorem permits arbitrary unequal fibers and graph correlations at this
half-digit scale.  It is a required stress test for any proposed fiber,
entropy, or collision inequality, not an upper asymptotic estimate.

**Kernel checked and accepted at restart.**  Revision
`d1c937ef2a05582745959eb3d8715463efa8a18d` restores the finite-reflection
module and proves the universal estimates
$$
M\ge\left\lfloor\frac{(m-1)^2}{4}\right\rfloor,
\qquad \nu(c)\le m-1,
\qquad E\le(m-1)M.
$$
The exact module and full `Erdos` umbrella build succeeded.  Mathematical,
vacuity, and foundations reviews were clean, and the public endpoints use
only `propext`, `Classical.choice`, and `Quot.sound`.  These estimates close
the sufficient second-moment route only when
$$
N^{2/3}(m-1)(m-N)^2
 \le \left\lfloor\frac{(m-1)^2}{4}\right\rfloor r(N)^{8/3},
$$
roughly $m\lesssim N^2(r(N)/N)^{8/3}$, rather than the desired exponent
$4/3$.  The archived source-audit document and conditional
`SquareScaleQuantitativeRate` candidate
`1de5c75987ad4f72f63682b3439ef1f5556b4cf7` were also reviewed
substantially but not adopted.  Neither supplies the missing structural
estimate; the latter only formalizes a conditional transfer from a
caller-supplied Raghavan-shaped lower envelope.

**Active research ownership.**  Three independent peers now own disjoint
lanes: proof or falsification of the reflection candidates (C)/(O); a new
global unequal-fiber inequality retaining all carries $-1,0,1$; and an exact
primary-source search for a Bohr-to-interval averaging or genuinely two-scale
density-increment theorem.  The coordinating lane is recovering only finite
infrastructure that directly supports those investigations and will not
count conditional bookkeeping or finite computation as a solution.

**Peer-derived carry checkpoint; not kernel checked.**  Put $Q=4N$,
$e_Q(u)=\exp(2\pi i u/Q)$, and
$$
\phi_y(x)=\mathbf 1_A(x+Ny),\qquad
\widehat\phi_y(r)=\sum_{x=0}^{N-1}\phi_y(x)e_Q(-rx),
$$
with $\phi_y=0$ for $y\notin[0,N)$.  For the convention in which the low
and high residuals are respectively $tN$ and $-t$, define
$$
\gamma_t(y,q)=\mathbf 1_{[0,N)}(y-q)
 \mathbf 1_{[0,N)}(y+q-t)
$$
and
$$
F_r=\frac1Q\sum_{t=-1}^1\sum_{y,q}
 e_Q(tNr)\gamma_t(y,q)
 \widehat\phi_{y-q}(r)\widehat\phi_y(-2r)
 \widehat\phi_{y+q-t}(r).
$$
The positive phase here results from replacing the orthogonality variable by
its negative; before that replacement the phase is $e_Q(-tNr)$ and all three
Fourier frequencies have the opposite signs.  With the displayed convention,
the exact scalar 3-AP count is $\sum_{r\bmod Q}F_r$.  Thus the three carries
$t=-1,0,1$, middle frequency $-2r$, and factor $(4N)^{-1}$ are retained
without the aliasing in a naive modulus-$N$ formula.  This is only an
identity, not a nonlinear estimate.

The universal phase-blind proposal, writing $M_0=F_0$ and
$S=\sum_{r\ne0}|F_r|$,
$$
S\le M_0+|A|-\frac{|A|^3}{N^{4/3}r(N)^{8/3}},
$$
is false.  For base $N=3$ and the accepted half-digit cap
$A=\{0,3\}\subset[0,9)$, exact calculation in
$\mathbb Q(\zeta_{12})$ from the displayed formula gives
$$
F_r=\begin{cases}
1/2,&r\equiv0\pmod4,\\
1/6,&r\equiv1\pmod4,\\
-1/6,&r\equiv2\pmod4,\\
1/6,&r\equiv3\pmod4,
\end{cases}
$$
so $M_0=1/2$, $S=5/2$, and $\sum_rF_r=2=|A|$.  Since $r(3)=2$, the
proposed right side is strictly below $5/2$.  This refutes the universal
phase-blind bound, not a version restricted to the high-cardinality regime,
and it does not refute the desired square gain.  Any viable Fourier estimate
must retain phases, coupled unequal fibers, or additional incidence
information.

For a full half-digit product $A=B+NC$, where
$B\subset[0,\lceil N/2\rceil)$ and $C\subset[0,N)$ are scalar caps, define
for $0\le x<N$ and every integer $t$
$$
L_x^+=\#\{(b,b')\in B^2:2b-b'=x\},\qquad
L_x^-=\#\{(b,b')\in B^2:2b-b'=x-N\},
$$
$$
H_t=\#\{(c,c')\in C^2:2c-c'=t\}.
$$
For $0\le h<N$, the peer-derived exact two-carry factorization is
$$
\nu(x+Nh)=L_x^+H_h+L_x^-H_{h+1}
 -\mathbf 1_B(x)\mathbf 1_C(h),
$$
where $\nu$ counts ordered nontrivial global representations.  The half-digit
condition eliminates a positive low-digit carry, and the subtraction removes
exactly the simultaneous diagonal.  This yields exact formulas for $M$, $E$,
and $S$.  For arbitrary relations $G\subseteq B\times C$, however, the
factors become correlated edge-pair counts; controlling that correlation is
the unresolved estimate.  Exhaustive product checks through $N=35$ found no
violation of (O), but this finite computation is evidence only.

A separate active target is the following exact entropy conjecture.  If
$A\subset[0,N^2)$ is scalar-3AP-free with
$|A|\ge N^{2/3}r(N)^{4/3}$ and $(X,Y)$ is its uniform base-$N$ digit pair,
put $d_X=\log N-H(X)$ and $d_Y=\log N-H(Y)$.  The target is an absolute
constant $K$ such that
$$
I(X;Y)\le d_X+d_Y+K.
$$
Each row and column fiber is a scalar cap, so
$H(X\mid Y),H(Y\mid X)\le\log r(N)$ and hence
$d_X+I,d_Y+I\ge\lambda(N)$.  Together with the conjectured inequality these
fiber bounds would give
$$
\log\frac{N^2}{|A|}=d_X+d_Y+I
 \ge \frac43\lambda(N)-\frac K3,
$$
and therefore the desired $\eta=1/3$ square gain up to the constant
$e^{K/3}$.  The conjecture is distinct from the already-refuted
lower-threshold conjecture at $N\sqrt{r(N)}$.  The accepted half-digit
arbitrary-relation construction is only a qualitative stress test: its
full-product cardinality is at most $r(N)^2$, smaller than the new threshold
by the factor $(N/r(N))^{2/3}$.

**New route-specific stopping evidence.**  Let $N\ge3$, let $P>2N$ be
prime, and view the rank-one interval Bohr set
$B=\{0,\ldots,N\}\subset\mathbb Z_P$.  Its only contained nonconstant
unit-step $N$-term interval copies, up to orientation, are
$\{0,\ldots,N-1\}$ and $\{1,\ldots,N\}$.  Every interior point belongs to
both, so every mixture of their normalized counting measures assigns it mass
$1/N$, rather than the uniform Bohr-set mass $1/(N+1)$.  Thus no such mixture
has a uniform one-point marginal.  This refutes averaging over this generic
family from rank, radius, size, and containment alone.  It does not rule out
other affine-copy measures or a source-specific theorem exploiting the
Fourier support produced by a Roth iteration, and it does not settle
Erdős 142.

Within the bounded sources examined in the source audit, no substitute was
identified.  Green's 2025 Oxford notes, Proposition 1.2, retain only a fifth
power of the interval length.  Tao, *Arithmetic Progressions and the Primes*,
Proposition 2.3 and Lemma 2.10, gives an analogous square-root-scale route.
Bloom--Sisask, arXiv:2309.02353, Proposition `prop-it`, supplies one later
high-rank Bohr increment with polylogarithmic rank and measure losses, not a
density-preserving family of length-$N$ affine copies.  Its intermediate
progression extraction (`lem-bohrap`, used toward `th-3A`) places a
progression in a sumset such as $3A$; this is not a claim that the paper fails
to prove its Roth theorem for $A$.  These are applicability barriers for the
proposed two-scale proof, not evidence that no stronger source-specific
argument exists.

## Recovery lane

### Square-scale negative theorem

**Kernel checked.**  The reviewed theorem was adopted in revision
`4a7e259353bfbbefa05531207582c88609bafd5c`.  The integration candidate
compiled both the exact module and `Proofs/Erdos.lean`; the principal endpoints
use exactly the permitted axioms `propext`, `Classical.choice`, and
`Quot.sound`.  A vacuity review required and then certified an explicit
`1 ≤ M` guard on the square-root logarithm helper, excluding the totalized
`Real.log 0` boundary case.

The main claimed endpoint is that for every fixed $M\ge3$ and
$0<\varepsilon<2-\sqrt2$, frequently in $k$,

$$
X(M^{2^k})\le
 -(2-\sqrt2-\varepsilon)\lambda(M^{2^k}).
$$

It consequently makes $r(N^2)/r(N)^2$ unbounded.  This is one-sided negative
excursion information; it does not prove $D(N)\to0$, positive excursions,
two-sided oscillation, or an asymptotic formula.  Independent mathematical
and vacuity reviews certified the theorem and its advertised scope.

### Tower-index negative-defect density and quantitative rate

**Kernel checked.** At revision `6a6bb75bfbaa7301070a3ab5a5c24a3fde9b626b`, `Proofs/Erdos/Erdos142/SquareScaleNegativeDensity.lean`, imported by `Proofs/Erdos.lean`, proves the density results recorded in `Documents/erdos142-negative-defect-density.md`. The public endpoints are `Erdos142.eventually_card_squareScaleDefect_le_neg_mul_rothLogDeficit`, `Erdos142.eventually_card_squareScaleDefect_le_neg_const`, `Erdos142.eventually_card_squareScaleDefect_neg`, and `Erdos142.eventually_card_squareScaleDefect_nonpos`. The first pair give the existing $\delta_\beta=1-\log\sqrt2/\log(2-\beta)$ lower-density curve and its fixed-$H$ consequence. The new endpoint corollaries say that for every fixed tower $N_k=M^{2^k}$ with $M\ge3$ and every real $\delta<1/2$, eventually at least $\delta K$ indices $k<K$ have, respectively, $X(N_k)<0$ and $X(N_k)\le0$. Equivalently, the strict-negative set has tower-index lower density at least $1/2$.

The half-density proof chooses $\beta>0$ in the existing curve with $\delta<\delta_\beta$; it does not apply the source theorem at $\beta=0$. Positivity of $\lambda(N_k)$ at every tower scale makes the source bound imply strict negativity. The focused module and full `Erdos` umbrella builds succeeded; the exact axiom audit is `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`. This uses accepted Roth and EHPS/Behrend inputs, not Raghavan. It is tower-index density, not integer density or exact density, and does not assert the eventual-cardinality bound at $\delta=1/2$ or any endpoint magnitude. No overlap with P-shaped good scales, bounded gaps, $D\to0$, or asymptotic formula follows. The parameter endpoint $\beta=2-\sqrt2$ in the original density curve remains excluded, and no common set as $\beta$ varies is asserted.

Issue [#57](https://github.com/thatnealpatel/proofs/issues/57) tracks independent evaluation of soundness and global novelty. A scoped literature review found the growth-budget lemma standard and no explicit published Roth-number application. The live status remains **repository-level consequence / no global novelty claim**; issue #57 is not external certification of novelty.

**Accepted prose deduction plus external theorem.**  The separately accepted `Documents/erdos142-raghavan-square-defect-rate.md` combines the density theorem with Raghavan, arXiv:2603.27045v3, Theorem 1.4. On the same lower-density set (up to deleting finitely many indices), it yields the explicit growing bound

$$
X(N_k)\le-\beta c_R\left(\frac{\log N_k}{\log\log N_k}\right)^{1/6}.
$$

The density theorem itself is kernel checked and unconditional from accepted inputs; this quantitative magnitude is not Lean formalized and its Raghavan input remains external. This is a repository-level consequence, not an Erdős 142 solution or a global novelty claim.

This complements the existing positive-density P-shaped good-scale result in `Documents/erdos142-positive-density-square-scales.md`: on its positive-density tower-index set the good ratio gives a lower bound $X(N_k)\ge-(2-q)\lambda(N_k)$, whereas the new theorem gives an upper bound $X(N_k)\le-\beta\lambda(N_k)$ on a positive-lower-density set. No overlap, bounded-gap conclusion, or two-sided oscillation follows. Neither result proves eventual P, $D(N)\to0$, or an asymptotic formula.

### EHPS Chebyshev refinement

**Accepted prose deduction.**  The reviewed artifact was adopted in revision
`f6b62ff20a59cf775dae717430b0a217feb5a3f9`.  It ports the final archived
argument with one corrected primary-source locator.  Conditional on the cited
EHPS building-block proposition, it derives

$$
r(N)\ge
 \kappa N e^{-2\sqrt{\log(24/7)\log N}}(\log N)^{-5/4}
$$

and excludes only the specified critical-leading-coefficient comparison
profiles with logarithmic exponent $\beta>5/4$.  Independent mathematical and
provenance reviews found the deduction sound and its status accurate.  It is
not an EHPS theorem as stated, a Lean formalization, or an asymptotic formula.

## Campaign outputs and closed lanes

### Normalized square-tower excursions

**Kernel checked.**  The reviewed theorem was adopted in revision
`d2dd236dc67994865746894441a2e3213d0253aa`.  The integration candidate
compiled both the exact module and `Proofs/Erdos.lean`; the three new theorems
use exactly `propext`, `Classical.choice`, and `Quot.sound`.  For fixed
$M\ge3$ and $c>0$, if frequently
$D(M^{2^k})\ge c$, then frequently

$$
\frac{X(M^{2^k})}{\sqrt{\log(M^{2^k})}}
\le -(2-\sqrt2)c.
$$

The sequence kernel uses
$Z_k=\sqrt2D_{k+1}-2D_k$: if the displayed negative excursion failed
eventually, the excess $D_k-c$ would grow geometrically by a factor exceeding
one, contradicting the accepted eventual upper envelope for $D$.  This does
not prove that the premise holds, and therefore does not prove nonconvergence
or two-sided oscillation.

### High-mass entropy conjecture

**Accepted prose deduction.**  The reviewed counterexample was adopted in
revision `0dc08fc9cf05124ac1e93ddea3e8af41aac615f4` as
`Documents/erdos142-high-mass-entropy-counterexample.md`; it closes the
conjecture as stated.  Let $B\subseteq[0,N-1]$ be a maximum 3-AP-free set,
$|B|=r(N)$, and take a suitably regular $m$-element subset
$A\subseteq B\times B$ with $m=\lceil N\sqrt{r(N)}\rceil$.  Every subset of
$B\times B$ is a vector cap, so this meets the proposed threshold.  A random
$m$-subset has all row and column degrees asymptotic to $m/r(N)$ with positive
probability, giving

$$
H(X)=H(Y)=\log r(N)-o(1),\qquad H(X,Y)=\log m.
$$

Writing $\lambda=\log(N/r(N))$, it follows that

$$
I(X;Y)=\tfrac12\log N-\tfrac32\lambda+o(1),
\qquad d_X+d_Y=2\lambda+o(1).
$$

The accepted lower bound $\lambda=O(\sqrt{\log N})$ makes
$I/(d_X+d_Y+1)$ unbounded.  This defeats the entropy inequality but not the
desired P-shaped cardinality bound, which this family still satisfies.
Independent mathematical review certified the ceiling, concentration,
entropy calculation, asymptotic bookkeeping, and exact non-consequence.

### Carry-cardinality obstruction

**Kernel checked.** At revision
`37a2ec6468a5a33ee7e3dd966ecc816d0971f46c`,
`Proofs/Erdos/Erdos142/CarryCardinalityCapObstruction.lean`, imported by
`Proofs/Erdos.lean`, proves the finite endpoint
`Erdos142.exists_carryCardinalityCap`. Focused and full `Erdos` builds
succeeded (8813 jobs); independent vacuity and foundations reviews were clean.
The public endpoints use exactly `[propext, Classical.choice, Quot.sound]`,
with no `sorryAx`.

For each $N\ge3$, it constructs a bounded $G\subseteq[0,N)^2$ with every
ordinary natural-number row and column fiber 3-AP-free; all in-range fibers
have common size $b$, $2b\le N$, and
$N\,r(N)\le2|G|$. It also contains $(0,0),(1,1),(2,2)$, so its base-$N$
scalar image contains the nontrivial progression $0,N+1,2(N+1)$. The scalar
encoding is injective on the bounded square, but the witness is deliberately
not scalar-3-AP-free.

The finite construction half-slices a maximum ordinary 3-AP-free subset of
$[0,N)$, translates and (if needed) shrinks the dense piece into a short
interval, embeds it as a modular cap $B\subseteq\mathbb Z/N\mathbb Z$, and
translates $B$ to contain zero. The graph $x-y\in B$ has fibers that are
translates/reflections of $B$, and has $N|B|$ edges. Thus this relaxation,
using only ordinary row/column freeness and the pair-size cap, cannot imply a
universal $o(Nr(N))$ cardinality upper bound, and alone cannot prove the
P-shaped saving. This closes a proof method, not Erdős 142; it is not an
asymptotic theorem about $r(N)$.

See [`erdos142-carry-cardinality-obstruction.md`](erdos142-carry-cardinality-obstruction.md)
for the proof sketch and the closed computational lead. Evidence labels and
scope are preserved there as well. Issue [#58](https://github.com/thatnealpatel/proofs/issues/58)
requests external evaluation of this obstruction; it is not a novelty
certification.

### Unequal-fiber carry Fourier lane

**Accepted prose deduction plus exploratory computation.** The new note
[`erdos142-unequal-fiber-fourier.md`](erdos142-unequal-fiber-fourier.md)
records the exact $Q=4N$ low-digit carry identity for the scalar encoding
$n=x+Ny$.  Orthogonality gives the ordered scalar count $T=\sum_r C_r$
with all three carry modes, the hard boundary indicators, and no alias;
$C_{Q-r}=\overline{C_r}$.  For a scalar cap, $T=m$,
$M_0=C_0\ge m^3/(4N^3)$, and $R=m-M_0$, $S\ge|R|$.

The phase-blind high-mass candidate
$S\le M_0+m-m^3/K^2$ is open only for $N\ge3$ and
$m\ge K$, where $K=N^{2/3}r_3(N)^{4/3}$, and would imply
$r_3(N^2)\le\sqrt2N^{2/3}r_3(N)^{4/3}$, i.e. $\eta=1/3$.
The unrestricted-in-$N$ wording has a degenerate finite obstruction at
$N=1$: for $A=\{0\}$, $r_3(1)=K=m=1$, $C_r=1/4$ for all $r\bmod4$,
$M_0=1/4$, $R=S=3/4$, while the candidate's right-hand side is $1/4$.
This does not refute the eventual/asymptotic route.  At $N=2$,
$r_3(2)=2$, $K=4$, and $r_3(4)=3$, so no cap reaches the high-mass domain.
The nondegenerate $N=3$ half-digit/product/constant-graph example falsifies
only the candidate with the high-mass condition removed: it is low mass.
Arbitrary relations in the half-digit family satisfy $m\le K$; they do not
refute the high-mass claim.
The accepted prose spread/cancellation lemma gives large row and column
projections, many heavy fibers, and $R/M_0=-1+o(1)$ from the accepted
Behrend/EHPS lower input, but no phase-sensitive upper bound on $S$.
Exact Sage/GLPK finite checks are exploratory computation only; $N=7 timed
out.  A proof must account for the exact deficit $m^3/K^2$ from baseline
$M_0+m$; in high mass this is at least $m$, with equality at $m=K$, and it
need not put $S$ below $M_0$.  A disproof needs an actual high-mass scalar cap.
No novelty claim or issue was filed.

### High-cardinality relaxation obstruction for the unequal-fiber target

**Exact finite computational certificate/evidence, not a general proof or Lean theorem.**
The new script
`Programs/Erdos142/verify_unequal_fiber_relaxation.sage` verifies the relation
at $N=16$, $Q=64$, with $r_3(16)=8$ and
$K=16^{2/3}8^{4/3}\approx101.5937$.  It uses
$B=\{0,1,6,8,13,14\}$ and the six exceptional ordered pairs
$(9,0),(10,1),(1,12),(2,13),(3,14),(4,15)$.  The resulting $G$ has
$m=102$, both full projections, and every row and column is an ordinary
3-AP-free set of size at most $8$.  The exact comparison
$102^3=1,061,208>1,048,576=16^2\cdot8^4$ verifies $m>K$.

The note gives a rigorous finite justification of $r_3(16)=8$: the
16 possible three-element complements that hit all consecutive progressions
in $[0,8)$ each miss a listed longer progression, so $r_3(8)=4$; parity
rescaling gives the upper bound $8$ in $[0,16)$, and
$\{0,1,3,4,9,10,12,13\}$ gives equality.  The relation is not a scalar cap,
since $0,9,18\in A$, while the exact grouped calculation gives $T=1564$
rather than $m$, $M_0=48183/32$, and the exact real-algebraic calculation
places $S$ in
$1508.87835005088420127094169298<S<1508.87835005088420127094169300$
and the candidate right-hand side in
$1504.90120266375311107163647228<M_0+m-m^3/K^2<
1504.90120266375311107163647229$, a positive gap of approximately
$3.97714738713109019930522069850$.

This is a high-mass **relaxation** obstruction, not a scalar-cap
counterexample.  It rules out deriving (*) from projection spread,
heavy-fiber counts, degree bounds, Jensen's $M_0$ lower bound, or even
ordinary 3-AP-freeness of every row and column.  The next condition must be
mixed-fiber/carry exclusion entering distributionally: on scalar caps this
is the exact condition $T=m$, but that signed identity alone is only
$R=m-M_0$ and returns the prior tautology, not a new estimate.  The scalar-cap
high-mass candidate remains open.

### Reflection-shadow route

**Kernel checked.** At accepted revision `66eca70dc75c548dcf27862d0f8c8bcc5e436f67`, `Proofs/Erdos/Erdos142/ReflectionShadow.lean`, imported by `Proofs/Erdos.lean`, defines the integer `reflectionShadow` and `differenceSources`. It proves that a finite ordinary 3AP-free `A⊂ℤ` is disjoint from its nontrivial reflection shadow, and that `2·|{x∈A:x+d∈A}|≤|A|` for every nonzero `d`. Focused and full builds succeeded (8814 jobs); the public endpoints use only `[propext, Classical.choice, Quot.sound]`. Independent mathematical review was clean. A vacuity audit found no semantic/trust issue; additional scratch cardinality probes did not complete and are not integrated.

**Kernel checked: ReflectionMultiplicityCap.** At adopted revision
`03698c3b0724a6591300cfab6bec371558e880f2`,
`Proofs/Erdos/Erdos142/ReflectionMultiplicityCap.lean` proves that, for
`A⊂[0,L)` scalar 3-AP-free, every in-range ordered reflection-target
multiplicity `ν(c)` equals the cardinality of an admissible center set. The
center set is 3-AP-free inside an interval of length `ceil(L/2)`, so
`ν(c)≤r_3(ceil(L/2))`. At `L=N²`, this gives
`ν(c)≤ceil(N/2) r_3(N)`, and pointwise-to-energy summation gives
`E≤r_3(ceil(L/2)) M`. Focused and full builds and an independent axiom audit
passed with only `propext`, `Classical.choice`, and `Quot.sound`; static
semantic review was **CLEAN**, with nonvacuous endpoint examples. This
pointwise cap alone does not prove (O), (C), or Erdős 142.

**Informal finite mathematics, independently audited but not Lean formalized.** For scalar-free `A⊂[0,N²)` with `m=|A|`, the target-wise union of valid carry cases is exactly the in-range nontrivial reflection shadow `S(A)`, so `|S(A)|≤N²−m`; median reflection gives `|S(A)|≥floor((m−1)/2)`. With in-range representation multiplicities `ν(c)=#{(a,b)∈A²:a≠b:2a−b=c}`, `M=Σν`, `E=Σν²`, and `r_A(d)=|{x∈A:x+d∈A}|`, the informal collision count gives `E≤M+Σ_{d≠0}r_A(d)r_A(2d)≤Σ_d r_A(d)r_A(2d)`. The formal fixed-difference theorem is exactly `r_A(d)≤floor(m/2)` for `d≠0`, but using it naively is far too weak. The formal module does **not** contain the carry-union identity, median bound, mass/energy identities, or candidate below.

**Exploratory/conjectural.** The candidate `|S(A)|³ r(N)^8 ≥ N²(m−N)^6` for `m>N` is unproved and would imply `r(N²)≤N+N^(2/3)r(N)^(4/3)≤2N^(2/3)r(N)^(4/3)` eventually, a P-shaped gain with `η=1/3`; this would be an intermediate estimate, not an asymptotic formula. It is checked informally for `N=3`, eventual fixed-linear `m≤KN` regimes, and short ternary Cartesian products; exhaustive `N≤6` and structured searches are computation only. A sufficient second-moment overlap bound `E≤M²r(N)^(8/3)/(N^(2/3)(m−N)²)` remains unproved and undisproved. The fixed-difference matching argument does not bound fixed-target multiplicity: `{1,2,4,8}⊂[9]` has `ν(0)=3`. A capped-at-2 moment variant is also unproved and at most within factor `9/8` of the desired support bound, not an independent breakthrough. See [`erdos142-reflection-shadow-route.md`](erdos142-reflection-shadow-route.md) for definitions, exact status, and derivations.

**Independently reviewed informal counterfamily.** An auxiliary
shadow-support lower bound comparable to `min{b²,L}` is false. For `d=q≥4`,
let `Q=4q`, take a largest sphere `X_d⊂{0,…,q−1}^d`, and base-`Q` encode it
as `B_d⊂[0,L_d)`, where

$$
L_d=1+(q-1)\frac{Q^d-1}{Q-1},
\qquad b_d=|B_d|\ge\frac{q^d}{d(q-1)^2+1}.
$$

Put `M_d=3L_d−1` and

$$
P_d=\{2x-y:x,y\in B_d,\ x\ne y,\ 0\le2x-y<M_d\},
\qquad I_d=P_d\cap(M_d-1-P_d).
$$

Then `B_d` is scalar 3-AP-free and

$$
b_d-1\le2|P_d|-|I_d|\le2(3q-2)^d.
$$

Writing `U_d=2|P_d|-|I_d|` and taking `q=d` gives

$$
\frac{U_d}{b_d^2}\le2d^6(3/d)^d,
\qquad
\frac{U_d}{L_d}\le\frac{8d}{d-1}(3/4)^d,
$$

and both ratios tend to zero. Thus no uniform lower bound comparable to
`min{b_d²,L_d}` can prove (C). The ordered multiplicity energy nevertheless
has the lower bound

$$
\sum_c\nu(c)^2\ge\frac{\binom{b_d}{2}^2}{(3q-2)^d}.
$$

This does not refute (C), (O), or Erdős 142: the construction uses a separate
cutoff `M_d` and omits the `r(N)` factor.

**Settled q=d two-cluster stress test for (C).** After taking `q=d` in the
preceding construction, the same `B_d` gives a settled two-cluster stress
test, not a counterexample. Let

$$
A=B_d\cup(T-1-B_d),
\qquad T=3L_d-1,
\qquad N=\lceil\sqrt T\rceil,
\qquad b=|B_d|,
\qquad m=2b.
$$

For all large `d`, `m>N`. Using `|S(A)|≥b-1≥b/2`, `b≤d^d`, and

$$
N^6\ge T^3\ge27(d-1)^3(4d)^{3d-3},
$$

the candidate ratio is

$$
R=\frac{|S(A)|^3r(N)^8}{N^2(m-N)^6}
\ge\frac{27}{512}\left(\frac{d-1}{d}\right)^3
64^{d-1}\left(\frac{r(N)}{N}\right)^8
=\exp\bigl(d\log64-O(\sqrt{d\log d})\bigr)\longrightarrow\infty.
$$

Here only the lower bound
$r(N)/N\ge\exp(-C\sqrt{\log N})$ for the true `r(N)` is used. The constant
is `1/512`, not `1/64`: `|S(A)|³` contributes `1/8`
and `m^6` contributes `64`. Thus this explicit family eventually satisfies
(C) by a growing margin; it does not prove (C) for arbitrary sets.

**Conditional significance only:** if an eventual P bound with `η=1/3` and fixed constant held, its iteration would give `λ(M^{2^k})≳_M(4/3)^k` on a sufficiently large fixed square tower, equivalently a tower lower bound of logarithmic exponent `log₂(4/3)≈0.415`. This is not an all-scale interpolation or a solution of Erdős 142. The carry-sensitive route complements, but does not remove, the relaxation obstruction in [`erdos142-carry-cardinality-obstruction.md`](erdos142-carry-cardinality-obstruction.md); the comparison with the square-defect threshold is recorded in [`erdos142-negative-defect-density.md`](erdos142-negative-defect-density.md). No global novelty claim is made. Issue [#59](https://github.com/thatnealpatel/proofs/issues/59)
requests external evaluation of the reflection-shadow route and cubic
candidate; it is not a novelty certification.

### Incidence-biclique obstruction

**Independently audited finite/prose route closure; not Lean formalized.** For
scalar 3AP-free $A\subseteq[0,L)$, put
$I_A=\{(c,d):0\le c<L,\ d\ne0,\ c+d,c+2d\in A\}$. Its row degree is
exactly the reflection multiplicity
$\nu_A(c)=\#\{(a,b)\in A^2:a\ne b,2a-b=c\}$, via
$(a,b)=(c+d,c+2d)$. Its column degree is exactly
$\#\{a\in A:a+d\in A,0\le a-d<L\}\le r_A(d)\le\lfloor m/2\rfloor$;
the last bound is the disjointness of $X_d$ and $X_d+d$. For every nonempty
biclique $C\times D\subseteq I_A$, both $C$ and $D$ are scalar 3AP-free and
$((C-C)\setminus\{0\})\cap D=\varnothing$. The proofs and the precise
scope are recorded in
[`Programs/Erdos142/incidence-biclique-obstruction.md`](../Programs/Erdos142/incidence-biclique-obstruction.md).

The exact digit construction uses $b=128$,
$E_1=\{0,1,5,7,11,12,16,18,26,38,39,42,44,48,53,55,59,61\}$,
$E_P=\{17,18,21,23\}$, and
$E_2=E_P\cup2E_P=\{17,18,21,23,34,36,42,46\}$. Finite midpoint checks
(computation evidence only) certify that $E_1,E_2$ are 3AP-free,
$E_1,E_2\subset[0,64)$, $E_P\subset[1,32)$, and
$E_P\cap2E_P=\varnothing$. The even-$E_1$/odd-$E_2$ digit cap $T_k$ has
$|T_k|=144^k$ and lies in $[0,128^{2k})$ by the no-carry proof. The even
$E_1$ digit set $C_k$ and odd $E_P$ digit set $P_k$ have sizes $18^k$ and
$4^k$, and $C_k+P_k,C_k+2P_k\subseteq T_k$. Thus at
$N=128^k$, $L=N^2$, and $m=144^k>N$, the incidence graph contains
$K_{18^k,4^k}$.

Consequently no fixed $K_{s_0,t_0}$-free property and no absolute-constant
bound on $|C||D|$ can follow from cap structure, even when $m>N$.
This does not refute bounds depending on $m,L$, candidate (C), candidate (O),
or Erdős 142. The tempting union
$(C_k+P_k)\cup(C_k+2P_k)$ has size $2\cdot72^k$ when disjoint, not
$144^k$; for $k>1$ it is not the dense scalable family. Unsupported
asymptotics for digit-set sizes are discarded.

### Exact $b=128$ reflection transfer

**Accepted prose deduction plus exact finite computation.** The adopted artifact
[`reflection-transfer-b128.md`](../Programs/Erdos142/reflection-transfer-b128.md)
received an independent exact review. It studies the alternating digit cap with
$b=128$, $N=128^k$, and $m=144^k$. The exact borrow-transfer matrices have
Perron roots $20736$ for mass and $81580$ for energy; their formulas give
$$
M\ge \frac45\,144^{2k},
\qquad
E\le81580^k.
$$
The true Roth bound from the $E_1$ digit product is
$r_3(128^k)\ge18^k$, so these estimates verify candidate (O), with constant
$1$, for every $k\ge1$. This rules out this specific dense tensor family as a
counterexample to (O), but neither proves (O) for general scalar caps nor
Erdős 142. The exact matrices and computations are audit evidence, not a
general theorem.

**Conjectural missing lemma, with a proved special case and conditional
consequence.**  The statement `RAI(K)` asks for one fixed integer $K\ge1$: whenever
$\beta=r(N)/N$, a proper AP has length at least $16N/\beta$, and a
3-AP-free subset has relative density $0<\delta\le(9/8)\beta$, there is a
proper sub-AP retaining at least $\delta^K/2$ of the length and increasing
the density by a factor $9/8$.  This theorem is not proved.

If the accepted Behrend lower bound is written
$\log(1/\beta)\le B\sqrt{\log N}$, then `RAI(K)` implies the eventual bound

$$
r(N^2)\le2N^{1-\eta}r(N)^{1+\eta},
\qquad
\eta=\min\left\{\sqrt2-1,
 \frac{\log(9/8)}{4KB^2}\right\}>0.
$$

The complete iteration is recorded in
[`erdos142-relative-rank-one-checkpoint.md`](erdos142-relative-rank-one-checkpoint.md).
There are at most
$\lfloor\eta\log(1/\beta)/\log(9/8)\rfloor+2$ increments.  The cumulative
length remains at least $N^{2-\sqrt2/4-o(1)}$, hence at least
$16N/\beta$.  At the terminal density $>(9/8)\beta$, partitioning the
proper AP parameter interval into $N$-blocks gives the contradictory upper
bound $(17/16)\beta$.

The exact rank-one Fourier special case is proved in the checkpoint.  If the
balanced indicator on the AP parameter interval has a rational Fourier
coefficient of magnitude at least $\delta/4$ and coprime period
$d\le\delta^{-K}$, splitting into residue classes modulo $d$ gives a class
with density at least $9\delta/8$ and length at least
$\delta^K L/2$.  This is the complete `RAI(K)` conclusion with its exact
constants.

**The corresponding universal spectral input is false.**  The checkpoint
constructs a deterministic computable diagonal family of scalar 3-AP-free
$A_j\subseteq[0,p_j)$, where $p_j\asymp N_j^2$, whose densities satisfy
$0<\delta_j\le\beta_j^2\le(9/8)\beta_j$ and
$p_j\ge16N_j/\beta_j$, but every reduced rational coefficient with
$d\le\delta_j^{-j}$ has magnitude less than $\delta_j/j$.  The proof starts
with a modular Behrend set, takes a fixed-size subset, and uses the exact
second moment under the 2-transitive affine group plus a union bound.  For
each fixed $K$, eventually all $d\le\delta_j^{-K}$ coefficients are
$o(\delta_j)$.  This refutes the precise spectral claim, not `RAI(K)`:
rank-one density increments can arise by mechanisms not detected by one such
coefficient.

The unconditioned random-affine route cannot by itself be an RAI
counterexample.  Every set in that construction remains inside the proper
cyclic progression $u[0,\lfloor p/3\rfloor)+v$, of length about $p/3$, where
its density is exactly $(p/\lfloor p/3\rfloor)\delta\ge3\delta$.  For every
fixed $K$ this carrier is eventually longer than $\delta^Kp/2$.  In standard
integer representatives the cyclic carrier may wrap into many ordinary
pieces, so this is directly a cyclic structural obstruction.  The
carrier-dependent direction argument below is what permits selection of one
multiplier that is flat on all relevant ordinary APs.

A further fourth-moment shortcut fails in its uniform form.  If
$H=\lfloor p/7\rfloor$, $C\subseteq[0,H)$ is a Behrend cap of density
$\delta=|C|/p$, $R=[0,2H)$, and
$X_{u,v}=|(uC+v)\cap R|$, then the at least $p/7$ affine pairs with $u=1$
and $0\le v\le H$ give
$$
\mathbb E_{u\ne0,v}|X_{u,v}-\delta|R||^4
 \ge\frac{625}{7^5}\delta^4p^3.
$$
This exceeds a proposed $O((\delta|R|)^2)$ bound by an unbounded factor at
Behrend density.  The same failure occurs at the exact critical length.
With $H=\lfloor p/8\rfloor$, place a Behrend cap $C$ of density $\delta$ in
the middle of $[0,H)$ and put $\ell=\lceil\delta^Kp/2\rceil$.  Sliding
$\ell$-windows shows that at least $(55/64)\delta p$ translations have
density at least $9\delta/8$ on the fixed interval $[0,\ell)$.  Consequently
$$
\mathbb E_{u\ne0,v}
 \bigl|| (uC+v)\cap[0,\ell)|-\delta\ell\bigr|^4
 \ge\frac{55}{2^{18}}\frac{\delta^5\ell^4}{p},
$$
which exceeds $(\delta\ell)^2$ by at least
$(55/2^{20})\delta^{2K+3}p\to\infty$.  This closes the unconditioned
fourth-moment strategy: the rare aligned images actually have the required
increment.  The residual argument below instead selects a multiplier outside
all empirically base-dense directions and then applies fixed-size thinning.

### Ordinary-direction refinement of the critical-scale obstruction

A proved direction count narrows this open tail problem.  For a prime $p$,
fixed $K$, and

$$
\ell=\left\lceil\frac{\delta^Kp}{2}\right\rceil,
\qquad
D=\left\lfloor\frac{p-1}{\ell-1}\right\rfloor,
$$

any ordinary AP $\{a+jd:0\le j<L\}\subseteq[0,p)$ of length
$L\ge\ell$, oriented with $d\ge1$, satisfies

$$
1\le d\le\left\lfloor\frac{p-1}{L-1}\right\rfloor\le D.
$$

Indeed $(L-1)d\le p-1$; a longer target may be reduced to a consecutive
critical block of $\ell$ terms for direction bookkeeping.  When
$\delta^Kp/2\ge2$, $\ell-1\ge\delta^Kp/4$, so
$D\le4\delta^{-K}$.  The endpoint $\ell=1$ is excluded: the denominator
$\ell-1$ vanishes and a one-point target has no direction information.  At
Behrend scale and sufficiently large $p$, $\ell\ge2$ (in fact
$\delta^Kp\to\infty$).

For an interval carrier $[0,H)$ with $H\asymp p$ and $1\le H\le p-1$, set
$R=\lfloor H/\ell\rfloor$ and

$$
U_{\mathrm{al}}=\{u\in\mathbb F_p^\times:
 \exists\,1\le d\le D\text{ with }0<|du^{-1}|_p\le R\}.
$$

For each fixed $d$, $u\mapsto du^{-1}$ bijects $\mathbb F_p^\times$, and
there are exactly $2R$ nonzero residues with least absolute residue at most
$R$ (because $\ell\ge2$ gives $R\le(p-1)/2$).  Pair counting therefore
proves

$$
|U_{\mathrm{al}}|\le2D\left\lfloor\frac H\ell\right\rfloor
 =O(\delta^{-2K}),
\qquad
\frac{|U_{\mathrm{al}}|}{p-1}
 =O\left(\frac{\delta^{-2K}}p\right)=o(1)
$$

for fixed $K$ at Behrend scale.  This is a direction-level quarantine, not
an RAI counterexample: if a carrier-aligned image has density at least
$9\delta/8$ on an ordinary critical block, that block is itself the RAI
increment, has length $\ell\ge\delta^Kp/2$, and is proper in the asymptotic
regime.  A wrapped cyclic carrier is
not automatically an ordinary AP, so it proves neither the ordinary theorem
nor its negation.  After the coarse carrier quarantine, define the actual residual bad set from
the cap $C_0$ of density $\rho$.  For each length $t$ in a fixed
multiplicative net of $[r,2r]$, where
$r=\lceil\delta^Kp/2\rceil$, let $W_t$ consist of directions $w$ for which
some modular $t$-window contains at least $(33/32)\rho t$ points of $C_0$.
The exact affine variance is

$$
\mathbb E_{w\ne0,x}
 (|C_0\cap(x+w[0,t))|-\rho t)^2
 =t\rho(1-\rho)\frac{p-t}{p-1}.
$$

One dense witness remains above $(1+1/64)\rho t$ through
$\gg\rho t$ consecutive shifts, since a shift changes the count by at most
one.  Summing their squared deviations proves

$$
|W_t|\ll\frac{p^2}{\rho^2t^2},
\qquad
|W|\ll\rho^{-2}\delta^{-2K}.
$$

The length net, with thresholds $33/32<35/32<9/8$, implies that every
window of every length in $[r,2r]$ and every direction outside $W$ has base
density less than $(35/32)\rho$.

All relevant positive ordinary differences satisfy $d\le D\ll\delta^{-K}$.
The multiplier set

$$
\mathcal U=\{dw^{-1}:1\le d\le D,\ w\in W\}
$$

has size $O(\rho^{-2}\delta^{-3K})$.  When this is $o(p)$, choose
$u\notin\mathcal U$.  Retain a uniform fixed-size $m=\delta p$ subset
$C\subseteq C_0$.  For each target AP $P$ of length $s\in[r,2r]$,
$|uC\cap P|$ is hypergeometric with mean below $(35/32)\delta s$; hence

$$
\Pr(|uC\cap P|\ge(9/8)\delta s)\le e^{-c\delta s}.
$$

There are $O(p^2)$ such ordinary APs.  Therefore a simultaneous-flat subset
exists provided

$$
p\delta^{K+1}\gg\log p,
\qquad
\rho^{-2}\delta^{-3K}=o(p).
$$

Longer APs are partitioned into consecutive blocks with lengths in
$[r,2r]$.  Thus the resulting standard representative of $uC$ has density
less than $9\delta/8$ on every ordinary AP of length at least $r$.
In terms of $\theta=\delta/\rho$, the two conditions are

$$
p(\theta\rho)^{K+1}\gg\log p,
\qquad
\theta^{-3K}\rho^{-(3K+2)}=o(p).
$$

For $\rho=p^{-b+o(1)}$ and $\delta=p^{-a+o(1)}$, the sufficient exponent
regime is $a(K+1)<1$, $2b+3Ka<1$, and $a\ge b$.  In particular it holds at
Behrend scale, where both densities are $p^{-o(1)}$.

This refutes ordinary `RAI(K)` for every fixed $K$.  Given large $N$, take a
prime $p\in[N^2,2N^2]$, an interval-supported modular Behrend cap $C_0$, and

$$
\delta=p^{-1}\left\lfloor\frac p2
             \min\{\rho,(r_3(N)/N)^2\}\right\rfloor.
$$

Both $\rho$ and $\delta$ are $p^{-o(1)}$.  The affine-flat thinning theorem
produces an ordinary 3-AP-free $A\subseteq[0,p)$ with no required increment,
while $\delta\le\beta^2/2\le9\beta/8$ and
$p\ge16N/\beta$ eventually.  This disproves the auxiliary rank-one
hypothesis, not Erdős 142.  It also does not contradict the aligned
sliding-window calculation: those rare images do have the asserted density
increment, while the selected multiplier avoids every residual base-dense
direction relevant to an ordinary target.

The earlier stress tests remain informative but are no longer needed to
decide RAI.  The carry-free digit product has only short obvious coordinate
increments; the half-digit relation is not scalar-free; Green's rank-one
increment is too short; and the audited Bohr/GAP outputs do not imply the
fixed-factor, fixed-power statement.  These remain precise barriers to
those proposed proof routes.

## Dead ends and guardrails

- Exhaustive and sampled tests suggested a target-wise union-reflection
  coverage inequality implying
  $r(N^2)\le N+\sqrt N\,r(N)^{3/2}$. This is a dead exploratory lead, not a
  live conjecture or accepted computation theorem. The accepted Behrend lower
  bound absorbs $N$ eventually, yielding a P-shaped estimate with
  $\eta=1/2>\sqrt2-1$. That eventual estimate would imply
  $X(N)\ge-\tfrac12\lambda(N)-O(1)$, contradicted on fixed square towers by
  the accepted negative square-defect theorem (choose
  $\varepsilon<2-\sqrt2-\tfrac12$). Finite tests therefore cannot support
  this inequality asymptotically. A viable positional/collision route must
  retain reflected-digit locations and target $\eta\le\sqrt2-1$.
- The universal mutual-information bound without a high-mass hypothesis is
  false for graph caps.
- Pairwise fiber sizes or energies cannot force a local mixed midpoint count;
  translated-fiber examples kill that inference.
- The one-scale edge/window LP has a uniform feasible point of order
  $Nr(N)$, so its dual cannot produce the required power saving.
- **Kernel checked:** row/column ordinary freeness and the pair-size cap
  alone permit cardinality at least $Nr(N)/2$; see the carry-cardinality
  obstruction above. They cannot force a universal $o(Nr(N))$ bound.
- Rank, radius, and measure of a generic Bohr set do not guarantee an
  interval-scale affine copy; one copy would not provide density averaging
  anyway.
- The carry modes in base $N$ are all of $-1,0,1$.  Any scalar fiber theorem
  must either retain all three or explicitly pass to a valid stronger vector
  relaxation.
- $r(N)$ is monotone, but arbitrary monotonicity of $\lambda(N)$ is not
  available.  The accepted reverse comparison loses $\log2$.

## Next decisions

1. Treat fixed-power rank-one amplification as refuted: the affine-flat
   thinning counterfamily disproves `RAI(K)` for every fixed $K$.  Any
   replacement sufficient hypothesis must exclude these selected affine
   images without assuming the false universal bounded-denominator Fourier
   coefficient statement.  The conditional implication from `RAI(K)` to the
   square-scale estimate remains logically correct but cannot be used as an
   available theorem.
2. Sharpen the negative-defect distribution: the strict-negative set now has
   lower tower-index density at least $1/2$ (every fixed $\delta<1/2$ is
   eventually attained). Investigate exact density or endpoint magnitude,
   overlap with the positive-density P-shaped good scales, and gap control.
   The original $\beta$-curve endpoint remains excluded; no cardinal bound at
   $\delta=1/2$, no bounded gaps, and no common set across $\beta$ is known.
3. Develop carry-sensitive global aggregation retaining reflected-digit
   locations. The reflection-shadow candidate and its open second-moment overlap
   estimate are recorded in
   [`erdos142-reflection-shadow-route.md`](erdos142-reflection-shadow-route.md).
   The new unequal-fiber Fourier identity, open phase-blind high-mass
   candidate, low-mass falsifier limitation, half-digit exclusion, and
   spread/cancellation stopping evidence are recorded in
   [`erdos142-unequal-fiber-fourier.md`](erdos142-unequal-fiber-fourier.md).
   The new $N=16$ relaxation obstruction rules out deriving the target from
   projection and one-dimensional fiber restrictions alone.  The precise
   next condition is mixed-fiber/carry exclusion entering distributionally:
   $T=m$ on scalar caps is necessary context, but the signed equality alone
   is the prior tautology and is not a new estimate.
   Keep unequal-fiber aggregation and Cartesian sub-products as stress tests.
   Any P-shaped exponent target must satisfy $\eta\le\sqrt2-1$.
4. Keep the entropy route closed unless a replacement inequality either
   excludes sub-products or applies only within an $\exp(O(\lambda))$ factor
   of the row-cap maximum.

## Current handoff

See [`erdos142-research-handoff-2026-09-27.md`](erdos142-research-handoff-2026-09-27.md)
for the self-contained frontier at accepted revision
`596825af4c347bbb311da8a340bec333c45b2f9a`. Any new potential novelty claim
must receive its own repository issue or an explicit scoped update to the
matching existing issue before it is advertised; filed requests are external
evaluation, not novelty certification.
