# Exact relative rank-one increment checkpoint

## Status

This note isolates one exact missing theorem for the analytic route to a
fixed-power square estimate.  The theorem below is **conjectural**.  The
argument after it proves that theorem would imply the desired estimate with
an explicit fixed exponent.  It does not prove the theorem or Erdos problem
142.

Write

$$
r(N)=r_3(N),\qquad \beta=\frac{r(N)}N,
\qquad s=\log\frac1\beta.
$$

The accepted Behrend--Elkin--Green--Wolf lower bound supplies fixed constants
$B>0$ and $N_B$ such that

$$
s\le B\sqrt{\log N}\tag{1}
$$

for $N\ge N_B$.  No unproved regularity of $r(N)$ is used below.

## One exact missing theorem

**Relative affine increment $\operatorname{RAI}(K)$ (conjectural).**  There
are a fixed integer $K\ge1$ and a threshold $N_0$ such that the following
holds for every $N\ge N_0$.  Let $P$ be a proper integer arithmetic
progression of length $L$ satisfying

$$
L\ge \frac{16N}{\beta}.
$$

If $A\subseteq P$ is 3-AP-free and has relative density

$$
0<\delta=\frac{|A|}{|P|}\le\frac98\beta,
$$

then there is a proper subprogression $P'\subseteq P$ such that

$$
|P'|\ge \frac12\delta^K|P|,
\qquad
\frac{|A\cap P'|}{|P'|}\ge\frac98\delta.\tag{RAI}
$$

Equivalently, the conclusion may be stated as a probability measure on such
subprogressions for which the expected relative density is at least
$9\delta/8$: a point mass at $P'$ gives the formulation above.  This
probability wording adds no many-copy or marginal claim.  The displayed
single-witness version is deliberately the minimal statement used by the
iteration.

Every quantifier matters.  In particular, the progression is proper, its
length loss is a fixed power of the current density, its density gain is a
fixed factor, and the assertion is relative to the target scale $N$ through
both $\beta=r(N)/N$ and the terminal length $16N/\beta$.

## Conditional fixed-power consequence

Put

$$
q=\frac98,\qquad h=\log q,
\qquad
\eta=\min\left\{\sqrt2-1,\frac{h}{4KB^2}\right\}.\tag{2}
$$

Then $0<\eta\le\sqrt2-1$.  Assuming $\operatorname{RAI}(K)$, for all
sufficiently large $N$,

$$
r(N^2)\le 2N^2\beta^{1+\eta}
=2N^{1-\eta}r(N)^{1+\eta}.\tag{3}
$$

Thus the missing theorem gives the requested P-shaped estimate with the
fixed constants $C=2$ and $\eta$ in (2).

### Starting set and rounding

Suppose instead that a maximum 3-AP-free
$E\subseteq\{0,\ldots,N^2-1\}$ has

$$
|E|>2N^2\beta^{1+\eta}.
$$

Set $x=\beta^{1+\eta}$ and thin $E$ to a subset $A_0$ of size
$m=\lceil xN^2\rceil$.  This is possible eventually because

$$
xN^2=\exp\bigl(2\log N-(1+\eta)s\bigr)\longrightarrow\infty,
$$

so $m\le2xN^2<|E|$.  With
$P_0=\{0,\ldots,N^2-1\}$, $L_0=N^2$, and
$\delta_0=m/N^2$, one has

$$
\beta^{1+\eta}\le\delta_0
\le\beta^{1+\eta}+N^{-2}\le q\beta\tag{4}
$$

eventually.  Here $\beta^\eta\to0$ by Roth's theorem, while (1) gives
$1/(N^2\beta)\to0$.

### Number of increments

Apply (RAI) while the current density is at most $q\beta$, and stop as soon
as it exceeds $q\beta$.  If $P_i,A_i,L_i,\delta_i$ denote the successive
objects, then

$$
L_{i+1}\ge\frac12\delta_i^K L_i,
\qquad
\delta_{i+1}\ge q\delta_i.
$$

As long as the process continues,

$$
\delta_i\ge q^i\delta_0\ge q^i\beta^{1+\eta}.
$$

It must therefore stop after at most

$$
T=\left\lfloor\frac{\eta s}{h}\right\rfloor+2\tag{5}
$$

applications.  This remains true if an increment overshoots its guaranteed
factor.

### Complete length budget

After any $j\le T$ already-valid applications,

$$
\begin{aligned}
L_j
&\ge N^2 2^{-j}\prod_{i<j}\delta_i^K\\
&\ge N^2 2^{-j}\delta_0^{Kj}q^{Kj(j-1)/2}\\
&\ge N^2 2^{-j}\delta_0^{Kj}.
\end{aligned}\tag{6}
$$

Consequently, using (4) and (5),

$$
\log\frac{N^2}{L_j}
\le
\left(\frac{\eta s}{h}+2\right)
\left(\log2+K(1+\eta)s\right).
$$

Its quadratic leading term is bounded by

$$
\frac{K\eta(1+\eta)}h s^2
\le\frac{1+\eta}{4B^2}s^2
\le\frac{\sqrt2}{4}\log N,\tag{7}
$$

and all remaining terms are $O_B(\sqrt{\log N})$.  Uniformly for
$j\le T$,

$$
L_j\ge N^{2-\sqrt2/4-o(1)}
\ge\frac{16N}{\beta}\tag{8}
$$

for all sufficiently large $N$.  The last comparison uses
$\log(16N/\beta)=\log N+O_B(\sqrt{\log N})$.

This is not circular.  Initially (8) holds for $P_0$.  After any sequence of
applications already justified by the theorem, (6)--(8) show that the next
input still satisfies its length hypothesis.  Induction therefore justifies
every application through the stopping time.

### Terminal contradiction

At termination, $\delta_t>q\beta$ and $L_t\ge16N/\beta$.  Parameterize the
proper progression by the injective affine map

$$
j\longmapsto a+dj,\qquad 0\le j<L_t,
$$

where $d\ne0$.  The preimage $S$ of $A_t$ is 3-AP-free.  Partition
$\{0,\ldots,L_t-1\}$ into consecutive full blocks of length $N$ and one
remainder of length less than $N$.  Each full block contains at most
$r(N)=\beta N$ points of $S$.  Hence

$$
|S|\le\beta L_t+N,
\qquad
\delta_t\le\beta+\frac{N}{L_t}
\le\frac{17}{16}\beta<\frac98\beta,
$$

which contradicts the stopping condition and proves (3) conditionally.

## A proved nontrivial special case

The full statement remains open, but its conclusion is provable when the
rank-one Fourier obstruction has both a fixed-size coefficient and a
fixed-power rational period.

**Rational rank-one proposition.**  Let $K\ge1$, let
$P=\{a+vj:0\le j<L\}$ be a proper integer AP, and let $A\subseteq P$ have
relative density $0<\delta\le8/9$.  Put

$$
S=\{j\in\{0,\ldots,L-1\}:a+vj\in A\},
\qquad f(j)=1_S(j)-\delta.
$$

Suppose there are coprime integers $c,d$, with
$1\le d\le\delta^{-K}$, such that

$$
\left|\frac1L\sum_{j=0}^{L-1}
f(j)\exp\left(\frac{2\pi i c j}{d}\right)\right|
\ge\frac\delta4.\tag{9}
$$

Then there is a proper sub-AP $P'\subseteq P$ satisfying the complete (RAI)
conclusion

$$
|P'|\ge\frac12\delta^K L,
\qquad
\frac{|A\cap P'|}{|P'|}\ge\frac98\delta.\tag{10}
$$

**Proof.**  If $\delta^K L<2$, choose any point of $A$ as $P'$.  Its
length is at least $\delta^K L/2$, and its relative density is one, which is
at least $9\delta/8$.

Now suppose $\delta^K L\ge2$.  Then $d\le\delta^{-K}\le L/2$, so every
residue class modulo $d$ that occurs in $[0,L)$ has length either
$\lfloor L/d\rfloor$ or $\lceil L/d\rceil$.  For $0\le r<d$, let $L_r$ be
its length, let $w_r=L_r/L$, and let $\delta_r$ be the density of $S$ in
that class.  Thus

$$
\sum_{r<d}w_r(\delta_r-\delta)=0.
$$

The left side of (9) is

$$
\left|\sum_{r<d}w_r(\delta_r-\delta)
 \exp\left(\frac{2\pi i cr}{d}\right)\right|.
$$

Writing $x_r=\delta_r-\delta$ and using its weighted mean zero gives

$$
\frac\delta4
\le\sum_{r<d}w_r|x_r|
=2\sum_{x_r>0}w_rx_r
\le2\max_r(x_r)_+.
$$

Some residue class therefore has $\delta_r\ge\delta+\delta/8=9\delta/8$.
Its indices form an ordinary AP, and its image in $P$ is a proper sub-AP.
Moreover,

$$
L_r\ge\left\lfloor\frac Ld\right\rfloor
\ge\delta^K L-1
\ge\frac12\delta^K L.
$$

This proves (10). $\square$

For the conjectural theorem's range, $\delta\le(9/8)\beta\le8/9$ for all
sufficiently large $N$, since Roth's theorem gives $\beta\to0$.  Hence the
proposition proves the entire `RAI(K)` step whenever (9) is available.  It
also preserves the length budget (6) without any change.

The coefficient threshold in (9) is substantive.  A coefficient of size
$O(\delta^2)$ gives only an additive $O(\delta^2)$ density increase by this
argument.  Likewise, rank one without $d\le\delta^{-K}$ does not preserve
the required length.  The next proposition shows more: 3-AP-freeness in the
exact square-scale range does not force any linear-in-$\delta$ coefficient at
fixed-power rational denominator.

## Counterfamily to the missing spectral input

**Proposition (spectral claim false).**  There is a deterministic computable
sequence

$$
N_j\longrightarrow\infty,\qquad
P_j=\{0,\ldots,p_j-1\},\qquad A_j\subseteq P_j,
$$

where $p_j$ is prime and $N_j^2\le p_j\le2N_j^2$, with the following
properties.  If

$$
\beta_j=\frac{r(N_j)}{N_j},
\qquad \delta_j=\frac{|A_j|}{p_j},
$$

then $A_j$ is 3-AP-free,

$$
p_j\ge\frac{16N_j}{\beta_j},
\qquad 0<\delta_j\le\beta_j^2\le\frac98\beta_j,\tag{11}
$$

and for every reduced rational frequency $c/d$ with
$1\le d\le\delta_j^{-j}$,

$$
\left|\frac1{p_j}\sum_{x=0}^{p_j-1}
 (1_{A_j}(x)-\delta_j)
 \exp\left(\frac{2\pi i c x}{d}\right)\right|
<\frac{\delta_j}{j}.\tag{12}
$$

Consequently, for every fixed $K$, all sufficiently large members of this
sequence have every coefficient with $d\le\delta_j^{-K}$ equal to
$o(\delta_j)$.  This disproves the proposed universal spectral input,
including the threshold $\delta/4$ in (9), for every fixed $K$.

It does **not** disprove `RAI(K)`: a density-increment progression need not
be detected by one rational coefficient in this denominator range.

### Construction

For a large $N$, choose a prime $p\in[N^2,2N^2]$, which exists by
Bertrand's postulate, and put $M=\lfloor p/3\rfloor$.  Choose a deterministic
ordinary 3-AP-free
$C\subseteq\{0,\ldots,M-1\}$ with

$$
\frac{|C|}{p}\ge
 \exp\bigl(-C_0\sqrt{\log p}\bigr)\tag{13}
$$

for a fixed $C_0$; for example, take the lexicographically first maximum set
and use the accepted Behrend lower bound.  It is also 3-AP-free in
$\mathbb Z/p\mathbb Z$.  Indeed, both sides of a congruence
$a+c\equiv2b\pmod p$ among its elements lie in $[0,2M-2]\subset[0,p)$, so
the congruence is an ordinary equality.

Let $\beta=r(N)/N$ and set

$$
X=\min\{p\beta^2,|C|/2\},
\qquad m=\lfloor X\rfloor,
\qquad \delta=\frac mp.
$$

For large $N$, $X\ge2$, and hence

$$
\delta\ge
\min\left\{\frac{\beta^2}{2},\frac{|C|}{4p}\right\}
\ge\exp\bigl(-C_1\sqrt{\log p}\bigr)\tag{14}
$$

for a fixed $C_1$, by (1), (13), and $p\asymp N^2$.  Also
$\delta\le\beta^2$.  Fix any deterministic $m$-element subset
$C'\subseteq C$.

Choose $u\in(\mathbb Z/p\mathbb Z)^\times$ and
$v\in\mathbb Z/p\mathbb Z$, and represent

$$
A_{u,v}=uC'+v
$$

in $\{0,\ldots,p-1\}$.  Every such set is modularly, hence ordinarily,
3-AP-free.

### Exact second moment

Choose $(u,v)$ uniformly.  The affine group acts 2-transitively on
$\mathbb Z/p\mathbb Z$.  If $I_x=1_{A_{u,v}}(x)$, then

$$
\mathbb E I_x=\delta,
\qquad
\operatorname{Cov}(I_x,I_y)
=-\frac{\delta(1-\delta)}{p-1}
\quad(x\ne y).
$$

For any fixed $\psi:\mathbb Z/p\mathbb Z\to\mathbb C$ with
$|\psi(x)|=1$, put

$$
Z_\psi=\frac1p\sum_{x=0}^{p-1}(I_x-\delta)\psi(x).
$$

A direct covariance calculation gives the exact identity

$$
\mathbb E|Z_\psi|^2
=
\frac{\delta(1-\delta)}{p-1}
\left(1-
 \left|\frac1p\sum_{x=0}^{p-1}\psi(x)\right|^2\right)
\le\frac{\delta}{p-1}.\tag{15}
$$

Thus no mean-zero assumption on the rational phase is being smuggled in.
For
$\psi_{c,d}(x)=\exp(2\pi i cx/d)$, Markov's inequality gives

$$
\Pr\bigl(|Z_{\psi_{c,d}}|\ge\delta/j\bigr)
\le\frac{j^2}{\delta(p-1)}.\tag{16}
$$

There are at most
$\sum_{d\le D}d\le D^2$ reduced rational frequencies with denominator at
most $D$; the zero frequency has coefficient exactly zero.  With
$D=\lfloor\delta^{-j}\rfloor$, a union bound makes the probability of any
failure at most

$$
\frac{j^2D^2}{\delta(p-1)}
\le\frac{j^2}{(p-1)\delta^{2j+1}}.\tag{17}
$$

By (14), one can choose $N=N_j$ increasing so rapidly that

$$
p_j\delta_j^{2j+1}>4j^2.
$$

Then (17) is less than one, so some affine pair $(u,v)$ satisfies (12).
Choosing the lexicographically first such pair makes the set deterministic
and computable.  All comparisons are finite and decidable; alternatively,
the preceding averaging proof alone certifies existence.

Finally, (1) gives $N\beta\to\infty$, so
$p\ge N^2\ge16N/\beta$ eventually.  The other assertions in (11) follow
from the definition of $\delta$.  For every fixed $K$ and $j\ge K$,

$$
\delta_j^{-K}\le\delta_j^{-j},
$$

and (12) is $o(\delta_j)$ because $1/j\to0$.  This proves the proposition.

The counterfamily closes the most direct route to the rational rank-one
special case: scalar 3-AP-freeness, the square-scale length, and the relative
density range do not themselves force its spectral hypothesis.  Any proof
of full `RAI(K)` must either detect a different kind of increment or impose
additional source-generated structure not present in an arbitrary
3-AP-free set.

## Structural obstruction to the random-affine route

The preceding family defeats the spectral input, but the construction itself
cannot defeat a cyclic version of (RAI).  It retains an explicit long carrier
on which its density increases by a factor about three.

**Carrier proposition.**  In the construction above, let
$I=\{0,\ldots,M-1\}\subseteq\mathbb Z/p\mathbb Z$.  For every affine pair
$(u,v)$, not merely the pair selected by the averaging argument, put

$$
Q_{u,v}=uI+v.
$$

This is a proper cyclic arithmetic progression of length $M$, it contains
$A_{u,v}$, and

$$
\frac{|A_{u,v}\cap Q_{u,v}|}{|Q_{u,v}|}
=\frac mM=\frac pM\delta\ge3\delta.\tag{18}
$$

For every fixed $K\ge1$, eventually $\delta\le1/2$ and
$M=\lfloor p/3\rfloor\ge p/4$, so

$$
|Q_{u,v}|=M
\ge\frac p4
\ge\frac12\delta^Kp.\tag{19}
$$

Thus $Q_{u,v}$ satisfies a stronger-than-(RAI) length and density conclusion
in the cyclic ambient group.  Random affine motion changes the carrier's
location and direction but cannot remove it.  Randomly thinning $C$ also
cannot remove the increment: it changes $m$ and $\delta=m/p$ together, while
the ratio in (18) remains exactly $p/M$.

This explicitly closes the proposed random-affine route to a counterexample.
The low-denominator coefficient union bound sees individual rational tests
in the standard representatives; it does not see, and cannot destroy, the
moving cyclic carrier.

There is a definition point to preserve.  After representing
$\mathbb Z/p\mathbb Z$ by $\{0,\ldots,p-1\}$, $Q_{u,v}$ need not be an
ordinary integer AP because modular wraparound may split it into many short
ordinary pieces.  Hence (18) is directly an obstruction for the cyclic
rank-one formulation, not by itself a proof of the ordinary-integer (RAI)
conclusion.  But the same construction is still not a counterexample to the
integer statement: (12) controls only individual bounded-denominator
coefficients and gives no upper bound on the density over every long ordinary
AP.  Establishing that much stronger simultaneous flatness would require a
new globally spread cap construction; none is supplied here.

Consequently, this lane now has a sharp outcome:

1. the universal bounded-denominator spectral input is false, by (11)--(17);
2. the affine-randomized interval-contained Behrend construction necessarily
   retains the density increment (18)--(19) on its source-faithful cyclic
   carrier; and
3. neither fact decides full ordinary-integer `RAI(K)`.

### A macroscopic fourth-moment shortcut also fails

A proposed repair was to average ordinary-progression intersections over the
affine group and use a fourth-moment union bound.  The required uniform
estimate is false even for a modular cap.  Let $p$ be prime,
$H=\lfloor p/7\rfloor$, and let $C\subseteq[0,H)$ be an ordinary Behrend
cap, viewed in $\mathbb F_p$.  Since $2H-2<p$, it is also modularly
3-AP-free.  Write $\delta=|C|/p$, put $R=[0,2H)$, and set
$X_{u,v}=|(uC+v)\cap R|$.  For $u=1$ and every $0\le v\le H$,
$C+v\subseteq R$, so
$$
|X_{1,v}-\delta|R||=\delta(p-2H)\ge\frac57\delta p.
$$
There are at least $p/7$ such affine pairs among $p(p-1)$ pairs.  Hence
$$
\mathbb E_{u\ne0,v}|X_{u,v}-\delta|R||^4
 \ge \frac{625}{7^5}\delta^4p^3.
$$
On the other hand,
$(\delta|R|)^2\le(4/49)\delta^2p^2$, so their ratio is at least
$$
\frac{625}{1372}\delta^2p,
$$
which tends to infinity at Behrend-scale density.  Modular 3-AP-freeness
controls one three-point pattern, not the centered four-point affine-ratio
correlations appearing in this fourth moment.

The macroscopic witness does not by itself address the cutoff
$\ell=\lceil\delta^Kp/2\rceil$.  The same heavy-tail obstruction nevertheless
persists at that exact scale.  Fix $K\ge1$, put $H=\lfloor p/8\rfloor$, and
choose a Behrend cap $C$ of size $|C|=\delta p$ inside the middle half of
$[0,H)$.  Then $\delta=\exp(-O(\sqrt{\log p}))$, so $\ell=o(p)$ and, for
large $p$, every point of $C$ is at distance at least $\ell$ from both
endpoints of $[0,H)$.  Translation preserves ordinary and modular
3-AP-freeness.

For $0\le s\le H-\ell$, let
$$
X_s=|C\cap[s,s+\ell)|.
$$
Every point of $C$ belongs to exactly $\ell$ such windows, whence
$$
\sum_{s=0}^{H-\ell}X_s=\delta p\ell.
$$
If $T$ windows have $X_s\ge(9/8)\delta\ell$, then, since $X_s\le\ell$ and
$H-\ell+1\le p/8$,
$$
\delta p\ell
 \le T\ell+(H-\ell+1)\frac98\delta\ell,
\qquad
T\ge\frac{55}{64}\delta p.
$$
For every such $s$, the affine image $C-s$ has intersection $X_s$ with the
fixed ordinary interval $R=[0,\ell)$.  Therefore
$$
\mathbb E_{u\ne0,v}
 \bigl|| (uC+v)\cap R|-\delta\ell\bigr|^4
 \ge \frac{55}{2^{18}}\frac{\delta^5\ell^4}{p}.
$$
Relative to $(\delta\ell)^2$, this is at least
$$
\frac{55}{2^{20}}\delta^{2K+3}p\longrightarrow\infty.
$$
Thus the unconditioned fourth-moment estimate fails even at the critical
RAI length.  This still does not refute ordinary `RAI(K)`: the proof
exhibits aligned images of probability $\Omega(\delta/p)$, while the entire
$u=1$ orientation has probability $1/(p-1)=O(1/p)$, and every exhibited
image actually has the asserted interval density increment.  What
remains open is a simultaneous-flatness construction or a tail estimate
after conditioning away the aligned directions.  Neither the critical-scale
heavy tail nor the cyclic carrier decides ordinary `RAI(K)`.

## Attempts to prove or refute (RAI)

### Existing density-increment inputs do not prove it

Green's Oxford 2025 Proposition 1.2 gives, in the no-progression branch, a
subprogression of length at least $L^{1/5}$ and an additive density gain
$\delta^2/112$, under $L\ge(8/\delta)^{10}$.  At the relevant starting
scale $L=N^2$ and $\delta\asymp\beta^{1+\eta}=\exp(-O(\sqrt{\log N}))$,
(RAI) asks for length

$$
\delta^K L=N^{2-o(1)},
$$

whereas $L^{1/5}=N^{2/5}$.  Its gain is also not a fixed multiplicative
factor.  Iterating that proposition therefore does not establish (RAI).

The audited Bloom--Sisask/Kelley--Meka machinery likewise does not establish
(RAI).  Its conclusions are Bohr-set or GAP increments with growing rank and
logarithmic-power losses, not fixed-power rank-one retention.  In particular,
the later Bohr set is supplied with rank and cardinality bounds, not a width
lower bound.  One cannot infer a width from its cardinality.  Prime-cyclic AP
extraction uses cardinality and rank and, in the cited $3A$ application,
places an AP in $3A$, not in $A$ and not in a density-carrying affine
container for $A$.

These are insufficiency statements about guaranteed source conclusions, not
proofs that (RAI) is false.

### Carry-free digit-product stress test

Let $B\subseteq\{0,\ldots,N-1\}$ be 3-AP-free and put $Q=2N-1$.  Then

$$
A=B+QB
$$

is 3-AP-free: a scalar midpoint equation forces
$x_1+x_3-2x_2$ to be a multiple of $Q$, but its absolute value is less than
$Q$, so both digit equations vanish.  If $|B|=r(N)$, this construction has
density comparable to $\beta^2$ in an interval of length comparable to
$N^2$.

This example lies inside the density range of (RAI), but it does not yet
refute the theorem: no argument here excludes the required progression in
all scalar directions.  It is a genuine structural stress test.  The
obvious horizontal and vertical fibers have length only $N$ and density
$\beta$, while (RAI) demands at its first step a progression of length

$$
\gg \beta^{2K}N^2=N^{2-o(1)}.
$$

Thus the coordinate-fiber increment is much too short.  Proving (RAI) for
this example already requires control of arbitrary long scalar directions;
coordinatewise product structure does not supply the witness.  No argument
in this audit proves that such a witness exists, but neither was an infinite
family proved to exclude all of them.

The EHPS/Behrend density profile is consistent with a fixed-power length
contraction: replacing $L$ by $\delta^K L$ changes
$\sqrt{\log L}$ only by a bounded amount when
$\delta=\exp(-\Theta(\sqrt{\log L}))$.  This consistency is not a proof of
(RAI); it only shows that the known construction-level density scale does not
itself contradict the quantifiers.

### Half-digit arbitrary-relation stress test

The kernel-checked carry-cardinality obstruction supplies, for every
$N\ge3$, a relation $G\subseteq[0,N)^2$ whose rows and columns are all
ordinary 3-AP-free, whose common fiber size $b$ satisfies $2b\le N$, and
whose size satisfies

$$
|G|\ge\frac12N r(N).
$$

This has density at least $\beta/2$, squarely in the relative range tested by
(RAI).  But its scalar base-$N$ image contains

$$
0,\quad N+1,\quad2(N+1),
$$

and is deliberately not scalar-3-AP-free.  It therefore does not refute the
exact theorem.  It does decisively refute any attempted proof that replaces
the scalar premise by ordinary row/column caps and their cardinalities: that
relaxation already permits mass of order $Nr(N)$ and loses the carry
information on which (RAI) must depend.

Deleting the displayed diagonal is not a counterexample: other scalar
progressions remain uncontrolled, and no scalar-3-AP-free subrelation of the
required density with all long affine increments excluded has been proved.

## Bounded conclusion

The source audit has been reduced to the single quantified statement (RAI).
It survives the two required construction tests, but only in the precise
sense that neither construction satisfies all hypotheses and disproves the
conclusion.  The digit product exposes a real unresolved case: the obvious
increments are shorter than the theorem requires by a factor
$N^{1-o(1)}$.  The half-digit relation proves that scalar carry-freeness
cannot be relaxed away.

Accordingly, (RAI) remains an unproved, non-vacuous, source-specific missing
lemma.  The complete calculation above shows that no further asymptotic
regularity or generic Bohr-set claim would be needed after it: its fixed gain
and fixed-power rank-one retention are exactly enough to reach a terminal
progression of length at least $16N/\beta$ and prove (3).
