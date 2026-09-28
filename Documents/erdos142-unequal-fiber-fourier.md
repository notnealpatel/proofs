# Unequal-fiber carry Fourier lane

## Scope and status

This note records an exact Fourier organization of the base-$N carry
constraint for a scalar set.  It is a partial carry-sensitive calculation,
not a proof of P, not an asymptotic solution of Erdős 142, and not a
kernel-checked Lean artifact.  The scalar encoding throughout is

$$
 n=x+Ny,
 \qquad 0\le x,y<N.
$$

Write $r_3(N)$ for the largest ordinary 3-AP-free subset of $[0,N)$ and
call $A\subseteq[0,N^2)$ a scalar cap when it has no nontrivial ordered
three-term arithmetic progression.  All finite computations mentioned below
are exploratory evidence; the displayed root-of-unity identities and the
finite inequalities are the mathematical arguments.

## 1. The exact $Q=4N$ low-digit carry identity

Fix $N\ge1$ and put $Q=4N$.  For $0\le y<N$, let

$$
 \phi_y:[0,N)\longrightarrow\{0,1\},
 \qquad
 \phi_y(x)=1_A(x+Ny).
$$

Extend the fibers by zero in both coordinates: $\phi_y(x)=0$ if either
$x\notin[0,N)$ or $y\notin[0,N)$.  For $t\in\{-1,0,1\}$ and
$y,q\in\mathbb Z$, set

$$
 \gamma_{N,t}(y,q)=
 1_{[0,N)}(y-q)1_{[0,N)}(y+q-t).
$$

Thus $\gamma$ is a hard integer boundary indicator, not a smooth cutoff.
With

$$
 e_Q(u)=\exp(2\pi i u/Q),
 \qquad
 \widehat\phi_y(r)=\sum_x\phi_y(x)e_Q(-rx),
$$
where the sum may be taken over $\mathbb Z$ because of the zero extension,
define, for $r\in\mathbb Z/Q\mathbb Z$,

$$
 C_r=\frac1Q\sum_{t=-1}^{1}e_Q(tNr)
 \sum_{y=0}^{N-1}\sum_{q\in\mathbb Z}\gamma_{N,t}(y,q)
 \widehat\phi_{y-q}(r)
 \widehat\phi_y(-2r)
 \widehat\phi_{y+q-t}(r).
 \tag{1}
$$

The exact ordered scalar count is

$$
 T(A)=\sum_{r\bmod Q}C_r.
 \tag{2}
$$

Here is the orthogonality proof.  In a summand of (1), write
$y_0=y-q$, $y_1=y$, and $y_2=y+q-t$.  Expansion of the three DFTs gives
the phase

$$
 e_Q\bigl(r(tN-x_0+2x_1-x_2)\bigr)
 =e_Q\bigl(-r(x_0+x_2-2x_1-tN)\bigr).
$$

Summing over $r\bmod Q$ enforces

$$
 x_0+x_2-2x_1=tN.
$$
Indeed, if $L=x_0+x_2-2x_1$, then
$|L-tN|\le3N-2<Q$, while orthogonality first says only that $Q$ divides
$L-tN$; hence there is no alias and $L=tN$ exactly.  The corresponding
high-digit residual is

$$
 y_0+y_2-2y_1=-t.
$$

The two factors in $\gamma_{N,t}$ impose the hard bounds on $y_0$ and $y_2$;
the middle digit is already $0\le y<N$.  Conversely, every scalar ordered
triple satisfying $n_0+n_2=2n_1$ has a unique $t\in\{-1,0,1\}$: its low-digit
quantity $L$ is a multiple of $N$ and lies in
$[-2N+2,2N-2]$.  The associated $q=y_1-y_0$ then gives exactly one term in
(1).  This proves (2), including the boundary cases.

The fibers are real-valued, so

$$
 C_{Q-r}=\overline{C_r},
$$
with residues understood modulo $Q$, and consequently $T(A)$ is real.  The
sum in (2) includes the $m=|A|$ diagonal triples.  Thus the nontrivial
ordered count is $T(A)-m$, and the unoriented count is $(T(A)-m)/2$.  In
particular, for a scalar cap,

$$
 T(A)=m.
 \tag{3}
$$

## 2. Zero mode, signed defect, and total variation

Let

$$
 d_y=|A_y|=\sum_x\phi_y(x),
 \qquad m=|A|=\sum_{y=0}^{N-1}d_y,
$$

where $d_y=0$ outside $[0,N)$.  At $r=0$, (1) is the exact formula

$$
 M_0:=C_0
 =\frac1{4N}\sum_{t=-1}^{1}\sum_{y=0}^{N-1}
   \sum_{q\in\mathbb Z}
   \gamma_{N,t}(y,q)d_{y-q}d_y d_{y+q-t}.
 \tag{4}
$$

The $(t,q)=(0,0)$ summands give

$$
 M_0\ge\frac1{4N}\sum_{y=0}^{N-1}d_y^3
 \ge\frac{m^3}{4N^3},
 \tag{5}
$$

where the second inequality is the power-mean inequality over the $N$
rows.  Put

$$
 r=r_3(N),
 \qquad K=N^{2/3}r^{4/3},
 \qquad
 R=\sum_{r'\ne0}C_{r'},
 \qquad
 S=\sum_{r'\ne0}|C_{r'}|,
 \tag{6}
$$

where the $r'$ in (6) ranges over nonzero residues modulo $Q$.  For a scalar
cap, (3) gives

$$
 R=m-M_0,
 \qquad S\ge|R|.
 \tag{7}
$$

## 3. Exact carry-defect measure and Fourier consequences

For the remainder of this section, let $A$ be a scalar cap.  Expand the
three Fourier sums in (1).  Call
$(t,y,q,x_0,x_1,x_2)$ an **active expanded term** when
$t\in\{-1,0,1\}$, $y\in[0,N)$, $q\in\mathbb Z$, and

$$
 \gamma_{N,t}(y,q)\phi_{y-q}(x_0)\phi_y(x_1)
 \phi_{y+q-t}(x_2)=1.
$$

For such a term write
$y_0=y-q$, $y_1=y$, $y_2=y+q-t$, and put

$$
 u_0=x_0+x_2-2x_1-tN.
$$

For $u\in\mathbb Z/Q\mathbb Z$, let

$$
 \mu(u)=\#\{\text{active expanded terms with }u_0\equiv u\pmod Q\}.
$$

The expanded form of (1) is therefore

$$
 C_r=\frac1Q\sum_{u\bmod Q}\mu(u)e_Q(-ru).
$$

Because an active term has $0\le x_i<N$,

$$
 |u_0|\le (2N-2)+N=3N-2<Q.
$$

If $u_0\equiv0\pmod Q$, this strict bound gives $u_0=0$.  The defining
relations for the high digits give
$y_0+y_2-2y_1=-t$, so $u_0=0$ makes

$$
 (x_0+Ny_0)+(x_2+Ny_2)=2(x_1+Ny_1).
$$

The scalar-cap condition forces this ordered progression to be diagonal.
Uniqueness of the base-$N$ digits then gives $q=t=0$ and
$(x_0,y_0)=(x_1,y_1)=(x_2,y_2)$.  Conversely, every element of $A$ gives
exactly this diagonal active term.  Thus

$$
 \mu(0)=m.
$$

Define the zero-atom-removed defect measure by

$$
 \nu(u)=
 \begin{cases}
   \mu(u),&u\ne0,\\
   0,&u=0,
 \end{cases}
 \qquad (u\in\mathbb Z/Q\mathbb Z).
$$

Distinct nonzero integer defects may alias modulo $Q$; this is harmless,
because $\nu$ is defined after that grouping.  The strict bound above also
ensures that no nonzero integer defect aliases into the zero atom.  We obtain
the exact carry-defect formula

$$
 C_r-\frac mQ
 =F_r
 =\frac1Q\sum_{u\ne0}\nu(u)e_Q(-ru).
$$

Put $D=F_0=M_0-m/Q$.  Since $\nu\ge0$, the defect formula gives
$D\ge0$ and $|F_r|\le D$.  The same positive-measure representation gives
$|C_r|\le C_0=M_0$.  More precisely, the cyclic Toeplitz (equivalently,
circulant) matrix

$$
 \bigl(F_{j-k}\bigr)_{j,k\in\mathbb Z/Q\mathbb Z}
$$

is positive semidefinite, since for every complex vector $(z_j)$,

$$
 \sum_{j,k}\overline{z_j}F_{j-k}z_k
 =\frac1Q\sum_{u\ne0}\nu(u)
   \left|\sum_k z_k e_Q(ku)\right|^2\ge0.
$$

Parseval and the zero atom's removal give

$$
 \sum_{r\bmod Q}|F_r|^2
 =\frac1Q\sum_{u\ne0}\nu(u)^2.
$$

Also $\sum_{r\bmod Q}F_r=0$, so

$$
 \sum_{r\ne0}F_r=-D,
 \qquad
 \sum_{r\ne0}|F_r|^2\ge\frac{D^2}{Q-1}
$$

by Cauchy.  Equivalently, the defect collision energy on the right-hand
side of Parseval is at least $QD^2/(Q-1)$.  This theorem advances the
organization of the carry defects, but it does not prove the candidate (*):
no useful upper bound for the defect collision energy
$\sum_{u\ne0}\nu(u)^2$ is known.

## 3A. Mandatory scalar-realizability row pushforward

The carry expansion has a distinguished, mandatory block: the terms with
$q=t=0$.  Keep $Q=4N$ and write the row fibers and their indicators as
follows.  The following refinement is an independently audited prose
calculation, not a Lean formalization.  Write

$$
 B_y=\{x\in[0,N):x+Ny\in A\},
 \qquad
 \phi_y=1_{B_y},
 \qquad
 d_y=|B_y|,
 \qquad
 m=\sum_y d_y,
 \qquad
 T_3=\sum_y d_y^3,
 \qquad
 A_2=\sum_y d_y^2.
$$

For self-containment, define the full visible defect counting measure on
$\mathbb Z/Q\mathbb Z$ by

$$
 \mu(u)=\#\Bigl\{(t,y,q,x_0,x_1,x_2):
 \begin{array}{l}
 t\in\{-1,0,1\},\ y\in[0,N),\ q,x_0,x_1,x_2\in\mathbb Z,\\
 \gamma_{N,t}(y,q)\phi_{y-q}(x_0)\phi_y(x_1)\phi_{y+q-t}(x_2)=1,\\
 x_0+x_2-2x_1-tN\equiv u\pmod Q
 \end{array}\Bigr\}.
$$

Write $u_0=x_0+x_2-2x_1-tN$ for a visible tuple.  Its zero-frequency
Fourier expansion is

$$
 C_r=\frac1Q\widehat\mu(r),
 \qquad
 \widehat\mu(r)=\sum_{u\bmod Q}\mu(u)e_Q(-ru).
$$

The visible bounds give $|u_0|\le3N-2<Q$, so $u_0\equiv0\pmod Q$ implies
$u_0=0$.  If $y_0=y-q$, $y_1=y$, and $y_2=y+q-t$, then
$y_0+y_2-2y_1=-t$ and $u_0=0$ make the corresponding scalar triple a
3-term progression.  Scalar capness forces it to be diagonal; uniqueness of
base-$N$ digits then gives $q=t=0$ and
$x_0=x_1=x_2$.  Conversely every element of $A$ supplies exactly one such
visible diagonal tuple.  Hence

$$
 \mu(0)=m,\qquad |\mu|=QM_0.
$$

Define

$$
 \nu=\mu-m\delta_0.
$$

Then $\nu\ge0$, $\nu(0)=0$, and

$$
 C_r=\frac{m+\widehat\nu(r)}{Q},
 \qquad |\nu|=QM_0-m.
$$

(The first identity is the displayed expansion of $C_r$ after removing the
zero atom.)

For an occupied
midpoint $(x,y)$, so $x\in B_y$, define the integer defect measure

$$
 \lambda_{y,x}
 =\sum_{a,c\in B_y}\delta_{a+c-2x}.
$$

Here $\delta_z$ denotes the unit point mass at $z$.  Its zero atom has mass
exactly one.  Indeed, a pair with $a+c=2x$ gives the
scalar progression
$(a+Ny,x+Ny,c+Ny)$.  Scalar capness forces this progression to be diagonal,
so $a=c=x$; the converse pair is present.  Therefore
$\lambda_{y,x}-\delta_0\ge0$.

Aggregate these row-pushforward defects as an integer measure by

$$
 \lambda=\sum_{y,x\in B_y}(\lambda_{y,x}-\delta_0).
$$

Thus $\lambda\ge0$.  Every defect $a+c-2x$ lies in
$[-2N+2,2N-2]$, and the subtraction removes the zero atom.  The interval
has diameter $4N-4<Q$, so its nonzero integer support embeds injectively in
$\mathbb Z/Q\mathbb Z$ without alias.  Counting the mass at each occupied
midpoint gives

$$
 |\lambda|=\sum_y d_y(d_y^2-1)=T_3-m.
$$

The $q=t=0$ nonzero block is exactly $\lambda$, so it is a submeasure of
$\nu$.  Thus, after viewing $\lambda$ in $\mathbb Z/Q\mathbb Z$, there is an
$\eta\ge0$ with

$$
 \nu=\lambda+\eta,
 \qquad
 |\eta|=(QM_0-m)-(T_3-m)=QM_0-T_3.
$$

The row-pushforward has exact transform

$$
 \widehat\lambda(r)
 =\sum_y\widehat\phi_y(r)^2\widehat\phi_y(-2r)-m.
$$

Consequently, with

$$
 P_r=\sum_y\widehat\phi_y(r)^2\widehat\phi_y(-2r),
$$

and with $C_r=(m+\widehat\nu(r))/Q$ from the visible-measure expansion,

$$
 C_r=\frac{P_r+\widehat\eta(r)}{Q}.
$$

This gives the exact triangle estimate

$$
 S\le
 \frac{(Q-1)(QM_0-T_3)}{Q}
 +\frac1Q\sum_{r\ne0}|P_r|.
 \tag{B}
$$

Indeed, $|\widehat\eta(r)|\le|\eta|$ for every $r$.  Thus (B) is the
strongest immediate estimate from this decomposition when the cross-row
phases in $P_r$ are retained but only the total mass of $\eta$ is used.

There is a valid rowwise energy bound, but it does not recover the desired
threshold.  For an ordinary integer set $B\subseteq[0,N)$, define

$$
 E_+(B)=|\{(a,b,c,d)\in B^4:a+b=c+d\}|.
$$

For $B=B_y$, the no-wraparound range
$0\le a+b,c+d\le2N-2<Q$ gives

$$
 \sum_{r\bmod Q}|\widehat\phi_y(r)|^4=Q E_+(B_y).
$$

The map $r\mapsto-2r$ on $\mathbb Z/Q\mathbb Z$ is two-to-one onto the
even residues.  Moreover, again without wraparound,

$$
 \sum_{s\text{ even}}|\widehat\phi_y(s)|^2
 =2N d_y=\frac{Qd_y}{2},
 \qquad
 \sum_{r\bmod Q}|\widehat\phi_y(-2r)|^2=Qd_y.
$$

Here the first equality follows by writing $s=2k$, summing over
$k\bmod 2N$, and observing that $|a-b|<N<2N$ makes $a-b\equiv0\pmod{2N}$
iff $a=b$.  Cauchy--Schwarz therefore gives, with the factor two from the
frequency map accounted for exactly,

$$
 \sum_{r\bmod Q}
 |\widehat\phi_y(r)|^2|\widehat\phi_y(-2r)|
 \le Q\sqrt{d_yE_+(B_y)}.
$$

Since $E_+(B_y)\le d_y^3$ (choose three entries; the fourth is determined
if it exists), (B) implies the two valid bounds

$$
 U_E=\frac{(Q-1)(QM_0-T_3)}{Q}
       +\sum_y\sqrt{d_yE_+(B_y)},
 \qquad S\le U_E,
$$

$$
 U_2=\frac{(Q-1)(QM_0-T_3)}{Q}+A_2,
 \qquad S\le U_2.
$$

For the cap-specific sharpening, let $B$ be an ordinary cap of size $d$ and
for $h>0$ put
$r_B(h)=|B\cap(B-h)|$.  The fixed-$h$ edges form a matching: two adjacent
edges would give the forbidden progression $z,z+h,z+2h$.  Hence
$r_B(h)\le\lfloor d/2\rfloor$, while every unordered pair has one
positive difference and therefore
$\sum_{h>0}r_B(h)=\binom d2$.  The ordinary energy identity and this bound
are

$$
 E_+(B)=d^2+2\sum_{h>0}r_B(h)^2
 \le d^2+\lfloor d/2\rfloor d(d-1).
$$

Define

$$
 g(d)=d\sqrt{d+\lfloor d/2\rfloor(d-1)},
 \qquad
 U_{\rm cap}=\frac{(Q-1)(QM_0-T_3)}{Q}+\sum_y g(d_y).
$$

Then $S\le U_{\rm cap}$ is also valid.

Every row $B_y$ of a scalar cap is an ordinary cap, so $d_y\le r=r_3(N)$.
Here is the quantitative audit of what these bounds do in the candidate's
high-mass range $N\ge3$, $m\ge K$.  With

$$
 \Theta=M_0+m-\frac{m^3}{K^2},
 \qquad K=N^{2/3}r^{4/3},
 \qquad r=r_3(N),
$$

we have

$$
 \frac{K}{r^2}=\left(\frac Nr\right)^{2/3}\ge1,
 \qquad
 \frac{m^3}{K^2}\ge m,
 \qquad
 M_0\ge\frac{T_3}{Q},
 \qquad
 T_3\le rA_2\le NA_2.
$$

The first inequality uses $r\le N$, the second uses $m\ge K$, the lower
bound for $M_0$ is the $q=t=0$ contribution to (4), and the last one uses
$d_y\le r\le N$.  Exact subtraction gives

$$
 U_2-\Theta
 =(Q-2)\left(M_0-\frac{T_3}{Q}\right)
  +\left(A_2-\frac{T_3}{Q}\right)
  +\left(\frac{m^3}{K^2}-m\right),
$$

so, since $Q=4N$,

$$
 U_2-\Theta\ge\frac34A_2>0.
$$

Likewise, with $G=\sum_y g(d_y)$,

$$
 U_{\rm cap}-\Theta
 =(Q-2)\left(M_0-\frac{T_3}{Q}\right)
  +\left(G-\frac{T_3}{Q}\right)
  +\left(\frac{m^3}{K^2}-m\right).
$$

For $d=0$ the claimed lower bound is immediate.  For $d\ge1$,
$\lfloor d/2\rfloor\ge(d-1)/2$ and therefore
$d+\lfloor d/2\rfloor(d-1)\ge(d^2+1)/2\ge d^2/2$.  Thus

$$
 g(d)\ge\frac{d^2}{\sqrt2}.
$$

Also $d_y^3/Q\le d_y^2/4$ for $d_y\le r\le N$.  Consequently

$$
 G-\frac{T_3}{Q}
 \ge\left(\frac1{\sqrt2}-\frac14\right)A_2>0.
$$

These are upper bounds on $S$ that remain above $\Theta$: they cannot prove
(*), but they are not counterexamples and do not show that the actual $S$ is
larger than $\Theta$.  The exact bound (B) may still exploit cancellation
among the cross-row phases in $P_r$.  In the full identity
$C_r=(P_r+\widehat\eta(r))/Q$, a further phase-sensitive coupling between
$P_r$ and $\eta$ is also available before taking absolute values.

The missing scalar information is therefore phase-sensitive control of
$\eta$ and its coupling to $P_r$, or a collision/$L^1$ estimate for the
off-diagonal $(q,t)\ne(0,0)$ defect blocks.  Abstract PSD, mass, and degree
constraints, as well as rowwise energy bounds, lose precisely this coupling.

## 4. The open high-mass candidate

The phase-blind high-mass candidate is the following statement, proposed only
when $N\ge3$, $A$ is scalar-free, and $m\ge K$:

$$
 \boxed{\quad S\le M_0+m-\frac{m^3}{K^2}.\quad}
 \tag{*}
$$

It is open.  It has neither been proved nor refuted in the high-mass regime.
The restriction $N\ge3$ is intentional: at $N=2$, $r_3(2)=2$ and $K=4$,
while $r_3(4)=3$, so no scalar cap can meet $m\ge K$.  Nevertheless, its
elementary consequence is useful.  From (7), always and
without assuming $M_0\ge m$,

$$
 S\ge -R=M_0-m.
$$

Combining this with (*) gives

$$
 M_0-m\le M_0+m-\frac{m^3}{K^2},
 \qquad\text{so}\qquad m\le\sqrt2K.
 \tag{8}
$$

The low-mass alternative $m<K$ is already bounded by $K$.  Therefore (*) in
the high-mass range would imply

$$
 r_3(N^2)\le\sqrt2\,N^{2/3}r_3(N)^{4/3},
 \tag{9}
$$

which is the P-shaped exponent $\eta=1/3$.  This implication is
conditional on the open candidate and is not an asymptotic result.

The weakest signed condition obtained by replacing total variation with the
one-sided estimate $S\ge-R$ is

$$
 R\ge -M_0-m+\frac{m^3}{K^2}.
 \tag{10}
$$

For cap indicators this is exactly equivalent to $m\le\sqrt2K$, since
$R=m-M_0$; no information about $M_0$ is needed.  Thus (10) is only a
reformulation of the desired cardinality bound, not analytic progress.  The
candidate (*) is strictly stronger: it controls the total variation of all
nonzero grouped modes, whereas (10) controls only a signed sum and allows
cancellation.

The unrestricted-in-$N$ formulation is false at the degenerate endpoint
$N=1$.  In this case $r_3(1)=K=m=1$ for $A=\{0\}\subseteq[0,1)$ and
$Q=4$.  Directly from (1),

$$
 C_r=\frac14\quad(r\bmod4),
 \qquad M_0=\frac14,
 \qquad R=S=\frac34.
$$

The right-hand side of (*) is
$M_0+m-m^3/K^2=\frac14$, so this is an exact high-mass counterexample to
the unrestricted-in-$N$ wording.  It is a degenerate finite obstruction only;
it does not refute the $N\ge3$ candidate or the eventual/asymptotic route.

## 5. Finite counterexamples and their limitations

### Nondegenerate $N=3$ low-mass obstruction

There is an exact small counterexample if the high-mass condition is removed,
even at $N=3$.  Take

$$
 N=3,\qquad Q=12,\qquad B=\{0\},\qquad C=\{0,1\},
 \qquad G=B\times C,
 \qquad A=\{0,3\}.
$$

This is a half-digit arbitrary relation, a product, and the graph of the
constant map $C\to B$.  It has $m=2$.  If

$$
 H_s(C)=\#\{(c_0,c_1,c_2)\in C^3:c_0+c_2-2c_1=s\},
$$

then $H_s(C)=2$ for each $s=-1,0,1$.  Grouping all carry cases in (1),
not taking the scalar DFT of $1_A$, gives the exact grouped spectrum

$$
 C_r=\frac16\left(1+2\cos\frac{\pi r}{2}\right).
 \tag{11}
$$

Thus $C_r$ is $1/2$ for $r=0\pmod4$, $-1/6$ for $r=2\pmod4$, and $1/6$
for odd $r$ (all residues are modulo $12$).  In particular,

$$
 M_0=\frac12,
 \qquad R=\frac32,
 \qquad S=\frac52=M_0+m.
 \tag{12}
$$

Every positive defect in (*) therefore fails for this candidate without
the high-mass condition.  An exact Sage cyclotomic computation reproduces
(11)--(12), but that computation is evidence only; the displayed root-of-unity
calculation is the proof.  This does **not** refute the high-mass candidate:
here

$$
 r_3(3)=2,
 \qquad K=3^{2/3}2^{4/3}>2.
$$

The distinction between the grouped $C_r$ in (1) and the scalar Fourier
transform of $1_A$ is essential.  Also, each translate
$\{s,s+3\}$ for $0\le s\le5$ has the same exact grouped spectrum.  Translations
therefore do not repair the candidate without the high-mass condition.
They likewise do not close the high-mass route.

## 6. Why the half-digit family is not high mass

Let $H=\lceil N/2\rceil$.  If $B,C\subseteq[0,H)$ are ordinary caps and
$G\subseteq B\times C$ is an arbitrary indicator relation, then

$$
 m=|G|\le |B||C|\le r_3(H)^2\le r^2\le K.
 \tag{13}
$$

The final inequality is $r\le N$; it is strict for $N\ge3$ because the full
interval is not 3-AP-free.  Thus $m<K$ for $N\ge3$.  This excludes the
accepted half-digit family from the high-mass regime, regardless of which
indicator relation is chosen.  The argument is only about that indicator
relation and its cardinality; it makes no false weighted $L^1$ assertion.
Consequently this family cannot refute (*), even though its unrestricted
Fourier behavior can be extremal.

## 7. High-mass spread and cancellation lemma

**Lemma (high-mass spread and cancellation, accepted prose deduction).**
Let $A\subseteq[0,N^2)$ be a scalar cap, let $m=|A|$, and suppose
$N\ge3$ and $m\ge K$.  Every row and every column of the scalar array is an
ordinary 3-AP-free set, so all row and column degrees are at most
$r=r_3(N)$.  If $Y$ and $X$ are respectively the occupied row and column
projections, then

$$
 |Y|\ge\frac mr\ge N^{2/3}r^{1/3}>r,
 \qquad
 |X|\ge\frac mr\ge N^{2/3}r^{1/3}>r.
 \tag{14}
$$

Therefore both projections contain ordinary nontrivial 3-APs.  This is a
spread conclusion, not a scalar progression in $A$.

For the quantitative fiber statement, call a row heavy when
$d_y\ge m/(2N)$.  Rows that are not heavy have total degree strictly less
than $m/2$, because there are at most $N$ rows and each has degree strictly
less than $m/(2N)$.  Hence heavy rows carry strictly more than $m/2$ total
mass.  Since each row has degree at most $r$, the number of heavy rows is
strictly greater than $m/(2r)$ (equivalently, it is at least
$\lfloor m/(2r)\rfloor+1$).  The identical argument for columns gives the
same two statements in the other orientation.  Finally, (5) gives
$M_0\ge m^3/(4N^3)$.

There is also an asymptotic near-cancellation consequence.  Use the accepted
Behrend/EHPS lower input, in its uniform form

$$
 r_3(N)\ge N\exp\bigl(-O(\sqrt{\log N})\bigr).
 \tag{15}
$$

For any sequence with $m\ge K$, (5) gives

$$
 \frac{m}{M_0}
 \le\frac{4N^3}{m^2}
 \le\frac{4N^{5/3}}{r^{8/3}}=o(1).
 \tag{16}
$$

Thus, using $R=m-M_0$ and $S\ge|R|$,

$$
 \frac{R}{M_0}=-1+o(1),
 \qquad
 S\ge(1-o(1))M_0.
 \tag{17}
$$

The last asymptotic sentence (15)--(17) is an accepted prose deduction from
the accepted lower input, not a Lean theorem.  The finite spread statements
and (5) likewise do not prove (*): they give no phase-sensitive upper bound
on $S$.

## 8. Stress tests and computational status

For a product $G=B\times C$, define

$$
 L_t(B)=\#\{(b_0,b_1,b_2)\in B^3:b_0+b_2-2b_1=tN\},
$$

$$
 H_s(C)=\#\{(c_0,c_1,c_2)\in C^3:c_0+c_2-2c_1=s\}.
$$

The physical carry counts factor exactly as

$$
 T_t=L_t(B)H_{-t}(C).
 \tag{18}
$$

Translations can redistribute mass among the carry cases, but the total
identity (2) remains exact.  For the full box at $N=3$, the three counts are
$(T_{-1},T_0,T_1)=(8,25,8)$, totaling the $41$ ordered progressions in
$[0,8]$.

Exact Sage exhaustive enumeration found no high-mass scalar caps for
$N=2,3,4$: respectively,

$$
 r_3(4)=3<K=4,
 \qquad r_3(9)=5<K\mathrel{\approx}5.24,
 \qquad r_3(16)=8<K\mathrel{\approx}10.90.
$$

Exact-integer GLPK optimization gave

$$
 r_3(25)=10<K\mathrel{\approx}18.57,
 \qquad r_3(36)=14<K\mathrel{\approx}20.97.
$$

These are finite computations, not proofs of (*) or evidence strong enough
to settle it in general.  The $N=7$ computation timed out and was not
retried unchanged.  In particular, the low-mass counterexample above does not
close the high-mass route.

## 9. A high-mass relaxation obstruction at $N=16$

The following is an exact finite computational certificate/evidence for the
relaxation in which only one-dimensional row and column restrictions are
retained.  It is not a scalar-cap counterexample and is not a refutation of
(*) on scalar caps.  Set

$$
 N=16,
 \qquad Q=64,
 \qquad r_3(16)=8,
 \qquad K=16^{2/3}8^{4/3}\mathrel{\approx}101.5937.
$$

Let

$$
 B=\{0,1,6,8,13,14\}\subseteq\mathbb Z/16\mathbb Z,
$$

and let the ordered exceptional pairs be

$$
 E=\{(9,0),(10,1),(1,12),(2,13),(3,14),(4,15)\}.
$$

Define

$$
 G=\{(x,y)\in[0,16)^2:(x-y)\bmod16\in B\}\cup E,
 \qquad
 A=\{x+16y:(x,y)\in G\}.
$$

The two pieces of $G$ are disjoint, so $m=|A|=|G|=96+6=102$.  Moreover,

$$
 m^3=1{,}061{,}208>1{,}048{,}576=16^2\cdot8^4,
$$

which is the exact integer comparison $m>K$.  Every row and every column
fiber is an ordinary integer 3-AP-free set of size at most $8$, and both
projections are all $16$ digits.  Thus this relation satisfies strictly more
than projection spread and cardinality bounds: it has the actual
row/column capness and degree bound.

Here is a short exact justification of the value $r_3(16)=8$ used above.
The lower bound $r_3(8)\ge4$ is witnessed by
$\{0,1,3,4\}$.  If a 5-element cap in $[0,8)$ existed, its 3-element
complement $H$ would have to hit all six consecutive progressions
$(i,i+1,i+2)$ for $i=0,\ldots,5$.
The only 16 such $H$ are

$$
\begin{gathered}
(0,2,5),(0,3,5),(0,3,6),(1,2,5),(1,3,5),(1,3,6),\\
(1,4,5),(1,4,6),(1,4,7),(2,3,5),(2,3,6),(2,4,5),\\
(2,4,6),(2,4,7),(2,5,6),(2,5,7).
\end{gathered}
$$

They respectively miss a longer progression as follows: the six
$H=(0,2,5),(0,3,5),(0,3,6),(2,3,5),(2,3,6),(2,5,6)$ miss
$(1,4,7)$; the six
$H=(1,2,5),(1,4,5),(1,4,7),(2,4,5),(2,4,7),(2,5,7)$ miss
$(0,3,6)$; $H=(1,3,5),(1,3,6)$ miss $(0,2,4)$; $H=(1,4,6)$ misses
$(3,5,7)$; and $H=(2,4,6)$ misses $(1,3,5)$.  Thus no 5-set cap
exists in $[0,8)$.  Thus $r_3(8)=4$.  For a cap in $[0,16)$, its even
and odd parts each rescale to a cap in $[0,8)$, so its size is at most $8$.
The set

$$
\{0,1,3,4,9,10,12,13\}
$$

is a cap: each four-point block is $\{0,1,3,4\}$ up to translation, and a
three-term progression cannot use points from both blocks because the gap is
larger than the block diameter in either possible two-low/one-high or
one-low/two-high arrangement.  Thus it proves $r_3(16)=8$.

The relation $G$ is not a scalar cap: $0,9,18\in A$ and
$0+18=2\cdot9$.  The exact ordered scalar triple count from (1), however,
is

$$
 T=\sum_{r=0}^{63}C_r=1564,
$$

rather than $m$.  For the fixed grouped identity (1), exact evaluation gives

$$
 M_0=C_0=\frac{48183}{32}=1505.71875,
$$

and the real-algebraic total variation and candidate right-hand side satisfy

$$
\begin{aligned}
1508.87835005088420127094169298&<S<
1508.87835005088420127094169300,\\
1504.90120266375311107163647228&<M_0+m-\frac{m^3}{K^2}<
1504.90120266375311107163647229.
\end{aligned}
$$

Consequently the positive gap is certified, with

$$
3.97714738713109019930522069849
< S-\left(M_0+m-\frac{m^3}{K^2}\right)
<3.97714738713109019930522069850,
$$

so this relation violates (*).
The Sage certificate computes $S$ as an exact sum of algebraic square roots
and computes $K^2=(16^4\cdot8^8)^{1/3}$ in the real algebraic field; it is
finite computational evidence, not a general proof or a Lean theorem.

This is precisely a high-mass **relaxation** counterexample.  It does not
refute (*) for scalar caps.  It does show that projection spread, heavy-fiber
counts, degree $\le r$, the Jensen lower bound for $M_0$, and even ordinary
3-AP-freeness of every row and every column cannot prove (*).  A successful
phase-sensitive or restriction estimate must use the mixed-fiber scalar
condition $T=m$, equivalently exclude carry-coupled progressions such as
$0,9,18$, rather than merely impose one-dimensional fiber restrictions.  The
condition $T=m$ itself is not a new estimate: on scalar caps it is exactly the
signed cancellation $R=m-M_0$, and using only that signed equality returns the
prior tautology.  The still-needed ingredient is a nontrivial distributional
consequence of mixed-fiber AP exclusion.

## 10. Stopping evidence and next requirement

The explicit $N=16$ relation rules out any proof of (*) based only on
projection spread, heavy-fiber counts, degree bounds, Jensen's $M_0$ bound,
or ordinary 3-AP-freeness of each row and column.  The scalar-cap
high-mass candidate remains open: this relation is not a scalar-cap
counterexample, and the required mixed-fiber/carry exclusion has not yet been
converted into a distributional estimate.

The current facts include the exact visible-measure organization and the
mandatory scalar-realizability split in §3A, as well as projection spread and
near-cancellation of the signed nonzero sum.  Pair-energy, row/column degree,
and related phase-blind estimates remain insufficient: the split yields only
mass control for $\eta$, while the candidate needs the exact deficit
$m^3/K^2$ from the baseline $M_0+m$.  In the high-mass range $m\ge K$ this
is at least $m$, with equality at $m=K$, and it need not put $S$ below $M_0$.
A disproof
would require an actual high-mass scalar cap, either a finite exact example
with the exact value of $r_3(N)$ or an infinite family.  Any successful
phase-sensitive route must instead exploit a nontrivial distributional
consequence of the mixed-fiber condition $T=m$, not the signed equality alone.

This note makes no novelty claim, and no issue was filed.  Its status is
therefore a precisely delimited open Fourier lane: the exact identity is
established, the relaxation obstruction is certified computationally, the
scalar-cap candidate is open, and neither the unrestricted examples nor the
computations decide the high-mass scalar question.
