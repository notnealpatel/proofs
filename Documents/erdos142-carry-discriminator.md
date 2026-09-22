# Erdos 142: repository-specific k=3 route target — carry discriminator and route audit

> **Status.** This is partial progress, not a solution. It records the exact proposed intermediate statement, the carry bookkeeping it would have to control, and a one-scale obstruction to a particularly tempting LP route. It is a written contract and route audit before Lean proof work; it does not claim novelty. P is a repository-specific k=3 route target, not the canonical Erdős #142 problem, which asks for an asymptotic formula for \(r_k\).

## 1. The proposed unconditional target

Write
\[
 r_3(M)=\max\{|A|:A\subseteq [M]\text{ contains no nontrivial 3-term arithmetic progression}\},
\]
where the choice of the interval convention (for example \([M]=\{0,\ldots,M-1\}\)) is fixed throughout. The proposed statement, called **P**, is the following exact quantifier pattern:

\[
\exists C>0,\ \exists\eta\ (0<\eta\leq \sqrt 2-1),\ \exists N_0,\ \forall N\geq N_0,
\qquad
r_3(N^2)\leq C\,r_3(N)^{1+\eta}N^{1-\eta}.
\tag{P}
\]

The intended status of P is unconditional: it is not to be introduced as a hypothesis in a formal proof, and no conditional consequence should be presented as if P had been proved. The immediate mathematical task is to determine whether a genuine unequal-fiber carry-supersaturation lemma can establish it.

For bookkeeping, put
\[
 \lambda(N)=\log\frac{N}{r_3(N)},\qquad
 X(N)=\log\frac{r_3(N)^2}{r_3(N^2)}.
\]
Taking logarithms of P gives the two useful consequences
\[
 \lambda(N^2)\geq (1+\eta)\lambda(N)-\log C,
 \tag{1}
\]
and
\[
 X(N)\geq -(1-\eta)\lambda(N)-\log C.
 \tag{2}
\]
Equation (2) is not the full square-scale objective \(X(N)\geq-o(\sqrt{\log N})\). P is logically incomparable with that objective without additional information on the size and regularity of \(\lambda\): P is a fixed-power inequality, while the latter is an asymptotic lower bound on a different error term. As a synthetic comparison-function stress test, take \(r(N)=N/\log N\). Then
\[
 X_r(N)= -\log\log N+O(1)=o(\sqrt{\log N}),
\]
so the corresponding normalized square-scale behavior can hold, but the P-shaped inequality fails for this function: its right side is of order \(N^2/(\log N)^{1+\eta}\), whereas \(r(N^2)\asymp N^2/(2\log N)\). This synthetic comparison function is used only to prove formal non-equivalence of the estimate shapes, not as a model of the actual Roth numbers. Thus neither slogan “square-scale control” nor (2) may be substituted for P. Since \(C r_3(N)^{1+\eta}N^{1-\eta}=C N^2 \rho^{1+\eta}=C \rho^\eta N r_3(N)\), P asks for a factor \(\rho^{1+\eta}\) relative to ambient \(N^2\), or equivalently an additional factor \(\rho^\eta\) relative to the slicing baseline \(N r_3(N)\). Roth implies P is \(o(N r_3(N))\), but the converse is weaker and not equivalent because an arbitrary little-o need not have a fixed power rate.

The quantifier order matters operationally. One first fixes a single \(\eta\), then a single constant \(C\), and only then is allowed to discard finitely many scales by choosing \(N_0\). A scale-dependent \(\eta_N\), a constant that grows with the number of carry types, or a statement holding only along a favorable subsequence is a different assertion. Likewise, estimates proved for an arbitrary set with balanced fibers do not imply P unless an additional reduction handles the unbalanced fibers without changing the exponent.

## 2. Digits, carries, and what must actually be counted

Represent each point of \([N^2]\) in base \(N\) as
\[
 n=x+Ny,\qquad 0\leq x,y<N.
\]
For a scalar 3-term progression \(n_i=x_i+Ny_i\), the equation \(n_1+n_3=2n_2\) is equivalent to
\[
 x_1+x_3-2x_2=tN,\qquad y_1+y_3-2y_2=-t,
 \qquad t\in\{-1,0,1\}.
 \tag{3}
\]
These are three distinct carry modes, not three optional descriptions of one coordinatewise argument. The mode \(t=0\) is the no-carry case; \(t=1\) and \(t=-1\) are the two opposite carry directions. All three must be included, with the nontriviality condition on the scalar progression. The restriction to these values follows from the digit ranges: the first expression is a multiple of \(N\), while the second is an integer in the corresponding short range; the putative larger carries cannot satisfy both equations for a nontrivial progression in the base-\(N\) box. Conversely, whenever digits satisfy (3), adding the two equations recovers the scalar equation, so no scalar edge may be discarded merely because its coordinate projections are not progressions of the same type.

For counting, it is useful to regard (3) as a three-part incidence problem: a choice of the middle digit pair, a choice of the carry mode, and compatible endpoint digits. The endpoint choices for \(t=1\) are not the same as those for \(t=-1\), and boundary truncation makes their fiber multiplicities unequal even before restricting to \(A\). Any supersaturation statement must therefore specify whether it counts ordered triples or unoriented edges, how boundary points are weighted, and where the no-carry and carry contributions are combined. Those conventions affect constants, but they cannot remove the need to count all three modes.

If \(A\subseteq[N^2]\), its digit fibers are
\[
 A_y=\{x<N:x+Ny\in A\}.
\]
There is no reason for the fibers \(A_y\) to have equal size, or for the three fibers participating in (3) to have comparable density. A proof that averages a one-dimensional estimate over rows and silently replaces the fibers by a common model loses precisely the information needed to distinguish the carries. For a fixed mode, a triple can lie in three different fibers, and its admissibility is a coupled condition on those fibers. The correct stress test is the Cartesian-product test: substitute \(A=B+N D=\{x+Ny:x\in B,y\in D\}\), and compute contributions from each of the three values of \(t\) separately. Any proposed fiber inequality must survive this test, as well as versions with deliberately unequal fiber sizes; a coordinatewise estimate that sees only \(B\) and \(D\) independently is not yet a scalar estimate on \([N^2]\).

Small cases make the warning concrete. Conceptually, \(r_3(1)=1\), \(r_3(2)=2\), and \(r_3(3)=2\) under the convention above. For \(N=1\), every digit is zero and only the vacuous \(t=0\) equation can occur. For \(N=2\), the scalar edges \((0,1,2)\) and \((1,2,3)\) exhibit respectively \(t=-1\) and \(t=1\). For \(N=3\), \((0,1,2)\) exhibits \(t=0\), while translated progressions such as \((1,2,3)\) and \((5,6,7)\) exhibit the two carry directions. These checks are conceptual sanity checks, not evidence for P. In particular, “independent slicing” that counts only coordinatewise progressions is not equivalent to counting all scalar progressions.

## 3. Parameter audit

The parameter \(\eta\) in P must be fixed once and for all in
\[
 0<\eta\leq\sqrt2-1.
\]
There is no free moment parameter, DRC parameter, or scale-dependent choice left to optimize after P is stated. The endpoint is forced by the model calculation. If
\[
 r_3(N)\approx N\exp(-c\sqrt{\log N}),
\]
then the logarithms of the two sides of P, after cancelling \(2\log N\), have square-root terms \(-c\sqrt{2\log N}\) and \(-(1+\eta)c\sqrt{\log N}\), respectively. Compatibility is exactly
\[
 1+\eta\leq\sqrt2,
\]
that is, \(\eta\leq\sqrt2-1\). The smooth model above fails for every fixed \(\eta>0\).

The upper restriction is also visible by iteration, and is not merely a feature of the model. If P holds and \(a=1+\eta\), (1) iterated at \(N,N^2,N^4,\ldots\) gives, up to the geometric accumulation of \(\log C\),
\[
 \lambda(N^{2^k})\ \geq\ a^k\lambda(N)-\log C\,\frac{a^k-1}{a-1}.
\]
Against the accepted EHPS/Behrend-type lower-bound input from the repository frontier, namely the upper bound \(\lambda(M)=O(\sqrt{\log M})\), and the condition \(\lambda(N)\to\infty\), choosing a starting scale with a sufficiently large deficit forces \(a\leq\sqrt2\); otherwise the lower bound grows faster than \(\sqrt{\log(N^{2^k})}=2^{k/2}\sqrt{\log N}\). This is a consistency restriction, not a proof of P.

## 4. Falsifiers and stop conditions

A genuine infinite family of integers \(N\) violating P for every proposed fixed triple \((C,\eta,N_0)\), or a contradiction between P and an established theorem, is a falsifier and a stop condition. Finite numerical examples cannot refute an eventual statement with free \(C\) and \(N_0\); they can only refute a proposed uniform finite lemma (for example, a claim asserted for every \(N\) with a specified constant). Synthetic functions or toy fiber systems can refute derivability of P from a collection of abstract inequalities, but they do not refute P for the actual Roth numbers.

None of the bounded set of sources audited below establishes or directly implies P. The missing mathematical input should be named accurately: an **unequal-fiber carry supersaturation lemma** that controls all three equations in (3), rather than a coordinatewise or equal-fiber surrogate. Until such a lemma is supplied, P remains an unconditional target, not an available premise.

## 5. The one-scale LP obstruction

There is a precise reason not to spend the first Lean effort on the most naive linear program. Let
\[
 \rho=\frac{r_3(N)}{N},
\]
and put a variable \(z_v\) on each vertex \(v\in[N^2]\). Include the bounds \(0\leq z_v\leq1\), the inequality
\[
 \sum_{v\in e}z_v\leq2
\]
for every nontrivial scalar 3AP edge \(e\subseteq[N^2]\) (including every carry mode), and, for every injective affine window
\[
 P=\{a+bd:0\leq d<L\}\subseteq[N^2],\qquad 1\leq L\leq N,
\]
include the cap \(\sum_{v\in P}z_v\leq r_3(L)\). “Injective” means \(b\neq0\) and the displayed points are distinct and in the interval; without it, the cap is not the claimed one-dimensional constraint. These window inequalities are valid because the preimage of a 3AP-free subset of an injective affine copy of \([L]\) is 3AP-free.

The uniform assignment
\[
 z_v=\rho/2\qquad(v\in[N^2])
\]
is feasible for exactly these constraints. Indeed, the elementary window covering bound
\[
 r_3(N)\leq\left\lceil\frac NL\right\rceil r_3(L),
 \qquad \left\lceil\frac NL\right\rceil\leq\frac{2N}{L}
\]
for \(1\leq L\leq N\) implies \(L\rho/2\leq r_3(L)\). Every edge has uniform sum \(3\rho/2\leq3/2<2\), and the vertex bounds are immediate. Its objective value is
\[
 \sum_{v\in[N^2]}z_v=N^2\frac{\rho}{2}=\frac{N r_3(N)}2.
\]
Therefore weak duality says that no nonnegative linear combination—equivalently, no ordinary LP dual certificate—formed from exactly these constraints can prove an upper bound \(o(Nr_3(N))\) for the LP objective: the feasible point already has a constant fraction of \(Nr_3(N)\). This is directly relevant to P because Roth's theorem gives \(\rho\to0\), while the P bound equals
\[
 C r_3(N)^{1+\eta}N^{1-\eta}=C\rho^\eta\,N r_3(N)=o(Nr_3(N)).
\]
Thus this LP route cannot prove P by dual certification alone. More explicitly, a putative dual proof would assign nonnegative multipliers to the edge, window, and box inequalities and combine them to dominate the all-ones objective coefficientwise. Weak duality would then upper-bound every feasible objective by the resulting dual value. The displayed uniform feasible point forces every such valid upper bound to be at least \(Nr_3(N)/2\), regardless of how cleverly the constraints are combined. Adding the three carry modes one at a time does not change this conclusion, because the uniform edge calculation already checks every edge.

The obstruction does **not** rule out integrality, higher-order valid inequalities, nonlinear arguments, semidefinite or lifted hierarchies, windows with \(L>N\), or the actual statement P. It is only a one-scale obstruction to the explicitly listed relaxation; it also does not claim novelty. In particular, an argument using correlations among many windows, or a supersaturation theorem that is not a linear consequence of these caps, lies outside this stop condition and remains mathematically possible.

## 6. Smallest worthwhile Lean artifact and literature resolution

The smallest useful formal artifact is the elementary one-scale lemma
\[
 1\leq L\leq N\quad\Longrightarrow\quad
 L\,r_3(N)\leq 2N\,r_3(L),
 \tag{4}
\]
written with the project’s natural-number definition. In Lean-facing notation its core conclusion is `L * rothNumberNat N <= 2 * N * rothNumberNat L`, under the hypotheses `1 <= L` and `L <= N`. It packages the ceiling estimate used above. Real-valued corollaries for \(\rho\), the uniform LP assignment, and the weak-duality lower obstruction may be added if they simplify later work. P itself should not be formalized as a hypothesis merely to make downstream statements compile.

The bounded literature pointers audited here are: Kelley–Meka, [arXiv:2302.05537](https://arxiv.org/abs/2302.05537), for the modern quantitative Roth bound; Bloom–Sisask, [arXiv:2309.02353](https://arxiv.org/abs/2309.02353) (and the earlier [arXiv:2007.03528](https://arxiv.org/abs/2007.03528)), for related quantitative progression technology; Croot–Sisask/Varnavides, [arXiv:0801.2577](https://arxiv.org/abs/0801.2577), for the almost-periodicity/Varnavides framework; Milićević, “skew corners,” [arXiv:2404.07180](https://arxiv.org/abs/2404.07180), for a related but differently structured multidimensional configuration; and Diaconis–Shao–Soundararajan, [arXiv:1309.0434](https://arxiv.org/abs/1309.0434), for carry phenomena in a probabilistic digit setting. These pointers motivate the audit and delimit analogies; none is being cited as support for the LP lemma or as a theorem implying P. The next honest proof milestone is therefore (4), followed by an explicit unequal-fiber carry lemma—or a documented stop if that lemma cannot be obtained.
