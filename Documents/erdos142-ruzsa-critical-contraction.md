# Erdős 142: the Ruzsa critical-contraction reduction

This note records a conditional reduction, not **P**, and makes no novelty claim. Use natural logarithms; \(r_3(N)\) is the largest 3AP-free subset of \(\{0,\ldots,N-1\}\), and write
\[
 r(N)=r_3(N),\quad \lambda(N)=\log\frac N{r(N)},\quad
 R_2(N)=\max\{|A|:A\subseteq\{0,\ldots,N-1\}^2\text{ has no nonconstant coordinatewise 3AP}\}.
\]
Put \(\Delta_2(N)=\log(N^2/R_2(N))\) and \(X(N)=\log(r(N)^2/r(N^2))\).

## The reduction

Let \(A\) be an extremal set for \(R_2(N)\), with \(n=|A|\). Apply Ruzsa’s theorem for a finite 3AP-free set of size \(n\) in a torsion-free abelian group:
\[
 |A+A-A-A|\geq \frac{n^2}{4r(n)}.
\]
Here this is used precisely as reproduced in *Sumsets and Structure*, Ch. 2, §9, Theorem 9.1 (the source cited there as Ruzsa, “Arithmetical progressions and the number of sums,” *Period. Math. Hung.* 25 (1992), 105–111, DOI [10.1007/BF02454387](https://doi.org/10.1007/BF02454387)). The original publisher pages were not independently inspected.

Since \(A+A-A-A\subseteq[-2N+2,2N-2]^2\),
\[
 R_2(N)^2\leq4(4N-3)^2r(R_2(N))\leq64N^2r(R_2(N)),
\]
so
\[
 \Delta_2(N)\geq\lambda(R_2(N))-\log64. \tag{1}
\]
For \(x\geq y\geq1\), interval partitioning gives
\[
 r(x)\leq\lceil x/y\rceil r(y)\leq2(x/y)r(y),
 \qquad \lambda(x)\geq\lambda(y)-\log2. \tag{2}
\]
If \(B\subseteq\{0,\ldots,N-1\}\) is extremal, \(B\times B\) is a coordinatewise cap, hence \(R_2(N)\geq r(N)^2\). Equations (1)–(2) yield
\[
 \Delta_2(N)\geq\lambda(r(N)^2)-\log128. \tag{3}
\]

Now digitize a scalar set by \(m=x+Ny\). Any coordinatewise vector 3AP maps to an integer 3AP, so digitizing a scalar AP-free \(S\subseteq\{0,\ldots,N^2-1\}\) gives a vector cap and
\[
 r(N^2)\leq R_2(N). \tag{4}
\]
Only this vector-to-integer implication is used. The converse fails: integer carries give \(x_1+x_3-2x_2=tN\), \(y_1+y_3-2y_2=-t\), with \(t=\pm1\) as well as \(t=0\).

Consequently, the uniformly quantified scalar hypothesis, for fixed \(\eta>0\), \(K\), and \(N_0\),
\[
 \forall N\geq N_0,\qquad \lambda(r(N)^2)\geq(1+\eta)\lambda(N)-K, \tag{H}
\]
implies
\[
 r(N^2)\leq128e^K r(N)^{1+\eta}N^{1-\eta}\qquad(N\geq N_0). \tag{5}
\]
Indeed, (3) and (H) lower-bound \(\Delta_2\), and exponentiating the lower bound on \(\Delta_2\) and using (4) gives (5). Also \(X(N)\geq\Delta_2(N)-2\lambda(N)\), hence
\[
 X(N)\geq-(1-\eta)\lambda(N)-K-\log128,
\]
which is the logarithmic form of (5).

## Eight-part contract

1. **Quantifiers.** (H) has one fixed \(\eta,K,N_0\) and holds for every \(N\geq N_0\); the conclusion has the same eventual quantifier. For repository **P**, take \(0<\eta\leq\sqrt2-1\) and \(C=128e^K\). No restriction on \(\eta\) is algebraically needed for (5).
2. **Modality and source.** This is a sufficient conditional reduction (a strong intermediate, not an equivalent reformulation). Ruzsa is an external input, used exactly through the reproduction and citation above; neither (H) nor **P** is proved here.
3. **Additive/carry structure.** The Ruzsa support is the fourfold set \(A+A-A-A\), with four independent elements, not the ternary support \(a_1+a_3-2a_2\). No entropy assertion is involved. Scalar digit equations have all three carry modes, including \(t=\pm1\).
4. **\(\lambda/X\) implication.** The actual output is (5), equivalently the displayed lower bound on \(X\), not an assertion that scalar regularity is equivalent to **P**.
5. **Constants and \(\eta\).** Ruzsa contributes \(4\); together with the endpoint box this gives \(64\), and the interval partition contributes the extra factor \(2\), giving \(128\). Under the Behrend model \(\lambda\approx c\sqrt{\log N}\), (H) predicts \(1+\eta\leq\sqrt2\); at the endpoint there is no leading-order slack, so constant losses matter.
6. **Stress tests.** Products \(B\times B\) establish the lower comparison; Ruzsa’s whole-set step covers unequal fibers and assumes no equal-fiber structure. Endpoint counts and the ceiling in (2) explain the constants. The comparison model \(r(N)\approx N/\log N\) fails both (H) and **P**. The contraction is exactly \(N^2\to r(N)^2\), whose factor \(\exp(2\lambda(N))\) is critical under the accepted EHPS envelope; accepted subcritical growing-dilation regularity does not prove (H).
7. **Falsifier/termination.** An unbounded family violating (H) for every fixed \((\eta,K,N_0)\), or a theorem contradicting (H), stops this route. Finite computations do not refute an eventual statement. This note stops at the conditional reduction.
8. **Minimal Lean artifact.** Formalize only the abstract arithmetic implication “(3), (4), and (H) imply (5)” over ordered positive reals (with `128 * exp K`); keep Ruzsa’s theorem and the extremal/additive argument external. No Lean formalization of **P** or entropy is claimed.
