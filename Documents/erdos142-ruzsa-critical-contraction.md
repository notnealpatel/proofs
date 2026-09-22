# Erdős 142: dominated Ruzsa route—closed by a direct audit

This is a route-closure audit, not **P**, and makes no novelty claim. Use natural logarithms; let \(r(N)=r_3(N)\) be the largest 3AP-free subset of \(\{0,\ldots,N-1\}\), and put
\[
 \lambda(N)=\log\frac N{r(N)},\qquad
 R_2(N)=\max\{|A|:A\subseteq\{0,\ldots,N-1\}^2\text{ has no nonconstant coordinatewise 3AP}\},
\]
\(\Delta_2(N)=\log(N^2/R_2(N))\) and \(X(N)=\log(r(N)^2/r(N^2))\). **The Ruzsa step is unnecessary: elementary carry-free encoding and interval partitioning give a strictly stronger bound.**

## The independent direct reduction

For a vector-3AP-free \(A\), define
\[
 f(x,y)=x+(2N-1)y.
\]
This is injective: equality of two values makes the difference of the \(x\)-coordinates, whose absolute value is at most \(N-1\), a multiple of \(2N-1\). If three image values form a scalar 3AP, then
\[
 (x_1+x_3-2x_2)+(2N-1)(y_1+y_3-2y_2)=0.
\]
The first parenthesis has absolute value at most \(2N-2<2N-1\), so both coordinate defects vanish. The vector triple is therefore constant, and \(f(A)\) is scalar-3AP-free. Its image is contained in an interval of at most \(2N^2\) integers (indeed its endpoint span is \(2N^2-2N\)). Interval partitioning, \(r(x)\le\lceil x/y\rceil r(y)\le2(x/y)r(y)\) for \(x\ge y\ge1\), therefore gives
\[
 R_2(N)\le r(2N^2)\le2r(N^2),\qquad
 \Delta_2(N)\ge\lambda(N^2)-\log2. \tag{D1}
\]
Since \(N^2\ge r(N)^2\), the same partitioning gives \(\lambda(N^2)\ge\lambda(r(N)^2)-\log2\), and thus
\[
 \boxed{\Delta_2(N)\ge\lambda(r(N)^2)-\log4.} \tag{D2}
\]
This argument is independent of Ruzsa and is the quantitative closure of that lead.

For fixed \(\eta>0,K\), assume the eventual hypothesis
\[
 \forall N\ge N_0,\qquad \lambda(r(N)^2)\ge(1+\eta)\lambda(N)-K. \tag{H}
\]
The canonical scalar conclusion follows directly, with no vector intermediate:
\[
 r(N^2)\le2e^K r(N)^{1+\eta}N^{1-\eta}. \tag{P}
\]
The same hypothesis gives the stronger vector statement only with the worse constant
\[
 R_2(N)\le4e^K r(N)^{1+\eta}N^{1-\eta}.
\]
Thus (H) is a strong sufficient condition for **P**, not an equivalent reformulation; the stronger-intermediate classification is independent reduction \((H)\Rightarrow(P)\) versus the separately proved \((H)\Rightarrow\) the displayed \(R_2\) bound.

## Rejected but valid Ruzsa lead

For completeness, the source result and its calculation remain recorded. Apply Ruzsa’s theorem for a finite 3AP-free set of size \(n\) in a torsion-free abelian group:
\[
 |A+A-A-A|\geq\frac{n^2}{4r(n)}.
\]
Here this is used precisely as reproduced in *Sumsets and Structure*, Ch. 2, §9, Theorem 9.1 (the source cited there as Ruzsa, “Arithmetical progressions and the number of sums,” *Period. Math. Hung.* 25 (1992), 105–111, DOI [10.1007/BF02454387](https://doi.org/10.1007/BF02454387)). The original publisher pages were not independently inspected. For \(n=R_2(N)\), the fourfold sumset lies in \([-2N+2,2N-2]^2\), so
\[
 n^2\le4(4N-3)^2r(n)\le64N^2r(n),\quad
 \Delta_2(N)\ge\lambda(n)-\log64.
\]
Using \(n\ge r(N)^2\) and interval partitioning recovers only
\[
 \Delta_2(N)\ge\lambda(r(N)^2)-\log128. \tag{R}
\]
The old scalar transfer here was base-\(N\) digitization: a scalar AP-free set in \(\{0,\ldots,N^2-1\}\), written \(x+Ny\), is a vector cap, so \(r(N^2)\le R_2(N)\). Thus (R) and (H) would give the old \(128e^K\) version of (P), equivalently \(X(N)\ge-(1-\eta)\lambda(N)-K-\log128\). The direct \(-\log4\) bound (D2) dominates (R). Ruzsa therefore supplies no bridge toward proving (H), and is a rejected lead, not a productive new mechanism. The four summands are independent elements in \(A+A-A-A\), not the ternary defect \(a_1+a_3-2a_2\); no entropy assertion is hidden here.

## Eight-part contract/audit

1. **Quantifiers and status.** One fixed \(\eta,K,N_0\) in (H) applies for every \(N\ge N_0\), with the same eventual quantifier in (P). (H) remains an unproved strong sufficient condition at the critical contraction; this is conditional and makes no claim to prove **P**.
2. **Independent routes.** Combined with (H), direct interval partitioning proves **P**, while carry-free encoding gives the stronger \(R_2\) intermediate with constant \(4e^K\). Ruzsa is valid but dominated; neither route makes (H) necessary, so there is no equivalence.
3. **Constants and directions.** Direct constants are \(2\) for the image/partition step and \(4\) in (D2); the vector conclusion is \(4e^K\). The rejected route is \(4\), then \(64\), then \(128\). Base-\(N\) digitization has carry directions \(x_1+x_3-2x_2=tN\), \(y_1+y_3-2y_2=-t\), with \(t=\pm1\) as well as \(0\); the \(2N-1\) map is carry-free.
4. **Products and fibers.** \(B\times B\) gives \(R_2(N)\ge r(N)^2\). The whole-set Ruzsa argument does not assume equal fibers and covers unequal fibers; endpoints and ceilings account for every factor \(2\).
5. **Models and criticality.** Under Behrend-type \(\lambda(N)\approx c\sqrt{\log N}\), (H) predicts \(1+\eta\le\sqrt2\), with no leading-order endpoint slack. The comparison \(r(N)\approx N/\log N\) fails (H) and **P**. The contraction \(N^2\to r(N)^2\) is critical under the accepted EHPS envelope; accepted subcritical growing-dilation regularity does not prove (H).
6. **Carry/endpoint checks.** The image endpoint span is \(2N^2-2N\), hence at most \(2N^2\) integer points; interval partitioning applies because \(N^2\ge r(N)^2\). These checks include unequal fibers, products, and all relevant \(N\)- and \(\log N\)-scale losses.
7. **Exact falsifier and termination.** An unbounded family violating (H) for every fixed \((\eta,K,N_0)\), or a theorem contradicting (H), falsifies this conditional route. Finite computations do not refute an eventual assertion; absent such a falsifier, the audit terminates here.
8. **Minimal Lean artifact.** Formalize only the ordered-positive-real arithmetic from (H) and the direct inequalities to obtain (P) and the \(4e^K\) vector bound (including `128 * exp K` only if the rejected calculation is retained). Keep Ruzsa, extremal sets, carries, and **P** itself external; claim no Lean formalization of entropy or equivalence.
