# Log-log density of square scales

Put \(r(N)=r_3(N)\), where \(r_3(N)\) is the maximum size of a nontrivial-3AP-free subset of \(\{1,\ldots,N\}\). Translation identifies this with Lean `rothNumberNat N` on `Finset.range N`. Also put \(\lambda(N)=\log(N/r(N))\), and
\[
w_n=\log\log(n+1)-\log\log n.
\]
All logarithms below are natural unless a subscript is displayed. Fix \(1<q<2^{1/9}\), and let \(G_q=\{n\ge3:\lambda(n^2)\ge q\lambda(n)\}\). Then
\[
 \liminf_{M\to\infty}\frac{\displaystyle\sum_{\substack{3\le n\le M\\n\in G_q}}w_n}{\log\log M}
 \ge \delta(q):=\frac{1/9-\log_2q}{1-\log_2q}>0. \tag{1}
\]

More precisely, define
\[
 S(M)=\sum_{3\le n\le M}w_n\log_2\frac{\lambda(n^2)}{\lambda(n)}.
\]
The stronger asymptotic weighted-sum identity is
\[
 S(M)=\log\lambda(M+1)+o(\log\log M). \tag{2}
\]
The right side is a natural logarithm: there is no factor \(1/\log2\), because the endpoint window has length \(h=\log2\), which cancels that factor.

## Proof

Set \(h=\log2\), \(n(x)=\lfloor e^{e^x}\rfloor\), \(a(x)=\lambda(n(x))\), and \(b(x)=a(x)+2h\). For \(z=e^{e^x}\), write \(n=n(x)\) and \(m=n(x+h)=\lfloor z^2\rfloor\). Eventually \(n^2\le m<2n^2\), so monotonicity and restriction to two intervals give
\[
 r(n^2)\le r(m)\le2r(n^2),\qquad |\lambda(m)-\lambda(n^2)|\le h. \tag{3}
\]
The accepted cardinal theorem `rothNumberNat_sq_le_two_mul_rothNumberNat_sq` gives \(\lambda(n^2)\le2\lambda(n)+h\), hence
\[
 a(x+h)\le2a(x)+2h,\qquad b(x+h)\le2b(x). \tag{4}
\]
Also \(r(n^2)\le nr(n)\), so \(\lambda(n^2)\ge\lambda(n)\).

Define, for large \(x\),
\[
 C(x)=\log_2\frac{\lambda(n(x)^2)}{\lambda(n(x))},\qquad
 D(x)=\log_2\frac{b(x+h)}{b(x)},\qquad L(x)=\log b(x).
\]
The accepted qualitative Roth theorem gives \(\lambda(N)\to\infty\) (this is not Bloom--Sisask). Thus (3), (4), and the additive shift imply the existing estimate
\[
 C(x)-D(x)=o(1) \quad\text{uniformly as }x\to\infty, \tag{5}
\]
and \(0\le C(x)\le1+o(1)\). Bloom--Sisask, arXiv:2309.02353, Theorem 1, is used only in its eventual quantitative form \(\lambda(N)\ge c(\log N)^{1/9}\), so \(L(x)\ge x/9+O(1)\).

Let \(T=\log\log(M+1)\) and \(R=\log\log3\). Since \(n(x)=n\) on \([\log\log n,\log\log(n+1))\), (5) and continuous telescoping give
\[
\begin{aligned}
 S(M)&=\int_R^T C(x)\,dx+o(T)\\
 &=\frac1h\int_T^{T+h}L(y)\,dy+o(T). \tag{6}
\end{aligned}
\]
(The fixed initial endpoint term is absorbed.) To evaluate this endpoint, put \(N=M+1\). For \(y\in[T,T+h]\), \(m=n(y)\) lies in \([N,N^2]\). Interval subadditivity gives
\[
 r(m)\le\lceil m/N\rceil r(N),\qquad r(N^2)\le\lceil N^2/m\rceil r(m),
\]
and \(\lceil t\rceil\le2t\) for \(t\ge1\) gives the displayed bounds in (7). Therefore
\[
 \lambda(N)-h\le\lambda(m)\le\lambda(N^2)+h\le2\lambda(N)+2h. \tag{7}
\]
Since \(\lambda(N)\to\infty\), uniformly on this window \(\log b(y)=\log\lambda(N)+O(1)\). Substitution in (6) proves (2), with the endpoint length \(h\) cancelling the prefactor \(1/h\).

Bloom--Sisask and (2) yield the existing conclusion
\[
\liminf_{M\to\infty}S(M)/\log\log M\ge1/9. \tag{8}
\]
Using \(\alpha=\log_2q\), the envelope \(0\le C\le1+o(1)\) and (8) give the lower density \((1/9-\alpha)/(1-\alpha)\) of \(C\ge\alpha\), which is exactly (1). The accepted Behrend/EHPS upper-deficit input—EHPS, arXiv:2406.12290, Theorem 1.1 (as accepted in this repository)—gives \(\lambda(N)=O(\sqrt{\log N})\), and together with (2) additionally gives
\[
 \limsup_{M\to\infty}S(M)/\log\log M\le\tfrac12. \tag{9}
\]
This is an endpoint-effective-exponent reformulation at the weighted-mean level; no novelty claim is made, and it is neither an \(r_3\) asymptotic nor progress toward eventual \(P\).

Finally, \(n\in G_q\) is equivalent to \(r(n^2)\le r(n)^q n^{2-q}\). With \(X(n)=\lambda(n^2)-2\lambda(n)\), this is exactly the accepted Lean `squareScaleDefect` sign (not its opposite), and implies \(X(n)\ge-(2-q)\lambda(n)\). Thus for \(\eta=q-1\), property \(P\) with \(C=1\) holds on a positive log-log weighted-density set; no eventual validity is claimed. No vector-grid reduction is used.

## Eight-part contract/audit

1. **Quantifiers:** every \(1<q<2^{1/9}\) is covered directly; no threshold is lost.
2. **Modality:** Bloom--Sisask supplies only the quantitative lower bound; qualitative Roth, the square-scale inequality, and Behrend/EHPS are accepted inputs.
3. **Exact additive structure:** \(b=a+2h\) gives (4), and floor/interval losses are the fixed \(h\) in (3) and (7).
4. **\(\lambda/X\) implication:** the displayed equivalence and the sign and bound for \(X\) are exact.
5. **Optimization:** the asymptotic identity (2), its lower bound \(1/9\), and \(0\le C\le1+o(1)\) yield \(\delta(q)\).
6. **Models/endpoints:** all scales are good at \(q=1\), so the actual density is \(1\) (the density lower bound \(1/9\) is nonsharp); \(\delta=0\) at \(q=2^{1/9}\). The Behrend-scale model \(\lambda\approx a\sqrt{\log N}\) gives eventual goodness for \(q<\sqrt2\); the accepted Behrend/EHPS theorem here only gives \(\lambda(N)=O(\sqrt{\log N})\). \(N/\log N\) contradicts Bloom--Sisask and is inconsistent.
7. **Falsifier:** the identity would be falsified by a discrepancy of order \(\log\log M\) between \(S(M)\) and \(\log\lambda(M+1)\); the proof only needs accumulated comparison and endpoint errors \(o(\log\log M)\), while the proved errors are \(O(1)\)/uniform \(o(1)\).
8. **Future formalization:** the minimal Lean artifact is an abstract positive-sequence prefix-density lemma; the analytic inputs remain hypotheses. This is an ambient integer weighted-density conclusion, not a formal strengthening or subsumption of the fixed-base tower-density statement.
