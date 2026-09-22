# A local log-log recurrence for square scales

All logarithms in this document are natural, except \(\log_2\). Put
\[
 \lambda(N)=\log\frac{N}{r_3(N)},\qquad
 w_n=\log\log(n+1)-\log\log n,
 \qquad C_n=\log_2\frac{\lambda(n^2)}{\lambda(n)}.
\]
We use the accepted weighted identity
\[
 S(M):=\sum_{3\le n\le M}w_nC_n
   =\log\lambda(M+1)+o(\log\log M),
\]
together with the tail-uniform bounds \(0\le C_n\le1+o(1)\), and the external envelopes
\[
 \tfrac16\log\log M-\tfrac16\log\log\log M+O(1)\le \log\lambda(M)\le
 \tfrac12\log\log M+O(1).                                      \tag{1}
\]
The lower envelope follows from Rushil Raghavan, *Improved Bounds for 3-Progressions*, [arXiv:2603.27045v3 (15 May 2026)](https://arxiv.org/abs/2603.27045v3), Theorem 1.4, a preprint and external/non-Lean input. Its source theorem is for all \(N\), so no odd-to-all-\(N\) conversion is needed. The \(-\tfrac16\log\log\log M\) term is essential: this is not a pure \(\tfrac16\log\log M+O(1)\) lower bound; the theorem/source is cited rather than the stale abstract.

## Theorem

Fix \(\rho>3\). For every real \(T\to\infty\), define, with integer endpoints,
\[
 a(T)=\min\{n\ge3:\log\log n\ge T\},\qquad
 b(T)=\max\{n:\log\log n\le\rho T\}.
\]
For all sufficiently large \(T\), the interval is nonempty, and, writing
\[
 W_T=\sum_{a(T)\le n\le b(T)}w_n,
\]
we have, with liminf taken over all real \(T\),
\[
 W_T=(\rho-1)T+o(T),\qquad
 \liminf_{T\to\infty}\frac{\sum_{a(T)\le n\le b(T)}w_nC_n}{W_T}
 \ge A(\rho):=\frac{\rho/6-1/2}{\rho-1}.                    \tag{2}
\]
Consequently, for every fixed \(0<c<A(\rho)\),
\[
 \liminf_{T\to\infty}
 \frac{\sum_{a(T)\le n\le b(T)}w_n\,\mathbf 1_{\{C_n\ge c\}}}{W_T}
 \ge \frac{A(\rho)-c}{1-c}>0.                              \tag{3}
\]
Thus every sufficiently large multiplicative-log-log window \(T\le\log\log n\le\rho T\) contains such an \(n\), and the set of such \(n\) has positive relative \(w_n\)-weight. For fixed \(0<c<1/6\), this applies whenever
\[
 \rho>\frac{1/2-c}{1/6-c}.
\]
At \(\rho=3\), the mean lower bound in (2) is \(0\), hence vacuous.

## Proof

Minimality and maximality of the endpoints give
\[
 0\le\log\log a-T<w_{a-1},\qquad
 0\le\rho T-\log\log b<w_b.
\]
As \(a(T),b(T)\to\infty\), both right sides tend to zero. Telescoping (with the displayed integer endpoint convention) therefore yields
\[
 W_T=\log\log(b+1)-\log\log a=(\rho-1)T+o(T).             \tag{4}
\]
For large \(T\), subtract the accepted identity at \(M=b\) and at \(M=a-1\):
\[
 \sum_{a\le n\le b}w_nC_n
 =\log\lambda(b+1)-\log\lambda(a)+o(T).                    \tag{5}
\]
Apply the lower envelope in (1) at \(b+1\), and the upper envelope at \(a\). The endpoint estimates above give
\[
 \log\lambda(b+1)-\log\lambda(a)
 \ge \left(\frac\rho6-\frac12\right)T-\tfrac16\log\log\log(b+1)+o(T).
\]
Now \(\log\log(b+1)=\rho T+o(T)\), so explicitly the terminal lower-order term is
\[
 -\tfrac16\log\log\log(b+1)=O(\log T)=o(T),
\]
with \(\log\log\log(b+1)=\log T+O(1)\), not \(\log\log T\). Hence (5) and (4) prove (2), including its asserted all-real-\(T\) liminf.

Let \(E_T=\{n\in[a,b]:C_n\ge c\}\), and let \(q_T=\sum_{E_T}w_n/W_T\). Tail-uniformity supplies \(\varepsilon_T\to0\) with \(C_n\le1+\varepsilon_T\) throughout this window. Since the complement has \(C_n<c\),
\[
 \frac{\sum_{a\le n\le b}w_nC_n}{W_T}
 \le c+(1+\varepsilon_T-c)q_T.
\]
Taking liminfs and using (2) proves (3). Its right side is positive, so eventually \(q_T>0\), proving both the existence and the positive-relative-weight assertions.

Finally, if \(C_n\ge c\) and \(\eta=2^c-1\), then
\[
 \lambda(n^2)\ge(1+\eta)\lambda(n).
\]
A direct expansion of \(\lambda\) gives the equivalent statement
\[
 r_3(n^2)\le n^{1-\eta}r_3(n)^{1+\eta}.
\]
This is a strictly local recurrence on arbitrarily large prescribed log-log windows. It does not imply eventual \(P\), \(D\to0\), or an asymptotic formula. The scalar model \(\lambda(N)=\log\log N\), arising from \(r_3(N)=N/\log N\), violates the present lower envelope and therefore cannot test this conclusion. A Behrend-scale model \(\lambda(N)\sim c\sqrt{\log N}\) has \(C_n\to1/2\) and is compatible with the envelopes, though nonsharp. A falsifier would be a sequence of windows whose means fall below \(A(\rho)\) by a fixed amount; (5) shows that this would contradict the accepted identity or an envelope at order \(T\). The argument terminates at this local recurrence and makes no eventuality claim. See the predecessor document `erdos142-loglog-dense-square-scales.md`. A minimal Lean formalization would first need the accepted weighted identity and envelopes as formal inputs; there is no vacuous-premise theorem here.
