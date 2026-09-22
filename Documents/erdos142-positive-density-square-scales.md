# Erdős #142: a positive-density square-scale consequence

This is a mathematical consequence of the external Raghavan estimate below and the elementary square inequality below, **not** the proposed statement P, not an asymptotic formula, and not a Lean theorem. Let
\[
 r_3(N)=\max\{|A|:A\subseteq\{1,\ldots,N\},\ A\text{ has no nontrivial 3-term progression}\},
 \qquad
 \lambda(N)=\log\frac{N}{r_3(N)}.
\]
The interval convention is immaterial here, provided it is fixed. All logarithms are natural unless a subscript is displayed.

## External input and exact square towers

We use, and do not formalize in Lean, Rushil Raghavan, *Improved Bounds for 3-Progressions*, [arXiv:2603.27045v3 (15 May 2026)](https://arxiv.org/abs/2603.27045v3), Theorem 1.4, a preprint and external/non-Lean input. Its source theorem is for all \(N\), with some \(c>0\), and gives
\[
 r_3(N)\leq N\exp\!\left(-c\,(\log N)^{1/6}(\log\log N)^{-1/6}\right).
\]
Hence eventually for all \(N\),
\[
 \lambda(N)\geq c\frac{(\log N)^{1/6}}{(\log\log N)^{1/6}},\qquad
 \log\lambda(N)\geq\tfrac16\log\log N-\tfrac16\log\log\log N+O(1). \tag{R}
\]
The denominator is essential: this does not imply a pure \(c(\log N)^{1/6}\) bound. The theorem/source is cited rather than the abstract, whose loglog exponent is stale. Roth's theorem separately gives \(\lambda(N)\to\infty\).

Fix an integer \(B\geq2\), put \(N_k=B^{2^k}\), and write \(a_k=\lambda(N_k)\). The elementary accepted parity-product bound is
\[
 r_3(N)^2\leq 2r_3(N^2).
\]
Indeed, rearranging it in terms of \(\lambda\) gives
\[
 \lambda(N^2)=\log\frac{N^2}{r_3(N^2)}
 \leq \log2+2\log\frac{N}{r_3(N)}
 =2\lambda(N)+\log2.
\tag{1}
\]
Thus (1) is not an unsupported input. Consequently, after discarding finitely many indices so that all \(a_k>0\), for every \(\varepsilon>0\) we have
\[
 \frac{a_{k+1}}{a_k}\leq2+\varepsilon
\tag{2}
\]
for all sufficiently large \(k\): indeed, use (1) and \(\log2/a_k\leq\varepsilon\). On the other hand, (R) gives the exact eventual consequence
\[
 a_k\geq c\,\frac{(\log B)^{1/6}2^{k/6}}{(k\log2+\log\log B)^{1/6}}
 \geq c'\frac{2^{k/6}}{k^{1/6}}
\tag{3}
\]
for all sufficiently large \(k\), where \(c'>0\) depends on \(B\).

## Density of good ratios

Fix \(1<q<2^{1/6}\), and set
\[
 G_q=\{k:a_{k+1}\geq q a_k\}.
\]
Choose \(k_0\) after both eventual statements above hold. For \(K>k_0\), let
\(g_K=|G_q\cap\{k_0,\ldots,K-1\}|\). Multiplying the ratios over this prefix, using a factor less than \(q\) at a bad index and (2) at a good index, gives
\[
 a_K\leq a_{k_0}\,q^{K-k_0-g_K}(2+\varepsilon)^{g_K}.
\tag{4}
\]
Combining (4) with (3), taking logarithms, and dividing by \(K\), yields explicitly
\[
 \frac{1}{K}\log a_K\geq \frac16\log2-\frac16\frac{\log K}{K}+o(1).
\]
The exact correction \(-\tfrac16(\log K)/K=o(1)\) is retained in this averaged logarithm. Therefore, after rearranging (4),
\[
 \liminf_{K\to\infty}\frac{|G_q\cap\{0,\ldots,K-1\}|}{K}
 \geq
 \frac{\frac16\log2-\log q}{\log(2+\varepsilon)-\log q}.
\]
The finitely many indices below \(k_0\) do not affect the liminf. Since this holds for every \(\varepsilon>0\), let \(\varepsilon\downarrow0\) to obtain
\[
 \boxed{\displaystyle
 \liminf_{K\to\infty}\frac{|G_q\cap\{0,\ldots,K-1\}|}{K}
 \geq
 \delta(q):=\frac{1/6-\log_2q}{1-\log_2q}>0.}
\tag{5}
\]
This is a product-of-ratios argument; the additive \(\log2\) in (1) is handled by eventual positivity and (2), rather than silently discarded.

## Exact translation to a P-shaped inequality

For \(N=N_k\), direct rearrangement gives the exact equivalence
\[
 k\in G_q
 \quad\Longleftrightarrow\quad
 r_3(N^2)\leq r_3(N)^qN^{2-q}.
\tag{6}
\]
Writing \(q=1+\eta\), this is
\[
 r_3(N^2)\leq r_3(N)^{1+\eta}N^{1-\eta},
\]
that is, the P-shaped inequality with \(C=1\), on the set of good tower indices. Here
\[
 0<\eta<2^{1/6}-1.
\]
Therefore, for every such fixed \(\eta\), the \(C=1\) inequality holds on a positive-lower-density set of indices along every fixed square tower. It does **not** assert that the inequality holds for all sufficiently large \(N\), and hence does not prove P.

Since (5) in particular gives infinitely many good indices, and \(q\) may tend upward to \(2^{1/6}\), we get the genuine square-scale conclusion
\[
 \boxed{\displaystyle
 \limsup_{N\to\infty}\frac{\lambda(N^2)}{\lambda(N)}\geq2^{1/6}.}
\tag{7}
\]
Equivalently, with
\[
 X(N)=\lambda(N^2)-2\lambda(N),
\]
(6) says on a good scale
\[
 X(N)\geq-(2-q)\lambda(N).
\tag{8}
\]
This is not the claim \(X(N)\geq-o(\sqrt{\log N})\); the two estimates must not be conflated.

## Limitations

* The density in (5) is density in the tower index \(k\), not natural density or logarithmic density of the integers \(N\).
* Positive index density gives neither bounded gaps nor an all-large-\(N\) statement.
* No equality or sharpness is claimed for the actual Roth numbers, and no full P is proved.
* (R) is an external preprint input, not a Lean-formalized repository theorem.
* The argument bridges the square scale \(M=N\) to a genuine limsup lower bound, but gives no liminf/limsup separation unless a strict upper or lower counterpart is proved.
