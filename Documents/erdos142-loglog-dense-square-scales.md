# Log-log density of square scales

Put \(r(N)=r_3(N)\), where \(r_3(N)\) is the maximum size of a nontrivial-3AP-free subset of \(\{1,\ldots,N\}\). Translation identifies this with Lean `rothNumberNat N` on `Finset.range N`. Also put \(\lambda(N)=\log(N/r(N))\), and
\[
w_n=\log\log(n+1)-\log\log n.
\]
All logarithms below are natural unless a subscript is displayed. Fix
\(1<q<2^{1/9}\), and let
\(G_q=\{n\ge3:\lambda(n^2)\ge q\lambda(n)\}\). Then
\[
 \liminf_{M\to\infty}\frac{\displaystyle
\sum_{\substack{3\le n\le M\\n\in G_q}}w_n}{\log\log M}
 \ge \delta(q):=\frac{1/9-\log_2q}{1-\log_2q}>0. \tag{1}
\]

## Proof

Set \(h=\log2\), \(n(x)=\lfloor e^{e^x}\rfloor\),
\(a(x)=\lambda(n(x))\), and \(b(x)=a(x)+2h\). For
\(z=e^{e^x}\), write \(n=n(x)\) and \(m=n(x+h)=\lfloor z^2\rfloor\). Eventually
\[
 n^2\le m<2n^2. \tag{2}
\]
Indeed, \(n\le z<n+1\), and \((n+1)^2<2n^2\) for large \(n\).
Monotonicity of \(r\), and restriction of an \(m\)-set to the two
intervals of lengths at most \(n^2\), give
\[
 r(n^2)\le r(m)\le2r(n^2).
\]
Together with (2), this says
\[
 |\lambda(m)-\lambda(n^2)|\le h. \tag{3}
\]
In particular \(\lambda(n^2)\ge a(x+h)-h\). The displayed lambda inequality \(\lambda(n^2)\le2\lambda(n)+h\) is derived from the accepted cardinal theorem `rothNumberNat_sq_le_two_mul_rothNumberNat_sq`, and therefore gives
\[
 a(x+h)\le2a(x)+2h,\qquad b(x+h)\le2b(x). \tag{4}
\]
The elementary block partition gives \(r(n^2)\le n r(n)\), hence
\(\lambda(n^2)\ge\lambda(n)\); the square-scale logarithmic ratios below are
therefore nonnegative.

The only external analytic input is Bloom--Sisask, arXiv:2309.02353,
Theorem 1, used only in its eventual form
\(\lambda(N)\ge c(\log N)^{1/9}\). Thus
\[
 L(x):=\log b(x)\ge x/9+O(1). \tag{5}
\]
This is a lower bound, not an asymptotic formula or an upper bound.

First prove the stronger weighted mean statement. Define, for large \(x\),
\[
 C(x)=\log_2\frac{\lambda(n(x)^2)}{\lambda(n(x))},\qquad
 D(x)=\log_2\frac{b(x+h)}{b(x)}.
\]
By (3), (4), and \(a(x)\to\infty\) (from (5)), one has uniformly
\(b(x)/a(x)=1+o(1)\) and
\[
 C(x)-D(x)=o(1). \tag{6}
\]
Indeed, replacing each quantity by its version with an additive \(2h\), or
replacing \(\lambda(n(x)^2)\) by \(a(x+h)\), changes its logarithm by \(o(1)\).
Also (4) gives \(0\le C(x)\le1+o(1)\).

For \(T=R+Kh\), continuous telescoping gives
\[
 \int_R^T D(x)\,dx
 =\frac1h\left(\int_T^{T+h}L(y)\,dy-
                    \int_R^{R+h}L(y)\,dy\right).
\]
Using (5), then letting \(K\to\infty\), proves
\[
 \liminf_{T\to\infty}\frac1T\int_R^T C(x)\,dx\ge\frac19. \tag{7}
\]
The same holds with arbitrary endpoints, since the integrand is nonnegative
and bounded by \(1+o(1)\). Since \(n(x)=n\) exactly on
\([\log\log n,\log\log(n+1))\), whose length is \(w_n\), (7) is precisely
\[
 \liminf_{M\to\infty}\frac1{\log\log M}
 \sum_{3\le n\le M}w_n\log_2\frac{\lambda(n^2)}{\lambda(n)}\ge\frac19. \tag{8}
\]

Put \(\alpha=\log_2q\). On the set where \(C(x)<\alpha\), use
\(C\le\alpha\), and on its complement use \(C\le1+o(1)\). Combining this
with (7) shows that the lower density of \(\{x:C(x)\ge\alpha\}\) is at least
\[
 \frac{1/9-\alpha}{1-\alpha}=\delta(q).
\]
The interval partition just noted converts this density exactly into (1);
endpoint truncation is harmless because numerator and denominator are
monotone and \(\log\log(M+1)\sim\log\log M\).

Finally, \(n\in G_q\) is equivalent to
\[
 r(n^2)\le r(n)^q n^{2-q}.
\]
With \(X(n)=\lambda(n^2)-2\lambda(n)\), this displayed \(X\) is exactly the accepted Lean `squareScaleDefect`, not its opposite sign. It implies
\(X(n)\ge-(2-q)\lambda(n)\). Thus, for \(\eta=q-1\), property \(P\) with
\(C=1\) holds on a positive log-log weighted-density set; no eventual validity is claimed.
No vector-grid reduction is used.

## Eight-part contract/audit

1. **Quantifiers:** every \(1<q<2^{1/9}\) is covered directly; no auxiliary
   threshold is lost.
2. **Modality:** the only external input is the explicitly cited external
   Bloom--Sisask lower bound; the square-scale inequality is the accepted lemma.
3. **Exact additive structure:** the shift \(b=a+2h\) gives the exact (4),
   while the floor/interval-partition loss is the fixed \(h\) in (3).
4. **\(\lambda/X\) implication:** the displayed equivalence and the bound on
   \(X\) are exact.
5. **Optimization:** the mean \(1/9\), together with the sharp envelope
   \(0\le C\le1+o(1)\), yields the displayed \(\delta(q)\).
6. **Models/endpoints:** although \(q=1\) is outside the assertion, all scales
   are good by \(\lambda(n^2)\ge\lambda(n)\), so \(1/9\) is nonsharp; at
   \(q=2^{1/9}\),
   \(\delta=0\) and no positive claim is made. Behrend-scale
   \(\lambda\approx a\sqrt{\log N}\) makes all sufficiently large scales good for \(q<\sqrt2\),
   whereas \(N/\log N\) contradicts Bloom--Sisask and is not a consistent model.
7. **Falsifier:** in the equivalent phase sampling, a bad phase with too few
   good prefixes contradicts prefix telescoping from (4) and (5); no tail-interval
   estimate is used. Any non-\(O(1)\) floor loss would break the proof.
8. **Future formalization:** the minimal Lean artifact is an abstract positive
   sequence prefix-density lemma; the analytic bound remains a hypothesis. This gives a
   different ambient log-log weighted-density conclusion over all integers; it does not
   formally strengthen or subsume the fixed-base tower-density statement.
