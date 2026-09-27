# Chebyshev refinement of the EHPS torus slice

**Source and status.** Christian Elsholtz, Zach Hunter, Laura Proske and Lisa Sauermann (EHPS), *Improving Behrend's construction: Sets without arithmetic progressions in integers and over finite fields*, [arXiv:2406.12290v1](https://arxiv.org/abs/2406.12290v1), Proposition 2.1 (the torus set), Proposition 2.2 (the two-dimensional block), and §3, the direct-embedding remark (after the proof of the integer theorem). EHPS publish the measure factor \(n^{-3}\), and their direct deduction gives a \((\log N)^{-3/2}\) prefactor. The \(n^{-5/2}\) and \((\log N)^{-5/4}\) factors below are an elementary **source-derived refinement**, not claimed as an EHPS result. We make no novelty or priority claim. The proof here takes EHPS's block proposition as an external input; it is not Lean-formalized. Erdős’s authoritative problem-142 catalog entry (retrieved with `erdos fetch 142`) asks for an asymptotic formula for \(r_k(N)\) and says this remains out of reach even for \(k=3\).

**Refined torus statement.** For even \(n\ge4\) and \(0<\delta<1\), there exists measurable \(S\subseteq[0,1)^n\) with
\[
 \mu(S)\ge 10^{-5}\delta^2n^{-5/2}(7/24)^{n/2}, \tag{1}
\]
such that every \(x,y,z\in S\) satisfying \(x+z\equiv2y\pmod1\) obeys \(|x_i-z_i|<\delta\) in every coordinate. The endpoint difference, rather than the step \(x-y\), matters here.

**Proof.** Put \(m=n/2\), \(\varepsilon=1/n\). EHPS Proposition 2.2 supplies \(T\subseteq[0,1)^2\) and measurable \(f:T\to[0,100n^2]\), with \(\mu(T)\ge 7/24-1/n\), satisfying, for block progressions \(u+w\equiv2v\pmod1\),
\[
 f(u)+f(w)-2f(v)\ge\|u-w\|_2^2. \tag{2}
\]
Write \(p=\mu(T)\) and \(F=\sum_{h=1}^{m}f(U_h)\), where the \(U_h\) are **independent uniform points of \(T\)** (normalized Lebesgue measure). In particular \(\mu(T^m)=p^m\ge 10^{-2}(7/24)^m\), as estimated in EHPS's proof of Proposition 2.1. This lower bound also follows directly: \((1-24/(7n))^{n/2}\) is increasing for real \(n\ge4\), and its value at \(n=4\) is \(1/49>10^{-2}\). Independence and the bounded-variable variance bound give
\[
 \operatorname{Var}(F)\le m(100n^2)^2/4,
 \qquad \Pr(|F-\mathbb EF|\le100n^2\sqrt m)\ge3/4. \tag{3}
\]
The central interval of length \(200n^2\sqrt m\) intersects at most \(400n^2\sqrt m\,\delta^{-2}+2\le402n^2\sqrt m\,\delta^{-2}\) intervals of the fixed half-open grid of width \(\delta^2/2\). Thus one grid bin cuts out a measurable slice \(S\subseteq T^m\) of measure at least
\[
 \frac{(3/4)\,10^{-2}(7/24)^m\delta^2}{402n^2\sqrt m}
 =\frac{3\sqrt2}{160800}\,\delta^2n^{-5/2}(7/24)^m
 >10^{-5}\delta^2n^{-5/2}(7/24)^m.
\]
For \(x,y,z\) in this slice, sum (2) over blocks. Since all three \(F\)-values lie in one half-open bin, \(\sum_i(x_i-z_i)^2\le F(x)+F(z)-2F(y)<\delta^2\), proving the strict coordinate bound. (The independence in (3) is under the product measure conditioned on \(T^m\), not an unconditional probability on the ambient torus.)

**Direct integer consequence.** EHPS §2 credits the direct embedding idea to Green--Wolf, *A Note on Elkin's Improvement of Behrend's Construction* (2010); the execution and the present Chebyshev replacement are separated here. Let \(N\) be an integer with \(L=\ln N\ge4c\), where \(c=\ln(24/7)\); set \(n=2\lceil\sqrt{L/c}\rceil\), \(\delta=N^{-1/n}/4\). Choose \(b\) uniformly on \([0,1)^n\). For each \(1\le t\le N\), \(tb\pmod1\) is uniform, so by the union bound the probability that *some* \(tb\) has a representative in \([-\delta,\delta]^n\) is at most \(N(2\delta)^n=2^{-n}<1\). Fix a \(b\) for which none does. For each \(a\in[0,1)^n\), take
\(A_a=\{j\in\{1,\ldots,N\}:a+jb\pmod1\in S\}\). If distinct \(j,k,\ell\in A_a\) form an integer three-term AP with \(j+\ell=2k\), interchange \(j\) and \(\ell\) if necessary, so \(d=j-\ell\in\{1,\ldots,N\}\). The torus statement makes the endpoint difference a representative of the avoided positive multiple \(db\) in \((-\delta,\delta)^n\), a contradiction. Thus every \(A_a\) is AP-free. Averaging over uniform \(a\) yields some \(|A_a|\ge N\mu(S)\), hence
\[
 r_3(N)\ge \kappa N\exp(-2\sqrt{cL})L^{-5/4},\qquad
 \kappa=\frac{10^{-5}(7/24)c^{5/4}}{16\,3^{5/2}}. \tag{4}
\]
Indeed, writing \(q=\sqrt{L/c}\ge2\), we have \(n\le3q\), \((7/24)^{n/2}\ge(7/24)e^{-\sqrt{cL}}\), and \(\delta^2\ge e^{-\sqrt{cL}}/16\). The Lean convention \(\mathrm{rothNumberNat}(N)\) uses \(\{0,\ldots,N-1\}\); translate by the AP-preserving bijection \(j\mapsto j-1\) from \(\{1,\ldots,N\}\), so (4) transfers unchanged.

**Natural comparison class, not Erdős #142.** Set \(a_*=2\sqrt{\ln(24/7)}\). For every fixed \(\beta>5/4\), (4) implies
\[
 \frac{r_3(N)}{N e^{-a_*\sqrt{\ln N}}(\ln N)^{-\beta}}
 \ge\kappa(\ln N)^{\beta-5/4}\longrightarrow\infty.
\]
Consequently no such fixed-\(\beta\) function is asymptotic to \(r_3(N)\). This sharpens this **particular lower-bound comparison** from the published \(\beta>3/2\) threshold; it does not determine an asymptotic equivalent or solve Erdős #142.
