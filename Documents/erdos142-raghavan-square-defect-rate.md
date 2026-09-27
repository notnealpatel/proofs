# A quantitative square-defect consequence from Raghavan’s bound

Let \(r(N)=r_3(N)\), the maximum size of a subset of \(\{1,\ldots,N\}\) containing no nontrivial 3-term arithmetic progression, and let
\[
\lambda(N)=\log\frac{N}{r(N)},\qquad X(N)=\lambda(N^2)-2\lambda(N),
\]
with natural logarithms. Fix an integer \(M\ge3\) and set \(N_k=M^{2^k}\). The conclusion below is an **unconditional corollary** of one kernel-checked Lean theorem and one external preprint theorem. Their combination is a reviewed prose argument; it is **not** itself Lean-formalized.

The kernel-checked input is `Erdos142.frequently_squareScaleDefect_iterated_square_le_negative_fraction` in `Proofs/Erdos/Erdos142/SquareScaleNegative.lean`: for every \(0<\varepsilon<2-\sqrt2\), frequently in \(k\),
\[
X(N_k)\le -(2-\sqrt2-\varepsilon)\lambda(N_k).
\tag{1}
\]
Here “frequently” means for arbitrarily large indices (equivalently, the set of such indices is unbounded).

The quantitative lower bound used here is Theorem 1.4 of Rushil Raghavan, *Improved Bounds for 3-Progressions*, [arXiv:2603.27045v3](https://arxiv.org/abs/2603.27045v3), source label `3APbound` in `main__2_.tex`, lines 91–92. This external preprint result gives, for some implicit absolute constant \(c_R>0\) and all sufficiently large \(N\),
\[
r(N)\le N\exp\!\left(-c_R\left(\frac{\log N}{\log\log N}\right)^{1/6}\right).
\tag{2}
\]
This uses the v3 theorem text, not the stale abstract. Taking logarithms in (2) yields the corresponding eventual lower bound for \(\lambda(N)\).

## Quantitative consequence

For every fixed integer \(M\ge3\) and every \(0<\varepsilon<2-\sqrt2\), frequently in \(k\),
\[
\boxed{\displaystyle
X(N_k)\le -(2-\sqrt2-\varepsilon)c_R
\left(\frac{\log N_k}{\log\log N_k}\right)^{1/6}.}
\tag{3}
\]

Indeed, the logarithms on this tower satisfy
\[
\log N_k=2^k\log M,\qquad
\log\log N_k=k\log2+\log\log M>0.
\]
For the last inequality, \(M\ge3>e\) implies \(\log\log M>0\), and \(k\log2\ge0\). Also \(N_k\to\infty\), so (2) supplies a cutoff \(K\) such that for every \(k\ge K\),
\[
\lambda(N_k)\ge c_R\left(\frac{\log N_k}{\log\log N_k}\right)^{1/6}.
\]
For the fixed \(\varepsilon\), let \(S\) be the frequent set of indices in (1). The intersection \(S\cap\{k:k\ge K\}\) remains frequent: removing finitely many indices from an unbounded set leaves an unbounded set. On this intersection, the coefficient \(2-\sqrt2-\varepsilon\) is positive, and substituting the lower bound for \(\lambda(N_k)\) into (1) gives (3).

Since \(X(N)=\log(r(N)^2/r(N^2))\), exponentiating (3) gives the equivalent ratio statement, frequently in \(k\),
\[
\boxed{\displaystyle
\frac{r(N_k^2)}{r(N_k)^2}\ge
\exp\!\left((2-\sqrt2-\varepsilon)c_R
\left(\frac{\log N_k}{\log\log N_k}\right)^{1/6}\right).}
\tag{4}
\]

## Scope

The coefficient in (3) approaches \((2-\sqrt2)c_R\) as \(\varepsilon\downarrow0\), but does not attain it: the input requires \(\varepsilon>0\). The constant \(c_R\) is implicit, and no single common frequent set for all \(\varepsilon\) is asserted. For each fixed admissible \(\varepsilon\), the scale on the right of (3) tends to infinity along the tower.

This quantitatively strengthens the previously packaged fixed-threshold consequence `frequently_squareScaleDefect_lt_neg` in the same Lean file, which says that for every fixed \(B\), \(X(N_k)<-B\) frequently. The strengthening is logically derived from the stronger existing inputs (1) and (2); it is not an independent proof of the kernel-checked result. It is not an asymptotic formula, does not establish \(D\to0\), and gives neither two-sided oscillation nor a solution to Erdős 142.
