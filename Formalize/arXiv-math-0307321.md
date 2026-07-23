# arXiv-math-0307321

Title: A Group-theoretic Approach to Fast Matrix Multiplication
Year: 2003

### Cohn-Umans Theorem 4.1 (pseudo-exponent bounds omega)

The foundational theorem: if G has pseudo-exponent alpha and character degrees {d_i}, then |G|^{omega/alpha} <= sum d_i^omega. This is the theorem that makes the entire group sieve framework possible.

### Cohn-Umans Lemma 3.1 (Abelian groups: pseudo-exponent 3)

Abelian groups satisfy alpha(G) = 3. The base negative result.

### Cohn-Umans Theorem 7.5 (Wreath product amplification)

For A = C_{2n} (cyclic of order 2n), the wreath product G_n = A wr S_n satisfies alpha(G_n) <= gamma(G_n) = 2 + (1+log 2)/log n + O(1/(log n)^2). The pseudo-exponent approaches 2 but the theorem only shows alpha <= gamma (not strict), so the hypothesis alpha < gamma of Corollary 4.2 may fail, giving no nontrivial omega bound from this family alone. This is the key amplification result that IDEA.md identifies as the path to omega bounds via the sieve. Formalizing this theorem (and the inequality alpha <= gamma blocking direct application) is critical.

### Cohn-Umans Theorem 6.1 (SL_n(R) Lie pseudo-exponent)

The upper unitriangular, lower unitriangular, and SO_n(R) subgroups satisfy TPP in SL_n(R), giving Lie pseudo-exponent at most 2+2/n. This is the key linear-group continuous construction (the solvable Heisenberg construction in Section 7 achieves 2+1/n).
