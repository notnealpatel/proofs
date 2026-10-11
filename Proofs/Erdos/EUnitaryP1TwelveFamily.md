# An exponent-12 family excluded from e-unitary perfection

**INFORMAL PROOF NOTE — independently reviewed mathematics, not a Lean proof.**
This note preserves the complete all-exponent family exclusion from §8 of the
reviewed report identified below. It does not prove nonexistence outside this
family, resolve the general existence question, establish present-day openness,
or claim novelty. The proof is unbounded in the exponent and prime sizes; it
is not a finite-search certificate.

## Primary definitions and historical question

László Tóth and Nicuşor Minculete, *Exponential unitary divisors*,
[arXiv:0910.2798](https://arxiv.org/abs/0910.2798), §2, define the following.
A positive integer $d$ is a **unitary divisor** of a positive integer $a$,
written $d\parallel a$, when $d\mid a$ and $\gcd(d,a/d)=1$.
For an actual prime factorization $n=\prod_{i=1}^r p_i^{a_i}>1$, an
**e-unitary divisor** is $\prod_{i=1}^r p_i^{d_i}$ with
$d_i\parallel a_i$ for every $i$. In particular, the bases remain the actual
prime bases of $n$, and the exponent divisors are positive. The e-unitary
divisor sum is

$$
\sigma^{(e)*}(n)
 =\sum_{d\mid_{e*}n}d
 =\prod_{i=1}^r\left(\sum_{d\parallel a_i}p_i^d\right),
 \qquad \sigma^{(e)*}(1)=1.
$$

This is not the ordinary unitary divisor sum. Write $\sigma_{eu}$ for
$\sigma^{(e)*}$ here. The paper's §4 defines e-unitary perfection by
$\sigma_{eu}(n)=2n$ and asks in its historical **Problem 1**:

> Is there any e-unitary perfect number which is not e-squarefree,
> therefore not e-perfect?

Here *e-squarefree* means that all positive prime-factorization exponents are
squarefree, not that the integer itself is squarefree. The theorem below
excludes one specified family with nonsquarefree exponent $12$; it does not
answer that historical question in general. Only the definitions and question
are attributed to the primary paper, not this family exclusion. No use is made
of a blanket parity claim about exponent-one local factors.

For a prime $p$ and a positive exponent $a$, put

$$
A(p,a)=\sum_{d\parallel a}p^{d-1}.
$$

Then $\sigma_{eu}(p^a)=pA(p,a)$ and its ratio to $p^a$ is
$A(p,a)/p^{a-1}$. The term $d=1$ is the unique constant term, so
$p\nmid A(p,a)$. Exponent $1$ has ratio $1$ and can be stripped exactly;
exponent $0$ means an absent prime base, not an extra local term. In
particular,

$$
A(2,12)=1+2^2+2^3+2^{11}=2061=3^2\cdot229,
\qquad A(q,2)=1+q.
$$

## Exact theorem

Let $b$ be any positive integer, let $S$ be any finite set of distinct primes
with $2,3\notin S$, and let $t$ be any positive squarefree integer such that

$$
\gcd\left(t,6\prod_{q\in S}q\right)=1.
$$

Define

$$
n=t\,2^{12}\,3^b\prod_{q\in S}q^2.
$$

Then $\sigma_{eu}(n)\ne2n$. The empty set $S$ and $t=1$ are allowed.
The coprimality hypothesis ensures that every prime of $t$ is a distinct
exponent-one decoration, disjoint from $2$, $3$, and $S$; the displayed
prime-power components therefore have exactly their stated exponents.

## Complete informal proof

Suppose instead that $\sigma_{eu}(n)=2n$. Strip $t$: every one of its
prime factors has exponent $1$ and local ratio $1$. Multiplicativity on the
actual, disjoint prime bases gives exactly

$$
2061\,A(3,b)\prod_{q\in S}(q+1)
 =2^{12}\,3^{b-1}\prod_{q\in S}q. \tag{1}
$$

If $b=1$, base $3$ is another exponent-one decoration. The left side of
(1) has the factor $3^2$ from $2061$, whereas the right side has no factor
$3$, because $3\notin S$. This is a contradiction. Hence $b\ge2$.

The prime $229$ divides the left side of (1), so it must belong to $S$:
it is neither $2$ nor $3$. Its successor $230=2\cdot5\cdot23$ now
occurs on the left and forces $5,23\in S$ by the same prime-divisibility
argument. These forced factors contribute at least four factors of $3$:
two from $2061$, one from $5+1=6$, and one from $23+1=24$.
Since $3\notin S$, equation (1) gives $b-1\ge4$, hence $b\ge5$.
Also $3\nmid A(3,b)$, by the unique constant term above.

Set $U=S\setminus\{229,5,23\}$. Its elements are distinct primes
excluding $2,3,5,23,229$. The forced local ratios multiply to

$$
\frac{230}{229}\frac{24}{23}\frac65=\frac{288}{229}.
$$

Cancelling these factors in (1) yields

$$
\prod_{q\in U}\frac{q+1}{q}
 =\frac{128\,3^{b-5}}{A(3,b)}. \tag{2}
$$

Equivalently, $A(3,b)\prod_{q\in U}(q+1)
=128\,3^{b-5}\prod_{q\in U}q$. Taking the exponent $v_2$ of the
prime $2$ in this positive-integer identity gives

$$
v_2(A(3,b))+\sum_{q\in U}v_2(q+1)=7. \tag{3}
$$

For $b>1$, the unitary divisors of $b$ number $2^{\omega(b)}$, which
is even: each prime-power component of $b$ is either included wholly or
omitted. Every summand $3^{d-1}$ is odd, so $A(3,b)$ is even. Every
$q\in U$ is odd and contributes at least one to the sum in (3).
Consequently $|U|\le6$.

Each factor $(q+1)/q=1+1/q$ is greater than $1$ and strictly decreases
with $q$. The six smallest primes permitted in $U$ are
$7,11,13,17,19,29$. Thus, including $U=\varnothing$, the product is
bounded by the product at those six primes: ordering any $k\le6$ selected
primes bounds the $i$th factor by that at the $i$th least permitted prime,
and adding the remaining positive factors only increases the upper bound.
Therefore

$$
\prod_{q\in U}\frac{q+1}{q}\le M
 :=\frac87\frac{12}{11}\frac{14}{13}\frac{18}{17}
   \frac{20}{19}\frac{30}{29}
 =\frac{14515200}{9376367}
 =\frac{2073600}{1339481}.
$$

The exact strict comparison is

$$
14515200\cdot165=2395008000
 <2400349952=256\cdot9376367,
 \qquad M<\frac{256}{165}. \tag{4}
$$

For $b\ge7$, every proper positive unitary divisor of $b$ is in
particular a proper divisor and is at most $m=\lfloor b/2\rfloor$.
Bounding its sum by all positive integers up to $m$ gives

$$
\begin{aligned}
A(3,b)
 &\le3^{b-1}+\sum_{d=1}^{m}3^{d-1}
  =3^{b-1}+\frac{3^m-1}{2}\\
 &<3^{b-1}+\frac{3^m}{2}
  \le\frac{55}{54}\,3^{b-1}.
\end{aligned}
$$

For the last inequality,
$m-(b-1)=1-\lceil b/2\rceil\le-3$, so
$3^m/2\le3^{b-1}/54$. It follows that the right side of (2) is
strictly greater than

$$
\frac{128}{81}\frac{54}{55}=\frac{256}{165}>M,
$$

contradicting the left-side bound. This treats every $b\ge7$ without
an exponent cutoff or prime-size bound.

If $b=5$, its unitary divisors are $1,5$, so $A(3,5)=1+81=82$.
The right side of (2) is $64/41>256/165>M$ (indeed
$64\cdot165=10560>10496=256\cdot41$), again a contradiction.
If $b=6$, its unitary divisors are $1,2,3,6$, so
$A(3,6)=1+3+9+243=256$. Its two-valuation is $8$, contradicting (3).
Together with the preceding $b\le4$ exclusion, this exhausts all positive
$b$ and proves the stated family theorem. $\square$

## Review and source provenance

This note is a faithful documentation extraction of §8, with its review
status corrected by §9, of the final report
`erdos-program-eunitary-p1-01a125d8.md`. Its source-gated SHA256 is
`af07f08458abafa2e633b9fdd1490d8899d66a945885d73dedfaa132171ade12`.
The independent review `eunitary-p1-class-review-01a125d8.md`, SHA256
`351f636e74ab337856bb3599aa2b228a55d66351691a9d6f96e3c2c4067821f6`,
passed the final §8 theorem and primary-source fidelity, used an adversarial
isolated mathematical check, and independently reran the exact constants.
It did not review all earlier report claims or establish a Lean proof.
The complete proof is included above, so consulting those temporary report
files is not necessary to recover the theorem or argument.

The checked primary LaTeX `paper.tex` for arXiv:0910.2798 has SHA256
`362bd72b8d0e355840bf3452e49bae4c9929c848f65d83313986bea09ecb29a5`:
§2, lines 176–193, supplies the divisor definition and multiplicative sum;
§4, lines 474–476, supplies perfection; lines 518–521 give the historical
Problem 1. These are source-copy line numbers, not printed page numbers.
The exact rational computations above are explanatory arithmetic within
an informal proof, not a computational proof of the quantified theorem.
No missing original task exit receipt is inferred from the independent rerun.
