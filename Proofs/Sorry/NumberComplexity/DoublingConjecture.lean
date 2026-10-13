import NumberComplexity.DoublingConjecture

/-!
# Quarantined admissions

The original source and disclosure documentation is retained below as historical context.
Descriptions of the original file refer to its pre-quarantine layout: independent proven
infrastructure now lives in the imported production module; the admissions and their
admission-dependent consequences live only here. No proof closure is claimed.
-/

/-
  NumberComplexity/DoublingConjecture — the powers-of-two hypothesis
  `‖2^a‖ = 2a` for integer (Mahler–Popken) complexity: Guy, *Unsolved
  Problems in Number Theory*, §F26; Hypothesis 1 of Iraids et al.
  (arXiv:1203.6462).  OPEN — carried here as one intended, disclosed
  `sorry` over a proved sanity layer.

  AI disclosure: produced with AI assistance (see Proofs/README).
-/

/-!
# `‖2^a‖ = 2a` — the powers-of-two hypothesis (Guy F26)

`NumberComplexity.complexity` (`NumberComplexity/IntComplexity.lean`) is
integer (Mahler–Popken) complexity, OEIS A005245: the least number of `1`'s
in a `{1, +, ×}`-expression evaluating to `n`, written `‖n‖` below and in the
literature.  Writing `2^a` as a product of `a` copies of `1 + 1` costs `2a`
ones; the hypothesis is that nothing beats it.

## Primary sources (pinned VERBATIM)

`goof oeis show A005245`, pulled live 2026-08-05 —

> name: "The (Mahler-Popken) complexity of n: minimal number of 1's required
> to build n using + and *."

> terms: 1,2,3,4,5,5,6,6,6,7,8,7,8,8,8,8,9,8,9,9,9,10,11,9,10,10,9,10,11,10,
> 11,10,11,11,11,10,11,11,11,11,12,11,12,12,11,12,13,11,12,12,12,12,13,11,12,
> 12,12,13,14,12,13,13,12,12,13,13,14,13,14,13,14,12,13,13,13,13,14,13,14

> formula: "It is known from the work of Selfridge and Coppersmith that
> 3 log_3 n <= a(n) <= 3 log_2 n = 4.754... log_3 n for all n > 1. [Guy,
> Unsolved Problems in Number Theory, Sect. F26.] - _Charles R Greathouse IV_,
> Apr 19 2012 [Comment revised by _N. J. A. Sloane_, Jul 17 2016]"

The entry's own term list already exhibits the hypothesis at
`a = 1, …, 6`: a(2) = 2, a(4) = 4, a(8) = 6, a(16) = 8, a(32) = 10,
a(64) = 12.

J. Iraids, K. Balodis, J. Čerņenoks, M. Opmanis, R. Opmanis, K. Podnieks,
*Integer complexity: experimental and analytical results*, arXiv:1203.6462
(`References/arXiv-1203-6462`, fetched 2026-08-05) — Hypothesis 1,
verbatim from `_1introduction.tex`:

> \begin{hypo}
> \label{powtwohypo}
> For all $a\geq 1$, $\f{2^a}=2a$ (moreover, the product of $1+1$s is shorter
> than any other representation of $2^a$).
> \end{hypo}
>
> $\f{2^a}=2a$ is true for all powers $2^a<10^{12}$, i.e. for all $a$,
> $0<a\leq 39$ – as verified by Jānis Iraids. We consider proving or
> disproving of Hypothesis \ref{powtwohypo} as one of the biggest challenges
> of number theory.

and Theorem 1 of the same paper, the classical two-sided bound:

> \begin{theorem}
> \label{cbounds}
> For all $n>1$, \[3\log_3 n \leq \f{n} \leq 3\log_2 n \approx 4.755 \log_3 n\]
> \end{theorem}
> In \cite{f26}, Guy attributes this result to Dan Coppersmith.

and its Theorem `cbounds2`, the base-3 statement that *is* a theorem — the
contrast that makes the base-2 hypothesis sharp:

> \begin{theorem}
> \label{cbounds2}
> $\f{n}= 3\log_3n$, if and only if $n=3^b$ for some $b\geq 1$. In particular,
> for all $b\geq 1$, $\f{3^b}=3b$ (moreover, the product of $1+1+1$s is shorter
> than any other representation of $3^b$).
> \end{theorem}

H. Altman, J. Zelinsky, *Numbers with integer complexity close to the lower
bound*, arXiv:1207.4841 (`References/arXiv-1207-4841`, fetched 2026-08-05) —
abstract and Theorem 1.7, verbatim:

> John Selfridge showed that $\cpx{n}\ge 3\log_3 n$ for all $n$.

> \begin{thm}\label{th11main}
> For all $0\le a \le 21$ and any $k\ge 0$ having $a+k \ge 1$, there holds
> $$
> \cpx{2^a3^k}=2a+3k.
> $$
> \end{thm}

H. Altman, *Integer complexity: algorithms and computational results*,
arXiv:1606.03635 (`References/arXiv-1606-03635`, fetched 2026-08-05) —
Theorem 1.6, verbatim (the paper's `\NUM` macro expands to `48`):

> \begin{thm}
> \label{frontpage2comput}
> For $k\le \NUM$ and arbitrary $\ell$, so long as $k$ and $\ell$ are not both
> zero,
> \[ \cpx{2^k 3^\ell} = 2k+3\ell.\]
> \end{thm}

so the verified range for the hypothesis is `a ≤ 48`, superseding the
`a ≤ 39` of the 2012 paper.  A literature sweep on 2026-08-05 found no proof,
disproof, or lower bound of the form `‖2^a‖ ≥ (2 − ε)a`; the hypothesis is
open.

## What is proved here, and what is not

* `Expr.twoPowSucc` — the canonical witness, the product of `a + 1` copies of
  `1 + 1`, with `eval = 2 ^ (a + 1)` at `cost = 2 * (a + 1)`; hence
  `complexity_two_pow_le`, the **upper** bound `‖2^a‖ ≤ 2a` for every `1 ≤ a`.
  The whole content of the hypothesis is the matching lower bound
  (`complexity_two_pow_eq_iff_two_mul_le` isolates exactly that).
* `Expr.pow_three_eval_le_three_pow_cost`, `pow_three_le_three_pow_complexity`,
  `three_mul_logb_three_le_complexity` — the Selfridge/Coppersmith **lower**
  bound `3 log₃ n ≤ ‖n‖`, in its arithmetic form `n ^ 3 ≤ 3 ^ ‖n‖` and in the
  real-logarithmic form quoted by the OEIS entry.  Proved.
* `complexity_three_pow` — the base-3 sibling `‖3^b‖ = 3b` for `1 ≤ b`
  (Theorem `cbounds2` above), **proved for all `b`**, because there the same
  cube bound is *tight*: `(3^b)^3 = 3^(3b)` exactly.  This is the whole
  difference between the two bases.
* `complexity_two_pow_of_le_nine` — the hypothesis **proved** for `1 ≤ a ≤ 9`,
  as a corollary of the two bounds above: `‖2^a‖ ≥ ⌈3a log₃ 2⌉ = 2a` exactly
  when `a ≤ 9`.
* `cube_bound_insufficient_at_ten` — and it stops there: at `a = 10` the
  Selfridge/Coppersmith bound is consistent with `‖2^10‖ = 19`, so it cannot
  certify the hypothesis.  The bound is short by `(2 − 3 log₃ 2) a ≈ 0.107 a`.
* `complexity_two_pow_mul_three_pow` — the three-smooth extension of the
  window: `‖2^a · 3^b‖ = 2a + 3b` for `a ≤ 9` and **arbitrary** `b` (not both
  zero).  Cubing `2^a · 3^b` gives `8^a · 27^b` against `3^(2a+3b) =
  9^a · 27^b`, and the `27^b` factors cancel *exactly* — powers of three ride
  along for free, as in `complexity_three_pow`, so the window on `a` is
  unchanged.  This is the `a ≤ 9` analogue of Altman–Zelinsky Thm 1.7
  (`a ≤ 21`) and Altman Thm 1.6 (`a ≤ 48`) quoted above, whose statements
  have exactly this shape.
* `Expr.two_mul_eval_le_two_pow_cost`, `log_two_add_one_le_complexity`,
  `log_two_bound_lt_two_mul` — the weaker `log₂` layer (`⌊log₂ n⌋ + 1 ≤ ‖n‖`,
  the shape carried elsewhere in this campaign) and its **strict separation**
  from the hypothesis: at `2^a` it certifies only `a + 1`, strictly less than
  `2a` for every `2 ≤ a`.
* `complexity_two_pow` — THE HYPOTHESIS, `‖2^a‖ = 2a` for `1 ≤ a`.  OPEN;
  one intended, disclosed `sorry`.

NOT formalized: the parenthetical "moreover" clause of Hypothesis 1 ("the
product of `1+1`s is shorter than **any other** representation").  As an
inequality over all witnesses it is the same statement as the equality; as a
uniqueness claim it needs `Expr` quotiented by associativity/commutativity,
which this campaign's term language does not carry.

## Junk-value discipline

`complexity 0 = 0` is junk (`complexity_zero`: `0` is not expressible, and
`Nat.sInf ∅ = 0`), and `2 ^ 0 = 1` with `complexity 1 = 1 ≠ 0`, so every
statement below about `2 ^ a` carries the guard `1 ≤ a` — exactly the guard
of the source ("For all $a\geq 1$").  `Real.logb 3 n` is guarded by `1 ≤ n`.
-/

set_option autoImplicit false

namespace NumberComplexity

/-! ## 5. The hypothesis

One intended, disclosed `sorry`.  Everything above is sorry-free. -/

/-- **GUY F26 / IRAIDS ET AL. HYPOTHESIS 1** — OPEN: `‖2^a‖ = 2a` for every
`a ≥ 1`, i.e. the product of `a` copies of `1 + 1` is an optimal
`{1, +, ×}`-representation of `2 ^ a`.

Status (sweep 2026-08-05): open.  Verified for `a ≤ 48` (Iraids et al.,
arXiv:1606.03635, Thm 1.6); proved for `a ≤ 21` by classification of low-defect
representations (Altman–Zelinsky, arXiv:1207.4841, Thm 1.7); proved here for
`a ≤ 9` (`complexity_two_pow_of_le_nine`).  The source calls proving or
disproving it "one of the biggest challenges of number theory".

The guard `1 ≤ a` is the source's own (`For all $a\geq 1$`) and is necessary:
at `a = 0` the claim would read `complexity 1 = 0`, false since
`complexity 1 = 1`.

The obstruction is precisely quantified in this file: the upper bound
`‖2^a‖ ≤ 2a` is `complexity_two_pow_le`, proved for all `a`; the best
unconditional lower bound is `3 log₃ 2 · a ≈ 1.893 a`
(`three_mul_logb_three_le_complexity`), which reaches `2a` only for `a ≤ 9`
(`cube_bound_insufficient_at_ten`).  No lower bound of the form
`(2 − ε) a ≤ ‖2^a‖` is known. -/
theorem complexity_two_pow {a : ℕ} (ha : 1 ≤ a) : complexity (2 ^ a) = 2 * a := by
  -- INTENDED SORRY: open problem (Guy, UPINT §F26; arXiv:1203.6462 Hyp. 1).
  -- Proved for `a ≤ 9` by `complexity_two_pow_of_le_nine`; the general case
  -- needs a lower bound strictly stronger than Selfridge/Coppersmith.
  sorry

end NumberComplexity
