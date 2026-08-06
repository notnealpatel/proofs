/-
  NumberComplexity/DoublingConjecture — the powers-of-two hypothesis
  `‖2^a‖ = 2a` for integer (Mahler–Popken) complexity: Guy, *Unsolved
  Problems in Number Theory*, §F26; Hypothesis 1 of Iraids et al.
  (arXiv:1203.6462).  OPEN — carried here as one intended, disclosed
  `sorry` over a proved sanity layer.

  AI disclosure: produced with AI assistance (see Proofs/README).
-/
import Mathlib
import NumberComplexity.IntComplexity

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

/-! ## 1. The canonical witness and the upper bound

`2^a` is the product of `a` copies of `1 + 1`, which costs `2a` ones.  The
witness is indexed by `a - 1` so that it is total without a junk case (the
same convention as `Expr.ones` in `IntComplexity.lean`, which evaluates to
`n + 1`). -/

namespace Expr

/-- `Expr.twoPowSucc a` : the product `(1+1) · ((1+1) · (⋯ · (1+1)))` of
`a + 1` copies of `1 + 1`.  It evaluates to `2 ^ (a + 1)` at cost
`2 * (a + 1)` — the representation of a power of two that Hypothesis 1 of
arXiv:1203.6462 asserts to be optimal. -/
def twoPowSucc : ℕ → Expr
  | 0 => add one one
  | a + 1 => mul (add one one) (twoPowSucc a)

/-- `Expr.twoPowSucc a` evaluates to `2 ^ (a + 1)`. -/
theorem eval_twoPowSucc (a : ℕ) : (twoPowSucc a).eval = 2 ^ (a + 1) := by
  induction a with
  | zero => rfl
  | succ a ih => simp only [twoPowSucc, eval, ih]; ring

/-- `Expr.twoPowSucc a` costs `2 * (a + 1)` ones. -/
theorem cost_twoPowSucc (a : ℕ) : (twoPowSucc a).cost = 2 * (a + 1) := by
  induction a with
  | zero => rfl
  | succ a ih => simp only [twoPowSucc, cost, ih]; ring

-- ground checks: three copies of `1+1` make 8 at cost 6
example : (twoPowSucc 0).eval = 2 := rfl
example : (twoPowSucc 0).cost = 2 := rfl
example : (twoPowSucc 2).eval = 8 := rfl
example : (twoPowSucc 2).cost = 6 := rfl
example : (twoPowSucc 5).eval = 64 := rfl
example : (twoPowSucc 5).cost = 12 := rfl

end Expr

/-- **Upper bound, proved for every exponent**: `‖2^a‖ ≤ 2a` for `1 ≤ a`,
witnessed by the product of `a` copies of `1 + 1` (`Expr.twoPowSucc`).  This
is the easy half of Hypothesis 1; all of its content is the reverse
inequality. -/
theorem complexity_two_pow_le {a : ℕ} (ha : 1 ≤ a) : complexity (2 ^ a) ≤ 2 * a := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  have hc := complexity_le_cost (Expr.eval_twoPowSucc b)
  rw [Expr.cost_twoPowSucc] at hc
  exact hc

/-! ## 2. The Selfridge/Coppersmith lower bound `3 log₃ n ≤ ‖n‖`

In arithmetic form: every `{1,+,×}`-expression satisfies
`eval ^ 3 ≤ 3 ^ cost`, equivalently `eval ≤ 3 ^ (cost / 3)`.  The
multiplicative step is immediate; the additive step is the whole difficulty
and is isolated in `add_pow_three_le_three_pow_add`. -/

/-- Additive step of the Selfridge/Coppersmith bound, in the asymmetric form
`x ≤ y` in which it is actually proved.  Two regimes: for `2 ≤ p` the crude
estimate `x + y ≤ 2y` already suffices because `8 ≤ 3 ^ p`; for `p = 1` the
hypothesis `x ^ 3 ≤ 3` pins `x = 1`, and then `y ∈ {1, 2}` are finite checks
(the case `y = 2` is the tight one, `27 = 3 ^ 3`) while `3 ≤ y` follows from
`3 * (1 + y) ≤ 4 * y`. -/
private theorem add_pow_three_le_aux {x y p q : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hxp : x ^ 3 ≤ 3 ^ p) (hyq : y ^ 3 ≤ 3 ^ q)
    (hxy : x ≤ y) : (x + y) ^ 3 ≤ 3 ^ (p + q) := by
  rw [pow_add]
  rcases Nat.lt_or_ge p 2 with hp1 | hp2
  · have hpe : p = 1 := by omega
    subst hpe
    have hx1 : x = 1 := by
      by_contra hne
      have h2 : 2 ≤ x := by omega
      have h8 : 2 ^ 3 ≤ x ^ 3 := Nat.pow_le_pow_left h2 3
      norm_num at hxp
      omega
    subst hx1
    rcases Nat.lt_or_ge y 3 with hy3 | hy3
    · interval_cases y
      · -- y = 1 : the cube is 8, and `3 ^ 1 * 3 ^ q ≥ 9`
        have h3 : (3:ℕ) ^ 1 ≤ 3 ^ q := Nat.pow_le_pow_right (by omega) hq
        norm_num at h3 ⊢
        omega
      · -- y = 2 : the tight case; `8 ≤ 3 ^ q` forces `2 ≤ q`, so the bound is 27
        have hq2 : 2 ≤ q := by
          by_contra hne
          have hq1 : q = 1 := by omega
          subst hq1
          norm_num at hyq
        have h9 : (3:ℕ) ^ 2 ≤ 3 ^ q := Nat.pow_le_pow_right (by omega) hq2
        norm_num at h9 ⊢
        omega
    · -- 3 ≤ y : cube `3 * (1 + y) ≤ 4 * y` and absorb `64 ≤ 81`
      have hstep : 3 * (1 + y) ≤ 4 * y := by omega
      have hcube : (3 * (1 + y)) ^ 3 ≤ (4 * y) ^ 3 := Nat.pow_le_pow_left hstep 3
      have hexp : (27:ℕ) * (1 + y) ^ 3 ≤ 64 * y ^ 3 := by
        rw [mul_pow, mul_pow] at hcube
        norm_num at hcube
        omega
      have hy3q : (64:ℕ) * y ^ 3 ≤ 64 * 3 ^ q := Nat.mul_le_mul_left 64 hyq
      have hfin : (27:ℕ) * (1 + y) ^ 3 ≤ 27 * (3 ^ 1 * 3 ^ q) := by
        rw [pow_one]
        omega
      omega
  · -- 2 ≤ p : `(x + y) ^ 3 ≤ 8 * y ^ 3` and `8 ≤ 9 ≤ 3 ^ p`
    have hdouble : x + y ≤ 2 * y := by omega
    have hcube : (x + y) ^ 3 ≤ (2 * y) ^ 3 := Nat.pow_le_pow_left hdouble 3
    have hexp : (2 * y) ^ 3 = 8 * y ^ 3 := by ring
    have h9 : (3:ℕ) ^ 2 ≤ 3 ^ p := Nat.pow_le_pow_right (by omega) hp2
    have h8 : (8:ℕ) * y ^ 3 ≤ 8 * 3 ^ q := Nat.mul_le_mul_left 8 hyq
    have hfin : (8:ℕ) * 3 ^ q ≤ 3 ^ p * 3 ^ q :=
      Nat.mul_le_mul_right (3 ^ q) (by norm_num at h9; omega)
    omega

/-- **Additive step of the Selfridge/Coppersmith bound**: if `x ^ 3 ≤ 3 ^ p`
and `y ^ 3 ≤ 3 ^ q` for positive `x, y, p, q`, then
`(x + y) ^ 3 ≤ 3 ^ (p + q)`.

The exponent guards `1 ≤ p` and `1 ≤ q` are NECESSARY, not cosmetic:
at `x = y = 1`, `p = 0`, `q = 1` the hypotheses hold and the conclusion
`8 ≤ 3` fails (`add_pow_three_guard_necessary` below).  The value guards
`1 ≤ x`, `1 ≤ y` are what the expression language supplies
(`Expr.one_le_eval`) and are what this proof consumes; the statement happens
to survive `x = 0` as well. -/
theorem add_pow_three_le_three_pow_add {x y p q : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hxp : x ^ 3 ≤ 3 ^ p) (hyq : y ^ 3 ≤ 3 ^ q) :
    (x + y) ^ 3 ≤ 3 ^ (p + q) := by
  rcases le_total x y with hxy | hxy
  · exact add_pow_three_le_aux hx hy hp hq hxp hyq hxy
  · rw [Nat.add_comm x y, Nat.add_comm p q]
    exact add_pow_three_le_aux hy hx hq hp hyq hxp hxy

/-- **Selfridge/Coppersmith, expression form**: every `{1,+,×}`-expression
satisfies `e.eval ^ 3 ≤ 3 ^ e.cost`.  The bound is attained — by any
expression of value `3 ^ b` and cost `3 * b`, for instance a product of `b`
copies of `1+1+1` (`Expr.threePowSucc`) — and that is exactly why `‖3^b‖ = 3b`
is a theorem (`complexity_three_pow`) while `‖2^a‖ = 2a` is not: at `2 ^ a`
the same bound leaves a multiplicative slack of `(9/8)^a`. -/
theorem Expr.pow_three_eval_le_three_pow_cost (e : Expr) : e.eval ^ 3 ≤ 3 ^ e.cost := by
  induction e with
  | one => decide
  | add a b iha ihb =>
      simp only [Expr.eval, Expr.cost]
      exact add_pow_three_le_three_pow_add a.one_le_eval b.one_le_eval
        a.one_le_cost b.one_le_cost iha ihb
  | mul a b iha ihb =>
      simp only [Expr.eval, Expr.cost]
      calc (a.eval * b.eval) ^ 3 = a.eval ^ 3 * b.eval ^ 3 := by ring
        _ ≤ 3 ^ a.cost * 3 ^ b.cost := Nat.mul_le_mul iha ihb
        _ = 3 ^ (a.cost + b.cost) := (pow_add 3 _ _).symm

/-- **Selfridge/Coppersmith lower bound, arithmetic form**: `n ^ 3 ≤ 3 ^ ‖n‖`
for `1 ≤ n`.  The guard keeps `complexity` off its junk value at `0` (where
the inequality `0 ≤ 1` would hold vacuously and carry no content). -/
theorem pow_three_le_three_pow_complexity {n : ℕ} (hn : 1 ≤ n) :
    n ^ 3 ≤ 3 ^ complexity n := by
  obtain ⟨e, he, hc⟩ := exists_cost_eq_complexity hn
  have h := e.pow_three_eval_le_three_pow_cost
  rw [he, hc] at h
  exact h

/-- **Selfridge/Coppersmith lower bound, logarithmic form** — the inequality
`3 log_3 n ≤ a(n)` quoted in the OEIS A005245 entry and stated as Theorem 1
of arXiv:1203.6462.  The guard `1 ≤ n` keeps `Real.logb 3 n` off the junk
value `Real.logb 3 0 = 0` and `complexity` off `complexity 0 = 0`. -/
theorem three_mul_logb_three_le_complexity {n : ℕ} (hn : 1 ≤ n) :
    3 * Real.logb 3 n ≤ (complexity n : ℝ) := by
  have hb : (1 : ℝ) < 3 := by norm_num
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hcube : n ^ 3 ≤ 3 ^ complexity n := pow_three_le_three_pow_complexity hn
  have hcast : ((n : ℝ)) ^ 3 ≤ (3 : ℝ) ^ complexity n := by exact_mod_cast hcube
  have hpos : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
  have hmono : Real.logb 3 ((n : ℝ) ^ 3) ≤ Real.logb 3 ((3 : ℝ) ^ complexity n) :=
    Real.logb_le_logb_of_le hb hpos hcast
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one hb] at hmono
  push_cast at hmono
  linarith

/-- The exponent guards of `add_pow_three_le_three_pow_add` are load-bearing:
drop `1 ≤ p` and the statement is false at `x = y = 1`, `p = 0`, `q = 1`,
where the hypotheses `1 ≤ 3 ^ 0` and `1 ≤ 3 ^ 1` hold but `(1+1)^3 = 8` is not
`≤ 3 ^ (0 + 1) = 3`. -/
theorem add_pow_three_guard_necessary :
    (1:ℕ) ^ 3 ≤ 3 ^ 0 ∧ (1:ℕ) ^ 3 ≤ 3 ^ 1 ∧ 3 ^ (0 + 1) < (1 + 1 : ℕ) ^ 3 :=
  ⟨by norm_num, by norm_num, by norm_num⟩

/-! ### The base-3 sibling: `‖3^b‖ = 3b`, proved

The cube bound `n ^ 3 ≤ 3 ^ ‖n‖` is *tight* at `n = 3 ^ b`, where it reads
`3 ^ (3b) ≤ 3 ^ ‖3^b‖`, i.e. `3b ≤ ‖3^b‖` with no rounding loss at all.  With
the product of `b` copies of `1+1+1` as witness, `‖3^b‖ = 3b` follows for
every `b ≥ 1` — Theorem `cbounds2` of arXiv:1203.6462.  The powers-of-two
hypothesis is exactly this argument with the slack `(9/8)^b` reinstated, and
that slack is the whole open problem. -/

namespace Expr

/-- `Expr.threePowSucc b` : the product of `b + 1` copies of `1 + (1 + 1)`.
It evaluates to `3 ^ (b + 1)` at cost `3 * (b + 1)` — the optimal
representation of a power of three. -/
def threePowSucc : ℕ → Expr
  | 0 => add one (add one one)
  | b + 1 => mul (add one (add one one)) (threePowSucc b)

/-- `Expr.threePowSucc b` evaluates to `3 ^ (b + 1)`. -/
theorem eval_threePowSucc (b : ℕ) : (threePowSucc b).eval = 3 ^ (b + 1) := by
  induction b with
  | zero => rfl
  | succ b ih => simp only [threePowSucc, eval, ih]; ring

/-- `Expr.threePowSucc b` costs `3 * (b + 1)` ones. -/
theorem cost_threePowSucc (b : ℕ) : (threePowSucc b).cost = 3 * (b + 1) := by
  induction b with
  | zero => rfl
  | succ b ih => simp only [threePowSucc, cost, ih]; ring

-- ground checks: two copies of `1+1+1` make 9 at cost 6
example : (threePowSucc 0).eval = 3 := rfl
example : (threePowSucc 0).cost = 3 := rfl
example : (threePowSucc 1).eval = 9 := rfl
example : (threePowSucc 1).cost = 6 := rfl
example : (threePowSucc 3).eval = 81 := rfl
example : (threePowSucc 3).cost = 12 := rfl

end Expr

/-- **`‖3^b‖ = 3b` for every `b ≥ 1`** — Theorem `cbounds2` of
arXiv:1203.6462, and the reason the base-2 analogue is hard.  The upper bound
is the product of `b` copies of `1+1+1`; the lower bound is the
Selfridge/Coppersmith cube bound, which at a power of three is an exact
identity `(3^b)^3 = 3^(3b)` and so loses nothing.  The guard `1 ≤ b` is the
source's own and is necessary: `‖3^0‖ = ‖1‖ = 1 ≠ 0`.

Contrast `complexity_two_pow`, where the same bound gives only
`⌈3a log₃ 2⌉ ≈ 1.893a` and the statement is open. -/
theorem complexity_three_pow {b : ℕ} (hb : 1 ≤ b) : complexity (3 ^ b) = 3 * b := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  refine le_antisymm ?_ ?_
  · have hc := complexity_le_cost (Expr.eval_threePowSucc c)
    rw [Expr.cost_threePowSucc] at hc
    exact hc
  · have hcube : (3 ^ (c + 1)) ^ 3 ≤ 3 ^ complexity (3 ^ (c + 1)) :=
      pow_three_le_three_pow_complexity (Nat.one_le_pow _ _ (by omega))
    rw [← pow_mul] at hcube
    have hexp := (Nat.pow_le_pow_iff_right (by omega : 1 < 3)).mp hcube
    omega

/-! ## 3. The weak `log₂` layer, and its strict separation from the hypothesis

`2 · eval ≤ 2 ^ cost` gives `⌊log₂ n⌋ + 1 ≤ ‖n‖`, the shape already carried
for addition chains (`SlizkovDoubling.log_two_le_l`) and for the
quasi-logarithm (`Quasilog.log_two_le_quasilog`).  At `n = 2 ^ a` it certifies
`a + 1` and nothing more — barely half of the conjectured `2a`.  (A private
twin of the expression-level lemma lives in `ComplexityPatterns.lean`; it is
reproved here rather than exported, so this file stands alone.) -/

/-- Every `{1,+,×}`-expression satisfies `2 * e.eval ≤ 2 ^ e.cost`: an
addition of two expressions is dominated by their product once both costs are
at least one. -/
theorem Expr.two_mul_eval_le_two_pow_cost (e : Expr) : 2 * e.eval ≤ 2 ^ e.cost := by
  induction e with
  | one => decide
  | add a b iha ihb =>
      have h2a : (2:ℕ) ≤ 2 ^ a.cost := by
        calc (2:ℕ) = 2 ^ 1 := rfl
          _ ≤ 2 ^ a.cost := Nat.pow_le_pow_right (by omega) a.one_le_cost
      have h2b : (2:ℕ) ≤ 2 ^ b.cost := by
        calc (2:ℕ) = 2 ^ 1 := rfl
          _ ≤ 2 ^ b.cost := Nat.pow_le_pow_right (by omega) b.one_le_cost
      have hmul : (2:ℕ) ^ a.cost + 2 ^ b.cost ≤ 2 ^ a.cost * 2 ^ b.cost :=
        Nat.add_le_mul h2a h2b
      simp only [Expr.eval, Expr.cost]
      rw [pow_add]
      omega
  | mul a b iha ihb =>
      have heb : b.eval ≤ 2 ^ b.cost := by omega
      simp only [Expr.eval, Expr.cost]
      rw [pow_add, ← Nat.mul_assoc]
      exact Nat.mul_le_mul iha heb

/-- The exponential form of the `log₂` lower bound: `2 * n ≤ 2 ^ ‖n‖` for
`1 ≤ n`. -/
theorem two_mul_le_two_pow_complexity {n : ℕ} (hn : 1 ≤ n) :
    2 * n ≤ 2 ^ complexity n := by
  obtain ⟨e, he, hc⟩ := exists_cost_eq_complexity hn
  have h := e.two_mul_eval_le_two_pow_cost
  rw [he, hc] at h
  exact h

/-- The `log₂` lower bound: `⌊log₂ n⌋ + 1 ≤ ‖n‖` for `1 ≤ n`.  The guard keeps
`Nat.log` off its junk value at `0`. -/
theorem log_two_add_one_le_complexity {n : ℕ} (hn : 1 ≤ n) :
    Nat.log 2 n + 1 ≤ complexity n := by
  have h2 : 2 * n ≤ 2 ^ complexity n := two_mul_le_two_pow_complexity hn
  have hlog : Nat.log 2 (n * 2) = Nat.log 2 n + 1 :=
    Nat.log_mul_base one_lt_two (by omega)
  calc Nat.log 2 n + 1 = Nat.log 2 (n * 2) := hlog.symm
    _ = Nat.log 2 (2 * n) := by rw [Nat.mul_comm]
    _ ≤ Nat.log 2 (2 ^ complexity n) := Nat.log_mono_right h2
    _ = complexity n := Nat.log_pow one_lt_two _

/-- What the `log₂` layer certifies at a power of two: `a + 1 ≤ ‖2^a‖`. -/
theorem add_one_le_complexity_two_pow (a : ℕ) : a + 1 ≤ complexity (2 ^ a) := by
  have h := log_two_add_one_le_complexity (n := 2 ^ a) Nat.one_le_two_pow
  rwa [Nat.log_pow one_lt_two] at h

/-- **STRICT SEPARATION**: the `log₂` lower bound is strictly weaker than the
hypothesis at every `2 ≤ a` — it certifies `⌊log₂ 2^a⌋ + 1 = a + 1`, and
`a + 1 < 2a`.  So no amount of sharpening *within* the `log₂` layer can reach
`‖2^a‖ = 2a`; the cube (base-3) bound of §2 is what does the work. -/
theorem log_two_bound_lt_two_mul {a : ℕ} (ha : 2 ≤ a) :
    Nat.log 2 (2 ^ a) + 1 < 2 * a := by
  rw [Nat.log_pow one_lt_two]
  omega

/-! ## 4. The certified window: the hypothesis holds for `a ≤ 9`

`n ^ 3 ≤ 3 ^ ‖n‖` at `n = 2 ^ a` reads `8 ^ a ≤ 3 ^ ‖2^a‖`, so
`‖2^a‖ < 2a` would force `3 · 8 ^ a ≤ 9 ^ a`, i.e. `3 ≤ (9/8) ^ a`, i.e.
`a ≥ log(3)/log(9/8) = 9.32…`.  Nine finite checks therefore settle
`1 ≤ a ≤ 9`, and — `cube_bound_insufficient_at_ten` — the argument genuinely
expires at `a = 10`. -/

/-- **Lower bound on the certified window**: `2a ≤ ‖2^a‖` for `1 ≤ a ≤ 9`, from
the Selfridge/Coppersmith bound plus nine numeral checks. -/
theorem two_mul_le_complexity_two_pow {a : ℕ} (h1 : 1 ≤ a) (h9 : a ≤ 9) :
    2 * a ≤ complexity (2 ^ a) := by
  by_contra hcon
  have hlt : complexity (2 ^ a) < 2 * a := Nat.not_le.mp hcon
  have hcube : (2 ^ a) ^ 3 ≤ 3 ^ complexity (2 ^ a) :=
    pow_three_le_three_pow_complexity Nat.one_le_two_pow
  have hstep : (3:ℕ) ^ (complexity (2 ^ a) + 1) ≤ 3 ^ (2 * a) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  rw [pow_succ] at hstep
  have hkey : (2 ^ a) ^ 3 * 3 ≤ 3 ^ (2 * a) :=
    le_trans (Nat.mul_le_mul_right 3 hcube) hstep
  interval_cases a <;> norm_num at hkey

/-- **THE HYPOTHESIS, PROVED ON ITS CERTIFIED WINDOW**: `‖2^a‖ = 2a` for
`1 ≤ a ≤ 9`.  Sorry-free: the upper bound is the explicit witness
`Expr.twoPowSucc`, the lower bound is Selfridge/Coppersmith.  Compare
Altman–Zelinsky (arXiv:1207.4841, Thm 1.7), who reach `a ≤ 21` by classifying
low-defect representations, and Altman (arXiv:1606.03635, Thm 1.6), who
reach `a ≤ 48` by computation. -/
theorem complexity_two_pow_of_le_nine {a : ℕ} (h1 : 1 ≤ a) (h9 : a ≤ 9) :
    complexity (2 ^ a) = 2 * a :=
  le_antisymm (complexity_two_pow_le h1) (two_mul_le_complexity_two_pow h1 h9)

/-- **THE WINDOW IS SHARP FOR THIS METHOD**: at `a = 10` the
Selfridge/Coppersmith bound `(2^a)^3 · 3 ≤ 3^(2a)` — the exact inequality
refuted for `a ≤ 9` inside `two_mul_le_complexity_two_pow` — becomes *true*
(`3 221 225 472 ≤ 3 486 784 401`).  So the base-3 bound is consistent with
`‖2^10‖ = 19` and cannot certify the hypothesis at `a = 10`, and a fortiori
not beyond: the deficit `(2 − 3 log₃ 2) a ≈ 0.107 a` grows. -/
theorem cube_bound_insufficient_at_ten : ((2:ℕ) ^ 10) ^ 3 * 3 ≤ 3 ^ (2 * 10) := by
  norm_num

/-! ### Independent `decide` cross-checks against the A005245 recurrence

The window theorem derives `‖2^a‖ = 2a` from two *proved* bounds.  The checks
below re-derive the same values straight from the computable A005245
recurrence `complexityRec` (`complexity_eq_complexityRec` is the bridge), so
the definition layer and the bound layer are confirmed against each other and
against the OEIS term list.  No `native_decide`: kernel reduction only.

Measured cost on this machine (2026-08-05): `complexityRec` at `2^6 = 64`
closes by plain `decide` in ≈ 6 s; at `2^7 = 128` it exceeds the elaborator's
default heartbeat budget and needs `decide +kernel` (≈ 28 s, verified, not
kept below); `2^8 = 256` was not attempted.  The checks kept here therefore
stop at `a = 6`, and the `decide` route as a whole reaches only `a ≤ 7` —
short of the *proved* window `a ≤ 9` above, which costs no computation at
all.  (This corrects a planning estimate of "`decide` window `a ≤ 10–12`",
which conflated `complexityRec 11` with `complexityRec (2 ^ 11)`.) -/

example : complexity 2 = 2 := by rw [complexity_eq_complexityRec]; decide
example : complexity 4 = 4 := by rw [complexity_eq_complexityRec]; decide
example : complexity 8 = 6 := by rw [complexity_eq_complexityRec]; decide

set_option maxRecDepth 8192 in
example : complexity 16 = 8 := by rw [complexity_eq_complexityRec]; decide

set_option maxRecDepth 8192 in
example : complexity 32 = 10 := by rw [complexity_eq_complexityRec]; decide

set_option maxRecDepth 16384 in
example : complexity 64 = 12 := by rw [complexity_eq_complexityRec]; decide

/-! ### The three-smooth extension: `‖2^a · 3^b‖ = 2a + 3b` for `a ≤ 9`

The window argument extends verbatim to three-smooth numbers `2^a · 3^b`:
cubing gives `8^a · 27^b`, the target is `3^(2a+3b) = 9^a · 27^b`, and the
`27^b` factors cancel **exactly** — `b` plays no role at all, so the certified
window is `a ≤ 9` with `b` unconstrained.  This matches the shape of the
literature statements (Altman, arXiv:1606.03635, Thm 1.6: "For `k ≤ 48` and
arbitrary `ℓ`, so long as `k` and `ℓ` are not both zero,
`‖2^k 3^ℓ‖ = 2k + 3ℓ`"; Altman–Zelinsky, arXiv:1207.4841, Thm 1.7, the same
for `a ≤ 21`): a cap on the exponent of `2`, no cap on the exponent of `3`.
The cap cannot be removed by this method — `cube_bound_insufficient_at_ten`
is the obstruction, and increasing `b` does not help, since `b` cancels.

NOTE (planning correction): the wave-3 sketch speculated that the cube bound
certifies the lower bound for **all** `a` because `8^a ≤ 9^a`.  That reverses
an inequality: the cube bound gives `8^a · 27^b ≤ 3^‖n‖`, and refuting
`‖n‖ < 2a + 3b` needs `3 · 8^a ≤ 9^a` to be FALSE, which holds exactly for
`a ≤ 9` (`3 ≤ (9/8)^a` first holds at `a = ⌈log 3 / log (9/8)⌉ = 10`).  The
window here is therefore `a ≤ 9`, the same as `two_mul_le_complexity_two_pow`
— consistent with the literature, where even `a ≤ 21` needs the Altman–
Zelinsky classification of low-defect representations, not just the cube
bound. -/

/-- **Upper bound**: `‖2^a · 3^b‖ ≤ 2a + 3b` whenever `a` and `b` are not
both zero, by gluing the optimal witnesses of the two prime-power factors
(`Expr.twoPowSucc`, `Expr.threePowSucc`) with `complexity_mul_le`; the pure
prime-power cases fall back on `complexity_two_pow_le` and
`complexity_three_pow`.  The guard `1 ≤ a + b` is necessary: at `a = b = 0`
the claim would read `‖1‖ ≤ 0`, false since `‖1‖ = 1`. -/
theorem complexity_two_pow_mul_three_pow_le {a b : ℕ} (hab : 1 ≤ a + b) :
    complexity (2 ^ a * 3 ^ b) ≤ 2 * a + 3 * b := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · -- a = 0 : the pure power of three, where the bound is exact
    have hb : 1 ≤ b := by omega
    rw [pow_zero, one_mul, mul_zero, zero_add]
    exact (complexity_three_pow hb).le
  · rcases Nat.eq_zero_or_pos b with rfl | hb
    · -- b = 0 : the pure power of two
      rw [pow_zero, mul_one, mul_zero, add_zero]
      exact complexity_two_pow_le ha
    · -- both positive : submultiplicativity glues the two optimal witnesses
      calc complexity (2 ^ a * 3 ^ b)
          ≤ complexity (2 ^ a) + complexity (3 ^ b) :=
            complexity_mul_le Nat.one_le_two_pow (Nat.one_le_pow _ _ (by omega))
        _ ≤ 2 * a + 3 * b := by
            rw [complexity_three_pow hb]
            exact Nat.add_le_add_right (complexity_two_pow_le ha) _

/-- **Lower bound on the certified window**: `2a + 3b ≤ ‖2^a · 3^b‖` for
`a ≤ 9` and **arbitrary** `b`, from the Selfridge/Coppersmith cube bound.
Cubing `2^a · 3^b` gives `8^a · 27^b`, the target `3^(2a+3b)` is
`9^a · 27^b`, and after cancelling `27^b` the contradiction is the same
numeral refutation of `3 · 8^a ≤ 9^a` as in `two_mul_le_complexity_two_pow`
— `b` cancels, which is why it needs no guard and no cap (at `a = b = 0` the
statement is the trivially true `0 ≤ ‖1‖`, so no vacuity either). -/
theorem two_mul_add_three_mul_le_complexity_two_pow_mul_three_pow {a b : ℕ}
    (h9 : a ≤ 9) : 2 * a + 3 * b ≤ complexity (2 ^ a * 3 ^ b) := by
  by_contra hcon
  have hlt : complexity (2 ^ a * 3 ^ b) < 2 * a + 3 * b := Nat.not_le.mp hcon
  have hn : 1 ≤ 2 ^ a * 3 ^ b := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hcube : (2 ^ a * 3 ^ b) ^ 3 ≤ 3 ^ complexity (2 ^ a * 3 ^ b) :=
    pow_three_le_three_pow_complexity hn
  have hstep : (3:ℕ) ^ (complexity (2 ^ a * 3 ^ b) + 1) ≤ 3 ^ (2 * a + 3 * b) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  rw [pow_succ] at hstep
  have hkey : (2 ^ a * 3 ^ b) ^ 3 * 3 ≤ 3 ^ (2 * a + 3 * b) :=
    le_trans (Nat.mul_le_mul_right 3 hcube) hstep
  rw [mul_pow, ← pow_mul, ← pow_mul, pow_add, Nat.mul_comm b 3,
    mul_right_comm] at hkey
  -- hkey : 2 ^ (a * 3) * 3 * 3 ^ (3 * b) ≤ 3 ^ (2 * a) * 3 ^ (3 * b)
  have hcancel : 2 ^ (a * 3) * 3 ≤ 3 ^ (2 * a) :=
    Nat.le_of_mul_le_mul_right hkey (pow_pos (by omega) _)
  interval_cases a <;> norm_num at hcancel

/-- **THE THREE-SMOOTH WINDOW THEOREM**: `‖2^a · 3^b‖ = 2a + 3b` for `a ≤ 9`
and arbitrary `b`, not both zero — the `a ≤ 9` analogue of Altman–Zelinsky
(arXiv:1207.4841, Thm 1.7: `a ≤ 21`) and Altman (arXiv:1606.03635, Thm 1.6:
`a ≤ 48`).  Subsumes both `complexity_two_pow_of_le_nine` (at `b = 0`) and
`complexity_three_pow` (at `a = 0`, where the cap `a ≤ 9` is idle).

The guard `1 ≤ a + b` is load-bearing for falsity: `a = b = 0` would read
`‖1‖ = 0`, false.  The cap `a ≤ 9` is load-bearing for the METHOD, not the
claim: the equality is known up to `a ≤ 48` (computation) and proved up to
`a ≤ 21` (low-defect classification), but the cube bound expires at `a = 10`
(`cube_bound_insufficient_at_ten`), and unbounded `a` at `b = 1` would come
within one step of Hypothesis 1 itself. -/
theorem complexity_two_pow_mul_three_pow {a b : ℕ} (h9 : a ≤ 9)
    (hab : 1 ≤ a + b) : complexity (2 ^ a * 3 ^ b) = 2 * a + 3 * b :=
  le_antisymm (complexity_two_pow_mul_three_pow_le hab)
    (two_mul_add_three_mul_le_complexity_two_pow_mul_three_pow h9)

/-! Ground truth for the three-smooth window against A005245 (terms pinned in
the header): each value is derived twice — once from the window theorem at
concrete `(a, b)`, once from the computable recurrence by kernel `decide` —
and the two derivations must agree with each other and with the OEIS list:
a(6) = 5, a(12) = 7, a(18) = 8, a(24) = 9, a(36) = 10, a(48) = 11. -/

example : complexity 6 = 5 := by
  have h := complexity_two_pow_mul_three_pow (a := 1) (b := 1) (by omega) (by omega)
  norm_num at h
  exact h

example : complexity 12 = 7 := by
  have h := complexity_two_pow_mul_three_pow (a := 2) (b := 1) (by omega) (by omega)
  norm_num at h
  exact h

example : complexity 18 = 8 := by
  have h := complexity_two_pow_mul_three_pow (a := 1) (b := 2) (by omega) (by omega)
  norm_num at h
  exact h

example : complexity 24 = 9 := by
  have h := complexity_two_pow_mul_three_pow (a := 3) (b := 1) (by omega) (by omega)
  norm_num at h
  exact h

example : complexity 36 = 10 := by
  have h := complexity_two_pow_mul_three_pow (a := 2) (b := 2) (by omega) (by omega)
  norm_num at h
  exact h

example : complexity 48 = 11 := by
  have h := complexity_two_pow_mul_three_pow (a := 4) (b := 1) (by omega) (by omega)
  norm_num at h
  exact h

example : complexity 6 = 5 := by rw [complexity_eq_complexityRec]; decide

set_option maxRecDepth 8192 in
example : complexity 12 = 7 := by rw [complexity_eq_complexityRec]; decide

set_option maxRecDepth 8192 in
example : complexity 18 = 8 := by rw [complexity_eq_complexityRec]; decide

set_option maxRecDepth 8192 in
example : complexity 24 = 9 := by rw [complexity_eq_complexityRec]; decide

set_option maxRecDepth 16384 in
example : complexity 36 = 10 := by rw [complexity_eq_complexityRec]; decide

set_option maxRecDepth 16384 in
example : complexity 48 = 11 := by rw [complexity_eq_complexityRec]; decide

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

/-- **THE OPEN HALF, ISOLATED**: given the proved upper bound, the hypothesis
at `a` is *equivalent* to the lower bound `2a ≤ ‖2^a‖`.  This is the exact
statement that `complexity_two_pow`'s `sorry` stands for. -/
theorem complexity_two_pow_eq_iff_two_mul_le {a : ℕ} (ha : 1 ≤ a) :
    complexity (2 ^ a) = 2 * a ↔ 2 * a ≤ complexity (2 ^ a) :=
  ⟨fun h => h.ge, fun h => le_antisymm (complexity_two_pow_le ha) h⟩

/-! ## 6. Satisfiability

Every hypothesis-bearing statement above is instantiated jointly at a concrete
model, so none of them is vacuous — including the sorried one, whose
hypothesis and conclusion are met outright at `a = 3` (`‖8‖ = 6`). -/

/-- Satisfiability of the sorried hypothesis: its guard and its conclusion hold
together at `a = 3`, proved outright (`‖2^3‖ = ‖8‖ = 6 = 2 · 3`), so
`complexity_two_pow` is not vacuous. -/
example : ∃ a : ℕ, 1 ≤ a ∧ complexity (2 ^ a) = 2 * a :=
  ⟨3, by omega, complexity_two_pow_of_le_nine (by omega) (by omega)⟩

/-- The guard `1 ≤ a` on every `2 ^ a` statement is load-bearing, not
decorative: at `a = 0` the hypothesis would read `complexity 1 = 0`, and
`complexity 1 = 1`.  (Same for `complexity_three_pow` at `b = 0`.) -/
example : complexity (2 ^ 0) = 1 ∧ complexity (2 ^ 0) ≠ 2 * 0 := by
  have h : complexity (2 ^ 0) = 1 := by rw [pow_zero]; exact complexity_one
  exact ⟨h, by rw [h]; omega⟩

-- the guarded statements at concrete parameters
example : complexity (2 ^ 4) ≤ 2 * 4 := complexity_two_pow_le (by omega)
example : complexity (3 ^ 4) = 3 * 4 := complexity_three_pow (by omega)
example : (Expr.threePowSucc 3).eval ^ 3 ≤ 3 ^ (Expr.threePowSucc 3).cost :=
  (Expr.threePowSucc 3).pow_three_eval_le_three_pow_cost
example : 2 * 9 ≤ complexity (2 ^ 9) := two_mul_le_complexity_two_pow (by omega) (by omega)
example : complexity (2 ^ 9) = 2 * 9 := complexity_two_pow_of_le_nine (by omega) (by omega)
example : complexity (2 ^ 6) = 2 * 6 ↔ 2 * 6 ≤ complexity (2 ^ 6) :=
  complexity_two_pow_eq_iff_two_mul_le (by omega)
example : (6:ℕ) ^ 3 ≤ 3 ^ complexity 6 := pow_three_le_three_pow_complexity (by omega)
example : 3 * Real.logb 3 ((6 : ℕ) : ℝ) ≤ (complexity 6 : ℝ) :=
  three_mul_logb_three_le_complexity (n := 6) (by omega)
example : 2 * 6 ≤ 2 ^ complexity 6 := two_mul_le_two_pow_complexity (by omega)
example : Nat.log 2 6 + 1 ≤ complexity 6 := log_two_add_one_le_complexity (by omega)
example : 5 + 1 ≤ complexity (2 ^ 5) := add_one_le_complexity_two_pow 5
example : Nat.log 2 (2 ^ 5) + 1 < 2 * 5 := log_two_bound_lt_two_mul (by omega)
example : (2 + 3 : ℕ) ^ 3 ≤ 3 ^ (2 + 3) :=
  add_pow_three_le_three_pow_add (x := 2) (y := 3) (p := 2) (q := 3)
    (by omega) (by omega) (by omega) (by omega) (by norm_num) (by norm_num)
example : (Expr.twoPowSucc 3).eval ^ 3 ≤ 3 ^ (Expr.twoPowSucc 3).cost :=
  (Expr.twoPowSucc 3).pow_three_eval_le_three_pow_cost
example : 2 * (Expr.twoPowSucc 3).eval ≤ 2 ^ (Expr.twoPowSucc 3).cost :=
  (Expr.twoPowSucc 3).two_mul_eval_le_two_pow_cost

/-- The two lower bounds are genuinely different at a power of two: the `log₂`
layer gives `10`, the Selfridge/Coppersmith layer gives the exact value `18`.
-/
example : Nat.log 2 (2 ^ 9) + 1 < 2 * 9 ∧ 2 * 9 ≤ complexity (2 ^ 9) :=
  ⟨log_two_bound_lt_two_mul (by omega), two_mul_le_complexity_two_pow (by omega) (by omega)⟩

-- the three-smooth window with all guards jointly satisfied, at the corner
-- `a = 9` of the window and a large `b` the cap does not touch
example : complexity (2 ^ 9 * 3 ^ 5) = 2 * 9 + 3 * 5 :=
  complexity_two_pow_mul_three_pow (by omega) (by omega)
example : complexity (2 ^ 4 * 3 ^ 1) ≤ 2 * 4 + 3 * 1 :=
  complexity_two_pow_mul_three_pow_le (by omega)
example : 2 * 9 + 3 * 100 ≤ complexity (2 ^ 9 * 3 ^ 100) :=
  two_mul_add_three_mul_le_complexity_two_pow_mul_three_pow (by omega)

-- the two subsumptions: `b = 0` recovers §4's window, `a = 0` recovers `‖3^b‖ = 3b`
example : complexity (2 ^ 9 * 3 ^ 0) = 2 * 9 + 3 * 0 :=
  complexity_two_pow_mul_three_pow (by omega) (by omega)
example : complexity (2 ^ 0 * 3 ^ 4) = 2 * 0 + 3 * 4 :=
  complexity_two_pow_mul_three_pow (by omega) (by omega)

/-- The guard `1 ≤ a + b` of the three-smooth window is load-bearing: at
`a = b = 0` the claim would read `‖1‖ = 0`, and `‖1‖ = 1`. -/
example : complexity (2 ^ 0 * 3 ^ 0) = 1 ∧ complexity (2 ^ 0 * 3 ^ 0) ≠ 2 * 0 + 3 * 0 := by
  have h : complexity (2 ^ 0 * 3 ^ 0) = 1 := by norm_num [complexity_one]
  exact ⟨h, by rw [h]; omega⟩

/-! ## 7. Axiom audit (sorry-free declarations only) -/

#print axioms Expr.twoPowSucc
#print axioms Expr.eval_twoPowSucc
#print axioms Expr.cost_twoPowSucc
#print axioms complexity_two_pow_le
#print axioms add_pow_three_le_three_pow_add
#print axioms add_pow_three_guard_necessary
#print axioms Expr.pow_three_eval_le_three_pow_cost
#print axioms pow_three_le_three_pow_complexity
#print axioms three_mul_logb_three_le_complexity
#print axioms Expr.threePowSucc
#print axioms Expr.eval_threePowSucc
#print axioms Expr.cost_threePowSucc
#print axioms complexity_three_pow
#print axioms Expr.two_mul_eval_le_two_pow_cost
#print axioms two_mul_le_two_pow_complexity
#print axioms log_two_add_one_le_complexity
#print axioms add_one_le_complexity_two_pow
#print axioms log_two_bound_lt_two_mul
#print axioms two_mul_le_complexity_two_pow
#print axioms complexity_two_pow_of_le_nine
#print axioms cube_bound_insufficient_at_ten
#print axioms complexity_two_pow_mul_three_pow_le
#print axioms two_mul_add_three_mul_le_complexity_two_pow_mul_three_pow
#print axioms complexity_two_pow_mul_three_pow
#print axioms complexity_two_pow_eq_iff_two_mul_le

end NumberComplexity
