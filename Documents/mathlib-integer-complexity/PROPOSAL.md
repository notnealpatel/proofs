# Mathlib PR proposal — integer (Mahler–Popken) complexity (OEIS A005245)

A review document, not a PR. Nothing has been branched, pushed, or announced.
Source: commit d657720 (sweep record now under PRIOR ART in
`Plans/PLAN.md`); ported from
`Proofs/NumberComplexity/IntComplexity.lean` and
`Proofs/NumberComplexity/DoublingConjecture.lean`.

```
TODO
- [ ] USER review of this document is the gate for any further step.
- [ ] NOT drafted now (follow-ups): PR 2 (the computable A005245 recurrence
      engine `minSplit`/`complexityFuel`/`complexityRec` + master bridge, which
      makes concrete values kernel-decidable); the P5 sunflower Mathlib PR
      (+ ALWZ bound sequel) is a separate work item; Zulip #mathlib4
      pre-announcement; fork/branch mechanics.
- [ ] Compile status: the drafting agent reported both draft files compiling
      against this repo's pinned Mathlib with the minimal imports listed below;
      the run was stopped before I independently confirmed — treat as
      UNVERIFIED, and revalidate on mathlib master regardless (module-system
      syntax and `Nat.sInf`/`Real.logb` lemma names are the churn risks).
```

## Scope

**In (all sorry-free in the repo, axioms `{propext, Classical.choice,
Quot.sound}`):**

1. The term language over `{1, +, ×}` (`Expr` → `Expression`), `eval`, `cost`.
2. The complexity function as an infimum over the witness subtype, with the
   junk value `‖0‖ = 0` pinned and documented.
3. Basic order API: infimum universal property, attainment for `1 ≤ n`,
   `1 ≤ ‖n‖`, `‖n‖ ≤ n`, `‖1‖ = 1`, subadditivity under `+` and `*`, and a new
   `‖n ^ k‖ ≤ k * ‖n‖`.
4. The Selfridge–Coppersmith cube bound: additive step, expression form
   `e.eval ^ 3 ≤ 3 ^ e.cost`, arithmetic form `n ^ 3 ≤ 3 ^ ‖n‖`, a
   contrapositive for reading off concrete lower bounds, and the `Real.logb`
   form `3 * logb 3 n ≤ ‖n‖`.
5. `‖3 ^ b‖ = 3 * b` for `1 ≤ b` (Theorem 2 of Iraids et al. arXiv:1203.6462,
   label `cbounds2` — numbering verified against the local tex source:
   `cbounds` and `cbounds2` are the paper's first two theorem environments).

**Out, deliberately:**

- `complexity_two_pow` (`‖2^a‖ = 2a`, Guy F26 / Iraids Hypothesis 1): OPEN,
  carried repo-side as an intended sorry. Mathlib takes no sorries; the PR
  mentions the open problem only neutrally in one docstring.
- The certified-window theorems (`a ≤ 9`, three-smooth window): method-bound
  statements whose docstrings are about an open problem; candidate for a later
  PR or the ITP paper, not for Mathlib core now.
- The computable recurrence engine: deferred to PR 2 to keep PR 1 small. The
  cost of deferral is visible and honest: without it, ground checks can pin
  only values reachable by subadditivity-upper + cube-lower (see below), and
  `a(11) = 8` is provably out of reach of the cube bound (it gives only
  `‖11‖ ≥ 7`).

## Placement and file layout

```
Mathlib/NumberTheory/IntegerComplexity/Basic.lean    (~270 lines)
Mathlib/NumberTheory/IntegerComplexity/Bounds.lean   (~290 lines)
```

- `NumberTheory` over `Combinatorics`: A005245 is arithmetic (Guy UPINT §F26;
  the substantive theorems are about powers and logarithms).
- `Basic.lean` carries `assert_not_exists Real` — the definition layer is
  real-free; everything analytic is quarantined in `Bounds.lean`.
- Proposed minimal imports (validated only against this repo's pinned Mathlib,
  per the TODO caveat): `Basic` ← `Mathlib.Order.Lattice.Nat`;
  `Bounds` ← `Mathlib.Analysis.SpecialFunctions.Log.Base` + `Basic`.
- Files use the current Mathlib module system (`module`, `public import`,
  `@[expose] public section`) and the standard copyright header
  (Author: Neal Patel).

**Namespaces.** The term language lives in `IntegerComplexity`
(`IntegerComplexity.Expression`); the function is `Nat.integerComplexity`, so
call sites read `n.integerComplexity` by dot notation. Bare `complexity` is too
generic for the root namespace; the infimum-over-witness-subtype style follows
`SimpleGraph.dist`.

## Proposed API (signatures for review)

`Basic.lean`:

```lean
inductive IntegerComplexity.Expression : Type
  | one | add (a b : Expression) | mul (a b : Expression)

def Expression.eval : Expression → ℕ          -- @[simp] eval_one/eval_add/eval_mul
def Expression.cost : Expression → ℕ          -- @[simp] cost_one/cost_add/cost_mul
theorem Expression.one_le_eval (e : Expression) : 1 ≤ e.eval
theorem Expression.one_le_cost (e : Expression) : 1 ≤ e.cost
def Expression.ones : ℕ → Expression          -- ones n denotes n; junk at 0
theorem Expression.eval_ones {n : ℕ} (hn : 1 ≤ n) : (ones n).eval = n
theorem Expression.cost_ones {n : ℕ} (hn : 1 ≤ n) : (ones n).cost = n

noncomputable def Nat.integerComplexity (n : ℕ) : ℕ :=
  ⨅ e : {e : Expression // e.eval = n}, e.1.cost
theorem Nat.integerComplexity_eq_sInf (n : ℕ) : ...
@[simp] theorem Nat.integerComplexity_zero : integerComplexity 0 = 0   -- junk pin
theorem Nat.integerComplexity_le_cost {n e} (he : e.eval = n) : n.integerComplexity ≤ e.cost
theorem Nat.exists_cost_eq_integerComplexity {n} (hn : 1 ≤ n) :
    ∃ e : Expression, e.eval = n ∧ e.cost = n.integerComplexity
theorem Nat.le_integerComplexity {n k} (hn : 1 ≤ n)
    (h : ∀ e : Expression, e.eval = n → k ≤ e.cost) : k ≤ n.integerComplexity
theorem Nat.one_le_integerComplexity {n} (hn : 1 ≤ n) : 1 ≤ n.integerComplexity
theorem Nat.integerComplexity_le_self {n} (hn : 1 ≤ n) : n.integerComplexity ≤ n
@[simp] theorem Nat.integerComplexity_one : integerComplexity 1 = 1
theorem Nat.integerComplexity_add_le {a b} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (a + b).integerComplexity ≤ a.integerComplexity + b.integerComplexity
theorem Nat.integerComplexity_mul_le {a b} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (a * b).integerComplexity ≤ a.integerComplexity + b.integerComplexity
theorem Nat.integerComplexity_pow_le {n k} (hn : 1 ≤ n) (hk : 1 ≤ k) :   -- NEW
    (n ^ k).integerComplexity ≤ k * n.integerComplexity
theorem Nat.integerComplexity_two_pow_le {a} (ha : 1 ≤ a) :
    (2 ^ a).integerComplexity ≤ 2 * a
```

`Bounds.lean`:

```lean
theorem IntegerComplexity.add_pow_three_le_three_pow_add
    {x y p q} (hx : 1 ≤ x) (hy : 1 ≤ y) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hxp : x ^ 3 ≤ 3 ^ p) (hyq : y ^ 3 ≤ 3 ^ q) : (x + y) ^ 3 ≤ 3 ^ (p + q)
theorem Expression.eval_pow_three_le_three_pow_cost (e : Expression) :
    e.eval ^ 3 ≤ 3 ^ e.cost
def Expression.threePowSucc : ℕ → Expression   -- product of b+1 copies of 1+(1+1)
theorem Expression.eval_threePowSucc (b : ℕ) : (threePowSucc b).eval = 3 ^ (b + 1)
theorem Expression.cost_threePowSucc (b : ℕ) : (threePowSucc b).cost = 3 * (b + 1)

theorem Nat.pow_three_le_three_pow_integerComplexity {n} (hn : 1 ≤ n) :
    n ^ 3 ≤ 3 ^ n.integerComplexity
theorem Nat.lt_integerComplexity_of_three_pow_lt {n k}                    -- NEW
    (h : 3 ^ k < n ^ 3) : k < n.integerComplexity
theorem Nat.three_mul_logb_three_le_integerComplexity {n} (hn : 1 ≤ n) :
    3 * Real.logb 3 n ≤ (n.integerComplexity : ℝ)
theorem Nat.integerComplexity_three_pow {b} (hb : 1 ≤ b) :
    (3 ^ b).integerComplexity = 3 * b
```

Ground checks (terminal `example`s in `Bounds.lean`, no recurrence needed):
`‖1‖=1, ‖2‖=2, ‖3‖=3, ‖6‖=5, ‖9‖=6, ‖12‖=7`, each pinned between a
subadditivity upper bound and a cube lower bound via
`lt_integerComplexity_of_three_pow_lt`. I re-verified the arithmetic of each
(e.g. `‖6‖`: upper `‖2‖+‖3‖ ≤ 5`, lower `3^4 = 81 < 216 = 6^3` ⇒ `‖6‖ > 4`).

## Name map (repo → proposed)

| Repo (`NumberComplexity`) | Proposed Mathlib | Note |
|---|---|---|
| `Expr` | `IntegerComplexity.Expression` | spelled out per Mathlib style |
| `Expr.eval` / `Expr.cost` | `Expression.eval` / `.cost` | + new `@[simp]` unfolding lemmas |
| `Expr.one_le_eval` / `one_le_cost` | same names | |
| `Expr.ones` (`ones n` denotes `n+1`) | `Expression.ones` (`ones n` denotes `n`) | **reindexed**; `eval_ones`/`cost_ones` gain `1 ≤ n` |
| `complexity` | `Nat.integerComplexity` | dot notation at call sites |
| `complexity_def` | `Nat.integerComplexity_eq_sInf` | named by shape |
| `complexity_zero` | `Nat.integerComplexity_zero` | now `@[simp]` |
| `complexity_le_cost` | `Nat.integerComplexity_le_cost` | |
| `exists_cost_eq_complexity` | `Nat.exists_cost_eq_integerComplexity` | |
| `le_complexity` | `Nat.le_integerComplexity` | |
| `one_le_complexity` | `Nat.one_le_integerComplexity` | |
| `complexity_le_self` | `Nat.integerComplexity_le_self` | |
| `complexity_one` | `Nat.integerComplexity_one` | now `@[simp]` |
| `complexity_add_le` / `complexity_mul_le` | `Nat.integerComplexity_add_le` / `_mul_le` | |
| — | `Nat.integerComplexity_pow_le` | **new**; makes `Expr.twoPowSucc` unnecessary |
| `complexity_two_pow_le` | `Nat.integerComplexity_two_pow_le` | reproved via `pow_le`; `twoPowSucc` witness dropped |
| `add_pow_three_le_three_pow_add` (+ private aux) | `IntegerComplexity.add_pow_three_le_three_pow_add` | proof unchanged |
| `Expr.pow_three_eval_le_three_pow_cost` | `Expression.eval_pow_three_le_three_pow_cost` | Mathlib naming grammar |
| `pow_three_le_three_pow_complexity` | `Nat.pow_three_le_three_pow_integerComplexity` | |
| — | `Nat.lt_integerComplexity_of_three_pow_lt` | **new** contrapositive |
| `three_mul_logb_three_le_complexity` | `Nat.three_mul_logb_three_le_integerComplexity` | |
| `Expr.threePowSucc` (+ eval/cost) | `Expression.threePowSucc` (+ eval/cost) | |
| `complexity_three_pow` | `Nat.integerComplexity_three_pow` | |
| `minSplit` / `complexityFuel` / `complexityRec` / `complexity_eq_complexityRec` | — | deferred to PR 2 |
| `complexity_two_pow` (sorry) | — | open problem, stays repo-side |
| window theorems (`…of_le_nine`, three-smooth) | — | excluded, see Scope |
| guard-necessity + satisfiability `example`s | — | STYLE.md artifacts; Mathlib carries the guards in docstrings instead |

## Review notes (things I would change before submission)

1. **Docstring nit in `Basic.lean`:** the module docstring asserts
   `‖11‖ = 8` "witnessed by `(1+1+1)*(1+1+1)+1+1`". The expression witnesses
   only `≤ 8` (its eval is 11 at cost 8 — arithmetic checks out); the equality
   is the OEIS value, not provable from this PR (cube bound gives `≥ 7`).
   Rephrase as "and `‖11‖ = 8` (OEIS A005245); the displayed expression is
   optimal".
2. **Attribution wording in `Bounds.lean`:** the draft splits credit as "the
   lower bound is due to Selfridge; Guy attributes the companion upper bound to
   Coppersmith". The sources are less precise: Altman–Zelinsky credit the lower
   bound to Selfridge; Iraids et al. say Guy attributes "this result" (their
   two-sided Theorem 1) to Coppersmith; the OEIS entry says "known from the
   work of Selfridge and Coppersmith". Soften to the OEIS/Iraids phrasing
   rather than asserting a sharper split than any source makes.
3. Bibliography keys (`[mahler-popken1953]`, `[guy2004unsolved]`,
   `[iraids2012integer]`, `[altman-zelinsky2012]`) must be added to
   `docs/references.bib` in the PR — remember this file when the PR is made.

## Proposed PR description

> **Title:** feat(NumberTheory): integer (Mahler–Popken) complexity of natural
> numbers (OEIS A005245)
>
> This PR defines the integer complexity `‖n‖` of a natural number — the least
> number of 1's needed to build `n` from the constant 1 using only addition and
> multiplication (OEIS A005245) — and proves the basic API and the classical
> Selfridge–Coppersmith lower bound.
>
> **Definitions.** `IntegerComplexity.Expression` is the term language over
> `{1, +, *}` with `eval` and `cost` (number of 1-leaves);
> `Nat.integerComplexity n` is the infimum of `cost` over the subtype of
> expressions denoting `n` (in the style of `SimpleGraph.dist`). `‖0‖ = 0` is a
> documented junk value (no expression denotes 0); statements carry `1 ≤ n`
> guards where the value at 0 would be load-bearing.
>
> **Main results.**
> - Attainment of the infimum, `1 ≤ ‖n‖`, `‖n‖ ≤ n`, and subadditivity
>   `‖a + b‖ ≤ ‖a‖ + ‖b‖`, `‖a * b‖ ≤ ‖a‖ + ‖b‖`, `‖n ^ k‖ ≤ k * ‖n‖`.
> - The cube bound `n ^ 3 ≤ 3 ^ ‖n‖`, equivalently `3 * logb 3 n ≤ ‖n‖`
>   (stated in the A005245 entry; Theorem 1 of Iraids et al., arXiv:1203.6462,
>   who record Guy's attribution to Coppersmith; the lower bound is credited to
>   Selfridge by Altman–Zelinsky, arXiv:1207.4841).
> - `‖3 ^ b‖ = 3 * b` for `1 ≤ b` (Theorem 2 of Iraids et al.): the cube bound
>   is exact at powers of three. The base-two analogue `‖2 ^ a‖ = 2 * a` is a
>   known open problem (Guy, *Unsolved Problems in Number Theory*, §F26); this
>   PR proves only the easy direction `‖2 ^ a‖ ≤ 2 * a` and takes no position
>   on the rest.
>
> Concrete values `‖n‖` for `n = 1, 2, 3, 6, 9, 12` are checked against the
> A005245 data as `example`s, pinned between the subadditivity upper bounds and
> the cube lower bound. A follow-up PR will add the standard A005245 recurrence
> as a computable, kernel-reducing companion function with an equivalence
> theorem, making all concrete values decidable.
>
> We found no prior formalization of integer complexity (OEIS A005245 /
> Mahler–Popken) in Mathlib, Isabelle AFP, Coq/Rocq, Mizar, Metamath, or HOL
> Light (literature sweep, 2026-08-07).

## Verification status

- All ported statements originate from sorry-free repo declarations whose
  axiom audits report exactly `{propext, Classical.choice, Quot.sound}`
  (`#print axioms` blocks in the two source files).
- The full Lean text of the two draft files (from the stopped drafting run)
  was reviewed by me against the repo sources and then removed from `Drafts/`
  per the markdown-only decision; it is recoverable from the goof trash if the
  proposal is approved, or cheaply regenerable from this document.
- Citation numbering for Iraids et al. Theorems 1/2 verified against
  `References/arXiv-1203-6462/_1introduction.tex`.
