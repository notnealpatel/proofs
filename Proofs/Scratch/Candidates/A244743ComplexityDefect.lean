/-
# A244743 — unboundedness of the integer-complexity defect ‖n−1‖ − ‖n‖

## OEIS source (re-pulled verbatim with `goof oeis show A244743`, 2026-08-05)

```
NAME:     Smallest number n with ||n-1||-||n|| = k where ||n||=A005245(n)
          denotes the complexity of n.
TERMS:    6,12,24,108,720,1440,81648,2041200,612360000
KEYWORDS: nonn,more
COMMENTS:
  The k-th term of this sequence is the least n with ||n-1||-||n|| = k if such
  an n exists.
  It is conjectured that ||n-1||-||n|| is not bounded. But there is no proof
  that the sequence is infinite or is well defined.
XREFS:
  Cf. A005245, A252739 (see comments).
```

The offset is `0` (`a(0) = 6`, `a(1) = 12`, `a(2) = 24`, …), consistent with the
defining relation: `‖5‖ − ‖6‖ = 5 − 5 = 0`, `‖11‖ − ‖12‖ = 8 − 7 = 1`,
`‖23‖ − ‖24‖ = 11 − 9 = 2`, all read off the A005245 DATA line
(`goof oeis show A005245`, offset 1):
```
TERMS:    1,2,3,4,5,5,6,6,6,7,8,7,8,8,8,8,9,8,9,9,9,10,11,9,10,10,9,10,11,10,…
```

Supporting A005245 comment (the definition the repo's `complexity` implements):
```
  The complexity of an integer n is the least number of 1's needed to represent
  it using only additions, multiplications and parentheses. This does not allow
  juxtaposition of 1's to form larger integers, so for example, 2 = 1+1 has
  complexity 2, but 11 does not ("pasting together" two 1's is not an allowed
  operation).
```

## Status

Open on **two** counts, and the entry is unusually explicit about it:
"there is no proof that the sequence is infinite **or is well defined**".  Those
are two different claims and both are stated separately below.

## Repo adjacency

`complexity` (A005245) is defined and proved-about in
`Proofs/NumberComplexity/IntComplexity.lean`.
-/
import Mathlib
import NumberComplexity.IntComplexity

set_option autoImplicit false

namespace Candidates.A244743

open NumberComplexity

/-! ## Definition layer

Existing repo definitions reused verbatim:

* `inductive Expr | one | add | mul` with `Expr.eval : Expr → ℕ` and
  `Expr.cost : Expr → ℕ` — `Proofs/NumberComplexity/IntComplexity.lean`.
* `noncomputable def complexity (n : ℕ) : ℕ := ⨅ e : {e : Expr // e.eval = n}, e.1.cost`
* `def complexityRec (n : ℕ) : ℕ := complexityFuel n n` — the **computable**
  mirror, with `theorem complexity_eq_complexityRec (n : ℕ) : complexity n = complexityRec n`.

  **This matters for the sanity layer.**  `complexity` is `noncomputable` (it is
  an `⨅` over a subtype), so `decide` and `native_decide` cannot see it.  Every
  ground check below is phrased over `complexityRec` and lifted by
  `complexity_eq_complexityRec`.  Writing `native_decide` against `complexity`
  directly would fail to elaborate — cf. the repo memory note
  "native_decide needs computable path".

* Available lemmas: `complexity_zero : complexity 0 = 0`,
  `complexity_one : complexity 1 = 1`,
  `complexity_add_le {a b} (ha : 1 ≤ a) (hb : 1 ≤ b) : …`,
  `complexity_mul_le …`, `complexity_le_self {n} (hn : 1 ≤ n) : complexity n ≤ n`.

**Subtraction discipline.**  `‖n−1‖ − ‖n‖` is a difference of naturals that is
routinely negative (`‖n−1‖ − ‖n‖ = −1` for every `n` in a chain of `+1` steps),
so STYLE.md forbids `↑(a - b)`.  Two moves are made:

1. reindex `n ↦ m + 1` so no `ℕ`-subtraction appears in the *argument*, and
2. cast both complexities to `ℤ` before subtracting.

The resulting `defect m = ‖m‖ − ‖m+1‖` satisfies `defect m = A244743`-defect at
`n = m + 1`, so `A244743 k = 1 + (least m with defect m = k)`.  The shift is
recorded explicitly in `a244743` below rather than left implicit. -/

/-- The complexity defect at `m`: `‖m‖ − ‖m+1‖`, as an integer.  This equals the
A244743 quantity `‖n−1‖ − ‖n‖` at `n = m + 1`. -/
noncomputable def defect (m : ℕ) : ℤ := (complexity m : ℤ) - (complexity (m + 1) : ℤ)

/-- Computable mirror of `defect`, for ground checks. -/
def defectRec (m : ℕ) : ℤ := (complexityRec m : ℤ) - (complexityRec (m + 1) : ℤ)

/-- The A244743 sequence itself, *conditional on well-definedness*: `a244743 k`
is the least `n` with `‖n−1‖ − ‖n‖ = k`, given a proof `h` that such an `n`
exists.  Packaging the existence proof as an argument is the honest encoding —
the entry says outright that no proof of well-definedness is known, so a
total `def a244743 : ℕ → ℕ` would be asserting something the source denies.  -/
noncomputable def a244743 (k : ℕ) (h : ∃ m : ℕ, defect m = (k : ℤ)) : ℕ :=
  Nat.find h + 1

/-! ## The conjectures -/

/-- **A244743 well-definedness (the stronger open claim).**

Verbatim: "The k-th term of this sequence is the least n with ||n-1||-||n|| = k
if such an n exists." … "there is no proof that the sequence is infinite or is
well defined."

Well-definedness is exactly: *every* `k` is attained.  Note this is strictly
stronger than unboundedness — a defect sequence could be unbounded while
skipping some value `k`. -/
theorem a244743_wellDefined : ∀ k : ℕ, ∃ m : ℕ, defect m = (k : ℤ) := by
  sorry

/-- **A244743 unboundedness (the conjecture as literally stated).**

Verbatim: "It is conjectured that ||n-1||-||n|| is not bounded."

`⨆`-free phrasing per STYLE.md (a bounded `iSup` over an empty `Prop` collapses
to a default), and `<` rather than `>`.

**Mathlib primitives available.**  `Nat.sInf`, `Nat.find`, `Nat.lt_wfRel`;
`Filter.Tendsto … atTop atTop` if one wants the "defect tends to infinity"
strengthening (which is *false* — `defect m = −1` infinitely often — so `atTop`
phrasing must be over a *subsequence*, i.e. `∀ B, ∃ m, B < defect m`, which is
what is written).  `Nat.log`, `Real.logb` for the `3 log₃ n` comparisons that
drive the known theory.

**Sketch of the known theory.**  The state of the art is Altman's:
`{‖n‖ − 3 log₃ n}` is a well-ordered subset of ℝ of order type `ω^ω`
(recorded in the A005245 comment by Jianing Song, Apr 13 2024).  The defect
conjecture would follow from a strong enough "defect spectrum is unbounded"
statement in that stratification, but the connection is not formal in the
literature.  Concretely:
* `‖ab‖ ≤ ‖a‖ + ‖b‖` and `‖a+b‖ ≤ ‖a‖ + ‖b‖` (both already in the repo as
  `complexity_mul_le`, `complexity_add_le`) give `defect m ≥ −1` always, since
  `‖m+1‖ ≤ ‖m‖ + 1`.  So the defect is bounded *below* trivially; only the
  upper bound is open.
* The known witnesses are highly composite: `6, 12, 24, 108, 720, 1440, 81648,
  2041200, 612360000`.  Note `720 = 6!`, `1440 = 2·720`, `2041200 = 2^4·3^5·5^2·… `
  — the pattern is "`n` very smooth, `n−1` prime or near-prime", which makes
  `‖n‖` small and `‖n−1‖` large.  A construction proving unboundedness would
  need a family of smooth `n` with `n − 1` of provably large complexity, and
  lower bounds on `‖·‖` are exactly the hard direction of the subject.

**Tactic families.**  `decide`/`native_decide` on `complexityRec` for ground
witnesses (see the sanity layer); `omega`/`linarith` for the integer
bookkeeping; `Nat.find_spec`/`Nat.find_min'` for the least-witness packaging;
`push_cast` for the `ℕ → ℤ` casts.

**Related work in this repo.**  `NumberComplexity.IntComplexity` (the definition
and the `complexityRec` bridge), `NumberComplexity.ComplexityPatterns`
(`smallestOfComplexity`), and the carded A005245/A348262 Hamilton–Ballinger
conjecture.  The addition-chain analogue is `A349044NonBrauer.lean` in this
directory. -/
theorem a244743_defect_unbounded : ∀ B : ℤ, ∃ m : ℕ, B < defect m := by
  sorry

/-- The trivial lower bound, stated because it is *provable today* and because it
shows the conjecture is genuinely one-sided: `‖m+1‖ ≤ ‖m‖ + 1` for `m ≥ 1`
(append `+1` to an optimal expression), so `defect m ≥ −1` always. -/
theorem neg_one_le_defect (m : ℕ) (hm : 1 ≤ m) : (-1 : ℤ) ≤ defect m := by
  sorry

/-! ## Sanity layer -/

-- PROVABLE: the computable mirror agrees with the noncomputable definition.
theorem defect_eq_defectRec (m : ℕ) : defect m = defectRec m := by
  unfold defect defectRec
  rw [complexity_eq_complexityRec, complexity_eq_complexityRec]

-- PROVABLE: the A005245 values quoted from the DATA line.
--   ‖5‖ = 5, ‖6‖ = 5, ‖11‖ = 8, ‖12‖ = 7, ‖23‖ = 11, ‖24‖ = 9
example : complexityRec 5 = 5 ∧ complexityRec 6 = 5 := by native_decide
example : complexityRec 11 = 8 ∧ complexityRec 12 = 7 := by native_decide
example : complexityRec 23 = 11 ∧ complexityRec 24 = 9 := by native_decide

-- PROVABLE: the first three A244743 terms, in the `defect` reindexing.
--   a(0) = 6  ⟺  defect 5 = 0
--   a(1) = 12 ⟺  defect 11 = 1
--   a(2) = 24 ⟺  defect 23 = 2
example : defectRec 5 = 0 := by native_decide
example : defectRec 11 = 1 := by native_decide
example : defectRec 23 = 2 := by native_decide

-- PROVABLE: minimality of `a(1) = 12`, i.e. no smaller `n` has defect `1`.
-- This is the check that the DATA line is the *least* witness, not just *a*
-- witness — without it the card would archive a weaker claim than the source.
example : ∀ m ∈ Finset.range 11, defectRec m ≠ 1 := by native_decide

-- PROVABLE: minimality of `a(2) = 24`.
example : ∀ m ∈ Finset.range 23, defectRec m ≠ 2 := by native_decide

-- PROVABLE: satisfiability of `a244743_wellDefined` at `k = 0, 1, 2` — the
-- existential is instantiable, so the statement is not vacuous.
example : ∃ m : ℕ, defectRec m = 2 := ⟨23, by native_decide⟩

-- PROVABLE: the defect really does go negative, so `a244743_defect_unbounded`
-- is not a statement about a monotone quantity.  `defect 1 = ‖1‖ − ‖2‖ = −1`.
example : defectRec 1 = -1 := by native_decide

/-! ## Notes for a follow-up card

`neg_one_le_defect` is provable today from `complexity_add_le` and
`complexity_one` and should be discharged rather than archived: it is the
statement that A244743 is a sequence of *nonnegative*-indexed defects at all,
and it is the only nontrivial general fact about the defect that is currently in
reach.

Beyond `k = 2` the sanity layer stops being cheap: `a(3) = 108` needs
`‖107‖ = 14`, and `complexityRec` is exponential-ish in practice.  Certifying
`a(4) = 720` (`‖719‖`) is likely infeasible with the current `complexityFuel`
implementation; if a card wants it, the right move is a memoised
bottom-up table, not a bigger fuel bound. -/

/-!
## Adversarial review verdict — **PASS** (no defects)

Independent re-pull of A244743 and A005245 by a source-fidelity reviewer,
2026-08-05.

Confirmed:
* `%O A244743 0,1` — offset `0`, as claimed.
* **The index shift is correct.**  Reading `‖·‖` off the A005245 DATA line
  (offset 1): `‖5‖ = ‖6‖ = 5`, `‖11‖ = 8`, `‖12‖ = 7`, `‖23‖ = 11`, `‖24‖ = 9`.
  So `defectRec 5 = 0`, `defectRec 11 = 1`, `defectRec 23 = 2`, and
  `a(k) = 1 + (least m with defect m = k)` reproduces `6, 12, 24`.
* `a244743_wellDefined` is genuinely **stronger** than
  `a244743_defect_unbounded`: unboundedness alone could skip values.
* Casts precede subtraction, per STYLE.md.
* `neg_one_le_defect` is true (`‖m+1‖ ≤ ‖m‖ + 1` via `complexity_add_le`),
  and the A005245 data never dips below `−1`.
* All cited `NumberComplexity.IntComplexity` names and signatures match
  (`complexity` noncomputable at `:132`, `complexityRec` at `:386`,
  `complexity_eq_complexityRec` at `:552`, `complexity_zero/one/add_le/mul_le/le_self`).
* The `native_decide`-vs-`decide` reasoning is sound and the `n ≤ 23` sweeps are
  judged feasible under `native_decide`.
-/

end Candidates.A244743
