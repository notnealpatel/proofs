/-
# A390813 — Erdős: Sidon subsets of the squares

## OEIS source (re-pulled verbatim with `goof oeis show A390813`, 2026-08-05)

```
NAME:     a(n) is the size of the largest Sidon subset of the first n positive
          perfect squares.
TERMS:    1,2,3,4,5,6,6,7,8,9,9,9,10,10,11,12,12,13,13,13,14,14,14,15,16,17,17,
          17,17,18,19,19,19,20,20,20,21,21,22,22,22,22,23,24,24,24,24,25,25,26,
          26,27,27,27,27,28,28,29,29,29,30,30,30,31,31,31,32,32
KEYWORDS: nonn
COMMENTS:
  A set S is a Sidon set if all sums of the form a + b (where a,b in S and
  a <= b) are distinct.
  Erdős asks if a(n) is n^(1-o(1)) (see Erdős problems link).
  Up to at least n=68, the case of n=32 is the only one where the maximum size
  cannot be attained with a subset that contains n^2.
  - _Christian Sievers_, Nov 27 2025
XREFS:
  Cf. A000290, A143824.
```

Offset `1`.  `a(7) = 6` is the first drop below `n`: the seven squares
`1, 4, 9, 16, 25, 36, 49` are **not** Sidon because `1 + 49 = 50 = 25 + 25`
(and `a ≤ b` permits `a = b`, so this counts as a collision).  Any six of them
work.

## "Asks", not "conjectures"

The entry says *"Erdős **asks** if a(n) is n^(1-o(1))"*.  That is a question, not
an asserted conjecture, and the card must not upgrade it.  The statement below
is therefore named `erdos_question_…` and the file also records its negation
with equal weight.

## Status

Open.  This is one of the Erdős problems (see the entry's "Erdős problems"
link).  The trivial bounds are `a(n) ≤ n` and `a(n) ≫ n^{1/2}` (any Sidon set
in `[1, n²]` has size `≪ n`, and the squares themselves contain large Sidon
subsets by greedy selection).
-/
import Mathlib
import Scratch.Candidates.A309370SidonHypercube

set_option autoImplicit false

namespace Candidates.A390813

open Candidates.A309370 (IsSidon)

/-! ## Definition layer

`IsSidon` is imported from `Scratch.Candidates.A309370SidonHypercube`:

```lean
def IsSidon {α : Type*} [AddCommMonoid α] [DecidableEq α] (S : Finset α) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)
```

**Are the two OEIS phrasings the same?**  A309370 says "the only solutions to
`a + b = c + d` are the trivial ones"; A390813 says "all sums `a + b` with
`a ≤ b` are distinct".  For a set of *numbers* these agree — the unordered-pair
sum map is injective iff the only `a+b = c+d` are trivial.  The equivalence is
in the PROVABLE layer (`isSidon_iff_sums_distinct`) rather than assumed, because
the two entries use different words and a silent identification is exactly the
kind of drift this card is supposed to catch.

`leandoc` confirms Mathlib has **no** Sidon-set predicate
(`grep -rn "Sidon" .lake/packages/mathlib/Mathlib/` is empty), so the shared
fresh definition is the only option. -/

/-- The first `n` positive perfect squares, `{1², 2², …, n²}`. -/
def squares (n : ℕ) : Finset ℕ := (Finset.Icc 1 n).image (fun k => k ^ 2)

/-- A390813: the size of the largest Sidon subset of the first `n` positive
squares.  `Finset.max'` on a nonempty set of achievable cardinalities; stated
via `sSup` over `ℕ`, whose junk value on `∅` is avoided by
`a390813_set_nonempty`. -/
noncomputable def a390813 (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ S ⊆ squares n, IsSidon S ∧ S.card = k}

/-! ## The question -/

/-- **Erdős's question (A390813).**

Verbatim: "Erdős asks if a(n) is n^(1-o(1)) (see Erdős problems link)."

`n^{1-o(1)}` unwinds to: for every `ε > 0`, eventually `a(n) ≥ n^{1-ε}`.
Stated with `Real.rpow` because the exponent is real.  Note this is **not** the
same as `a(n)/n → 1`; the DATA line shows `a(n)/n` decreasing (`a(68) = 32`), so
that stronger reading would be refuted by the data and must be avoided.

**Mathlib primitives available.**  `Real.rpow` and its API (`Real.rpow_natCast`,
`Real.rpow_le_rpow_left_iff`, `Real.rpow_natCast`), `Filter.atTop`,
`Filter.Eventually`, `Asymptotics.IsLittleO`.  Nothing Sidon-specific.

**Sketch of the two sides.**
* *Upper bound (easy).*  A Sidon subset of `[1, n²]` has
  `binom(|S|,2) ≤ n²`, so `|S| ≲ √2 · n`.  Combined with `|S| ≤ n` (the ambient
  set has `n` elements), `a(n) ≤ n` trivially.  So the question is entirely
  about the lower bound.
* *Lower bound (the content).*  A greedy/probabilistic argument gives
  `a(n) ≫ n^{1/3}` (each new square kills `O(k²)` candidates among `n`), which
  is far from `n^{1-o(1)}`.  Getting to `n^{1-o(1)}` would need the squares to
  behave "randomly" for additive quadruples `a² + b² = c² + d²` — and that
  equation has *many* solutions (it is the two-squares representation problem),
  which is precisely why the question is hard.  The number of solutions of
  `a² + b² = c² + d²` with all parts `≤ n` is `≍ n² log n`, so the "collision
  graph" on the `n` squares has `≍ n² log n / n = n log n` edges — a sparse but
  not-quite-forest graph, and its independence number is what `a(n)` is.
  So: **`a(n)` is the independence number of the collision graph on `{1,…,n}`
  given by `a² + b² = c² + d²`**, and Turán's bound gives `a(n) ≫ n/ log n`,
  which is *already* `n^{1-o(1)}`.  If that argument is correct the question is
  answerable — **so a card here should first check whether the Turán bound
  really applies**, i.e. whether the collision structure is genuinely a graph
  (pairwise) rather than a 4-uniform hypergraph.  It is a hypergraph
  (a collision involves four indices), which is why Turán does not immediately
  apply and the question stays open.  This trap is recorded so a follow-up does
  not fall into it.

**Tactic families.**  `decide`/`native_decide` for exact small values (the
search is over `2^n` subsets, so `n ≤ 20` needs pruning);
`Real.rpow` simp set; `Filter.eventually_atTop`; `Finset.card_le_card` for the
counting bounds.

**Related work in this repo.**  `A309370SidonHypercube.lean` (shared `IsSidon`),
`Proofs/Erdos/` (the Erdős-problem arc — this is one of the Erdős problems and
belongs there organizationally). -/
theorem erdos_question_sidon_squares :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) ^ (1 - ε) ≤ (a390813 n : ℝ) := by
  sorry

/-- The negation, stated with equal weight because the source *asks* rather than
conjectures. -/
theorem erdos_question_sidon_squares_neg :
    ∃ ε : ℝ, 0 < ε ∧ ∃ᶠ n : ℕ in Filter.atTop, (a390813 n : ℝ) < (n : ℝ) ^ (1 - ε) := by
  sorry

/-- The trivial upper bound, **provable today**: `a(n) ≤ n`. -/
theorem a390813_le (n : ℕ) : a390813 n ≤ n := by
  sorry

/-! ## Sanity layer -/

-- PROVABLE: the two OEIS phrasings of "Sidon" agree for sets of numbers.
theorem isSidon_iff_sums_distinct (S : Finset ℕ) :
    IsSidon S ↔ ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
      a ≤ b → c ≤ d → a + b = c + d → a = c ∧ b = d := by
  sorry

-- PROVABLE: `squares` ground truth.
example : squares 3 = {1, 4, 9} := by decide
example : squares 7 = {1, 4, 9, 16, 25, 36, 49} := by decide

-- PROVABLE: the collision that pins `a(7) = 6`.  `1 + 49 = 50 = 25 + 25`, and
-- the `a ≤ b` convention *permits* `a = b`, so this is a genuine collision.
-- Under a strict `a < b` reading it would not be, and `a(7)` would be `7` —
-- contradicting the DATA line.  This example fixes the convention.
example : ¬ IsSidon (squares 7) := by decide

-- PROVABLE: six of the seven squares *are* Sidon, so `a(7) = 6` is attained.
example : IsSidon ({1, 4, 9, 16, 36, 49} : Finset ℕ) := by decide

-- PROVABLE: the DATA head `a(1..6) = 1,2,3,4,5,6` — the first six squares are
-- Sidon outright.
example : IsSidon (squares 6) := by decide

-- PROVABLE: satisfiability and nondegeneracy.
example : IsSidon (∅ : Finset ℕ) := by decide
example : IsSidon ({1} : Finset ℕ) := by decide

-- PROVABLE: the `sSup` is over a nonempty bounded set, so `a390813 n` is not
-- the `sSup ∅ = 0` junk value.
theorem a390813_set_nonempty (n : ℕ) :
    {k : ℕ | ∃ S ⊆ squares n, IsSidon S ∧ S.card = k}.Nonempty := by
  sorry

-- PROVABLE: Sievers's observation, at the one exceptional index he reports.
-- "Up to at least n=68, the case of n=32 is the only one where the maximum size
-- cannot be attained with a subset that contains n^2."
-- Recorded as a target; verifying it needs the same search as `a390813 32`.

/-! ## Notes for a follow-up card

1. `isSidon_iff_sums_distinct` and `a390813_le` — provable today, and the first
   makes the shared `IsSidon` usable across both Sidon cards.
2. Exact values for `n ≤ 12` by pruned search — needs a computable mirror of
   `a390813` (it is `noncomputable`, being an `sSup` over a `Set ℕ`), same
   gating issue as `A244743ComplexityDefect.lean` and
   `A293771WhitneyMachine.lean`.
3. The greedy lower bound `a(n) ≫ n^{1/3}` — a real, provable theorem, and the
   first nontrivial statement about the sequence.
4. The question itself — open. -/

/-!
## Adversarial review verdict — **PASS-WITH-NOTES** (no defects)

Independent re-pull of A390813 by a source-fidelity reviewer, 2026-08-05.

Confirmed:
* `%O A390813 1,2` (offset `1`); `%A _Giorgos Kalogeropoulos_, Nov 20 2025`.
* **The DATA reproduces under the `a ≤ b` (equality-allowed) convention**:
  a python recomputation of "largest Sidon subset of `{1,4,…,n²}`" gives
  `1,2,3,4,5,6,6,7,8,9,9,9,10` for `n = 1..13`, matching the entry.  Under a
  strict `a < b` reading `a(7)` would be `7`, so the convention pin is real.
* `1 + 49 = 50 = 25 + 25` is the `a(7) = 6` obstruction, as claimed.
* The card does **not** upgrade Erdős's *question* to a conjecture: the theorem
  is named `erdos_question_…`, the docstring says "question", and the negation
  is stated with equal weight.
* The one-sided `n^{1−o(1)}` encoding is adequate **because** `a(n) ≤ n` is
  trivial, so the upper half of the two-sided definition is free.
* `IsSidon` really is declared in `Candidates.A309370`, and the module path
  `Scratch.Candidates.A309370SidonHypercube` is correct for
  `lakefile.toml`'s `[[lean_lib]] name = "Scratch", srcDir = "Proofs"`.
* `squares`, the `∃ S ⊆ t, P S` sugar, and the Sievers comment-only note are all
  well formed.

Notes: the collision-structure sketch in the main docstring is informally
phrased (the obstruction to Turán is that a Sidon set must avoid *all*
collisions simultaneously, not merely pairwise ones), but the warning it
carries is sound and achieves its purpose.
-/

end Candidates.A390813
