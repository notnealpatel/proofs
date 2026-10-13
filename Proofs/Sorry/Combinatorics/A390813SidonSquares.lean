/-
# A390813 — Erdős: Sidon subsets of the squares

## Preserved OEIS quotation from archive

Fresh retrieval unavailable (HTTP 503); contents not independently reverified
in this episode.

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
(and `a ≤ b` permits `a = b`, so this counts as a collision).  A six-element subset
works.

## "Asks", not "conjectures"

The entry says *"Erdős **asks** if a(n) is n^(1-o(1))"*.  That is a question, not
an asserted conjecture, and the card must not upgrade it.  The statement below
is therefore recorded as a named `Prop` definition `erdos_question_…`;
the file records the opposing alternative as another `Prop` definition.
Neither definition asserts or proves its proposition. Other theorem admissions
remain explicit and unresolved.

## Status

Open.  This is one of the Erdős problems (see the entry's "Erdős problems"
link).  The ambient-cardinality bound is `a(n) ≤ n`. No literature lower bound is
asserted here without a primary-paper audit.
-/
import Combinatorics.SidonSquares

set_option autoImplicit false

namespace Candidates.A390813

open Sidon (IsSidon)

/-- Compatibility alias for the first positive squares. -/
abbrev squares := SidonSquares.squares

/-- Compatibility alias for the maximum Sidon square-subset cardinality. -/
noncomputable abbrev a390813 := SidonSquares.a390813

/-! ## The question -/

/-- **Erdős's question (A390813), recorded as a proposition, not proved.**

Verbatim: "Erdős asks if a(n) is n^(1-o(1)) (see Erdős problems link)."

`n^{1-o(1)}` unwinds to: for every `ε > 0`, eventually `a(n) ≥ n^{1-ε}`.
Stated with `Real.rpow` because the exponent is real.  Note this is **not** the
same as `a(n)/n → 1`: that is a distinct and stronger assertion not expressed
by the question. Finite data alone do not settle either limit.

**Mathlib primitives available.**  `Real.rpow` and its API (`Real.rpow_natCast`,
`Real.rpow_le_rpow_left_iff`, `Real.rpow_natCast`), `Filter.atTop`,
`Filter.Eventually`, `Asymptotics.IsLittleO`.  Nothing Sidon-specific.

**Finite structural facts.** The ambient set has at most `n` elements, so
`a(n) ≤ n`. The lower-bound question remains open; no speculative collision
graph or unaudited greedy lower-bound derivation is used here.

**Tactic families.**  `decide`/`native_decide` for exact small values (the
search is over `2^n` subsets, so `n ≤ 20` needs pruning);
`Real.rpow` simp set; `Filter.eventually_atTop`; `Finset.card_le_card` for the
counting bounds.

**Related work in this repo.**  `A309370SidonHypercube.lean` (shared `IsSidon`),
`Proofs/Erdos/` (the Erdős-problem arc — this is one of the Erdős problems and
is retained under Sorry/Combinatorics in this migration). -/
def erdos_question_sidon_squares : Prop :=
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) ^ (1 - ε) ≤ (a390813 n : ℝ)

/-- The opposing alternative to Erdős’s question, recorded as a proposition,
not asserted as a theorem. The source asks rather than conjectures. -/
def erdos_question_sidon_squares_neg : Prop :=
    ∃ ε : ℝ, 0 < ε ∧ ∃ᶠ n : ℕ in Filter.atTop, (a390813 n : ℝ) < (n : ℝ) ^ (1 - ε)

-- These checks pin the new proposition definitions to the original formulas;
-- neither check supplies an inhabitant of either alternative.
example : erdos_question_sidon_squares ↔
    (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop,
      (n : ℝ) ^ (1 - ε) ≤ (a390813 n : ℝ)) := Iff.rfl

example : erdos_question_sidon_squares_neg ↔
    (∃ ε : ℝ, 0 < ε ∧ ∃ᶠ n : ℕ in Filter.atTop,
      (a390813 n : ℝ) < (n : ℝ) ^ (1 - ε)) := Iff.rfl

/-- The trivial upper bound, **provable today**: `a(n) ≤ n`. -/
theorem a390813_le (n : ℕ) : a390813 n ≤ n := SidonSquares.a390813_le n

/-! ## Sanity layer -/

/-- The two OEIS phrasings of Sidon agree for sets of natural numbers. -/
theorem isSidon_iff_sums_distinct (S : Finset ℕ) :
    IsSidon S ↔ ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
      a ≤ b → c ≤ d → a + b = c + d → a = c ∧ b = d :=
  SidonSquares.isSidon_iff_sums_distinct S

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
/-- The achievable-cardinality set is nonempty, so its supremum is not junk. -/
theorem a390813_set_nonempty (n : ℕ) :
    {k : ℕ | ∃ S ⊆ squares n, IsSidon S ∧ S.card = k}.Nonempty := SidonSquares.a390813_set_nonempty n

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
3. Any literature lower-bound formalization first needs a primary-paper audit.
4. The question itself — open. -/

/-!
## Amended representation review — unresolved alternatives

The old PASS-WITH-NOTES claim was unsound as a trust assessment: naming
opposing admitted assertions “questions” does not make asserting both as
theorems acceptable. Both are now `Prop` definitions with their original
quantifiers and inequalities, and neither is asserted. The remaining admitted
bounds and infrastructure are not proofs of either alternative.

Confirmed:
* `%O A390813 1,2` (offset `1`); `%A _Giorgos Kalogeropoulos_, Nov 20 2025`.
* **The DATA reproduces under the `a ≤ b` (equality-allowed) convention**:
  a python recomputation of "largest Sidon subset of `{1,4,…,n²}`" gives
  `1,2,3,4,5,6,6,7,8,9,9,9,10` for `n = 1..13`, matching the entry.  Under a
  strict `a < b` reading `a(7)` would be `7`, so the convention pin is real.
* `1 + 49 = 50 = 25 + 25` is the `a(7) = 6` obstruction, as claimed.
* The two alternatives are now proposition definitions, not opposing theorems.
* The one-sided `n^{1−o(1)}` encoding is adequate **because** `a(n) ≤ n` is
  trivial, so the upper half of the two-sided definition is free.
* `IsSidon` is now imported from production `Combinatorics.Sidon`; production
  modules do not import the archive.
* `squares`, the `∃ S ⊆ t, P S` sugar, and the Sievers comment-only note are all
  well formed.

Notes: the speculative collision-graph and greedy-bound prose has been removed.
-/

end Candidates.A390813
