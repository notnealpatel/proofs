/-
# A265262 — the Erdős–Turán additive basis conjecture via the hemitropic tree

## OEIS source (re-pulled verbatim 2026-08-05)

`goof oeis show A265262` plus `curl "https://oeis.org/search?q=id:A265262&fmt=text"`:

```
%N A265262 The tree of hemitropic sequences read by rows, arising from an
           Erdős-Turán conjecture.
%O A265262 0,3
%A A265262 _Labib Haddad_ and _Michel Marcus_, Dec 06 2015
%K A265262 nonn,tabf
%F A265262 For each k>=0, let u(k)=1 if k is in A, u(k)=0 is k is not in A. Then
           pA(n) = Sum_{k=0..floor(n/2)} u(k)*u(n-k). See formula (5) on p. 8
           and p. 28 in Haddad link.
%H A265262 P. Erdős and P. Turán, "On a problem of Sidon in additive number
           theory, and on some related problems", J. Lond. Math. Soc. 16 (1941),
           212-215.
%H A265262 Labib Haddad, "Some peculiarities of order 2 bases of N and the
           Erdos-Turan conjecture", arXiv:1507.05849 [math.NT], 2015
           (see The binary tree of hemitropic sequences chapter).
%H A265262 Wikipedia, "Erdős-Turán conjecture on additive bases".
TERMS: 1,1,2,0,1,1,2,0,1,1,2,1,2,2,3,0,1,1,2,0,1,1,2,0,1,1,2,1,2,2,3,0,1,1,2,0,
       1,1,2,1,2,2,3,1,2,2,3,0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,0,1,1,2,0,1,1,2,0,
       1,1,2,0,1,1,2,0,1,1,2,0,1,1,2
COMMENTS:
  Let A be a subset of the set N of nonnegative integers. Let pA(n) be the
  number of pairs (x, y) of elements of A such that n = x + y and x <= y. The
  sequence pA = [pA(0), pA(1), ... , pA(n), ... ] is called the profile of A. A
  Sidon set is a subset A whose profile has only 0's and 1's.
  An [order 2 additive] basis of N is a subset A whose profile has no 0's.
  Erdős and Turán conjectured that the profile of a basis is always unbounded
  (see the Erdős and Turán link). The conjecture is, up till now, still
  undecided.
  The tree below displays the infinite sequences [1, pA(2), ... ], associated to
  the profiles pA = [1, 1, pA(2), ... ] of all the subsets A of N to which 0 and
  1 belong. Those are the so-called hemitropic sequences. The Erdős-Turán
  conjecture would not hold if (and only if) the tree contained an infinite
  bounded branch with no 0's.
  The length of the n-th row is 2^n. The right leaf of a node is equal to the
  left leaf + 1.
XREFS:
  Cf. A004137, A066062, A217793.
```

Row structure, read off the TERMS with `2^n` per row (offset `0`):
row 0 `[1]`; row 1 `[1, 2]`; row 2 `[0, 1, 1, 2]`;
row 3 `[0, 1, 1, 2, 1, 2, 2, 3]`;
row 4 `[0, 1, 1, 2, 0, 1, 1, 2, 0, 1, 1, 2, 1, 2, 2, 3]`.

## Status

Open and famous.  Erdős–Turán 1941.

## Where the value of this card lies

The bare conjecture is one line and has no formalization content beyond the
statement.  **The interesting artifact is the entry's own equivalence**:

> "The Erdős-Turán conjecture would not hold if (and only if) the tree contained
> an infinite bounded branch with no 0's."

That is a König's-lemma-shaped statement, Lean handles those well, and
formalizing the *equivalence* is self-contained, novel, and does not require
settling anything.  It is the deliverable this card should aim at.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A265262

/-! ## Definition layer

`leandoc` findings:

* `leandoc "additive basis representation function"` → noise.  Mathlib has **no**
  representation function and **no** additive-basis predicate.  Defined fresh.
* `Finset.Nat.antidiagonal` / `Finset.antidiagonal` — the pairs `(x, y)` with
  `x + y = n`.  This is the right primitive for `profile` and avoids a
  hand-rolled filter over `Finset.range`.
* `BddAbove`, `Set.range`, `Set.Unbounded` — for "unbounded profile".
  STYLE.md warns against `iSup` over a bounded `Prop`; `¬ BddAbove (Set.range p)`
  is the safe spelling and is what is used.
* König's lemma: Mathlib has `WellFoundedOn`, `Set.Finite`, and
  `konigsLemma`-adjacent material?  `leandoc "Konig lemma"` finds
  `SimpleGraph.konigLemma`-free noise; the tree version would be
  `Nat.rec`+`Classical.choice` on a finitely-branching infinite tree, which is
  short to do by hand (`exists_seq_of_forall_finset_exists`-style). -/

/-- The **profile** (representation function) of `A ⊆ ℕ`:
`pA n = #{(x, y) : x, y ∈ A, x ≤ y, x + y = n}`.

Uses `Finset.antidiagonal n` — the pairs summing to `n` — filtered by
membership and `x ≤ y`.  The `x ≤ y` is the OEIS's unordered convention; the
ordered convention would double every value except the diagonal and give a
different sequence. -/
noncomputable def profile (A : Set ℕ) [DecidablePred (· ∈ A)] (n : ℕ) : ℕ :=
  ((Finset.antidiagonal n).filter (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 ≤ p.2)).card

/-- `A` is an **order-2 additive basis** of `ℕ`: its profile has no zeros, i.e.
every `n` is a sum of two elements of `A`. -/
def IsBasis2 (A : Set ℕ) [DecidablePred (· ∈ A)] : Prop := ∀ n : ℕ, 0 < profile A n

/-- `A` is a **Sidon set**: its profile takes only values `0` and `1`. -/
def IsSidonSet (A : Set ℕ) [DecidablePred (· ∈ A)] : Prop := ∀ n : ℕ, profile A n ≤ 1

/-- A **hemitropic sequence** is the profile of a subset containing `0` and `1`
(so `pA 0 = pA 1 = 1`).  This is the OEIS's own terminology; the tree's rows
enumerate these. -/
def Hemitropic (A : Set ℕ) [DecidablePred (· ∈ A)] : Prop := (0 : ℕ) ∈ A ∧ (1 : ℕ) ∈ A

/-! ## The conjecture -/

/-- **The Erdős–Turán conjecture on additive bases (A265262).**

Verbatim: "An [order 2 additive] basis of N is a subset A whose profile has no
0's. Erdős and Turán conjectured that the profile of a basis is always unbounded
(see the Erdős and Turán link). The conjecture is, up till now, still undecided."

`¬ BddAbove (Set.range …)` rather than `⨆ = ⊤`, per STYLE.md.

**Mathlib primitives available.**  `Finset.antidiagonal` and its API
(`Finset.Nat.antidiagonal_succ`, `Finset.Nat.sum_antidiagonal_eq_sum_range_succ`);
`BddAbove`, `Set.Unbounded`, `not_bddAbove_iff`;
`Finset.card_filter_le`, `Finset.card_le_card`.
Nothing about additive bases — that is all fresh.

**Sketch of the state of the art.**  Nothing close is known.  Erdős–Fuchs (1956)
shows the *average* of `pA` cannot be too close to a constant, which is a
different (and proved) statement; Ruzsa built a basis with
`Σ pA(n) x^n` well-behaved; Grekos–Haddad–Helou–Pihko showed
`limsup pA(n) ≥ 6`.  The conjecture as stated is untouched.

**Sketch of the tree reformulation, which is the formalizable content.**
For each `n`, `profile A n` depends only on `A ∩ [0, n]`.  Hence the map
`A ↦ (profile A 0, profile A 1, …)` factors through the finite prefixes, and
the set of prefixes of length `n` forms a binary tree of `2^n` nodes (the
membership decisions for `2, 3, …, n + 1`).  A branch is:
* *zero-free* iff the corresponding `A` is a basis, and
* *bounded* iff the corresponding profile is bounded.
So "no infinite bounded zero-free branch" is literally the conjecture.
The **content** is König: the tree is finitely branching, so
"no infinite bounded zero-free branch" ⟺ "for every bound `B`, the subtree of
nodes with all values in `[1, B]` is finite".  That reformulation is
self-contained and provable.

**Tactic families.**  `Finset.antidiagonal` simp set; `decide` on finite
prefixes; `Nat.rec` + `Classical.choice` for the König construction;
`Set.Finite.induction_on`; `omega` for the arithmetic.

**Related work in this repo.**  None directly.  `A309370SidonHypercube.lean` and
`A390813SidonSquares.lean` in this directory share the Sidon notion, and
`IsSidonSet` above is the "profile ≤ 1" phrasing of the same idea. -/
theorem erdosTuran_basis_profile_unbounded (A : Set ℕ) [DecidablePred (· ∈ A)]
    (hA : IsBasis2 A) : ¬ BddAbove (Set.range (profile A)) := by
  sorry

/-- **The tree reformulation — the formalizable deliverable.**

Verbatim: "The Erdős-Turán conjecture would not hold if (and only if) the tree
contained an infinite bounded branch with no 0's."

Stated as an equivalence between the conjecture and the nonexistence of a
uniformly bounded zero-free profile.  Note the right-hand side is *exactly* the
negation of the left in disguise; the mathematical content is the finitary
König step (`erdosTuran_konig` below), not this restatement.  Both are recorded
so the card's structure matches the entry's. -/
theorem erdosTuran_iff_no_bounded_branch :
    (∀ (A : Set ℕ) (_ : DecidablePred (· ∈ A)), IsBasis2 A →
        ¬ BddAbove (Set.range (profile A)))
      ↔ ¬ ∃ (A : Set ℕ) (_ : DecidablePred (· ∈ A)) (B : ℕ),
          (∀ n, 0 < profile A n) ∧ (∀ n, profile A n ≤ B) := by
  sorry

/-- **The König step — genuinely provable, and the novel content.**

`profile A n` depends only on `A ∩ [0, n]`, so the "profiles bounded by `B` with
no zeros" tree is finitely branching.  Hence a bounded zero-free *branch* exists
iff there are bounded zero-free prefixes of every length.  This converts an
infinitary statement into a family of finite ones and is what makes the tree
reformulation useful.

`profile_eq_of_inter_eq` below is the locality lemma it rests on. -/
theorem erdosTuran_konig (B : ℕ) :
    (∃ (A : Set ℕ) (_ : DecidablePred (· ∈ A)),
        (∀ n, 0 < profile A n) ∧ (∀ n, profile A n ≤ B))
      ↔ ∀ N : ℕ, ∃ (A : Set ℕ) (_ : DecidablePred (· ∈ A)),
          (∀ n ≤ N, 0 < profile A n) ∧ (∀ n ≤ N, profile A n ≤ B) := by
  sorry

/-! ## Sanity layer -/

-- PROVABLE: **locality** — `profile A n` depends only on `A ∩ [0, n]`.  This is
-- the lemma the whole tree picture rests on, and it is provable today.
theorem profile_eq_of_inter_eq {A A' : Set ℕ} [DecidablePred (· ∈ A)]
    [DecidablePred (· ∈ A')] (n : ℕ)
    (h : ∀ k ≤ n, (k ∈ A ↔ k ∈ A')) : profile A n = profile A' n := by
  sorry

-- PROVABLE: `profile ℕ n = ⌊n/2⌋ + 1` — the full set, whose profile is the
-- fastest-growing possible.  Ground truth for the fresh definition.
example : profile Set.univ 0 = 1 := by decide
example : profile Set.univ 1 = 1 := by decide
example : profile Set.univ 4 = 3 := by decide

-- PROVABLE: the hemitropic normalization.  `0, 1 ∈ A` forces `pA 0 = pA 1 = 1`,
-- which is why the tree's rows start `[1]` and `[1, 2]`.
theorem profile_zero_of_hemitropic {A : Set ℕ} [DecidablePred (· ∈ A)]
    (h : Hemitropic A) : profile A 0 = 1 ∧ profile A 1 = 1 := by
  sorry

-- PROVABLE: satisfiability — `ℕ` itself is a basis, so `IsBasis2` is
-- instantiable and `erdosTuran_basis_profile_unbounded` is not vacuous.
example : IsBasis2 (Set.univ : Set ℕ) := by
  sorry

-- PROVABLE: and its profile really is unbounded, so the conjecture's conclusion
-- is achievable rather than always-false.
example : ¬ BddAbove (Set.range (profile (Set.univ : Set ℕ))) := by
  sorry

-- PROVABLE: nondegeneracy in the other direction — the *even* numbers form a
-- non-basis (odd `n` has `profile = 0`), so `IsBasis2` is a real restriction.
example : ¬ IsBasis2 {n : ℕ | Even n} := by
  sorry

-- **ROW-INDEXING CONVENTION — RESOLVED.**
-- An earlier draft of this card flagged an apparent inconsistency (row 2 starts
-- with `0`, whereas `A ∩ [0,2] = {0,1}` gives `pA 2 = #{(1,1)} = 1`).  The
-- adversarial reviewer resolved it from the entry alone, no Haddad needed:
--
--   **row `n` stores `pA(n + 1)`, not `pA(n)`.**
--
-- The entry says so — "The tree below displays the infinite sequences
-- [1, pA(2), ...]" — and the entry's PARI program takes `polcoeff(pt, n+1)`.
-- Recheck: row 2, first node is `A ∩ [0,3] = {0,1}`, and `pA 3 = 0` (no pair
-- `x ≤ y` in `{0,1}` sums to `3`).  ✓  Matches the leading `0` of row 2.
--
-- Consequently the entry's "right leaf = left leaf + 1" rule reads: adjoining
-- `n + 2` to `A` adds exactly the pair `(0, n+2)` to the count at `pA(n + 2)`,
-- which is the row-`(n+1)` entry.  Recorded as a target below.

-- PROVABLE: the local recurrence behind "the right leaf of a node is equal to
-- the left leaf + 1".  Since `0 ∈ A`, inserting `m` into `A` adds exactly the
-- pair `(0, m)` to the count at `pA m`.
theorem profile_insert_self {A : Set ℕ} {m : ℕ} [DecidablePred (· ∈ A)]
    [DecidablePred (· ∈ insert m A)] (h0 : (0 : ℕ) ∈ A) (hm : m ∉ A) (hm0 : 0 < m) :
    profile (insert m A) m = profile A m + 1 := by
  sorry

-- PROVABLE: the resolved row-2 values.  `A ∩ [0,3] ⊇ {0,1}` and the four
-- membership choices for `{2, 3}` give `pA 3 ∈ {0, 1, 1, 2}`:
--   {0,1}       → pA 3 = 0
--   {0,1,3}     → pA 3 = 1   (pair (0,3))
--   {0,1,2}     → pA 3 = 1   (pair (1,2))
--   {0,1,2,3}   → pA 3 = 2   (pairs (0,3), (1,2))
-- which is exactly row 2 of the DATA line.
example : profile {0, 1} 3 = 0 := by decide
example : profile {0, 1, 3} 3 = 1 := by decide
example : profile {0, 1, 2} 3 = 1 := by decide
example : profile {0, 1, 2, 3} 3 = 2 := by decide

/-! ## Notes for a follow-up card

Order of attack:

1. `profile_eq_of_inter_eq` (locality) and `profile_zero_of_hemitropic` — free,
   and they are the foundation of everything else.
2. `erdosTuran_konig` — the finitary reduction.  This is the **deliverable**:
   self-contained, novel (Mathlib has no additive-basis material at all), and
   it does not require settling anything.
3. The explicit tree.  The row-indexing convention is now **resolved** (row `n`
   stores `pA(n + 1)`; see the sanity layer), so the tree can be built without
   first reading Haddad.  `profile_insert_self` is the local recurrence.
4. The conjecture itself — open since 1941.

References: Erdős & Turán, *On a problem of Sidon in additive number theory, and
on some related problems*, J. Lond. Math. Soc. 16 (1941) 212–215;
Haddad, arXiv:1507.05849. -/

/-!
## Adversarial review verdict — **PASS-WITH-NOTES**

Independent re-pull of A265262, 2026-08-05.

Confirmed:
* NAME, TERMS, COMMENTS, `%F`, `%H`, `%O 0,3`,
  `%A _Labib Haddad_ and _Michel Marcus_, Dec 06 2015` all verbatim.
* **The row split is right**: splitting the DATA at powers of two gives
  `[1] | [1,2] | [0,1,1,2] | [0,1,1,2,1,2,2,3] | [0,1,1,2,0,1,1,2,0,1,1,2,1,2,2,3]`.
* `Finset.antidiagonal n` over `ℕ` gives exactly the pairs summing to `n`
  (`Mathlib/Data/Finset/NatAntidiagonal.lean:39`), so `profile` is right, and
  `profile Set.univ 4 = 3` (pairs `(0,4), (1,3), (2,2)`).
* Mathlib has **no** additive-basis predicate and **no** representation function.
* `erdosTuran_iff_no_bounded_branch` is (as the file itself says) a logical
  restatement, not new content; `erdosTuran_konig` is genuinely true and
  genuinely needs König on a finitely-branching tree; `profile_eq_of_inter_eq`
  (locality) is true because `x + y = n` forces `x, y ≤ n`.

One defect, **FIXED**:
1. The card flagged the row-indexing convention as **UNRESOLVED** (row 2 starts
   with `0`, whereas `A ∩ [0,2] = {0,1}` gives `pA 2 = 1`).  The reviewer
   resolved it from the entry alone, without Haddad: **row `n` stores
   `pA(n + 1)`**, per the entry's own "[1, pA(2), …]" and its PARI program's
   `polcoeff(pt, n+1)`.  Recheck: `A ∩ [0,3] = {0,1}` gives `pA 3 = 0` ✓.
   The header note, the four row-2 `example`s, and `profile_insert_self` (the
   "right leaf = left leaf + 1" recurrence, now correctly indexed) were all
   rewritten.
-/

end Candidates.A265262
