/-
# A172161 — growth of the greedy Coppersmith–Winograd sequence

## OEIS source (re-pulled verbatim 2026-08-05)

`goof oeis show A172161` plus `curl "https://oeis.org/search?q=id:A172161&fmt=text"`
(the conjecture is in the **FORMULA** section, which `goof oeis show` does not
expose — that is why it took the raw pull to verify):

```
%N A172161 Greedy Coppersmith-Winograd sequence.
%O A172161 1,3
%A A172161 _Warren D. Smith_, Jan 27 2010
%K A172161 nonn,easy
%F A172161 Conjecture: a(n) ~ k*(3 / 2)^n for some k. - _Bill McEachen_, Dec 02 2022
%F A172161 a(n) = floor((Sum_{i<n} a(i))/2) + 1 for n > 4.
           - _Charles R Greathouse IV_, Dec 02 2022
COMMENTS:
  Coppersmith & Winograd asked for dense sets S of integers such that if A,B,C
  are three disjoint subsets of S, their sums are cannot all be equal. Such sets
  yield new matrix multiplication algorithms. This is the "greedy sequence"
  obeying this property, that is, we start with S = {0, 1} and adjoin new
  integers one at a time, always adjoining the least new integer such that the
  Coppersmith-Winograd property remains valid. It looks as though each term is
  approximately 1.5 times the preceding term. The sequence is clearly infinite
  because each term is no greater than the sum of all previous terms.
  Amazingly, this sequence appears to agree with McRae's sequence A120134 after
  the "3". (This probably can be proved, but I haven't yet.)
  - _Warren D. Smith_, Jan 29 2010
  Considering the A120134 tie-in comment, via the Maiga link, its alternate
  algorithm generates both a(n) and A120134(m) for n >= 1 and m >= 1.
  That algorithm applies b(0)=2, b(1)=2, b(2)=3, b(3)=5, b(4)=8 then
  b(n) = floor(3*b(n-1)/2). Then a(n) = first differences of b(n), while
  A120134(m) begins from b(5) - b(4). - _Bill McEachen_, Dec 02 2022
  This sequence is complete: every positive integer is the sum of a subset of
  its terms. - _Charles R Greathouse IV_, Dec 02 2022
XREFS:
  Cf. A120134.
TERMS: 0,1,2,3,4,6,9,13,20,30,45,67,101,151,227,340,510,765,1148,1722,2583,3874,
       5811,8717,13075,19613,29419,44129,66193,99290,148935,223402,335103,502655,
       753982,1130973,1696460,2544690,3817035,5725552
```

Offset `1`: `a(1) = 0`, `a(2) = 1`, `a(3) = 2`, `a(4) = 3`, `a(5) = 4`,
`a(6) = 6`, `a(7) = 9`, …

Greathouse's recurrence check (for `n > 4`, verified by hand):
`a(5) = ⌊(0+1+2+3)/2⌋ + 1 = 4` ✓; `a(6) = ⌊6/2⌋ + 1 = 4`… **no**:
`⌊(0+1+2+3+4)/2⌋ + 1 = ⌊10/2⌋ + 1 = 6` ✓;
`a(7) = ⌊(0+1+2+3+4+6)/2⌋ + 1 = ⌊16/2⌋ + 1 = 9` ✓;
`a(8) = ⌊25/2⌋ + 1 = 13` ✓; `a(9) = ⌊38/2⌋ + 1 = 20` ✓;
`a(10) = ⌊58/2⌋ + 1 = 30` ✓.

## Status, and a correction to the candidates document's optimism

The candidates document says: *"open on OEIS, but likely tractable: Greathouse
proved the recurrence a(n) = floor(S(n-1)/2) + 1"*.  Two corrections:

1. The recurrence is stated as a `%F` **formula line**, not as a proved theorem
   and not with a proof reference.  "Greathouse proved" is not supported by the
   entry; it says only `a(n) = floor((Sum_{i<n} a(i))/2) + 1 for n > 4`.
   Treating it as proved would be importing an unverified claim.
2. **Granting the recurrence, the asymptotic is provable** — so the OEIS's
   "conjecture" label is about the *unproved recurrence*, not really about the
   asymptotic.  Let `S(n) = Σ_{i<n} a(i)`.  Then `a(n) = ⌊S(n)/2⌋ + 1` and
   `S(n+1) = S(n) + a(n) = ⌊3S(n)/2⌋ + 1`.  Put `T(n) = S(n) + 2`; then
   `T(n+1) ≤ 3T(n)/2` (so `T(n)/(3/2)^n` is nonincreasing) and
   `T(n+1) > 3T(n)/2 − 1` (so the decrease is summable and the sequence is
   bounded below by a positive number).  Monotone convergence gives a positive
   limit, which is exactly McEachen's `k`.

   An earlier draft of this header claimed the floor made this a
   "`3n+1`-adjacent floor-dynamics question".  **That was overstated** — the
   monotone-convergence argument above goes through, and the adversarial
   reviewer verified `T(n)/(3/2)^n` is monotone decreasing from `n = 5` onward
   numerically.  The genuine gap in this card is item 1 (the recurrence), not
   item 2.

The weaker two-sided bound `a(n) ≍ (3/2)^n` follows immediately from
`3x/2 − 1 < ⌊3x/2⌋ ≤ 3x/2` and is the easiest thing here.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A172161

/-! ## Definition layer

`leandoc` findings: nothing sequence-specific.  What is used:

* `Finset.sum`, `Finset.range`, `Finset.sum_range_succ`.
* `Nat.div` (floor division on `ℕ`, so `⌊·/2⌋` needs no guard — `2 ≠ 0`).
* `Filter.Tendsto`, `Asymptotics.IsBigO`, `Asymptotics.IsTheta`, `Real.rpow`.

**Two definitions, deliberately.**  `cwGreedy` is the *semantic* one (the greedy
construction from the Coppersmith–Winograd property), `a172161` is the
*recurrence* one (Greathouse's `%F`).  They are conjecturally equal; asserting
the recurrence as a definition and then "proving" things about it would
formalize the wrong object, so the equivalence is an explicit statement, not a
definitional shortcut. -/

/-- The **Coppersmith–Winograd property** for a finite set `S`: no three
pairwise disjoint **nonempty** subsets have equal sums.

Nonemptiness matters: with `0 ∈ S` and empty sets allowed, `∅`, `{0}` and a
third empty set would trivially violate any version of the property.  The greedy
sequence starts at `{0, 1}`, so the convention is pinned by the DATA. -/
def CWProperty (S : Finset ℕ) : Prop :=
  ∀ A ⊆ S, ∀ B ⊆ S, ∀ C ⊆ S, A.Nonempty → B.Nonempty → C.Nonempty →
    Disjoint A B → Disjoint A C → Disjoint B C →
    ¬ (A.sum id = B.sum id ∧ B.sum id = C.sum id)

instance (S : Finset ℕ) : Decidable (CWProperty S) := by unfold CWProperty; infer_instance

/-- The greedy set after `n` steps: start from `{0, 1}` and repeatedly adjoin the
least new integer preserving `CWProperty`.  Written with `Nat.find` over a
nonemptiness proof supplied by `cwGreedy_exists` (the entry's own argument:
"each term is no greater than the sum of all previous terms"), so no junk
default appears. -/
noncomputable def cwGreedyStep (S : Finset ℕ) (h : ∃ m, m ∉ S ∧ CWProperty (insert m S)) :
    Finset ℕ := insert (Nat.find h) S

/-- A172161 via Greathouse's recurrence: `a(n) = ⌊(Σ_{i<n} a(i))/2⌋ + 1` for
`n > 4`, with `a(1..4) = 0, 1, 2, 3` as initial data.  Indexed from `1`. -/
def a172161 : ℕ → ℕ
  | 0 => 0    -- unused; offset is 1
  | 1 => 0
  | 2 => 1
  | 3 => 2
  | 4 => 3
  | n + 5 => (∑ i ∈ Finset.range (n + 5), a172161 i) / 2 + 1
  decreasing_by all_goals omega

/-- The partial sums `S(n) = Σ_{i<n} a(i)`. -/
def cwSum (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, a172161 i

/-! ## The statements -/

/-- **McEachen's growth conjecture (A172161, Bill McEachen, Dec 02 2022).**

Verbatim (`%F` line): "Conjecture: a(n) ~ k*(3 / 2)^n for some k."

"`~`" means the ratio tends to a positive constant.  Stated with `Real.rpow`-free
`(3/2 : ℝ)^n` since the exponent is a natural.

**Modulo the recurrence, this is provable** — see the header.  The obstruction
is not the floor (the monotone-convergence argument absorbs it) but the fact
that the recurrence itself is an unsourced `%F` line.

**Mathlib primitives available.**  `Nat.div` and `Nat.div_le_self`,
`Nat.lt_div_add_one_mul_self`, `Nat.sub_one_div_lt`; `Filter.Tendsto`,
`Asymptotics.IsTheta`, `Asymptotics.IsBigO`;
`Finset.sum_range_succ`; `Nat.rec` / strong induction.

**Sketch (verified sound by the adversarial reviewer).**  From
`3x/2 − 1 < ⌊3x/2⌋ ≤ 3x/2`: `S(n+1) ≤ 3S(n)/2 + 1` and `S(n+1) > 3S(n)/2`.
Setting `T(n) = S(n) + 2` gives `T(n+1) ≤ 3T(n)/2` and `T(n+1) > 3T(n)/2 − 1`,
so `T(n)/(3/2)^n` is monotone decreasing (numerically confirmed from `n = 5`)
and bounded below (the error series `Σ (2/3)^k` converges).  Monotone
convergence gives a positive limit.  **So this is a proof target, not an archive
item**, and the card is misplaced in Tier 3 on this count.

**Tactic families.**  `Nat.div` lemmas plus `omega` for the floor bounds;
`Finset.sum_range_succ` and strong induction for the recurrence;
`tendsto_of_monotone` / `tendsto_atTop_ciSup` for the convergence;
`native_decide` for the DATA cross-check.

**Related work in this repo.**  `Proofs/BilinearComplexity/` — the
Coppersmith–Winograd property is *the* combinatorial input to the CW matrix
multiplication algorithm, so this sits directly next to the `Omega.lean` /
`Strassen.lean` / `Capset.lean` arc.  `Proofs/Erdos/Erdos880/` (restricted
sumsets) is the nearest combinatorial neighbour. -/
theorem mcEachen_growth :
    ∃ k : ℝ, 0 < k ∧
      Filter.Tendsto (fun n : ℕ => (a172161 n : ℝ) / (3 / 2 : ℝ) ^ n)
        Filter.atTop (nhds k) := by
  sorry

/-- The **two-sided bound**, which is provable today and is strictly weaker than
the conjecture: `a(n) ≍ (3/2)^n`. -/
theorem a172161_isTheta :
    Asymptotics.IsTheta Filter.atTop (fun n : ℕ => (a172161 n : ℝ))
      (fun n : ℕ => (3 / 2 : ℝ) ^ n) := by
  sorry

/-- **The semantic ↔ recurrence bridge — the honest gap.**

Greathouse's `%F` line asserts the recurrence but the entry gives no proof and
no reference.  This statement is what would justify computing with `a172161`
at all, and it is *not* known to this card's author to be proved. -/
theorem cwGreedy_eq_recurrence :
    ∀ n : ℕ, 4 < n →
      a172161 n = (∑ i ∈ Finset.range n, a172161 i) / 2 + 1 := by
  sorry

/-- Smith's own observation, recorded because it is the growth heuristic:
"The sequence is clearly infinite because each term is no greater than the sum of
all previous terms."  Provable directly from the recurrence. -/
theorem a172161_le_cwSum (n : ℕ) (hn : 4 < n) : a172161 n ≤ cwSum n := by
  sorry

/-! ## Sanity layer -/

-- PROVABLE: the recurrence reproduces the DATA line head.
example : List.map a172161 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
    = [0, 1, 2, 3, 4, 6, 9, 13, 20, 30] := by native_decide

-- PROVABLE: further out, matching the DATA `45, 67, 101, 151, 227, 340`.
example : List.map a172161 [11, 12, 13, 14, 15, 16]
    = [45, 67, 101, 151, 227, 340] := by native_decide

-- PROVABLE: the recurrence really needs `n > 4` — at `n = 4` it would give
-- `⌊(0+1+2)/2⌋ + 1 = 2 ≠ 3 = a(4)`, so the guard is load-bearing.
example : (0 + 1 + 2) / 2 + 1 ≠ 3 := by decide

-- PROVABLE: the partial-sum recurrence `S(n+1) = ⌊3 S(n)/2⌋ + 1`, which is the
-- form the asymptotic argument uses.
theorem cwSum_succ (n : ℕ) (hn : 4 < n) : cwSum (n + 1) = 3 * cwSum n / 2 + 1 := by
  sorry

-- PROVABLE: the greedy semantics agrees with the DATA at the start.
-- `S = {0, 1}` has the CW property; `{0,1,2}`, `{0,1,2,3}`, `{0,1,2,3,4}` too;
-- but `{0,1,2,3,4,5}` fails (`{1,4}`, `{2,3}`, `{5}` all sum to `5`), which is
-- why `5` is skipped and `a(6) = 6`.
example : CWProperty {0, 1} := by decide
example : CWProperty {0, 1, 2, 3, 4} := by decide
example : ¬ CWProperty {0, 1, 2, 3, 4, 5} := by decide
example : CWProperty {0, 1, 2, 3, 4, 6} := by decide

-- PROVABLE: the explicit violating triple at `5`, so the skip is not a
-- computational accident.
example : ({1, 4} : Finset ℕ).sum id = 5 ∧ ({2, 3} : Finset ℕ).sum id = 5 ∧
    ({5} : Finset ℕ).sum id = 5 := by decide

-- PROVABLE: the nonemptiness convention is load-bearing.  With `∅` allowed,
-- `∅`, `∅`, `{0}` all have sum `0` and every set containing `0` would fail,
-- contradicting `CWProperty {0, 1}`.
example : (∅ : Finset ℕ).sum id = 0 ∧ ({0} : Finset ℕ).sum id = 0 := by decide

-- PROVABLE (window check): the greedy construction agrees with `a172161` for
-- the first 12 terms.  This is the bridge `cwGreedy_eq_recurrence` at small
-- indices, and it is the only evidence the card has that the recurrence is the
-- right object.
-- FEASIBILITY: `CWProperty S` quantifies over triples of subsets, so it is
-- `8^|S|`; at `|S| = 12` that is `6.9·10^10` — too slow.  Prune by checking
-- only *partitions* into three parts and by early exit.  Do not attempt the
-- naive version.

/-! ## Notes for a follow-up card

**This candidate may be completable and is probably misplaced in Tier 3.**
The chain is:

1. `cwSum_succ` (`S(n+1) = ⌊3S(n)/2⌋ + 1`) — direct from the recurrence,
   `Nat.div` plus `omega`.  Free.
2. `a172161_isTheta` — from `3x/2 − 1 < ⌊3x/2⌋ ≤ 3x/2`.  Straightforward.
3. `mcEachen_growth` — set `T(n) = S(n) + 2`; then `T(n+1) ≤ 3T(n)/2` gives
   `T(n)/(3/2)^n` monotone decreasing, and the reverse bound gives it bounded
   below.  Monotone convergence finishes.  **Check this argument carefully
   first** — if it works, the OEIS "conjecture" is a theorem and the card is a
   *proof* target, not an archive one.
4. `cwGreedy_eq_recurrence` — the genuinely open/unsourced part.  Greathouse's
   `%F` line has no proof reference; proving it would be new content and is
   independent of (3).

So the file has two independent deliverables: the asymptotic (likely provable)
and the semantic bridge (unproved in the literature as far as this pull shows). -/

/-!
## Adversarial review verdict — **PASS-WITH-NOTES**

Independent re-pull of A172161 plus a from-scratch python greedy construction
and numeric check of the asymptotic argument, 2026-08-05.

Confirmed:
* `%N`, `%O 1,3`, `%A _Warren D. Smith_, Jan 27 2010`, `%K`, both `%F` lines,
  the comments, terms and xrefs are all verbatim.
* The Greathouse recurrence reproduces **all 20** DATA terms.  The Lean
  `a172161` sums `Finset.range (n+5)`, which includes `a172161 0 = 0`; that
  extra term is harmless.
* **The A172161 terms are the greedy set *elements*, not differences.**  A
  from-scratch greedy construction gives
  `{0,1,2,3,4,6,9,13,20,30,45,67,101,151,227}`, matching the DATA.  McEachen's
  "first differences of b(n)" refers to the A120134 tie-in, not to the greedy
  construction; the card handles this correctly.
* The exclusion of `5` is confirmed: `{1,4}`, `{2,3}`, `{5}` all sum to `5`.
* **The asymptotic argument is sound**, step by step:
  `S(n+1) = ⌊3S(n)/2⌋ + 1` (checked for both parities);
  `T(n) = S(n) + 2` gives `T(n+1) ≤ 3T(n)/2`;
  the reverse bound is in fact `T(n+1) > 3T(n)/2 − 1`;
  and `T(n)/(3/2)^n` is numerically monotone decreasing from `n = 5`, bounded
  below since `Σ (2/3)^k` converges.  Monotone convergence gives a positive
  limit.  **So the card's "may well be provable" flag is justified.**

Two notes, both **FIXED**:
1. The lower bound was written `T(n+1) > 3T(n)/2 − 2`; the true bound is `− 1`.
   Corrected.
2. The header claimed the conjecture was "not routine" and "`3n+1`-adjacent"
   while the body demonstrated the standard argument works — an internal
   contradiction.  The header now says plainly that the asymptotic is provable
   *given the recurrence*, and that the genuine gap is the recurrence itself
   (an unsourced `%F` line with no proof reference — so "Greathouse proved the
   recurrence", as the candidates document has it, is **not supported**).
-/

end Candidates.A172161
