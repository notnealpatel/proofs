/-
  Erdős Problem #362 — subset-sum concentration (Erdős–Moser /
  Sárközy–Szemerédi / Halász).
  Status: proved.  Tier D archive with small-N sanity.

  Verbatim statement (`goof erdos fetch 362`, pulled 2026-08-05):

    "Let $A\subseteq \mathbb{N}$ be a finite set of size $N$. Is it
    true that, for any fixed $t$, there are
    \[\ll \frac{2^N}{N^{3/2}}\]
    many $S\subseteq A$ such that $\sum_{n\in S}n=t$?

    If we further ask that $\lvert S\rvert=l$ (for any fixed $l$)
    then is the number of solutions
    \[\ll \frac{2^N}{N^2},\]
    with the implied constant independent of $l$ and $t$?"

  DB remarks: Erdős–Moser proved the first bound with an extra
  (log N)^{3/2}; removed by Sárközy–Szemerédi [SaSz65] — first
  question YES.  Stanley [St80]: the maximizing set is the interval
  centered at 0 (over integer sets; Weisenberg's comment corrects the
  translation-invariance slip in the DB's earlier phrasing).  Second
  question YES by Halász [Ha77] (multi-dimensional concentration).

-/
import Mathlib
import Combinatorics.SubsetSumAntichain

set_option autoImplicit false

namespace ErdosCandidates.E362

/-- Ground truth: the subsets of `{1, 2, 3}` with sum `3` are `{3}` and `{1, 2}`. -/
example : sumCount {1, 2, 3} 3 = 2 := by
  decide

/-- **Erdős #362, first bound (Sárközy–Szemerédi)** ([SaSz65]): there
    is an absolute `C` with: for every finite `A` of positive
    integers (`0 ∉ A` — with 0 allowed the count doubles trivially
    but the bound shape survives; we take the honest positive-set
    reading of `A ⊆ ℕ`) of size `N ≥ 1` and every target `t`,
    `sumCount A t ≤ C·2^N/N^{3/2}` — stated multiplied out over ℝ.

    Archive rationale: the proof requires concentration estimates beyond
    the elementary Sperner bound proved below. -/
theorem sarkozy_szemeredi :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : Finset ℕ) (t : ℕ),
      (∀ a ∈ A, 1 ≤ a) → 1 ≤ A.card →
      (sumCount A t : ℝ) ≤ C * 2 ^ A.card / (A.card : ℝ) ^ ((3 : ℝ) / 2) := by
  sorry

/-- `sumCountSized A t l`: subsets of size `l` with sum `t`. -/
def sumCountSized (A : Finset ℕ) (t l : ℕ) : ℕ :=
  ((A.powersetCard l).filter (fun S => ∑ n ∈ S, n = t)).card

/-- **Erdős #362, second bound (Halász)** ([Ha77]): with the size
    restriction the count drops to `≪ 2^N/N²`, uniformly in `l` and
    `t`. -/
theorem halasz_sized :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : Finset ℕ) (t l : ℕ),
      (∀ a ∈ A, 1 ≤ a) → 1 ≤ A.card →
      (sumCountSized A t l : ℝ) ≤ C * 2 ^ A.card / (A.card : ℝ) ^ 2 := by
  sorry

/-- The elementary Sperner bound: equal-sum subsets of a positive set form
    an antichain under inclusion. This is the √N-weaker bound, not the sharp
    Sárközy–Szemerédi bound above. -/
theorem antichain_bound (A : Finset ℕ) (t : ℕ) (hA : ∀ a ∈ A, 1 ≤ a) :
    sumCount A t ≤ A.card.choose (A.card / 2) := by
  exact sumCount_le_choose A t hA

/-- Ground truth: the subsets of `{1, 2, 3, 4}` with sum `5` are
    `{1, 4}` and `{2, 3}`. -/
example : sumCount {1, 2, 3, 4} 5 = 2 := by
  decide

end ErdosCandidates.E362

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - Verbatim statement matches `goof erdos fetch 362` exactly.
   - Sarkozy-Szemeredi [SaSz65], Halasz [Ha77], Stanley [St80] attributions all
     confirmed.  Erdos-Moser extra (log N)^{3/2} factor matches the DB.
   - Weisenberg's comment (translation-invariance correction for Stanley's
     maximizer statement) is present in the docstring; the DB confirms the site
     was updated to address it.
   - 0 not-in A convention (1 <= a) is a defensible reading of A in N; the
     docstring correctly notes the trivial doubling if 0 is allowed.
   - Sanity arithmetic verified: sumCount {1,2,3} 3 = 2 ({3},{1,2}); sumCount
     {1,2,3,4} 5 = 2 ({1,4},{2,3}).
   - Antichain reasoning is sound: if all elements of A are >= 1, a proper
     superset has strictly larger sum, so same-sum subsets form an antichain
     under inclusion.  LYM then gives the C(N, N/2) bound.
-/
