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

  Mathlib inventory: `Finset.powerset`, `Finset.sum`;
  Littlewood–Offord material in Mathlib: leandoc probe
  ("littlewood offord") should be run at campaign start — the
  candidates doc flags possible existing material
  (Combinatorics/SetFamily? `Finset.exists_subset_sum...`); the
  Sárközy–Szemerédi proof itself is genuinely hard analysis.
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E362

/-- `sumCount A t`: the number of subsets of `A` with sum `t`. -/
def sumCount (A : Finset ℕ) (t : ℕ) : ℕ :=
  (A.powerset.filter (fun S => ∑ n ∈ S, n = t)).card

/-- Ground truth: `A = {1, 2, 3}`, `t = 3`: subsets {3} and {1,2} —
    `sumCount = 2`.  -- PROVABLE (decide). -/
example : sumCount {1, 2, 3} 3 = 2 := by
  sorry

/-- **Erdős #362, first bound (Sárközy–Szemerédi)** ([SaSz65]): there
    is an absolute `C` with: for every finite `A` of positive
    integers (`0 ∉ A` — with 0 allowed the count doubles trivially
    but the bound shape survives; we take the honest positive-set
    reading of `A ⊆ ℕ`) of size `N ≥ 1` and every target `t`,
    `sumCount A t ≤ C·2^N/N^{3/2}` — stated multiplied out over ℝ.

    Archive rationale: the proof is Fourier-analytic concentration
    (Littlewood–Offord technology); real work.  Check Mathlib's
    Littlewood–Offord holdings before scoping (leandoc probe listed
    in the header). -/
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

/-- The elementary Erdős–Moser-level warm-up — the genuinely
    formalizable slice: `sumCount A t ≤ C(N, ⌊N/2⌋)` — the number of
    subsets of any fixed sum is at most the largest binomial
    coefficient (Sperner-type: distinct-sum subsets of a positive set
    form an antichain? No — same-sum subsets form an ANTICHAIN under
    inclusion (a proper superset has strictly larger sum), and LYM /
    `Finset.card_le_choose...` applies).  Mathlib HAS Sperner-family
    material (`Finset.IsAntichain` + LYM in
    Combinatorics/SetFamily/LYM).  Effort S–M; lands
    `≪ 2^N/N^{1/2}` — the √N-weaker classical bound. -/
theorem antichain_bound (A : Finset ℕ) (t : ℕ) (hA : ∀ a ∈ A, 1 ≤ a) :
    sumCount A t ≤ A.card.choose (A.card / 2) := by
  sorry

/-- Sanity: the interval `A = {1, …, N}` at the central target
    realizes near-maximal concentration — small-N table:
    `sumCount {1,2,3,4} 5 = 3` ({1,4},{2,3},{5}? no 5 ∉ A: {1,4},
    {2,3} and... 5 = 1+4 = 2+3 → 2.  Recompute: subsets of {1,2,3,4}
    summing to 5: {1,4},{2,3} → 2.  -- PROVABLE (decide; the
    docstring miscount is corrected in the statement). -/
example : sumCount {1, 2, 3, 4} 5 = 2 := by
  sorry

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
     {1,2,3,4} 5 = 2 ({1,4},{2,3}).  Docstring self-corrects its initial
     miscount of 3.
   - Antichain reasoning is sound: if all elements of A are >= 1, a proper
     superset has strictly larger sum, so same-sum subsets form an antichain
     under inclusion.  LYM then gives the C(N, N/2) bound.
-/
