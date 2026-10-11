/-
  Erdős Problem #124 — completeness of sums of power-sets (second
  question).
  Status: open (second question ONLY; the first was proved and
  Lean-formalized by Alexeev/Aristotle, Nov 2025, per the DB).
  Tier UC lemma mine (completeness criterion + the {3,4,7} case).

  Verbatim statement (`goof erdos fetch 124`, pulled 2026-08-05):

    "For any $d\geq 1$ and $k\geq 0$ let $P(d,k)$ be the set of
    integers which are the sum of distinct powers $d^i$ with
    $i\geq k$. Let $3\leq d_1<d_2<\cdots <d_r$ be integers such that
    \[\sum_{1\leq i\leq r}\frac{1}{d_r-1}\geq 1.\]
    Can all sufficiently large integers be written as a sum of the
    shape $\sum_i c_ia_i$ where $c_i\in \{0,1\}$ and
    $a_i\in P(d_i,0)$?

    If we further have $\mathrm{gcd}(d_1,\ldots,d_r)=1$ then, for any
    $k\geq 1$, can all sufficiently large integers be written as a sum
    of the shape $\sum_i c_ia_i$ where $c_i\in \{0,1\}$ and
    $a_i\in P(d_i,k)$?"

  (NB the source's `1/(d_r−1)` is a typo for `1/(d_i−1)` — summed
  over i; kept verbatim above, formalized with the intended index.)

  DB remarks: second question conjectured by Burr–Erdős–Graham–Li
  [BEGL96], proved there for {3, 4, 7}.  First question: proved (and
  formalised in Lean) by Aristotle/Alexeev — only the SECOND question
  is open and carded here.  Pomerance: ∑ 1/(d_i − 1) ≥ 1 is necessary
  for both.  Melfi [Me04]: an infinite d-set variant with small sum.

  Mathlib inventory: `Finset.sum` over powers; no completeness
  criterion API — the sorted-partial-sum criterion is the reusable
  piece destined for `Proofs/Enumerative`.
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E124

/-- `PowSumSet d k`: integers of the form `∑_{i ∈ S} d^i` over finite
    index sets `S` with all exponents `≥ k` — the `P(d, k)` of the
    problem.  `0` (empty `S`) is included, which harmlessly absorbs
    the `c_i ∈ {0,1}` choice: `c_i = 0` ⟺ pick `a_i = 0`. -/
def PowSumSet (d k : ℕ) : Set ℕ :=
  {m : ℕ | ∃ S : Finset ℕ, (∀ i ∈ S, k ≤ i) ∧ m = ∑ i ∈ S, d ^ i}

/-- Ground truth: `P(3,1)` contains `0, 3, 9, 12, 27, 30, …`;
    `12 = 3 + 9` ∈ P(3,1), `4 = 1 + 3 ∉ P(3,1)` (needs exponent 0).
    -- PROVABLE (witness / small case analysis). -/
example : (12 : ℕ) ∈ PowSumSet 3 1 ∧ (4 : ℕ) ∉ PowSumSet 3 1 := by
  sorry

/-- `CompleteFor ds k`: all sufficiently large integers are sums
    `∑ a_i` with `a_i ∈ P(d_i, k)` (one term per base, zeros
    allowed = the `c_i ∈ {0,1}` form). -/
def CompleteFor (ds : List ℕ) (k : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ f : ℕ → ℕ, (∀ j < ds.length, f j ∈ PowSumSet (ds.getD j 0) k) ∧
      n = ∑ j ∈ Finset.range ds.length, f j

/-- **Erdős #124, second question (OPEN)**: if `3 ≤ d₁ < ⋯ < d_r`
    with `∑ 1/(d_i − 1) ≥ 1` and `gcd(d₁, …, d_r) = 1`, then for
    every `k ≥ 1` all sufficiently large integers are `{0,1}`-sums of
    elements of the `P(d_i, k)`.

    Stated over a strictly-sorted list `ds` with the harmonic
    condition in ℚ and the gcd via `List.foldr Nat.gcd 0`. -/
theorem erdos_124_second (ds : List ℕ) (k : ℕ) (hk : 1 ≤ k)
    (hsort : ds.Sorted (· < ·)) (h3 : ∀ d ∈ ds, 3 ≤ d)
    (hsum : 1 ≤ ∑ j ∈ Finset.range ds.length,
      (1 : ℚ) / ((ds.getD j 0 : ℚ) - 1))
    (hgcd : ds.foldr Nat.gcd 0 = 1) :
    CompleteFor ds k := by
  sorry

/-- **BEGL {3,4,7} case** ([BEGL96]) — the explicit bounded target:
    `1/2 + 1/3 + 1/6 = 1` and `gcd(3,4,7) = 1`; for every `k ≥ 1`
    the triple `(3,4,7)` is complete at level `k`.  The BEGL proof is
    an explicit finite-automaton/greedy argument — formalizable with
    effort M–L. -/
theorem begl_347 (k : ℕ) (hk : 1 ≤ k) : CompleteFor [3, 4, 7] k := by
  sorry

/-- Sanity for the hypothesis arithmetic of the {3,4,7} case:
    `1/(3−1) + 1/(4−1) + 1/(7−1) = 1` exactly, and `gcd(3,4,7) = 1`.
    -- PROVABLE (norm_num / decide). -/
example : (1 : ℚ) / 2 + 1 / 3 + 1 / 6 = 1 ∧
    Nat.gcd 3 (Nat.gcd 4 7) = 1 := by
  sorry

/-- **Pomerance's necessity** (recorded in DB; Tao sketched the
    argument in comments): if `∑ 1/(d_i − 1) < 1` then completeness
    FAILS at every level — the density of representable integers is
    too small.  The formalizable counting slice: the number of
    `{0,1}`-sums of P(d_i, 0)-elements below `X` is
    `O(X^{∑ 1/(d_i−1)})`-ish… archived at the qualitative level. -/
theorem pomerance_necessity (ds : List ℕ) (hsort : ds.Sorted (· < ·))
    (h3 : ∀ d ∈ ds, 3 ≤ d)
    (hsum : ∑ j ∈ Finset.range ds.length,
      (1 : ℚ) / ((ds.getD j 0 : ℚ) - 1) < 1) :
    ¬ CompleteFor ds 0 := by
  sorry

/-- The **sorted-partial-sum completeness criterion** (the reusable
    `Proofs/Enumerative` asset used by the Aristotle proof of question
    one): if a strictly increasing enumeration `a` of a set of
    positive integers satisfies `a(m+1) ≤ 1 + ∑_{j ≤ m} a j` for all
    `m ≥ M` (and the initial segment reaches every residue…),
    then all sufficiently large integers are finite subset-sums.
    Stated in the clean single-sequence form. -/
theorem partial_sum_completeness (a : ℕ → ℕ) (ha : StrictMono a)
    (h1 : ∀ m : ℕ, a (m + 1) ≤ 1 + ∑ j ∈ Finset.range (m + 1), a j)
    (h0 : a 0 = 1) :
    ∀ n : ℕ, ∃ S : Finset ℕ, n = ∑ i ∈ S, a i := by
  sorry

end ErdosCandidates.E124

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - Verbatim statement matches DB text (including the d_r typo).
   - The file correctly identifies the DB's "1/(d_r-1)" as a typo for "1/(d_i-1)".
     Confirmed by RealBelgian's comment (May 2026) on the DB itself. The Lean
     formalization correctly uses the intended per-index sum.
   - First question proved by Aristotle/Alexeev (Nov 2025); only second question
     (with gcd condition and k >= 1) is open. Matches DB remarks and comments.
   - BEGL {3,4,7}: 1/(3-1)+1/(4-1)+1/(7-1) = 1/2+1/3+1/6 = 1. Correct.
     gcd(3,4,7) = 1. Correct.
   - 12 = 3^1 + 3^2 = 3+9 in P(3,1). Correct. 4 = 3^0+3^1 needs exponent 0,
     so 4 not in P(3,1). Correct.
   - Pomerance necessity (sum < 1 implies not complete) matches DB.
   - Lean types faithful to the mathematical content.
-/
