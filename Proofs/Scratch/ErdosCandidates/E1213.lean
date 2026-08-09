/-
  Erdős Problem #1213 — equal-sum intervals in bounded-gap sequences.
  Status: proved (Hegyvári 1986).  Tier A proof target.

  Verbatim statement (`goof erdos fetch 1213`, pulled 2026-08-05):

    "Let $a,K\geq 1$. Does there exist $f(a,K)$ such that if
    \[a=a_1<\cdots <a_s\]
    is a sequence of integers with $a_s> f(a,K)$ and with bounded gaps
    $a_{i+1}-a_i\leq K$ then there are two distinct intervals $I$ and $J$
    such that \[\sum_{i\in I}a_i=\sum_{j\in J}a_j?\]"

  DB remarks: Hegyvári [He86] proved the answer is yes with an explicit
  bound of the shape f(a,K) ≪ a·e^{O(K)}, and believes the exponential
  dependence on K is not best possible.

  Mathlib inventory (leandoc, 2026-08-05): pure `Finset.Icc`/`Finset.sum`
  vocabulary; no new upstream definitions needed.  Same toolkit as
  `Proofs/Enumerative/NederGap.lean` and `StanleyDigits.lean`.
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E1213

/-- The sum of the block `a_i + a_{i+1} + ⋯ + a_j` of a sequence `a`.
    An "interval" of the sequence in the sense of the problem is a set of
    *consecutive indices*; we parametrize it by its endpoints `i ≤ j`. -/
def intervalSum (a : ℕ → ℕ) (i j : ℕ) : ℕ :=
  ∑ t ∈ Finset.Icc i j, a t

/-- Ground-truth check for the definition: `a = id` on `Icc 1 3` sums to 6.
    -- PROVABLE (rfl/decide). -/
example : intervalSum id 1 3 = 6 := by sorry

/-- `HasEqualIntervalSums a s`: among the first `s` terms of the sequence
    `a` there are two *distinct* index intervals with the same sum.
    Distinctness is as index sets, i.e. distinct endpoint pairs with both
    intervals nonempty (`i ≤ j`); two intervals with different endpoint
    pairs are different sets of indices. -/
def HasEqualIntervalSums (a : ℕ → ℕ) (s : ℕ) : Prop :=
  ∃ i j i' j' : ℕ, i ≤ j ∧ j < s ∧ i' ≤ j' ∧ j' < s ∧
    (i, j) ≠ (i', j') ∧ intervalSum a i j = intervalSum a i' j'

/-- Satisfiability of the conclusion at a concrete model: for
    `a = 1, 2, 3, …` the intervals `{1,2}` and `{3}` (indices `(0,1)` and
    `(2,2)` with `a t = t + 1`) both sum to `3`.
    -- PROVABLE (decide). -/
example : HasEqualIntervalSums (fun t => t + 1) 3 := by sorry

/-- **Erdős #1213, Hegyvári's theorem** (He86).  For every start value
    `a₀ ≥ 1` and gap bound `K ≥ 1` there is a threshold `F` such that any
    strictly increasing sequence starting at `a₀` with gaps at most `K`
    whose `s`-th term exceeds `F` contains two distinct intervals of
    consecutive terms with equal sums.

    Source text: "Does there exist $f(a,K)$ such that if $a=a_1<\cdots<a_s$
    ... with bounded gaps $a_{i+1}-a_i\leq K$ then there are two distinct
    intervals $I$ and $J$ such that $\sum_{i\in I}a_i=\sum_{j\in J}a_j$?"
    Answer YES (Hegyvári 1986).

    Formalization notes:
    * The sequence is indexed from `0`: `a 0 = a₀` is the Erdős `a_1`.
    * Gap hypothesis: `a (t+1) - a t ≤ K` for indices below `s - 1`; with
      `StrictMono` on the used range the ℕ-subtraction is the true gap
      (guarded per STYLE.md by the monotonicity hypothesis).
    * We require strict monotonicity only on the inspected window
      (`t < u < s → a t < a u`) so the ambient function carries no junk.

    Proof sketch (attack plan): pigeonhole on prefix sums.  Let
    `S_j = a_0 + ⋯ + a_j`.  Two intervals have equal sums iff
    `S_j - S_{i-1} = S_{j'} - S_{i'-1}`.  Bounded gaps force the prefix
    sums into an arithmetic-progression-like region of size controlled by
    `a₀` and `K`; once `a_s > f(a₀,K)` there are more intervals than
    available sum values in a suitable window.  Hegyvári's actual argument
    localizes to blocks where consecutive terms nearly repeat modulo small
    integers; the exponential in `K` enters through a covering of residue
    patterns.  Mathlib tools: `Finset.sum_Icc_succ_top`,
    `Finset.exists_ne_map_eq_of_card_lt_of_maps_to` (pigeonhole).
    OPEN in repo; proved in literature. -/
theorem hegyvari_equal_interval_sums (a₀ K : ℕ) (ha : 1 ≤ a₀) (hK : 1 ≤ K) :
    ∃ F : ℕ, ∀ (a : ℕ → ℕ) (s : ℕ),
      a 0 = a₀ →
      (∀ t u : ℕ, t < u → u < s → a t < a u) →
      (∀ t : ℕ, t + 1 < s → a (t + 1) - a t ≤ K) →
      (∀ hs : 0 < s, F < a (s - 1)) →
      HasEqualIntervalSums a s := by
  sorry

/-- Hegyvári's quantitative form: the threshold can be taken of the shape
    `f(a₀, K) ≤ a₀ * C^K` for an absolute constant `C` — the DB records
    the bound "$f(a,K) \ll a e^{O(K)}$".  Stated with an explicit
    existential constant.  Hegyvári believes the exponential dependence on
    `K` is not optimal; improving it would be new mathematics. -/
theorem hegyvari_quantitative :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (a₀ K : ℕ), 1 ≤ a₀ → 1 ≤ K →
      ∀ (a : ℕ → ℕ) (s : ℕ),
        a 0 = a₀ →
        (∀ t u : ℕ, t < u → u < s → a t < a u) →
        (∀ t : ℕ, t + 1 < s → a (t + 1) - a t ≤ K) →
        (∀ hs : 0 < s, a₀ * C ^ K < a (s - 1)) →
        HasEqualIntervalSums a s := by
  sorry

/-- Sanity layer: with gap bound `K = 1` the sequence is forced to be
    `a₀, a₀+1, a₀+2, …` and equal-sum interval pairs appear quickly
    (e.g. `(a₀+1) + (a₀+2) + ⋯` windows); for `a₀ = 1, s = 3` the witness
    is the example above.  A `decide`-scale certificate that every
    strictly-increasing gap-1 sequence of length 5 starting at 1 has two
    distinct equal-sum intervals.
    -- PROVABLE (decide after specializing `a` to `fun t => t + 1`). -/
example : HasEqualIntervalSums (fun t => t + 1) 5 := by sorry

end ErdosCandidates.E1213

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - DB statement matches file header verbatim.
   - DB says "sequence of integers"; file uses ℕ→ℕ. Since a >= 1 and strictly increasing, all terms are in ℕ. No information lost.
   - 0-indexing shift documented and consistent throughout.
   - `intervalSum id 1 3 = 6` verified: 1+2+3 = 6.
   - `HasEqualIntervalSums (fun t => t+1) 3` verified: intervals (0,1) and (2,2) both sum to 3.
   - Solver attribution Hegyvari [He86] matches DB.
   - `intervalSum` is a thin wrapper over `Finset.sum`/`Finset.Icc`; no Mathlib definition missed.
   - ℕ-subtraction in gap hypothesis `a(t+1) - a(t) ≤ K` guarded by `StrictMono` on the range.
   - Quantitative form `a₀ * C^K` consistent with DB's `f(a,K) ≪ a·e^{O(K)}`.
-/
