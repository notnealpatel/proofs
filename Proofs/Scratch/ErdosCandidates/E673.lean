/-
  Erdős Problem #673 — sums of ratios of consecutive divisors.
  Status: proved (trivially, per Tao's observation; Erdős himself
  later called it trivial in [Er82e]).  Tier C proof target
  (the pointwise inequality is a clean one-file goal).

  Verbatim statement (`goof erdos fetch 673`, pulled 2026-08-05):

    "Let $1=d_1<\cdots <d_{\tau(n)}=n$ be the divisors of $n$ and
    \[G(n) = \sum_{1\leq i<\tau(n)}\frac{d_i}{d_{i+1}}.\]
    Is it true that $G(n)\to \infty$ for almost all $n$? Can one prove
    an asymptotic formula for $\sum_{n\leq X}G(n)$?"

  DB remarks: Erdős writes it is 'easy' that the mean of G grows.
  The live entry attributes to Tao the claim that for any m ∣ n,
  τ(n/m)/m ≤ G(n) ≤ τ(n).  Its literal lower bound at m = 1 is false:
  n = 7 gives τ(7) = 2 but G(7) = 1/7.  The corrected lower bound assumes
  2 ≤ m; at m = 2 it still gives τ(n)/4 ≤ G(n) ≤ τ(n) for even n.
  Erdős [Er82e] recalls
  the conjecture as trivial; he and Tenenbaum proved G(n)/τ(n) has a
  continuous distribution function.

  Mathlib inventory (leandoc 2026-08-05): `Nat.divisors` (Finset),
  `Finset.sort (· ≤ ·)` for the increasing divisor list; τ(n) =
  `n.divisors.card`.  "Almost all" density language is mostly absent
  from Mathlib — the density statement is archived, the pointwise
  inequalities are the targets.
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E673

/-- The increasing list of divisors of `n`. -/
def divisorList (n : ℕ) : List ℕ := n.divisors.sort (· ≤ ·)

/-- `G n`: the sum of ratios of consecutive divisors,
    `∑_{i < τ(n)−1} d_i / d_{i+1} : ℚ`, via `zipWith` on the sorted
    divisor list and its tail. -/
def G (n : ℕ) : ℚ :=
  (List.zipWith (fun a b => (a : ℚ) / b) (divisorList n)
    (divisorList n).tail).sum

/-- Ground truth: divisors of 12 are 1,2,3,4,6,12;
    G(12) = 1/2 + 2/3 + 3/4 + 4/6 + 6/12 = 37/12.
    -- PROVABLE (decide/norm_num). -/
example : G 12 = 37 / 12 := by sorry

/-- Ground truth: G(p) = 1/p for primes; G(1) = 0 (empty sum).
    -- PROVABLE (decide at p = 7). -/
example : G 7 = 1 / 7 ∧ G 1 = 0 := by sorry

/-- The live entry's literal `m = 1` lower bound fails at `n = 7`.
    This remains quarantined with the other archival checks. -/
example : ¬(((7 / 1).divisors.card : ℚ) / 1 ≤ G 7) := by sorry

/-- **Upper inequality** (Tao; trivial): `G(n) ≤ τ(n)` — indeed
    `G(n) ≤ τ(n) − 1` since each of the `τ(n) − 1` ratios is `< 1`…
    stated with the clean bound `G n ≤ n.divisors.card`.
    -- PROVABLE (each summand ≤ 1; effort S — the first sorry-free
    landing of this file). -/
theorem G_le_tau (n : ℕ) (hn : 1 ≤ n) : G n ≤ n.divisors.card := by
  sorry

/-- **Corrected lower inequality**: if `m ∣ n` and `2 ≤ m`, then
    `τ(n/m) / m ≤ G(n)`.  The live entry attributes the unqualified
    inequality to Tao, but the `m = 1` boundary is false.  For `2 ≤ m`,
    each divisor `d` of `n/m` is a proper divisor of `n`, and its outgoing
    consecutive-divisor edge contributes at least `1/m` because the next
    divisor after `d` is at most `d*m`.  Effort S–M. -/
theorem tau_div_le_G (n m : ℕ) (hn : 1 ≤ n) (hm : m ∣ n) (hm2 : 2 ≤ m) :
    ((n / m).divisors.card : ℚ) / m ≤ G n := by
  sorry

/-- Corollary for even `n`: `τ(n)/4 ≤ G(n) ≤ τ(n)` (m = 2 gives
    τ(n/2)/2 ≥ τ(n)/4 by τ(n) ≤ 2·τ(n/2) for even n).
    -- PROVABLE from the two inequalities (effort S). -/
theorem G_even_bounds (n : ℕ) (hn : 2 ≤ n) (heven : 2 ∣ n) :
    (n.divisors.card : ℚ) / 4 ≤ G n ∧ G n ≤ n.divisors.card := by
  sorry

/-- **Question 1 (answered YES, trivially)**: `G(n) → ∞` for almost
    all `n` — density form: for every bound `M`, the set of `n ≤ X`
    with `G(n) ≤ M` has density 0.  Follows from the lower bound plus
    "τ(n) → ∞ for almost all n" (normal order of τ; the divisor-count
    density input is the missing Mathlib piece — archived until a
    density toolkit exists). -/
theorem G_tendsto_ae (M : ℚ) :
    Filter.Tendsto
      (fun X : ℕ =>
        (((Finset.Icc 1 X).filter (fun n => G n ≤ M)).card : ℝ) / X)
      Filter.atTop (nhds 0) := by
  sorry

/-- **Question 2 (asymptotic mean, archived)**: `∑_{n≤X} G(n)` has an
    asymptotic formula — per Tao's observation `G ≍ τ` on average, the
    mean is `≍ X log X`; stated at the order-of-growth level with
    two-sided constants (the precise constant is what Erdős asked for
    and remains the analytic content). -/
theorem G_mean_order :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧
      ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
        c₁ * X * Real.log X ≤ (((Finset.Icc 1 X).sum G : ℚ) : ℝ) ∧
        (((Finset.Icc 1 X).sum G : ℚ) : ℝ) ≤ c₂ * X * Real.log X := by
  sorry

end ErdosCandidates.E673

/- SOURCE-FIDELITY REVIEW (corrected 2026-09-12)
   Verdict: CORRECTED STATEMENTS, ARCHIVAL SORRIES (NOT FORMALLY PROVED HERE)
   - Verbatim statement matches `goof erdos fetch 673` exactly.
   - G(n) definition via zipWith on sorted divisors faithfully encodes
     sum of d_i/d_{i+1} over consecutive divisor pairs.
   - Arithmetic verified: G(12) = 37/12 correct (1/2+2/3+3/4+4/6+6/12);
     G(7) = 1/7 correct; G(1) = 0 correct (empty sum).
   - The live entry attributes tau(n/m)/m <= G(n) to Tao for any m | n,
     but its m = 1 boundary is false: n = 7 would require 2 <= 1/7.
   - The lower theorem is corrected to require 2 <= m; the upper bound is unchanged.
   - Even-n corollary tau(n)/4 <= G(n) remains correctly justified by
     tau(n) <= 2*tau(n/2) for even n.
   - Erdős–Tenenbaum distribution function and [Er82e] attribution correct.
   - Density-form Q1 and mean-order Q2 faithfully encode the two questions.
-/
