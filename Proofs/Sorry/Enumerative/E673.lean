/-
  Erdős Problem #673 — sums of ratios of consecutive divisors.
  The first question is proved in the literature (Erdős called it
  trivial in [Er82e]). The upper bound and ground checks are formalized
  in Enumerative.E673; the lower and analytic statements remain archived.

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
import Enumerative.E673

set_option autoImplicit false

namespace ErdosCandidates.E673

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

/-- **Mean order (archived, not a precise asymptotic formula)**:
    the sum `∑_{n≤X} G(n)` has order `X log X`, expressed by two-sided
    constants. This is weaker than the second question's request for
    an asymptotic formula; no literature-status claim for that question
    follows from the absence of a formal proof here. -/
theorem G_mean_order :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧
      ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
        c₁ * X * Real.log X ≤ (((Finset.Icc 1 X).sum G : ℚ) : ℝ) ∧
        (((Finset.Icc 1 X).sum G : ℚ) : ℝ) ≤ c₂ * X * Real.log X := by
  sorry

end ErdosCandidates.E673

/- SOURCE-FIDELITY REVIEW (corrected 2026-09-12)
   Verdict: CORRECTED LOWER STATEMENT; UPPER AND GROUND CHECKS IN PRODUCTION;
   LOWER AND ANALYTIC STATEMENTS STILL ARCHIVAL SORRIES
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
   - Density-form Q1 encodes the first question, answered in the literature.
   - Mean-order bounds are weaker than the precise asymptotic requested in Q2.
-/
