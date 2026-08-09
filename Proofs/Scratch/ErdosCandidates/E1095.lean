/-
  Erdős Problem #1095 — the Erdős–Selfridge function g(k).
  Status: open.  Tier UC lemma mine (small values decidable; EES74
  lower bound elementary).

  Verbatim statement (`goof erdos fetch 1095`, pulled 2026-08-05):

    "Let $g(k)>k+1$ be the smallest $n$ such that all prime factors
    of $\binom{n}{k}$ are $>k$. Estimate $g(k)$."

  DB remarks (Ecklund–Erdős–Selfridge [EES74]):
  k^{1+c} < g(k) ≤ exp((1+o(1))k); conjecture g(k) < lcm(1,…,k) for
  large k; also conjectured limsup g(k+1)/g(k) = ∞ and
  liminf g(k+1)/g(k) = 0.  Improvements: ELS93, Granville–Ramaré;
  record lower bound g(k) ≫ exp(c(log k)²) (Konyagin [Ko99b]).
  ELS93: "clear to every right-thinking person" that
  g(k) ≥ exp(ck/log k).  Sorenson–Sorenson–Webster [SSW20]:
  heuristics log g(k) ≍ k/log k.

  OEIS anchor: A003458 (Erdős–Selfridge function: 3, 6, 7, 7, 23, 62,
  143, 44, 159, 46, 47, 174, 2239, …; a(n) = least m > n+1 with least
  prime factor of C(m,n) > n).

  Mathlib inventory: `Nat.choose`, `Nat.primeFactors`, `Nat.minFac`;
  `Finset.Icc` lcm for the conjectured bound.  Shares the
  prime-factor toolkit with the E683/E1094 sketches.
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E1095

/-- `AllFactorsLarge n k`: every prime factor of `C(n,k)` exceeds `k`
    — equivalently `k < minFac (C(n,k))` when the binomial is ≥ 2. -/
def AllFactorsLarge (n k : ℕ) : Prop :=
  ∀ p ∈ (n.choose k).primeFactors, k < p

instance (n k : ℕ) : Decidable (AllFactorsLarge n k) := by
  unfold AllFactorsLarge; infer_instance

/-- `g k`: the least `n > k + 1` with all prime factors of `C(n,k)`
    greater than `k` — the Erdős–Selfridge function (A003458).
    `sInf` honesty: nonempty by EES74's `g(k) ≤ e^{(1+o(1))k}`
    (existence of SOME valid n is elementary: n ≡ special residues
    make C(n,k) rough; archived through `g_upper`). -/
noncomputable def g (k : ℕ) : ℕ :=
  sInf {n : ℕ | k + 1 < n ∧ AllFactorsLarge n k}

/-- Ground truth against A003458 (pulled 2026-08-05: 3, 6, 7, 7, 23,
    62, 143, 44, …): `g 1 = 3`, `g 2 = 6`, `g 3 = 7`, `g 4 = 7`,
    `g 5 = 23`, `g 6 = 62`.  Trace for g 2 = 6: C(4,2) = 6 (minFac 2),
    C(5,2) = 10 (2), C(6,2) = 15 = 3·5 — all factors > 2 ✓.
    -- PROVABLE (decide after sInf characterization). -/
theorem g_two : g 2 = 6 := by sorry

theorem g_five : g 5 = 23 := by sorry

theorem g_six : g 6 = 62 := by sorry

/-- **EES74 lower bound (the elementary target)**: there is `c > 0`
    with `k^{1+c} < g(k)` for large `k`.  The EES argument is
    elementary counting of smooth values of C(n,k) — a genuine but
    bounded analytic-combinatorial proof.  Effort M–L. -/
theorem ees_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      (k : ℝ) ^ (1 + c) < (g k : ℝ) := by
  sorry

/-- **EES74 upper bound**, archived: `g(k) ≤ e^{(1+o(1))k}` — stated
    with a clean explicit weakening `g k ≤ 4^k` for large `k` (any
    single-exponential cap; pin the constant during the campaign). -/
theorem g_upper : ∃ K : ℕ, ∀ k : ℕ, K ≤ k → g k ≤ 4 ^ k := by
  sorry

/-- **EES74 lcm conjecture (OPEN)**: `g(k) < lcm(1, …, k)` for all
    large `k`. -/
theorem ees_lcm_conjecture :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → g k < (Finset.Icc 1 k).lcm id := by
  sorry

/-- **Konyagin's record lower bound** ([Ko99b]), archived:
    `g(k) ≫ exp(c (log k)²)`. -/
theorem konyagin_lower :
    ∃ c : ℝ, 0 < c ∧ ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      Real.exp (c * Real.log k ^ 2) ≤ (g k : ℝ) := by
  sorry

/-- **EES74 oscillation conjectures (OPEN)**, archived: the ratio
    `g(k+1)/g(k)` has limsup ∞ and liminf 0 — stated as frequent
    exceedance/undercut of every bound. -/
theorem ees_ratio_limsup (M : ℝ) :
    ∃ᶠ k in Filter.atTop, M * (g k : ℝ) < (g (k + 1) : ℝ) := by
  sorry

theorem ees_ratio_liminf (ε : ℝ) (hε : 0 < ε) :
    ∃ᶠ k in Filter.atTop, (g (k + 1) : ℝ) < ε * (g k : ℝ) := by
  sorry

/-- Non-degeneracy: `A003458`'s non-monotonicity at `a(7) = 44 <
    a(6) = 143` — i.e. `g 8 = 44 < 143 = g 7` (offset: A003458's
    a(n) is our g n)…  verify offsets against OEIS during proof;
    recorded as the decide target `g 8 < g 7`.
    -- PROVABLE (decide). -/
example : g 8 < g 7 := by sorry

end ErdosCandidates.E1095

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - Verbatim statement matches erdos fetch 1095.
   - EES74 bounds, Konyagin exp(c(log k)^2), lcm conjecture, limsup/liminf ratio
     conjectures all faithful to DB remarks.
   - A003458 offset verified: OEIS says a(n) = least m > n+1 with least prime factor
     of C(m,n) > n, so a(k) = g(k) exactly. g(2)=6, g(5)=23, g(6)=62 all correct.
   - Non-monotonicity g(8)=44 < g(7)=143 confirmed from A003458 terms.
   - File header says "a(n) is our g n" — correct, no off-by-one.
   - g(2)=6 hand-verified: C(4,2)=6 has factor 2, C(5,2)=10 has factor 2,
     C(6,2)=15=3*5, all > 2. Correct.
-/
