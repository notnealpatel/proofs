/-
  Erdős Problem #1094 — the least prime factor of C(n,k).
  Status: open.  Tier UB archive target with decidable exception list.

  Verbatim statement (`goof erdos fetch 1094`, pulled 2026-08-05):

    "For all $n\geq 2k$ the least prime factor of $\binom{n}{k}$ is
    $\leq \max(n/k,k)$, with only finitely many exceptions."

  DB remarks: a stronger form of #384 from [ELS88].  Erdős: least
  prime factor ≤ n/k for n large in terms of k.  Selfridge [Se77]:
  conjecturally ≤ n/k once n ≥ k² − 1, except C(62,6).  ELS88
  conjecture: ≤ max(n/k, k) for n ≥ 2k with exactly 14 exceptions:
  C(7,3), C(13,4), C(23,5), C(14,4), C(44,8), C(46,10), C(47,10),
  C(47,11), C(62,6), C(74,10), C(94,10), C(95,10), C(241,16),
  C(284,28).  ELS93: possibly ≤ max(n/k, 13) with only 12 exceptions.
  Related to #1093 (counterexamples need deficiency ≥ 1).

  Formalization: least prime factor = `Nat.minFac` (Mathlib; junk:
  minFac 1 = 1, minFac 0 = 2 — binomials in range are ≥ 2 except the
  guard degeneracies, handled by `2 ≤ k` hypotheses).  `n/k ≤ …`
  encoded multiplicatively.

  Mathlib inventory: `Nat.minFac`, `Nat.choose`.  Hygiene note from
  the candidates doc honored: no Frankl-bound content here (that was
  #1020 cross-contamination).
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E1094

/-- The 14 ELS88 exceptional pairs `(n, k)`. -/
def exceptions : Finset (ℕ × ℕ) :=
  { (7, 3), (13, 4), (23, 5), (14, 4), (44, 8), (46, 10), (47, 10),
    (47, 11), (62, 6), (74, 10), (94, 10), (95, 10), (241, 16),
    (284, 28) }

/-- `SmallLeastFactor n k`: the least prime factor of `C(n,k)` is at
    most `max(n/k, k)`, encoded division-free:
    `minFac(C(n,k)) ≤ k ∨ minFac(C(n,k)) * k ≤ n`. -/
def SmallLeastFactor (n k : ℕ) : Prop :=
  (n.choose k).minFac ≤ k ∨ (n.choose k).minFac * k ≤ n

/-- Ground truth: C(10,4) = 210 has minFac 2 ≤ 4 ✓; the exception
    C(62,6): C(62,6) = 61474519, whose least prime factor is 19, and
    19 > 6 with 19·6 = 114 > 62 — genuinely exceptional.
    -- PROVABLE (decide). -/
example : SmallLeastFactor 10 4 ∧ ¬ SmallLeastFactor 62 6 := by
  sorry

/-- **Erdős #1094 (OPEN)**: for all `n ≥ 2k`, `k ≥ 2`, outside the 14
    listed exceptions, the least prime factor of `C(n,k)` is
    `≤ max(n/k, k)`.

    Source text: "For all $n\geq 2k$ the least prime factor of
    $\binom{n}{k}$ is $\leq \max(n/k,k)$, with only finitely many
    exceptions."  The DB's "finitely many" is conjecturally EXACTLY
    the 14 pairs (ELS88); we state the strong exact-list form (the
    literal finiteness form is `erdos_1094_finiteness` below). -/
theorem erdos_1094_exact (n k : ℕ) (hk : 2 ≤ k) (hn : 2 * k ≤ n)
    (hexc : (n, k) ∉ exceptions) :
    SmallLeastFactor n k := by
  sorry

/-- The literal statement: finitely many exceptions.  Implied by
    `erdos_1094_exact`; kept as the faithful weak form. -/
theorem erdos_1094_finiteness :
    {q : ℕ × ℕ | 2 ≤ q.2 ∧ 2 * q.2 ≤ q.1 ∧
      ¬ SmallLeastFactor q.1 q.2}.Finite := by
  sorry

/-- All 14 exceptions really are exceptions.
    -- PROVABLE (decide; the largest is C(284,28) ≈ 10³⁵ — minFac of a
    35-digit number whose least factor is moderate; kernel-feasible,
    else native_decide). -/
theorem exceptions_are_exceptional :
    ∀ q ∈ exceptions, ¬ SmallLeastFactor q.1 q.2 := by
  sorry

/-- Verified window: no exceptions outside the list with `n ≤ 300`.
    -- PROVABLE (decide/native_decide sweep). -/
theorem window_300 :
    ∀ n ∈ Finset.range 301, ∀ k ∈ Finset.range 151,
      2 ≤ k → 2 * k ≤ n → (n, k) ∉ exceptions →
      SmallLeastFactor n k := by
  sorry

/-- **Selfridge's refinement** ([Se77], archived): once `k² − 1 ≤ n`
    (stated additively `k² ≤ n + 1`), the least prime factor is
    `≤ n/k` — no `max` needed — except C(62,6). -/
theorem selfridge_refinement (n k : ℕ) (hk : 2 ≤ k) (hn : k ^ 2 ≤ n + 1)
    (hexc : ¬(n = 62 ∧ k = 6)) :
    (n.choose k).minFac * k ≤ n := by
  sorry

end ErdosCandidates.E1094

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - Statement matches DB verbatim (re-pulled 2026-08-05).
   - 14 exception pairs match DB list exactly (order preserved).
   - Division-free encoding: minFac <= k \/ minFac * k <= n faithfully
     encodes minFac <= max(n/k, k) for k > 0. Sound.
   - C(62,6)=61474519: factorization 19*29*31*59*61, minFac=19. 19 > 6
     and 19*6=114 > 62 -- genuinely exceptional. Correct.
   - C(10,4)=210, minFac=2 <= 4. SmallLeastFactor holds. Correct.
   - Selfridge refinement: DB says "n >= k^2 - 1 except C(62,6)".
     File encodes as k^2 <= n+1 (equivalent). Correct.
   - ELS93 stronger conjecture (max(n/k, 13) with 12 exceptions) mentioned
     in DB but not formalized -- no fidelity issue.
-/
