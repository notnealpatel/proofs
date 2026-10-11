/-
  Erdős Problem #1063 — near-uniform divisibility of C(n,k) by n − i.
  Status: open.  Tier UA attack target.

  Verbatim statement (`goof erdos fetch 1063`, pulled 2026-08-05):

    "Let $k\geq 2$ and define $n_k\geq 2k$ to be the least value of $n$
    such that $n-i$ divides $\binom{n}{k}$ for all but one $0\leq i<k$.
    Estimate $n_k$."

  DB remarks (Erdős–Selfridge, AMM Problem 6447; proof in Monier
  [Mo85]): for n ≥ 2k at least one 0 ≤ i < k has (n−i) ∤ C(n,k), so
  "all but one" is optimal.  Known values n₂ = 4, n₃ = 6, n₄ = 9,
  n₅ = 12 (OEIS A389360: 4, 6, 9, 12, 75, 30, 70, 56, 2403, 280, …).
  Monier: n_k ≤ k! for k ≥ 3 (C(k!, k) is divisible by k! − i for
  1 ≤ i < k).  Cambie (comments): n_k ≤ k·lcm(2,…,k−1) ≤ e^{(1+o(1))k}.
  rickyc + GPT (comments, Jun–Jul 2026, comment-sourced, unrefereed):
  n_k ≥ max(2k, ∏_{p^a ∥ k} p^{a + ⌊log_p (k−1)⌋}).

  Mathlib inventory (leandoc 2026-08-05): `Nat.choose`, `Finset.lcm`,
  `Nat.factorization` / `padicValNat` for the valuation argument;
  repo adjacency: `Proofs/Erdos/Erdos440/LcmCount.lean` (lcm layer).
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E1063

/-- `divisorDefect n k`: the number of indices `0 ≤ i < k` such that
    `n − i` does NOT divide `C(n,k)`.  (For `n ≥ 2k` the subtraction
    `n − i` never truncates since `i < k ≤ n`.) -/
def divisorDefect (n k : ℕ) : ℕ :=
  ((Finset.range k).filter (fun i => ¬ (n - i) ∣ n.choose k)).card

/-- Ground truth: `C(4,2) = 6` is divisible by `4` — no wait, `4 ∤ 6`;
    but `3 ∣ 6`.  Defect of `(4,2)` is exactly 1 (index i = 0 fails).
    -- PROVABLE (decide). -/
example : divisorDefect 4 2 = 1 := by sorry

/-- Ground truth: `(6,2)`: `C(6,2) = 15`; `6 ∤ 15`, `5 ∣ 15` — defect 1.
    But n₂ = 4 is the least.  `(5,2)`: `C(5,2) = 10`; `5 ∣ 10`,
    `4 ∤ 10` — defect 1 as well?  A389360 says n₂ = 4, and indeed 4 is
    the least n ≥ 2k = 4.  -- PROVABLE (decide). -/
example : divisorDefect 5 2 = 1 ∧ divisorDefect 4 2 = 1 := by sorry

/-- `nk k`: the least `n ≥ 2k` with divisor defect at most one — the
    quantity `n_k` of the problem.  By `erdos_selfridge_defect_pos`
    below the defect is never 0 in range, so "at most one" = "exactly
    one" = "n − i divides C(n,k) for all but one i".  `sInf` is
    justified nonempty by Monier's `k!` witness (`nk_le_factorial`). -/
noncomputable def nk (k : ℕ) : ℕ :=
  sInf {n : ℕ | 2 * k ≤ n ∧ divisorDefect n k ≤ 1}

/-- **Erdős–Selfridge non-divisibility lemma** (ErSe83; proof Monier
    Mo85): for `n ≥ 2k`, `k ≥ 2`, at least one `0 ≤ i < k` has
    `(n − i) ∤ C(n,k)` — i.e. the defect is positive, so "all but one"
    in the problem is optimal.

    Proof sketch (attack plan, from the rickyc comment thread's
    valuation identity): fix a prime power `p^a ∥ k`.  With
    `M = max_{i<k} v_p(n−i)` and `S = v_p(C(n,k))`, the factorization
    `S = Σ v_p(n−i) − v_p(k!)` cancels levels `p, …, p^a` exactly
    between the `k` consecutive integers and `k!`, giving `S ≤ M − a`;
    hence any `i` attaining `v_p(n−i) = M` has `(n−i) ∤ C(n,k)`.
    Self-contained: `padicValNat`, `Nat.factorization_choose`
    (Legendre/Kummer in Mathlib).  The natural first sorry-free target
    of this file.  -/
theorem erdos_selfridge_defect_pos (n k : ℕ) (hk : 2 ≤ k)
    (hn : 2 * k ≤ n) :
    1 ≤ divisorDefect n k := by
  sorry

/-- Small values against OEIS A389360 (pulled 2026-08-05:
    4, 6, 9, 12, 75, 30, 70, 56, …): `n₂ = 4`, `n₃ = 6`, `n₄ = 9`,
    `n₅ = 12`.  -- PROVABLE (decide after an sInf-characterization
    lemma; each requires checking finitely many n). -/
theorem nk_two : nk 2 = 4 := by sorry

theorem nk_three : nk 3 = 6 := by sorry

theorem nk_four : nk 4 = 9 := by sorry

theorem nk_five : nk 5 = 12 := by sorry

/-- **Monier's upper bound**: `n_k ≤ k!` for `3 ≤ k`, witnessed by
    `n = k!`: for `1 ≤ i < k`, `(k! − i) ∣ C(k!, k)`.
    Proof sketch: `C(k!, k) = k!(k!−1)⋯(k!−k+1)/k!`; for `1 ≤ i < k`
    write the product so that `k! − i` survives division — elementary
    manipulation of factorials; the divisor-defect at `n = k!`
    concentrates at `i = 0`.  -/
theorem nk_le_factorial (k : ℕ) (hk : 3 ≤ k) : nk k ≤ k.factorial := by
  sorry

/-- **Cambie's improvement** (DB comments): `n_k ≤ k · lcm(2, …, k−1)`,
    giving `n_k ≤ e^{(1+o(1))k}`.  Sits on the repo's Erdos440 lcm
    layer.  Comment-sourced; re-derive the witness before proving. -/
theorem nk_le_mul_lcm (k : ℕ) (hk : 3 ≤ k) :
    nk k ≤ k * (Finset.Icc 2 (k - 1)).lcm id := by
  sorry

/-- **rickyc–GPT lower bound** (comments, Jul 2026; comment-sourced,
    unrefereed — verify the valuation argument independently before
    building on it): `∏_{p^a ∥ k} p^{a + ⌊log_p (k−1)⌋} ≤ n_k`.
    Stated via `Nat.factorization`; `Nat.log p (k−1)` is Mathlib's
    floor-log. -/
theorem nk_lower_bound (k : ℕ) (hk : 2 ≤ k) :
    k.factorization.prod (fun p a => p ^ (a + Nat.log p (k - 1))) ≤ nk k := by
  sorry

-- The problem "Estimate n_k" itself remains OPEN: it is not even known
-- whether `(n_k)^{1/k}` converges (StijnC, comments: non-monotone;
-- min/max of `n_k^{1/k}` for k ≤ 37 at k = 10 and k = 31).  No formal
-- statement beyond the bounds above is attempted.

end ErdosCandidates.E1063

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - Verbatim statement matches DB pull exactly.
   - divisorDefect definition correctly counts i with (n-i) not dividing C(n,k).
   - nk uses sInf with {n | 2*k <= n /\ divisorDefect n k <= 1}: faithful to "least
     n >= 2k ... all but one".
   - OEIS A389360 prefix 4,6,9,12,75,30,70,56,2403,280 matches DB pull exactly.
   - nk values n_2=4, n_3=6, n_4=9, n_5=12 independently verified by computation.
   - defect(4,2)=1 verified (i=0 fails: 4 does not divide 6; i=1 passes: 3|6).
   - Monier bound nk <= k! for k >= 3: matches DB body "Monier observed n_k <= k!
     for k >= 3".
   - Cambie bound uses Finset.Icc 2 (k-1) for lcm(2,...,k-1): matches DB
     "k[2,3,...,k-1]". Comment-sourced: correctly flagged.
   - rickyc-GPT lower bound uses Nat.log p (k-1): matches the IMPROVED bound from
     post-7439 (Jul 2026), not the earlier k/2. File header correctly says "Jun-Jul
     2026". Correctly flagged comment-sourced, unrefereed.
   - Types: all ℕ, ℕ-subtraction in divisorDefect guarded by i < k <= n (noted in
     docstring). No junk.
-/
