/-
  Erdős Problem #663 — the least prime not dividing a product of
  consecutive integers.
  Status: open.  Tier UC lemma mine (the easy k·log n bound).

  Verbatim statement (`goof erdos fetch 663`, pulled 2026-08-05):

    "Let $k\geq 2$ and $q(n,k)$ denote the least prime which does not
    divide $\prod_{1\leq i\leq k}(n+i)$. Is it true that, if $k$ is
    fixed and $n$ is sufficiently large, we have
    \[q(n,k)<(1+o(1))\log n?\]"

  DB remarks (Erdős–Pomerance): the bound q(n,k) < (1+o(1))·k·log n
  is easy.  Possibly the improved bound holds up to k = o(log n).
  Tao sketched a supporting heuristic in the comments.  Sibling
  entry: #1181; see also #457.

  OEIS anchor: A391668 (table of least number coprime to all of
  [n+1, n+k] — the "least number" and "least prime" agree beyond 1:
  the least m ≥ 2 coprime to a product is prime).

  Mathlib inventory: `Nat.Prime`, `Finset.Icc` products,
  `Nat.exists_infinite_primes` (sInf honesty), primorial bounds
  (`Nat.primorial`) for the easy estimate.
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E663

/-- The block product `(n+1)(n+2)⋯(n+k)`. -/
def blockProd (n k : ℕ) : ℕ := ∏ i ∈ Finset.Icc 1 k, (n + i)

/-- `q n k`: the least prime not dividing the block product.  `sInf`
    honesty: primes larger than `(n+k)!` cannot divide the product,
    so the defining set is nonempty (via `Nat.exists_infinite_primes`). -/
noncomputable def q (n k : ℕ) : ℕ :=
  sInf {p : ℕ | p.Prime ∧ ¬ p ∣ blockProd n k}

/-- Ground truth: `blockProd 0 4 = 24`; least prime not dividing 24
    is 5, so `q 0 4 = 5`.  `blockProd 1 2 = 2·3 = 6`; `q 1 2 = 5`.
    -- PROVABLE (decide after sInf characterization). -/
example : blockProd 0 4 = 24 ∧ q 0 4 = 5 ∧ q 1 2 = 5 := by
  sorry

/-- **The easy bound (the lemma-mine target)**: for fixed `k ≥ 2` and
    every `ε > 0`, eventually `q(n,k) < (1+ε)·k·log n`.
    Attack: a prime `p` divides the product of `k` consecutive
    integers whenever `p ≤ k`… no — whenever some residue hits;
    the actual easy argument: if all primes `p ≤ T` DIVIDE the block
    product, then the product exceeds `∏_{p ≤ T} p = e^{(1+o(1))T}`
    divided by collision factors; conversely the block product is
    `≤ (n+k)^k = e^{k(1+o(1))log n}`, and each non-dividing prime is
    ruled out one per residue-coverage — Chebyshev/primorial growth
    (`Nat.primorial` bounds in Mathlib) closes it.  Effort M;
    pairs with the Covering lane arithmetic. -/
theorem easy_klog_bound (k : ℕ) (hk : 2 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (q n k : ℝ) < (1 + ε) * k * Real.log n := by
  sorry

/-- **Erdős #663, headline (OPEN)**: for fixed `k ≥ 2`, eventually
    `q(n,k) < (1+o(1))·log n` — the k-free bound. -/
theorem erdos_663 (k : ℕ) (hk : 2 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (q n k : ℝ) < (1 + ε) * Real.log n := by
  sorry

/-- Trivial floor — sanity keeping the statements honest: `q(n,k)` is
    genuinely large infinitely often: `q(n,k) ≥ 3` whenever the block
    contains an even number (k ≥ 2 always does), i.e. 2 always
    divides the block product for k ≥ 2.
    -- PROVABLE (two consecutive integers contain an even one;
    effort S). -/
theorem two_dvd_blockProd (n k : ℕ) (hk : 2 ≤ k) :
    2 ∣ blockProd n k := by
  sorry

/-- A391668 cross-check (its "least number coprime" is our least
    prime, for values ≥ 2): the table's antidiagonal entries at small
    (n, k) — e.g. least prime not dividing (2)(3) = 6 is 5 (matches
    T-entry 5 at the corresponding position).  Recorded at one
    concrete instance to pin the def-to-OEIS orientation.
    -- PROVABLE (decide). -/
example : q 1 2 = 5 := by
  sorry

end ErdosCandidates.E663

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - Verbatim statement matches DB fetch exactly.
   - q(n,k) definition, easy k*log n bound, and headline conjecture all faithful.
   - Erdos-Pomerance attribution confirmed in DB.
   - Arithmetic verified: blockProd 0 4 = 24, q(0,4) = 5, q(1,2) = 5.
   - #1181 cross-reference not present in DB (only #457); appears in commentary
     not the verbatim block, so not a fidelity error but ungrounded.
   - sInf honesty argument is sound (infinite primes guarantee nonemptiness).
-/
