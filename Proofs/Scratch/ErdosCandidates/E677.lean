/-
  Erdős Problem #677 — lcm of blocks of consecutive integers.
  Status: open.  Tier UB archive target with decide witnesses.

  Verbatim statement (`goof erdos fetch 677`, pulled 2026-08-05):

    "Let $M(n,k)=[n+1,\ldots,n+k]$ be the least common multiple of
    $\{n+1,\ldots,n+k\}$.

    Is it true that for all $m\geq n+k$\[M(n,k) \neq M(m,k)?\]"

  DB remarks: Thue–Siegel gives (ineffective) finiteness of
  coincidences for fixed k.  Erdős knew only the cross-k coincidences
  M(4,3) = M(13,2) and M(3,4) = M(19,2).  In [Er79d] Erdős conjectures
  the stronger fact that (finitely many exceptions) for k > 2,
  m ≥ n+k, the products ∏(n+i) and ∏(m+i) cannot have the same prime
  support.  Comment (qrdl, Apr 2026): more variable-k examples —
  M(8,4) = M(43,2) = 1980, M(153,3) = M(1363,2) = 1861860,
  M(0,7) = M(1,6) = M(2,5) = M(3,4) = M(19,2) = 420.

  Repo adjacency: `Proofs/Erdos/Erdos440/LcmCount.lean` (lcm-of-blocks
  counting layer).

  Mathlib inventory: `Finset.lcm` over `Finset.Icc`; nothing else.
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E677

/-- `M n k`: the lcm of the block `{n+1, …, n+k}`. -/
def M (n k : ℕ) : ℕ := (Finset.Icc (n + 1) (n + k)).lcm id

/-- Ground truth: `M 0 2 = lcm{1,2} = 2`, `M 4 3 = lcm{5,6,7} = 210`,
    `M 13 2 = lcm{14,15} = 210`, `M 3 4 = lcm{4,5,6,7} = 420`,
    `M 19 2 = lcm{20,21} = 420`.  -- PROVABLE (decide). -/
example : M 0 2 = 2 ∧ M 4 3 = 210 ∧ M 13 2 = 210 ∧ M 3 4 = 420 ∧
    M 19 2 = 420 := by
  sorry

/-- **Erdős #677 (OPEN)**: same-`k` blocks never repeat their lcm:
    for `k ≥ 2` (k = 1 is trivially injective) and `n + k ≤ m`,
    `M(n,k) ≠ M(m,k)`.

    Source text: "Is it true that for all $m\geq n+k$
    $M(n,k) \neq M(m,k)$?"

    Note the known coincidences (4,3)/(13,2) and (3,4)/(19,2) are
    CROSS-k, so they do not falsify this statement.  Thue–Siegel gives
    ineffective finiteness for fixed k; an unconditional proof needs
    effective Diophantine bounds — out of reach; archived. -/
theorem erdos_677 (n m k : ℕ) (hk : 2 ≤ k) (hm : n + k ≤ m) :
    M n k ≠ M m k := by
  sorry

/-- Sanity guard for the statement's honesty: the `k = 1` case is
    trivially true (`M n 1 = n + 1` is injective), so the content is at
    `k ≥ 2`; and the cross-k coincidences do NOT contradict the
    conjecture — recorded as decide witnesses above and here as the
    explicit non-example shape: `M 4 3 = M 13 2` with different k.
    -- PROVABLE (decide). -/
example : M 4 3 = M 13 2 ∧ (3 : ℕ) ≠ 2 := by
  sorry

/-- Verified window: no same-`k` coincidence with `k = 2, 3` and
    `n, m ≤ 300`.  -- PROVABLE (decide; lcms stay small). -/
theorem window_300 :
    ∀ k ∈ ({2, 3} : Finset ℕ), ∀ n ∈ Finset.range 301,
      ∀ m ∈ Finset.range 301, n + k ≤ m → M n k ≠ M m k := by
  sorry

/-- **Erdős' stronger prime-support conjecture** ([Er79d], archived):
    for `k > 2`, up to finitely many exceptions, blocks
    `{n+1, …, n+k}` and `{m+1, …, m+k}` with `m ≥ n + k` have distinct
    prime support of their products.  Stated per k as finiteness of
    the exceptional pair-set. -/
theorem erdos_prime_support (k : ℕ) (hk : 3 ≤ k) :
    {q : ℕ × ℕ | q.1 + k ≤ q.2 ∧
      (∏ i ∈ Finset.Icc 1 k, (q.1 + i)).primeFactors =
      (∏ i ∈ Finset.Icc 1 k, (q.2 + i)).primeFactors}.Finite := by
  sorry

/-- **Thue–Siegel finiteness** (ineffective; DB remarks), archived:
    for each fixed `k ≥ 2` there are only finitely many same-`k`
    coincidences `M(n,k) = M(m,k)` with `m ≥ n + k`.  (If the headline
    `erdos_677` is true this set is empty; the finiteness form is what
    is actually known.) -/
theorem thue_siegel_finiteness (k : ℕ) (hk : 2 ≤ k) :
    {q : ℕ × ℕ | q.1 + k ≤ q.2 ∧ M q.1 k = M q.2 k}.Finite := by
  sorry

end ErdosCandidates.E677

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - Verbatim statement matches DB fetch.
   - M n k = (Finset.Icc (n+1) (n+k)).lcm id faithfully encodes
     [n+1,...,n+k] as lcm.
   - Ground truth verified: M(0,2)=2, M(4,3)=210, M(13,2)=210, M(3,4)=420,
     M(19,2)=420 — all confirmed computationally.
   - erdos_677 uses hm : n + k <= m, matching source's "for all m >= n+k".
   - Cross-k coincidences (4,3)/(13,2) and (3,4)/(19,2) correctly noted as
     non-falsifying since k differs. qrdl's additional examples (M(8,4)=1980
     etc.) accurately reflected.
   - Stronger prime-support conjecture from [Er79d] for k > 2 stated as
     finiteness of exceptions, matching "aside from a finite number of
     exceptions".
   - Thue-Siegel finiteness for fixed k matches DB sections.
   - Product in erdos_prime_support uses Finset.Icc 1 k giving (q.1+1)...(q.1+k),
     correctly matching the source's product of the block.
-/
