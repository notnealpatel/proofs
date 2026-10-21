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

/-- The five original concrete block-lcm values. -/
theorem original_lcm_values : M 0 2 = 2 ∧ M 4 3 = 210 ∧ M 13 2 = 210 ∧
    M 3 4 = 420 ∧ M 19 2 = 420 := by
  decide

/-- Ground truth: `M 0 2 = lcm{1,2} = 2`, `M 4 3 = lcm{5,6,7} = 210`,
    `M 13 2 = lcm{14,15} = 210`, `M 3 4 = lcm{4,5,6,7} = 420`,
    `M 19 2 = lcm{20,21} = 420`.  -- PROVABLE (decide). -/
example : M 0 2 = 2 ∧ M 4 3 = 210 ∧ M 13 2 = 210 ∧ M 3 4 = 420 ∧
    M 19 2 = 420 := by
  exact original_lcm_values

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

/-- The original coincidence uses distinct block lengths. -/
theorem original_cross_k : M 4 3 = M 13 2 ∧ (3 : ℕ) ≠ 2 := by
  decide

/-- Sanity guard for the statement's honesty: the `k = 1` case is
    trivially true (`M n 1 = n + 1` is injective), so the content is at
    `k ≥ 2`; and the cross-k coincidences do NOT contradict the
    conjecture — recorded as decide witnesses above and here as the
    explicit non-example shape: `M 4 3 = M 13 2` with different k.
    -- PROVABLE (decide). -/
example : M 4 3 = M 13 2 ∧ (3 : ℕ) ≠ 2 := by
  exact original_cross_k

/-- `{n+1, …, n+2}` is the two-element set `{n+1, n+2}`. -/
private theorem icc_two (n : ℕ) : Finset.Icc (n + 1) (n + 2) = {n + 1, n + 2} := by
  ext x
  simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
  omega

/-- `{n+1, …, n+3}` is the three-element set `{n+1, n+2, n+3}`. -/
private theorem icc_three (n : ℕ) :
    Finset.Icc (n + 1) (n + 3) = {n + 1, n + 2, n + 3} := by
  ext x
  simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
  omega

/-- Consecutive naturals are coprime. -/
private theorem coprime_self_succ (a : ℕ) : Nat.Coprime a (a + 1) := by
  simp

/-- Closed form for `k = 2`: `M(n,2) = (n+1)(n+2)`. -/
private theorem M_two (n : ℕ) : M n 2 = (n + 1) * (n + 2) := by
  rw [M, icc_two, Finset.lcm_insert, Finset.lcm_singleton, id, id, normalize_eq,
    lcm_eq_nat_lcm]
  exact (coprime_self_succ (n + 1)).lcm_eq_mul

/-- `P n = (n+1)(n+2)(n+3)`, the product of the length-3 block. -/
private def P (n : ℕ) : ℕ := (n + 1) * (n + 2) * (n + 3)

example : P 2 = 60 ∧ P 3 = 120 := by decide

/-- Closed form for `k = 3`: `gcd(n+1, 2) · M(n,3) = (n+1)(n+2)(n+3)`. -/
private theorem M_three (n : ℕ) : Nat.gcd (n + 1) 2 * M n 3 = P n := by
  rw [M, icc_three, Finset.lcm_insert, Finset.lcm_insert, Finset.lcm_singleton, id, id,
    id, normalize_eq, lcm_eq_nat_lcm, lcm_eq_nat_lcm,
    (coprime_self_succ (n + 2)).lcm_eq_mul]
  have hg : Nat.gcd (n + 1) ((n + 2) * (n + 3)) = Nat.gcd (n + 1) 2 := by
    rw [Nat.Coprime.gcd_mul_left_cancel_right _ (coprime_self_succ (n + 1)).symm]
    have h3 : n + 3 = (n + 1) + 2 := by ring
    rw [h3, Nat.gcd_self_add_right]
  rw [← hg, Nat.gcd_mul_lcm, P, mul_assoc]

/-- `P` is strictly increasing. -/
private theorem P_lt {a b : ℕ} (h : a < b) : P a < P b := by
  unfold P
  exact Nat.mul_lt_mul'' (Nat.mul_lt_mul'' (by omega) (by omega)) (by omega)

/-- Candidate bracket index: approximately `2^{1/3}(n+2) - 2`, so that
    `P (certC n) < 2 P n < P (certC n + 1)` on the window. -/
private def certC (n : ℕ) : ℕ := 125992 * (n + 2) / 100000 - 2

example : certC 2 = 3 ∧ certC 300 = 378 := by decide

set_option maxRecDepth 20000 in
/-- Finite certificate: for each `n ≤ 300`, either `2 P n < P (n+3)` or
    `2 P n` lies strictly between two consecutive values of `P`. -/
private theorem cert : ∀ n < 301, 2 * P n < P (n + 3) ∨
    (P (certC n) < 2 * P n ∧ 2 * P n < P (certC n + 1)) := by
  decide

/-- On the window, `P m = 2 P n` has no solution with `n + 3 ≤ m`. -/
private theorem P_ne_two_mul {n m : ℕ} (hn : n < 301) (hm : n + 3 ≤ m) :
    P m ≠ 2 * P n := by
  intro h
  rcases cert n hn with h1 | ⟨h1, h2⟩
  · rcases Nat.lt_or_ge (n + 3) m with h3 | h3
    · have hlt := P_lt h3
      omega
    · have hmeq : m = n + 3 := by omega
      rw [hmeq] at h
      omega
  · rcases Nat.lt_or_ge (certC n) m with h3 | h3
    · rcases Nat.lt_or_ge (certC n + 1) m with h4 | h4
      · have hlt := P_lt h4
        omega
      · have hmeq : m = certC n + 1 := by omega
        rw [hmeq] at h
        omega
    · rcases Nat.lt_or_ge m (certC n) with h4 | h4
      · have hlt := P_lt h4
        omega
      · have hmeq : m = certC n := by omega
        rw [hmeq] at h
        omega

/-- `gcd(a, 2)` is `1` or `2`. -/
private theorem gcd_two_cases (a : ℕ) : Nat.gcd a 2 = 1 ∨ Nat.gcd a 2 = 2 :=
  (Nat.dvd_prime Nat.prime_two).mp (Nat.gcd_dvd_right a 2)

/-- Verified window: no same-`k` coincidence with `k = 2, 3` and
    `n, m ≤ 300`.  -- PROVABLE (decide; lcms stay small). -/
theorem window_300 :
    ∀ k ∈ ({2, 3} : Finset ℕ), ∀ n ∈ Finset.range 301,
      ∀ m ∈ Finset.range 301, n + k ≤ m → M n k ≠ M m k := by
  intro k hk n hn m _ hnm heq
  rw [Finset.mem_range] at hn
  rcases Finset.mem_insert.mp hk with rfl | hk3
  · rw [M_two, M_two] at heq
    have hlt : (n + 1) * (n + 2) < (m + 1) * (m + 2) :=
      Nat.mul_lt_mul'' (by omega) (by omega)
    omega
  · rw [Finset.mem_singleton] at hk3
    subst hk3
    have hn3 := M_three n
    have hm3 := M_three m
    have hP : P n < P m := P_lt (by omega)
    have hne := P_ne_two_mul hn hnm
    rw [heq] at hn3
    rcases gcd_two_cases (n + 1) with h1 | h1 <;> rcases gcd_two_cases (m + 1) with h2 | h2 <;>
      rw [h1] at hn3 <;> rw [h2] at hm3 <;> omega

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
