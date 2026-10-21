/-
  Erdős Problem #405 — (p−1)! + a^(p−1) = p^k.
  Archive status: the source reports finiteness (Brindza–Erdős 1991)
  and a complete resolution (Yu–Liu 1996). Those results are not proved
  here. Only three concrete certificate units are kernel-checked in
  Erdos.FactorialPowerCertificates; the bounded window remains admitted.

  Recorded statement (`goof erdos fetch 405`, pulled 2026-08-05):

    "Let $p$ be an odd prime. Is it true that the equation
    \[(p-1)!+a^{p-1}=p^k\]
    has only finitely many solutions?"

  Recorded DB remarks: Erdős–Graham originally allowed p = 2,
  "presumably an oversight" (the equation then becomes 1 + a = 2^k).
  The p = 2 example below proves this identity family, not formal
  infinitude, and does not assert Odd 2 or IsSolution at p = 2.
  The source attributes finiteness to Brindza–Erdős [BrEr91] and the
  complete list to Yu–Liu [YuLi96]:
    2! + 1² = 3,   2! + 5² = 3³,   4! + 1⁴ = 5².
  These attributions are archive context, not literature proofs.

  The side remark 6! + 2⁶ = 28² concerns being a perfect power,
  not the equation with right-hand side 7^k. The concrete check below
  establishes only that (7,2,2) is not a solution.
-/
import Mathlib
import Erdos.FactorialPowerCertificates

set_option autoImplicit false

namespace ErdosCandidates.E405

/-- The three listed triples satisfy the guarded equation; this is not
    a completeness assertion. -/
example :
    IsSolution 3 1 1 ∧ IsSolution 3 5 3 ∧ IsSolution 5 1 2 := by
  exact cert_solutions

/-- The `p = 2` identity family for positive `k`. This example is not a
    formal infinitude theorem and is not an `IsSolution` claim. -/
example : ∀ k : ℕ, 1 ≤ k →
    (2 - 1).factorial + (2 ^ k - 1) ^ (2 - 1) = 2 ^ k := by
  exact p2_family

/-- Archived finiteness statement attributed to Brindza–Erdős and
    Yu–Liu: the solution set over all odd primes is finite. This
    literature-level result remains unproved here. -/
theorem brindza_erdos_finite :
    {t : ℕ × ℕ × ℕ | IsSolution t.1 t.2.1 t.2.2}.Finite := by
  sorry

/-- Archived complete resolution attributed to Yu–Liu (YuLi96):
    exactly the three certified triples. Completeness remains unproved. -/
theorem yu_liu_complete :
    {t : ℕ × ℕ × ℕ | IsSolution t.1 t.2.1 t.2.2} =
      {(3, 1, 1), (3, 5, 3), (5, 1, 2)} := by
  sorry

set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Archived sanity window: no other solutions with `p, a, k ≤ 50`.
    This bounded statement remains admitted; no triple sweep is certified. -/
theorem window_50 :
    ∀ p ∈ Finset.range 51, ∀ a ∈ Finset.range 51, ∀ k ∈ Finset.range 51,
      IsSolution p a k →
        (p, a, k) = (3, 1, 1) ∨ (p, a, k) = (3, 5, 3) ∨
        (p, a, k) = (5, 1, 2) := by
  intro p hp a ha k hk hsol
  -- Only oddness and the equation are needed: no odd `p < 51`, prime or
  -- not, has further solutions with `a, k < 51`.
  obtain ⟨-, hodd, -, -, heq⟩ := hsol
  rw [Finset.mem_range] at hp ha hk
  simp only [Prod.mk.injEq]
  revert a k
  -- Even `p` contradict `Odd p`; each odd `p` is a kernel-checked
  -- sweep over `a, k < 51` (the raised instance limits let `Decidable`
  -- synthesize through the three-way disjunction).
  interval_cases p <;> first | (exact absurd hodd (by decide)) | decide +kernel

/-- The side remark is a square calculation, but not a solution at
    `(p,a,k) = (7,2,2)`. -/
example : 720 + 64 = 28 ^ 2 ∧ ¬ IsSolution 7 2 2 := by
  exact side_square_and_not_solution

end ErdosCandidates.E405

/- REVIEW STATUS
   The previous whole-source PASS is not supported by an accompanying
   audit and is superseded by this qualification. Concrete arithmetic
   certificates live in the production module; their verification does
   not certify source attributions, global finiteness, completeness, or
   the admitted window. IsSolution is unchanged: it requires p.Prime,
   Odd p, positive a and k, and the exact factorial-power equality.
   The prime guard keeps p - 1 off truncated subtraction; positivity
   specifies the intended base/exponent domain without external style
   assumptions. The p = 2 unit proves an identity only (also true at
   k = 0), retaining the requested positive-k signature.
-/
