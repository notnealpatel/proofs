/-
  Erdős Problem #405 — (p−1)! + a^(p−1) = p^k.
  Status: proved (Brindza–Erdős 1991; complete resolution Yu–Liu 1996).
  Tier B archive target with decide certificates.

  Verbatim statement (`goof erdos fetch 405`, pulled 2026-08-05):

    "Let $p$ be an odd prime. Is it true that the equation
    \[(p-1)!+a^{p-1}=p^k\]
    has only finitely many solutions?"

  DB remarks: Erdős–Graham originally allowed p = 2, "presumably an
  oversight" (infinitely many solutions: 1 + a = 2^k).  Brindza–Erdős
  [BrEr91] proved finiteness.  Yu–Liu [YuLi96] determined ALL solutions:
    2! + 1² = 3,   2! + 5² = 3³,   4! + 1⁴ = 5².
  (I.e. (p, a, k) ∈ {(3,1,1), (3,5,3), (5,1,2)}.)

  Fidelity note from the candidates doc resolved: the DB's "example"
  6! + 2⁶ = 28² belongs to the *separate* remark that (p−1)! + a^(p−1)
  is rarely a perfect power at all — it is NOT of the p^k form and does
  not contaminate the odd-p solution list above.

  Mathlib inventory (leandoc 2026-08-05): `Nat.factorial`, `Nat.Prime`,
  pow.  Baker-method effective bounds (the actual Yu–Liu engine —
  linear forms in p-adic logs) are absent from Mathlib: completeness
  stays archived; the solution certificates and small-window sweeps are
  the sorry-free layer.
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E405

/-- `IsSolution p a k`: `(p−1)! + a^(p−1) = p^k` with `p` an odd prime
    and `a, k ≥ 1`.  (`a = 0` would allow the degenerate
    `(p−1)! = p^k`, impossible anyway but excluded per STYLE.md
    nontriviality; `k = 0` likewise.) -/
def IsSolution (p a k : ℕ) : Prop :=
  p.Prime ∧ Odd p ∧ 1 ≤ a ∧ 1 ≤ k ∧
    (p - 1).factorial + a ^ (p - 1) = p ^ k

/-- The three Yu–Liu solutions, as certificates.
    2! + 1² = 3¹;  2! + 5² = 27 = 3³;  4! + 1⁴ = 25 = 5².
    -- PROVABLE (decide). -/
theorem cert_solutions :
    IsSolution 3 1 1 ∧ IsSolution 3 5 3 ∧ IsSolution 5 1 2 := by
  sorry

/-- Non-degeneracy of the odd-p hypothesis: for p = 2 there are
    infinitely many solutions (1! + a = 2^k for a = 2^k − 1), so the
    `Odd p` guard carries content.  -- PROVABLE (witness family). -/
example : ∀ k : ℕ, 1 ≤ k →
    (2 - 1).factorial + (2 ^ k - 1) ^ (2 - 1) = 2 ^ k := by
  sorry

/-- **Erdős #405, finiteness (Brindza–Erdős 1991)**: for each odd prime
    `p`, finitely many `(a, k)` solve the equation.  In fact the full
    solution set over all odd `p` is finite (Yu–Liu).  Archived —
    Baker's method (p-adic linear forms in logarithms) is absent from
    Mathlib. -/
theorem brindza_erdos_finite :
    {t : ℕ × ℕ × ℕ | IsSolution t.1 t.2.1 t.2.2}.Finite := by
  sorry

/-- **Yu–Liu complete resolution** (YuLi96): the solutions are exactly
    the three certificates. -/
theorem yu_liu_complete :
    {t : ℕ × ℕ × ℕ | IsSolution t.1 t.2.1 t.2.2} =
      {(3, 1, 1), (3, 5, 3), (5, 1, 2)} := by
  sorry

/-- Sanity window: no other solutions with `p, a, k ≤ 50`.
    -- PROVABLE (decide; 50³ triples with factorial/pow evaluation —
    stage the bound if kernel-slow).  Note `(p−1)!` for p ≤ 50 is a
    ~200-bit number; `Nat` kernel arithmetic handles it. -/
theorem window_50 :
    ∀ p ∈ Finset.range 51, ∀ a ∈ Finset.range 51, ∀ k ∈ Finset.range 51,
      IsSolution p a k →
        (p, a, k) = (3, 1, 1) ∨ (p, a, k) = (3, 5, 3) ∨
        (p, a, k) = (5, 1, 2) := by
  sorry

/-- The DB's side remark, for the record: `6! + 2⁶ = 784 = 28²` is a
    perfect square — an instance of "(p−1)! + a^(p−1) can be a power"
    with `p = 7`, but `784` is not a power of `7`, so it is NOT a
    solution of this problem's equation.  Guards future readers against
    the miscount flagged in the candidates document.
    -- PROVABLE (decide). -/
example : 720 + 64 = 28 ^ 2 ∧ ¬ IsSolution 7 2 2 := by
  sorry

end ErdosCandidates.E405

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - Statement matches source verbatim. Brindza-Erdos and Yu-Liu attributions correct.
   - Three Yu-Liu solutions verified: 2!+1^2=3=3^1, 2!+5^2=27=3^3, 4!+1^4=25=5^2.
   - Side remark 6!+2^6=784=28^2 correctly identified as NOT a solution (784 != 7^k).
     The file's guard example at line 90 correctly encodes this.
   - IsSolution predicate correctly requires p.Prime, Odd p, 1<=a, 1<=k, and uses
     (p-1).factorial + a^(p-1) = p^k. NAT-subtraction p-1 is exact since p >= 3.
   - Odd p guard justified: p=2 case gives infinitely many solutions (1!+a=2^k).
     The file's example at line 53 encodes this correctly.
   - p=2 non-degeneracy example: (2-1).factorial + (2^k-1)^(2-1) = 1+(2^k-1) = 2^k.
     NAT-subtraction 2^k-1 is exact for k>=1 (guard present). Correct.
   - No comment-sourced claims; source has no comments.
-/
