/-
  Erdős Problem #727 — factorial square divisibility (n+k)!² ∣ (2n)!.
  Status: open (even k = 2).  Tier UC lemma mine (Balakran's k = 1
  theorem + factorial-divisibility lemmas).

  Verbatim statement (`goof erdos fetch 727`, pulled 2026-08-05):

    "Let $k\geq 2$. Does\[(n+k)!^2 \mid (2n)!\]for infinitely many
    $n$?"

  DB remarks (EGRS75): open even for k = 2.  Balakran [Ba29]: the
  k = 1 analogue holds infinitely often — (n+1)!² ∣ (2n)!, i.e.
  (n+1)² ∣ C(2n,n); classical: (n+1) ∣ C(2n,n) always (Catalan).
  EGRS: Balakran's method gives (n+k)!(n+1)! ∣ (2n)! infinitely often
  (even for k < c·log n).  Erdős [Er68c]: a!b! ∣ n! forces
  a + b ≤ n + O(log n).

  OEIS anchors: A002503 (numbers n with (n+1)² ∣ C(2n,n):
  0, 5, 13, 14, 41, 55, 63, …), A343507, A389396.

  Mathlib inventory: `Nat.factorial`, `Nat.centralBinom`, `catalan`
  with `Nat.succ_mul_catalan_eq_centralBinom` (`(n+1)·Cₙ = C(2n,n)`)
  — the bridge making the k = 1 statement a divisibility fact about
  Catalan numbers.
-/
import Mathlib

set_option autoImplicit false

namespace ErdosCandidates.E727

/-- Ground truth for the k = 1 shape at the first nontrivial A002503
    term: n = 5: (5+1)!² = 518400 divides 10! = 3628800 = 7·518400.
    -- PROVABLE (decide). -/
example : (Nat.factorial 6) ^ 2 ∣ Nat.factorial 10 := by
  sorry

/-- The equivalence powering the k = 1 case: for `n ≥ 1`,
    `(n+1)!² ∣ (2n)! ↔ (n+1) ∣ catalan n`.
    Via `(2n)!/(n!)² = C(2n,n) = (n+1)·catalan n`.
    -- PROVABLE (Mathlib: `Nat.succ_mul_catalan_eq_centralBinom`,
    `Nat.choose_mul_factorial_mul_factorial`; effort S). -/
theorem sq_dvd_iff_dvd_catalan (n : ℕ) :
    (n + 1).factorial ^ 2 ∣ (2 * n).factorial ↔ (n + 1) ∣ catalan n := by
  sorry

/-- **Balakran's theorem (k = 1; the lemma-mine prize)** ([Ba29]):
    `(n+1)!² ∣ (2n)!` for infinitely many `n`.
    Proof route: via the equivalence, find infinitely many `n` with
    `(n+1) ∣ catalan n` — Balakran's construction takes `n + 1 = p`
    prime... (concretely A002503 contains 5, 13, 41: n+2 = 7, 15?, no —
    re-derive the construction from [Ba29] before the campaign; the
    OEIS terms 5, 13, 14, 41 suggest n ≡ p − 1 patterns).  Effort M. -/
theorem balakran_k1 :
    {n : ℕ | (n + 1).factorial ^ 2 ∣ (2 * n).factorial}.Infinite := by
  sorry

/-- **Erdős #727 (OPEN, even for k = 2)**: for each `k ≥ 2`,
    `(n+k)!² ∣ (2n)!` for infinitely many `n`. -/
theorem erdos_727 (k : ℕ) (hk : 2 ≤ k) :
    {n : ℕ | (n + k).factorial ^ 2 ∣ (2 * n).factorial}.Infinite := by
  sorry

/-- Satisfiability of the k = 2 property at SOME point — probe:
    does any small n satisfy (n+2)!² ∣ (2n)!?  (Density heuristics say
    solutions exist but are sparse; run a sage sweep before pinning a
    witness.  Recorded sorry'd with the witness left symbolic.)
    -- PROBE NEEDED. -/
theorem k2_witness_exists :
    ∃ n : ℕ, (n + 2).factorial ^ 2 ∣ (2 * n).factorial := by
  sorry

/-- **EGRS mixed-factorial theorem** (EGRS75), archived:
    `(n+k)!(n+1)! ∣ (2n)!` for infinitely many `n` (for each fixed
    `k`; in fact uniformly for `k < c log n`). -/
theorem egrs_mixed (k : ℕ) (hk : 1 ≤ k) :
    {n : ℕ | (n + k).factorial * (n + 1).factorial ∣
      (2 * n).factorial}.Infinite := by
  sorry

/-- **Erdős's a!b! ∣ n! bound** ([Er68c]), archived lemma-mine target:
    there is `C` such that `a!·b! ∣ n!` (with `a, b ≥ 1, n ≥ 2`)
    forces `a + b ≤ n + C·log n`.  (Stated with `Nat.log 2` for a
    concrete logarithm; the constant absorbs the base change.) -/
theorem factorial_mul_factorial_dvd_bound :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ a b n : ℕ, 1 ≤ a → 1 ≤ b → 2 ≤ n →
      a.factorial * b.factorial ∣ n.factorial →
      a + b ≤ n + C * Nat.log 2 n := by
  sorry

end ErdosCandidates.E727

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - Verbatim statement matches DB text exactly.
   - Balakran k=1 claim, EGRS mixed form, Erdos a!b!|n! bound all match DB remarks.
   - OEIS anchors A002503, A343507, A389396 match DB comments.
   - Arithmetic: 6!^2 = 518400, 10! = 3628800, quotient 7. Correct.
   - sq_dvd_iff_dvd_catalan equivalence: (2n)!/(n!)^2 = C(2n,n) = (n+1)*catalan(n),
     so (n+1)!^2 | (2n)! iff (n+1)^2 | C(2n,n) iff (n+1) | catalan(n). Plausible.
   - Lean types faithful to the mathematical content.
-/
