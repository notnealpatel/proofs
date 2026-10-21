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

  OEIS anchors: A002503 (positive numbers n with (n+1)² ∣ C(2n,n));
  `n = 0` is also a valid boundary case, A343507, A389396.

  Mathlib inventory: `Nat.factorial`, `Nat.centralBinom`, `catalan`
  with `succ_mul_catalan_eq_centralBinom` (`(n+1)·Cₙ = C(2n,n)`)
  — the bridge making the k = 1 statement a divisibility fact about
  Catalan numbers.
-/
import Mathlib
import Erdos.FactorialCatalan
import Erdos.FactorialSquareWitness

set_option autoImplicit false

namespace ErdosCandidates.E727

/-- Ground truth for the k = 1 shape at the first nontrivial A002503
    term: n = 5: (5+1)!² = 518400 divides 10! = 3628800 = 7·518400.
    Certified by the production ground-truth theorem. -/
example : (Nat.factorial 6) ^ 2 ∣ Nat.factorial 10 := by
  exact Erdos727.factorial_six_sq_dvd_factorial_ten

/-- The equivalence powering the k = 1 case, for every natural `n`, including `0`:
    `(n+1)!² ∣ (2n)! ↔ (n+1) ∣ catalan n`.
    Via `(2n)!/(n!)² = C(2n,n) = (n+1)·catalan n`.
    The production bridge uses `succ_mul_catalan_eq_centralBinom` and
    `Nat.choose_mul_factorial_mul_factorial`. -/
theorem sq_dvd_iff_dvd_catalan (n : ℕ) :
    (n + 1).factorial ^ 2 ∣ (2 * n).factorial ↔ (n + 1) ∣ catalan n := by
  exact Erdos727.sq_dvd_iff_dvd_catalan n

/-- **Balakran's theorem (k = 1; the lemma-mine prize)** ([Ba29]):
    `(n+1)!² ∣ (2n)!` for infinitely many `n`.
    This known infinitude theorem remains unformalized here; no sourced
    infinitude construction is formalized. -/
theorem balakran_k1 :
    {n : ℕ | (n + 1).factorial ^ 2 ∣ (2 * n).factorial}.Infinite := by
  sorry

/-- **Erdős #727 (OPEN, even for k = 2)**: for each `k ≥ 2`,
    `(n+k)!² ∣ (2n)!` for infinitely many `n`. -/
theorem erdos_727 (k : ℕ) (hk : 2 ≤ k) :
    {n : ℕ | (n + k).factorial ^ 2 ∣ (2 * n).factorial}.Infinite := by
  sorry

/-- Satisfiability of the k = 2 property: the production theorem certifies
    `(n+2)!² ∣ (2n)!` at `n = 208`. This single witness does not establish
    infinitude. -/
theorem k2_witness_exists :
    ∃ n : ℕ, (n + 2).factorial ^ 2 ∣ (2 * n).factorial := by
  exact Erdos727.k2_witness_exists

/-- **EGRS mixed-factorial theorem** (EGRS75), archived:
    `(n+k)!(n+1)! ∣ (2n)!` for infinitely many `n` (for each fixed
    `k`; in fact uniformly for `k < c log n`). -/
theorem egrs_mixed (k : ℕ) (hk : 1 ≤ k) :
    {n : ℕ | (n + k).factorial * (n + 1).factorial ∣
      (2 * n).factorial}.Infinite := by
  sorry

/-- Binary digit sum bound: `s₂(x) ≤ log₂ x + 1`. -/
private lemma digitSum_two_le_log (x : ℕ) : (Nat.digits 2 x).sum ≤ Nat.log 2 x + 1 := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  have hlen : (Nat.digits 2 x).length = Nat.log 2 x + 1 :=
    Nat.length_digits 2 x (by norm_num) hx.ne'
  have hle : (Nat.digits 2 x).sum ≤ (Nat.digits 2 x).length • 1 :=
    List.sum_le_card_nsmul _ 1 fun d hd =>
      Nat.le_of_lt_succ (Nat.digits_lt_base (by norm_num) hd)
  simpa [hlen] using hle

/-- Legendre at `p = 2`: `v₂(x!) + s₂(x) = x`. -/
private lemma padicValNat_two_factorial_add (x : ℕ) :
    padicValNat 2 x.factorial + (Nat.digits 2 x).sum = x := by
  have h := sub_one_mul_padicValNat_factorial (p := 2) x
  have hs := Nat.digit_sum_le 2 x
  simp only [Nat.reduceSub, one_mul] at h
  omega

/-- If `a! ∣ n!` with `0 < n` then `a ≤ n`. -/
private lemma le_of_factorial_dvd_factorial {a n : ℕ} (hn : 0 < n)
    (h : a.factorial ∣ n.factorial) : a ≤ n := by
  by_contra hlt
  have h1 : n.factorial < a.factorial := (Nat.factorial_lt hn).mpr (not_le.mp hlt)
  have h2 : a.factorial ≤ n.factorial := Nat.le_of_dvd (Nat.factorial_pos n) h
  omega

/-- **Erdős's a!b! ∣ n! bound** ([Er68c]), archived lemma-mine target:
    there is `C` such that `a!·b! ∣ n!` (with `a, b ≥ 1, n ≥ 2`)
    forces `a + b ≤ n + C·log n`.  (Stated with `Nat.log 2` for a
    concrete logarithm; the constant absorbs the base change.) -/
theorem factorial_mul_factorial_dvd_bound :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ a b n : ℕ, 1 ≤ a → 1 ≤ b → 2 ≤ n →
      a.factorial * b.factorial ∣ n.factorial →
      a + b ≤ n + C * Nat.log 2 n := by
  refine ⟨4, by norm_num, fun a b n _ _ hn hdvd => ?_⟩
  have hn0 : 0 < n := by omega
  have ha : a ≤ n :=
    le_of_factorial_dvd_factorial hn0 (dvd_trans (dvd_mul_right _ _) hdvd)
  have hb : b ≤ n :=
    le_of_factorial_dvd_factorial hn0 (dvd_trans (dvd_mul_left _ _) hdvd)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- 2-adic valuations add along `a! * b! ∣ n!`
  have hv : padicValNat 2 a.factorial + padicValNat 2 b.factorial ≤
      padicValNat 2 n.factorial := by
    rw [← padicValNat.mul (Nat.factorial_ne_zero a) (Nat.factorial_ne_zero b)]
    exact (padicValNat_dvd_iff_le (Nat.factorial_ne_zero n)).mp
      (dvd_trans pow_padicValNat_dvd hdvd)
  have hla : Nat.log 2 a ≤ Nat.log 2 n := Nat.log_mono_right ha
  have hlb : Nat.log 2 b ≤ Nat.log 2 n := Nat.log_mono_right hb
  have hlog : 1 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (by simpa using hn)
  have hsa := digitSum_two_le_log a
  have hsb := digitSum_two_le_log b
  have hea := padicValNat_two_factorial_add a
  have heb := padicValNat_two_factorial_add b
  have hen := padicValNat_two_factorial_add n
  -- a + b ≤ n + s₂(a) + s₂(b) ≤ n + 2 log₂ n + 2 ≤ n + 4 log₂ n
  omega

end ErdosCandidates.E727

/- SOURCE-FIDELITY REVIEW (flash, 2026-08-05)
   Verdict: PASS
   - Verbatim statement matches DB text exactly.
   - Balakran k=1 claim, EGRS mixed form, Erdos a!b!|n! bound all match DB remarks.
   - OEIS identifiers A002503, A343507, A389396 are recorded above;
     the previously listed unchecked examples were removed.
   - Arithmetic: 6!^2 = 518400, 10! = 3628800, quotient 7. Correct.
   - sq_dvd_iff_dvd_catalan equivalence: (2n)!/(n!)^2 = C(2n,n) = (n+1)*catalan(n),
     so (n+1)!^2 | (2n)! iff (n+1)^2 | C(2n,n) iff (n+1) | catalan(n). Plausible.
   - Lean types faithful to the mathematical content.
-/
