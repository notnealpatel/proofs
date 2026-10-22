/-
# Mertens' first theorem

## Source

F. Mertens, "Ein Beitrag zur analytischen Zahlentheorie",
J. reine angew. Math. 78 (1874), 46-62.  Restated as
Hardy & Wright, *An Introduction to the Theory of Numbers*, Thm 425,
and Apostol, *Introduction to Analytic Number Theory*, Thm 4.10.

## Informal statement (verbatim from the target card)

There is an absolute constant C such that for all real x >= 1,
|sum_{p <= x, p prime} (log p)/p - log x| <= C.

## Date

2026-10-21.

## Mathlib absence check

`leandoc` exact probes `mertens_first`, `Chebyshev.mertens` miss; the BM25
searches "sum log prime divided by prime mertens" and "vonMangoldt sum div
log" return only Chebyshev `ψ`/`θ` identities; `grep -ril mertens` over
Mathlib finds only `NumberTheory/Chebyshev.lean` (no Mertens theorem) and
`RingTheory/Polynomial/ContentIdeal.lean` (Mertens' content theorem,
unrelated).

## Proof route (Legendre / Chebyshev)

With `S n = ∑_{p ≤ n} log p / p` and `v_p = (n !).factorization p`:

* `log n! = ∑_{p ≤ n} v_p log p`;
* `n / p ≤ v_p ≤ n / (p - 1)` (Legendre);
* `n log n - n ≤ log n! ≤ n log n` (Stirling lower bound, `n! ≤ n^n`);
* `θ n ≤ n log 4` (Chebyshev, Mathlib);
* `∑_p log p / (p (p - 1))` is bounded by the convergent
  `∑_k log k / (k (k - 1))`.

Hence `log n - 1 - T ≤ S n ≤ log n + log 4`, and passing from `n = ⌊x⌋₊`
to `x` costs at most `log 2`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.MertensFirst

open Finset

/-- Legendre: `log n! = ∑_{p ≤ n prime} v_p(n!) · log p`. -/
theorem log_factorial_eq_sum (n : ℕ) :
    Real.log (n.factorial : ℝ) =
      ∑ p ∈ Nat.primesLE n, ((n.factorial.factorization p : ℕ) : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization]
  apply Finsupp.sum_of_support_subset
  · intro p hp
    rw [Nat.support_factorization] at hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hdvd : p ∣ n.factorial := Nat.dvd_of_mem_primeFactors hp
    exact Nat.mem_primesLE.mpr ⟨(hpp.dvd_factorial).mp hdvd, hpp⟩
  · intro p _
    simp

/-- Legendre lower bound: `⌊n / p⌋ ≤ v_p(n!)`. -/
theorem div_le_factorization_factorial {p : ℕ} (hp : p.Prime) (n : ℕ) :
    n / p ≤ n.factorial.factorization p := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hlog : Nat.log p n < n + 1 := Nat.lt_succ_of_lt (Nat.log_lt_self p hn.ne')
  rw [Nat.factorization_factorial hp hlog]
  have hmem : 1 ∈ Ico 1 (n + 1) := by simp [hn]
  have hsingle :=
    Finset.single_le_sum (f := fun i => n / p ^ i) (fun _ _ => Nat.zero_le _) hmem
  simpa using hsingle

/-- `(n : ℝ) / p ≤ ⌊n / p⌋ + 1` for `0 < p`. -/
theorem div_le_floor_div_add_one {p : ℕ} (hp : 0 < p) (n : ℕ) :
    (n : ℝ) / p ≤ ((n / p : ℕ) : ℝ) + 1 := by
  have h := Nat.lt_div_mul_add (a := n) hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  rw [div_le_iff₀ hpR]
  have h' : (n : ℝ) < ((n / p : ℕ) : ℝ) * p + p := by exact_mod_cast h
  linarith

/-- `log n! ≤ n log n`. -/
theorem log_factorial_le (n : ℕ) :
    Real.log (n.factorial : ℝ) ≤ n * Real.log n := by
  have hpos : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hle : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
  calc Real.log (n.factorial : ℝ) ≤ Real.log ((n : ℝ) ^ n) := Real.log_le_log hpos hle
    _ = n * Real.log n := by rw [Real.log_pow]

/-- `n log n - n ≤ log n!` for `n ≠ 0` (Stirling lower bound). -/
theorem le_log_factorial {n : ℕ} (hn : n ≠ 0) :
    n * Real.log n - n ≤ Real.log (n.factorial : ℝ) := by
  have h := Stirling.le_log_factorial_stirling hn
  have h1 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have h2 : 0 ≤ Real.log (2 * Real.pi) := by
    apply Real.log_nonneg
    linarith [Real.pi_gt_three]
  linarith

/-- Upper half: `∑_{p ≤ n} log p / p ≤ log n + log 4`. -/
theorem sum_log_div_le (n : ℕ) (hn : 1 ≤ n) :
    ∑ p ∈ Nat.primesLE n, Real.log p / p ≤ Real.log n + Real.log 4 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have key : (n : ℝ) * ∑ p ∈ Nat.primesLE n, Real.log p / p ≤
      Real.log (n.factorial : ℝ) + Chebyshev.theta n := by
    rw [log_factorial_eq_sum, Chebyshev.theta_eq_sum_primesLE_log, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro p hp
    have hpp : p.Prime := (Nat.mem_primesLE.mp hp).2
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hlog : 0 ≤ Real.log p := Real.log_natCast_nonneg p
    have h1 := div_le_floor_div_add_one hpp.pos n
    have h2 : ((n / p : ℕ) : ℝ) ≤ ((n.factorial.factorization p : ℕ) : ℝ) := by
      exact_mod_cast div_le_factorization_factorial hpp n
    calc (n : ℝ) * (Real.log p / p) = (n / p : ℝ) * Real.log p := by ring
      _ ≤ (((n.factorial.factorization p : ℕ) : ℝ) + 1) * Real.log p := by
          apply mul_le_mul_of_nonneg_right _ hlog; linarith
      _ = _ := by ring
  have hθ := Chebyshev.theta_le_log4_mul_x hnR.le
  have hf := log_factorial_le n
  have hmul : (n : ℝ) * ∑ p ∈ Nat.primesLE n, Real.log p / p ≤
      n * (Real.log n + Real.log 4) := by
    linarith
  exact le_of_mul_le_mul_left hmul hnR

/-- The convergent comparison series `log k / (k (k - 1))`. -/
noncomputable def tailTerm (k : ℕ) : ℝ := Real.log k / (k * ((k : ℝ) - 1))

example : tailTerm 1 = 0 := by simp [tailTerm]
example : tailTerm 2 = Real.log 2 / 2 := by norm_num [tailTerm]

/-- Each term of the comparison series is nonnegative. -/
theorem tailTerm_nonneg (k : ℕ) : 0 ≤ tailTerm k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [tailTerm]
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  unfold tailTerm
  apply div_nonneg (Real.log_natCast_nonneg k)
  apply mul_nonneg (by linarith) (by linarith)

/-- The comparison series `∑ log k / (k (k - 1))` converges. -/
theorem summable_tailTerm : Summable tailTerm := by
  have hs : Summable (fun k : ℕ => 4 * ((k : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
    (Real.summable_nat_rpow_inv.mpr (by norm_num)).mul_left 4
  refine Summable.of_nonneg_of_le tailTerm_nonneg (fun k => ?_) hs
  rcases lt_or_ge k 2 with hk | hk
  · interval_cases k <;> simp [tailTerm]
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hsq : (k : ℝ) ^ (1 / 2 : ℝ) * (k : ℝ) ^ (1 / 2 : ℝ) = k := by
    rw [← Real.rpow_add hk0]; norm_num
  have h32 : (k : ℝ) ^ (3 / 2 : ℝ) = k * (k : ℝ) ^ (1 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hk0, Real.rpow_one]
  have hlog : Real.log k ≤ (k : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) :=
    Real.log_le_rpow_div hk0.le (by norm_num)
  have hr : 0 < (k : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hk0 _
  unfold tailTerm
  rw [h32, div_le_iff₀ (by nlinarith)]
  rw [show 4 * (↑k * ↑k ^ (1 / 2 : ℝ))⁻¹ * (↑k * (↑k - 1)) =
      4 * (↑k - 1) / (k : ℝ) ^ (1 / 2 : ℝ) by field_simp]
  rw [le_div_iff₀ hr]
  nlinarith

/-- Lower half: `log n - 1 - T ≤ ∑_{p ≤ n} log p / p`, with `T = ∑' k, tailTerm k`. -/
theorem le_sum_log_div (n : ℕ) (hn : 1 ≤ n) :
    Real.log n - 1 - ∑' k, tailTerm k ≤ ∑ p ∈ Nat.primesLE n, Real.log p / p := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hT : ∑ p ∈ Nat.primesLE n, tailTerm p ≤ ∑' k, tailTerm k :=
    summable_tailTerm.sum_le_tsum _ (fun k _ => tailTerm_nonneg k)
  have key : Real.log (n.factorial : ℝ) ≤
      n * (∑ p ∈ Nat.primesLE n, Real.log p / p + ∑ p ∈ Nat.primesLE n, tailTerm p) := by
    rw [log_factorial_eq_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hpp : p.Prime := (Nat.mem_primesLE.mp hp).2
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hlog : 0 ≤ Real.log p := Real.log_natCast_nonneg p
    have hv : ((n.factorial.factorization p : ℕ) : ℝ) ≤ (n : ℝ) / ((p : ℝ) - 1) := by
      have h1 : n.factorial.factorization p ≤ n / (p - 1) :=
        Nat.factorization_factorial_le_div_pred hpp n
      have h2 : ((n / (p - 1) : ℕ) : ℝ) ≤ (n : ℝ) / ((p - 1 : ℕ) : ℝ) := Nat.cast_div_le
      have h3 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
        rw [Nat.cast_sub hpp.one_le, Nat.cast_one]
      rw [h3] at h2
      exact (Nat.cast_le.mpr h1).trans h2
    have hid : (n : ℝ) / ((p : ℝ) - 1) * Real.log p =
        n * (Real.log p / p + tailTerm p) := by
      unfold tailTerm
      have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
      have hp0 : (p : ℝ) ≠ 0 := by linarith
      field_simp
      ring
    calc ((n.factorial.factorization p : ℕ) : ℝ) * Real.log p
        ≤ (n : ℝ) / ((p : ℝ) - 1) * Real.log p := mul_le_mul_of_nonneg_right hv hlog
      _ = _ := hid
  have hst := le_log_factorial (n := n) (by omega)
  have hmul : (n : ℝ) * (Real.log n - 1 - ∑' k, tailTerm k) ≤
      n * ∑ p ∈ Nat.primesLE n, Real.log p / p := by
    nlinarith
  exact le_of_mul_le_mul_left hmul hnR

/-- **Mertens' first theorem.** There is an absolute constant `C` such that for all real
`x ≥ 1`, `|∑_{p ≤ x, p prime} log p / p - log x| ≤ C`. -/
theorem mertens_first : ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p - Real.log x| ≤ C := by
  refine ⟨Real.log 4 + Real.log 2 + 1 + ∑' k, tailTerm k, fun x hx => ?_⟩
  set n := ⌊x⌋₊ with hn_def
  have hn : 1 ≤ n := Nat.le_floor (by exact_mod_cast hx)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnx : (n : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxn : x < n + 1 := Nat.lt_floor_add_one x
  have hlog1 : Real.log n ≤ Real.log x := Real.log_le_log (by linarith) hnx
  have hlog2 : Real.log x ≤ Real.log 2 + Real.log n := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log (by linarith) (by linarith)
  have hup := sum_log_div_le n hn
  have hlo := le_sum_log_div n hn
  have hT : 0 ≤ ∑' k, tailTerm k := tsum_nonneg tailTerm_nonneg
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [abs_le]
  constructor <;> linarith

end Candidates.MertensFirst
