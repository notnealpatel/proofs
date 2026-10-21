/-
# A094291 — Kotesovec: `lim a(n)^(1/n) = (3 + √5)/2`

## OEIS source (retrieved with `oeis show A094291`, 2026-10-21)

```
NAME:     a(n) = maximal value of C(i, j) * C(n-j, n-i) for 0 <= j <= i <= n.
TERMS:    1,2,4,9,18,40,100,225,525,1225,3136,7056,17640,44100,108900,261360,
          637065,1656369,4008004,10020010,25050025,64128064,155739584, ...
          (offset 1: a(1) = 1, a(2) = 2, a(3) = 4, ...)
FORMULA (the conjecture):
  Conjecture: Limit_{n->oo} a(n)^(1/n) = (3 + sqrt(5))/2. - _Vaclav Kotesovec_,
  Sep 03 2026
FORMULA (companion, NOT formalized here):
  Conjecture: a(n) = C(n-k(n), j(n))*C(n-j(n), k(n)) where
  [n/4] <= j(n) <= k(n) <= j(n)+1; the j (resp. k) value can increase only when
  j = k-1 (resp. j = k). - _M. F. Hasler_, Sep 02 2026
```

## Status

Triage: open (no proof in the entry or the literature as far as the triage
could tell).  This file proves Kotesovec's limit.  Hasler's companion
conjecture (location of the maximizer) is a separate formula line and is not
addressed here.

## Proof outline

* Upper bound `a n ≤ F(2n+1)`: with `d = i - j`,
  `C(i, d) * C(n-j, d) ≤ C(n+d, 2d)` (one Vandermonde term), and
  `C(n+d, n-d)` is one term of `F(2n+1) = ∑_{p+q=2n} C(p, q)`.
* Lower bound `F(n+1)^2 ≤ (n+1)^2 a n`: the diagonal choice `i = n - j` gives
  `C(n-j, j)^2 ≤ a n`; Cauchy–Schwarz on `F(n+1) = ∑_{p+q=n} C(p, q)`.
* `φ^(m+1) ≤ 3 F(m+1)` and `F(m+1) ≤ φ^m`; squeeze `log (a n) / n → log φ^2`
  and `φ^2 = (3 + √5)/2`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A094291KotesovecSepLim

open Finset

/-! ## Definition and ground truth -/

/-- A094291: `a n` is the maximal value of `C(i, j) * C(n - j, n - i)` over
`0 ≤ j ≤ i ≤ n`.  The `Nat` subtractions are exact on this range. -/
def a (n : ℕ) : ℕ :=
  (range (n + 1)).sup fun i => (range (i + 1)).sup fun j => i.choose j * (n - j).choose (n - i)

example : (List.range 12).map (fun n => a (n + 1)) =
    [1, 2, 4, 9, 18, 40, 100, 225, 525, 1225, 3136, 7056] := by decide

/-- Every admissible product `C(i, j) * C(n - j, n - i)` is at most `a n`. -/
theorem choose_mul_choose_le_a {n i j : ℕ} (hji : j ≤ i) (hin : i ≤ n) :
    i.choose j * (n - j).choose (n - i) ≤ a n := by
  unfold a
  refine le_trans ?_ (le_sup (f := fun i => (range (i + 1)).sup fun j =>
    i.choose j * (n - j).choose (n - i)) (mem_range.2 (Nat.lt_succ_of_le hin)))
  exact le_sup (f := fun j => i.choose j * (n - j).choose (n - i))
    (mem_range.2 (Nat.lt_succ_of_le hji))

/-- Upper bound: every admissible product is at most `F(2n+1)`. -/
theorem choose_mul_choose_le_fib {n i j : ℕ} (hji : j ≤ i) (hin : i ≤ n) :
    i.choose j * (n - j).choose (n - i) ≤ Nat.fib (2 * n + 1) := by
  set d := i - j with hd
  have h1 : i.choose j = i.choose d := Nat.choose_symm_of_eq_add (by omega)
  have h2 : (n - j).choose (n - i) = (n - j).choose d := Nat.choose_symm_of_eq_add (by omega)
  have hvand : i.choose d * (n - j).choose d ≤ (i + (n - j)).choose (2 * d) := by
    rw [Nat.add_choose_eq]
    exact single_le_sum (f := fun ij : ℕ × ℕ => i.choose ij.1 * (n - j).choose ij.2)
      (fun _ _ => Nat.zero_le _) (show ((d, d) : ℕ × ℕ) ∈ antidiagonal (2 * d) by
        rw [HasAntidiagonal.mem_antidiagonal]; omega)
  have hsymm : (i + (n - j)).choose (2 * d) = (n + d).choose (n - d) :=
    by rw [show i + (n - j) = n + d by omega]; exact Nat.choose_symm_of_eq_add (by omega)
  have hfib : (n + d).choose (n - d) ≤ Nat.fib (2 * n + 1) := by
    rw [Nat.fib_succ_eq_sum_choose]
    exact single_le_sum (f := fun p : ℕ × ℕ => p.1.choose p.2)
      (fun _ _ => Nat.zero_le _) (show ((n + d, n - d) : ℕ × ℕ) ∈ antidiagonal (2 * n) by
        rw [HasAntidiagonal.mem_antidiagonal]; omega)
  rw [h1, h2]
  exact hvand.trans (hsymm ▸ hfib)

/-- Upper bound `a n ≤ F(2n+1)`. -/
theorem a_le_fib (n : ℕ) : a n ≤ Nat.fib (2 * n + 1) := by
  unfold a
  refine Finset.sup_le fun i hi => Finset.sup_le fun j hj => ?_
  exact choose_mul_choose_le_fib (Nat.lt_succ_iff.1 (mem_range.1 hj))
    (Nat.lt_succ_iff.1 (mem_range.1 hi))

/-- Lower bound `F(n+1)^2 ≤ (n+1)^2 * a n`, from the diagonal terms `i = n - j`
and Cauchy–Schwarz on `F(n+1) = ∑_{p+q=n} C(p, q)`. -/
theorem fib_sq_le (n : ℕ) : Nat.fib (n + 1) ^ 2 ≤ (n + 1) ^ 2 * a n := by
  have hterm : ∀ pq ∈ antidiagonal n, pq.1.choose pq.2 ^ 2 ≤ a n := by
    rintro ⟨p, q⟩ hpq
    rw [HasAntidiagonal.mem_antidiagonal] at hpq
    rcases le_or_gt q p with hqp | hpq'
    · have hprod := choose_mul_choose_le_a (n := n) hqp (by omega : p ≤ n)
      rwa [show n - q = p by omega, show n - p = q by omega, ← sq] at hprod
    · simp [Nat.choose_eq_zero_of_lt hpq']
  rw [Nat.fib_succ_eq_sum_choose]
  calc (∑ pq ∈ antidiagonal n, pq.1.choose pq.2) ^ 2
      ≤ #(antidiagonal n) * ∑ pq ∈ antidiagonal n, pq.1.choose pq.2 ^ 2 :=
        sq_sum_le_card_mul_sum_sq
    _ ≤ (n + 1) * ((n + 1) * a n) := by
        rw [Nat.card_antidiagonal]
        gcongr
        calc ∑ pq ∈ antidiagonal n, pq.1.choose pq.2 ^ 2 ≤ ∑ _pq ∈ antidiagonal n, a n :=
              sum_le_sum hterm
          _ = (n + 1) * a n := by rw [sum_const, Nat.card_antidiagonal, smul_eq_mul]
    _ = (n + 1) ^ 2 * a n := by ring

/-- `a n` is positive: the pair `i = j = 0` contributes `C(0,0) * C(n,n) = 1`. -/
theorem a_pos (n : ℕ) : 0 < a n := by
  have h := choose_mul_choose_le_a (n := n) (le_refl 0) (Nat.zero_le n)
  exact lt_of_lt_of_le Nat.one_pos (by simpa using h)

open Real

/-! ## Analytic layer -/

/-- Binet-type upper bound `F(m+1) ≤ goldenRatio^m`. -/
theorem fib_succ_le_goldenRatio_pow (m : ℕ) : (Nat.fib (m + 1) : ℝ) ≤ goldenRatio ^ m := by
  have h := goldenRatio_mul_fib_succ_add_fib m
  have hfib : (0 : ℝ) ≤ Nat.fib m := Nat.cast_nonneg _
  have hmul : goldenRatio * (Nat.fib (m + 1) : ℝ) ≤ goldenRatio * goldenRatio ^ m := by
    rw [← pow_succ']; linarith
  exact le_of_mul_le_mul_left hmul goldenRatio_pos

/-- Binet-type lower bound `φ^(m+1) ≤ 3 F(m+1)`. -/
theorem goldenRatio_pow_le_three_mul_fib (m : ℕ) : goldenRatio ^ (m + 1) ≤ 3 * (Nat.fib (m + 1) : ℝ) := by
  have h := goldenRatio_mul_fib_succ_add_fib m
  have hle : (Nat.fib m : ℝ) ≤ Nat.fib (m + 1) := by exact_mod_cast Nat.fib_le_fib_succ
  have hφ : goldenRatio < 2 := goldenRatio_lt_two
  have hfib : (0 : ℝ) ≤ Nat.fib (m + 1) := Nat.cast_nonneg _
  nlinarith

/-- Real upper bound `a n ≤ (goldenRatio^2)^n`. -/
theorem a_le_goldenRatio_sq_pow (n : ℕ) : (a n : ℝ) ≤ (goldenRatio ^ 2) ^ n := by
  calc (a n : ℝ) ≤ Nat.fib (2 * n + 1) := by exact_mod_cast a_le_fib n
    _ ≤ goldenRatio ^ (2 * n) := fib_succ_le_goldenRatio_pow _
    _ = (goldenRatio ^ 2) ^ n := pow_mul _ _ _

/-- Real lower bound `(goldenRatio^2)^(n+1) ≤ 9 (n+1)^2 a n`. -/
theorem goldenRatio_sq_pow_le (n : ℕ) :
    (goldenRatio ^ 2) ^ (n + 1) ≤ 9 * ((n : ℝ) + 1) ^ 2 * a n := by
  have h3 := goldenRatio_pow_le_three_mul_fib n
  have hpos : 0 ≤ goldenRatio ^ (n + 1) := pow_nonneg goldenRatio_pos.le _
  have hsq : (Nat.fib (n + 1) : ℝ) ^ 2 ≤ ((n : ℝ) + 1) ^ 2 * a n := by
    exact_mod_cast fib_sq_le n
  calc (goldenRatio ^ 2) ^ (n + 1) = (goldenRatio ^ (n + 1)) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
    _ ≤ (3 * (Nat.fib (n + 1) : ℝ)) ^ 2 := pow_le_pow_left₀ hpos h3 2
    _ = 9 * (Nat.fib (n + 1) : ℝ) ^ 2 := by ring
    _ ≤ 9 * (((n : ℝ) + 1) ^ 2 * a n) := by gcongr
    _ = 9 * ((n : ℝ) + 1) ^ 2 * a n := by ring

/-- `log (n + 1) / n → 0` along the naturals. -/
theorem tendsto_log_succ_div : Filter.Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) / n)
    Filter.atTop (nhds 0) := by
  have h := Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero
  have hn : Filter.Tendsto (fun n : ℕ => (n : ℝ) + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  refine (h.comp hn).congr fun n => ?_
  simp

/-- `log (a n) / n → log (goldenRatio^2)`. -/
theorem tendsto_log_a_div : Filter.Tendsto (fun n : ℕ => Real.log (a n) / n)
    Filter.atTop (nhds (Real.log (goldenRatio ^ 2))) := by
  set L := Real.log (goldenRatio ^ 2) with hL
  have hφ2 : 0 < goldenRatio ^ 2 := pow_pos goldenRatio_pos 2
  have hlow : Filter.Tendsto (fun n : ℕ => L + (L - Real.log 9) * (1 / (n : ℝ)) -
      2 * (Real.log ((n : ℝ) + 1) / n)) Filter.atTop (nhds L) := by
    have h1 := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (L - Real.log 9)
    have h2 := tendsto_log_succ_div.const_mul 2
    have h3 := (h1.const_add L).sub h2
    simpa using h3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hapos : (0 : ℝ) < a n := by exact_mod_cast a_pos n
    have hbound := goldenRatio_sq_pow_le n
    have hlog := Real.log_le_log (pow_pos hφ2 _) hbound
    have e1 : Real.log ((goldenRatio ^ 2) ^ (n + 1)) = ((n : ℝ) + 1) * L := by
      rw [Real.log_pow]; push_cast; rfl
    have e2 : Real.log (9 * ((n : ℝ) + 1) ^ 2 * a n)
        = Real.log 9 + 2 * Real.log ((n : ℝ) + 1) + Real.log (a n) := by
      rw [Real.log_mul (by positivity) hapos.ne', Real.log_mul (by norm_num) (by positivity),
        Real.log_pow]
      push_cast
      ring
    rw [e1, e2] at hlog
    rw [le_div_iff₀ hnpos]
    have hexp : (L + (L - Real.log 9) * (1 / (n : ℝ)) - 2 * (Real.log ((n : ℝ) + 1) / n)) * n
        = (n + 1) * L - Real.log 9 - 2 * Real.log ((n : ℝ) + 1) := by
      field_simp
      ring
    rw [hexp]
    linarith
  · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hapos : (0 : ℝ) < a n := by exact_mod_cast a_pos n
    have hlog := Real.log_le_log hapos (a_le_goldenRatio_sq_pow n)
    rw [Real.log_pow] at hlog
    rw [div_le_iff₀ hnpos]
    linarith

/-- `φ^2 = (3 + √5) / 2`. -/
theorem goldenRatio_sq_eq : goldenRatio ^ 2 = (3 + Real.sqrt 5) / 2 := by
  rw [goldenRatio_sq, goldenRatio]
  ring

/-- **Kotesovec's conjecture (A094291, Vaclav Kotesovec, Sep 03 2026).**

Verbatim: "Conjecture: Limit_{n->oo} a(n)^(1/n) = (3 + sqrt(5))/2."

Here `a n = max_{0 ≤ j ≤ i ≤ n} C(i, j) * C(n - j, n - i)`.  The value of the
real power at `n = 0` (exponent `1/0 = 0`) is irrelevant to the limit. -/
theorem kotesovec_limit : Filter.Tendsto (fun n : ℕ => (a n : ℝ) ^ ((1 : ℝ) / n))
    Filter.atTop (nhds ((3 + Real.sqrt 5) / 2)) := by
  have hexp := (Real.continuous_exp.tendsto _).comp tendsto_log_a_div
  rw [Real.exp_log (pow_pos goldenRatio_pos 2), goldenRatio_sq_eq] at hexp
  refine hexp.congr fun n => ?_
  have hapos : (0 : ℝ) < a n := by exact_mod_cast a_pos n
  rw [Function.comp_apply, Real.rpow_def_of_pos hapos, mul_one_div]

end Candidates.A094291KotesovecSepLim
