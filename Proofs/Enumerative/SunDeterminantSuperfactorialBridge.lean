/-
# Sun's composite determinant congruence

Yutong Zhang and Yaoran Yang, "A Determinant Congruence Conjectured by Sun",
arXiv:2605.19486, Section 2, Lemma 2.1 and Proposition 2.2;
Sun's Conjecture 4.1 (2024).
For every integer bivariate polynomial `F`, `sf(n-1)^2` divides
`det[F(i,j)]_(0≤i,j<n)`. Reduction modulo monic falling factorials
factors the evaluation matrix as `V A Vᵀ`, with integral `A` and
Vandermonde determinant `sf(n-1)`.
For composite `n ≥ 4`, `n ∣ sf(n-1)`, giving the exact Sun determinant
congruence without parity or Jacobi-symbol assumptions. The prime case
and the paper's alternating-polynomial Lemma 2.1 are not formalized here.
-/
import Mathlib

set_option autoImplicit false

namespace SunDeterminantSuperfactorialBridge

open Polynomial

/-! ## Definitions -/

/-- Sun's determinant `D_n(c,d) = det[(i^2 + c i j + d j^2)^(n-2)]_{0 ≤ i,j ≤ n-1}`
(arXiv:2605.19486, equation (1.1)).  The paper only uses it for `n > 3`, where the
natural-number exponent `n - 2` is the true difference. -/
noncomputable def sunDet (n : ℕ) (c d : ℤ) : ℤ :=
  (Matrix.of fun i j : Fin n =>
    (((i : ℕ) : ℤ) ^ 2 + c * ((i : ℕ) : ℤ) * ((j : ℕ) : ℤ) + d * ((j : ℕ) : ℤ) ^ 2) ^ (n - 2)).det

/-- The bivariate integer polynomial `(X^2 + c X Y + d Y^2)^(n-2)` as an element of
`ℤ[X][Y]`: the inner variable `X` carries the row index and the outer variable `Y`
the column index. -/
noncomputable def sunPoly (n : ℕ) (c d : ℤ) : ℤ[X][X] :=
  (C (X ^ 2) + C (C c * X) * X + C (C d) * X ^ 2) ^ (n - 2)

/-- The integer coefficient matrix obtained by reducing `F ∈ ℤ[X][Y]` modulo the
falling factorial `Y(Y-1)⋯(Y-n+1)` and then each coefficient modulo
`X(X-1)⋯(X-n+1)`; entry `(k, l)` is the coefficient of `X^k Y^l`. -/
noncomputable def redCoeff (F : ℤ[X][X]) (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun k l => ((F %ₘ descPochhammer ℤ[X] n).coeff l %ₘ descPochhammer ℤ n).coeff k

/-! ## Examples -/

/-- `sf(3) = 1! 2! 3! = 12`, the superfactorial used for `n = 4`. -/
example : Nat.superFactorial 3 = 12 := by decide

/-- `sf(5) = 1! 2! 3! 4! 5! = 34560`. -/
example : Nat.superFactorial 5 = 34560 := by decide

/-- For `n = 3` the determinant is `-4 c d` (Sage: `(-1) * 2^2 * d * c`); note
`sf(2)^2 = 4` divides it, as the bridge predicts. -/
example (c d : ℤ) : sunDet 3 c d = -4 * c * d := by
  simp only [sunDet, Nat.reduceSub, pow_one, Matrix.det_fin_three, Fin.isValue, Matrix.of_apply,
    Fin.coe_ofNat_eq_mod, Nat.zero_mod, CharP.cast_eq_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, mul_zero, add_zero, Nat.one_mod, Nat.cast_one, one_pow, mul_one,
    zero_mul, Nat.mod_succ, Nat.cast_ofNat, Int.reducePow, sub_self, zero_add, zero_sub,
    Int.reduceNeg, neg_mul]
  ring

/-- `sunPoly` evaluates to the entries of `sunDet`. -/
example (n : ℕ) (c d : ℤ) (i j : ℤ) :
    ((sunPoly n c d).eval (C j)).eval i = (i ^ 2 + c * i * j + d * j ^ 2) ^ (n - 2) := by
  simp [sunPoly]

/-! ## The superfactorial-squared bridge -/

/-- For `i < n`, the value `p(i)` agrees with the value at `i` of the remainder of
`p` modulo the monic falling factorial `X(X-1)⋯(X-n+1)`, written in the monomial
basis `X^k`, `k < n`. -/
theorem eval_eq_sum_modByMonic_descPochhammer {R : Type*} [CommRing R] [Nontrivial R]
    [NoZeroDivisors R] (p : R[X]) {n : ℕ} (i : Fin n) :
    p.eval ((i : ℕ) : R) =
      ∑ k : Fin n, (p %ₘ descPochhammer R n).coeff k * ((i : ℕ) : R) ^ (k : ℕ) := by
  have hmon : (descPochhammer R n).Monic := monic_descPochhammer R n
  have hzero : (descPochhammer R n).eval ((i : ℕ) : R) = 0 := by
    rw [descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_zero_iff_lt.mpr i.isLt,
      Nat.cast_zero]
  have hdeg : (p %ₘ descPochhammer R n).natDegree < n := by
    have hne : descPochhammer R n ≠ 1 := by
      intro h
      have hnat := descPochhammer_natDegree R n
      rw [h, natDegree_one] at hnat
      have hi := i.isLt
      omega
    simpa [descPochhammer_natDegree] using natDegree_modByMonic_lt p hmon hne
  conv_lhs => rw [← modByMonic_add_div p (descPochhammer R n)]
  rw [eval_add, eval_mul, hzero, zero_mul, add_zero, eval_eq_sum_range' hdeg,
    Fin.sum_univ_eq_sum_range (fun k => (p %ₘ descPochhammer R n).coeff k * ((i : ℕ) : R) ^ k)]

/-- For `i, j < n`, `F(i,j) = ∑_{k,l<n} i^k A_{kl} j^l` with `A = redCoeff F n`. -/
theorem eval_eval_eq_sum_redCoeff (F : ℤ[X][X]) {n : ℕ} (i j : Fin n) :
    (F.eval (C ((j : ℕ) : ℤ))).eval ((i : ℕ) : ℤ) =
      ∑ l : Fin n, (∑ k : Fin n, ((i : ℕ) : ℤ) ^ (k : ℕ) * redCoeff F n k l) *
        ((j : ℕ) : ℤ) ^ (l : ℕ) := by
  have hC : C ((j : ℕ) : ℤ) = (((j : ℕ) : ℤ[X])) := by simp
  rw [hC, eval_eq_sum_modByMonic_descPochhammer F j, eval_finsetSum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [eval_mul, eval_pow, eval_natCast, eval_eq_sum_modByMonic_descPochhammer _ i]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [redCoeff, Matrix.of_apply]
  ring

/-- The evaluation matrix `[F(i,j)]_{i,j<n}` factors as `V A Vᵀ`, with `V` the
Vandermonde matrix at `0, …, n-1` and `A = redCoeff F n`. -/
theorem evalMatrix_eq_vandermonde_mul_redCoeff_mul (F : ℤ[X][X]) (n : ℕ) :
    (Matrix.of fun i j : Fin n => (F.eval (C ((j : ℕ) : ℤ))).eval ((i : ℕ) : ℤ)) =
      Matrix.vandermonde (fun i : Fin n => ((i : ℕ) : ℤ)) * redCoeff F n *
        (Matrix.vandermonde (fun i : Fin n => ((i : ℕ) : ℤ))).transpose := by
  ext i j
  rw [Matrix.of_apply, eval_eval_eq_sum_redCoeff, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.mul_apply, Matrix.transpose_apply, Matrix.vandermonde_apply]
  congr 1

/-- The Vandermonde determinant at `0, 1, …, n-1` is `sf(n-1) = ∏_{k<n} k!`
(also for `n = 0`, where both sides are `1`). -/
theorem det_vandermonde_natCast (n : ℕ) :
    (Matrix.vandermonde (fun i : Fin n => ((i : ℕ) : ℤ))).det =
      ((n - 1).superFactorial : ℤ) := by
  cases n with
  | zero => simp
  | succ m => simpa using Matrix.det_vandermonde_id_eq_superFactorial (R := ℤ) m

/-- **Superfactorial-squared bridge.** For every integer bivariate polynomial
`F(X,Y)` (here `F ∈ ℤ[X][Y]`, `X` the row variable) and every `n`, the determinant
of `[F(i,j)]_{0 ≤ i,j ≤ n-1}` is divisible by `sf(n-1)^2 = (∏_{k<n} k!)^2
= (∏_{0≤r<s≤n-1}(s-r))^2`.  This is the specialisation step behind
arXiv:2605.19486, Proposition 2.2 (equation (2.1)). -/
theorem superFactorial_sq_dvd_det_eval (n : ℕ) (F : ℤ[X][X]) :
    ((n - 1).superFactorial : ℤ) ^ 2 ∣
      (Matrix.of fun i j : Fin n => (F.eval (C ((j : ℕ) : ℤ))).eval ((i : ℕ) : ℤ)).det := by
  rw [evalMatrix_eq_vandermonde_mul_redCoeff_mul, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, det_vandermonde_natCast]
  exact ⟨(redCoeff F n).det, by ring⟩

/-! ## The composite consumer -/

/-- For `a < m`, the product `a! · m!` divides `sf(m) = ∏_{k ≤ m} k!`. -/
theorem factorial_mul_factorial_dvd_superFactorial {a m : ℕ} (ham : a < m) :
    a.factorial * m.factorial ∣ m.superFactorial := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hsf : a.factorial ∣ m'.superFactorial := by
    rw [← Nat.prod_range_succ_factorial]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr (by omega))
  rw [Nat.superFactorial_succ, mul_comm a.factorial]
  exact Nat.mul_dvd_mul (dvd_refl _) hsf

/-- Every composite `n ≥ 4` divides `sf(n-1) = ∏_{0≤r<s≤n-1}(s-r)`
(the claim `n ∣ V_n` in the proof of arXiv:2605.19486, Proposition 2.2). -/
theorem self_dvd_superFactorial_of_not_prime {n : ℕ} (h4 : 4 ≤ n) (hn : ¬ n.Prime) :
    n ∣ (n - 1).superFactorial := by
  set a := n.minFac with ha
  have ha2 : 2 ≤ a := (Nat.minFac_prime (by omega)).two_le
  have hsq : a ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hn
  obtain ⟨b, hb⟩ : a ∣ n := Nat.minFac_dvd n
  have hab : a ≤ b := by nlinarith
  have hb_lt : b < n := by nlinarith
  have h2a : 2 * a ≤ n := by nlinarith
  have ha_lt : a < n - 1 := by omega
  have hb_pos : 0 < b := by nlinarith
  calc n = a * b := hb
    _ ∣ a.factorial * (n - 1).factorial :=
        Nat.mul_dvd_mul (Nat.dvd_factorial (by omega) le_rfl)
          (Nat.dvd_factorial hb_pos (by omega))
    _ ∣ (n - 1).superFactorial := factorial_mul_factorial_dvd_superFactorial ha_lt

/-- **Proposition 2.2 of arXiv:2605.19486 (composite case of Sun's Conjecture 4.1,
strengthened).** For every composite integer `n > 3` and all `c, d ∈ ℤ`,
`D_n(c,d) = det[(i^2 + c i j + d j^2)^(n-2)]_{0 ≤ i,j ≤ n-1} ≡ 0 (mod n^2)`. -/
theorem sq_dvd_sunDet_of_not_prime {n : ℕ} (h4 : 4 ≤ n) (hn : ¬ n.Prime) (c d : ℤ) :
    (n : ℤ) ^ 2 ∣ sunDet n c d := by
  have hbridge := superFactorial_sq_dvd_det_eval n (sunPoly n c d)
  have hentry : (Matrix.of fun i j : Fin n =>
      ((sunPoly n c d).eval (C ((j : ℕ) : ℤ))).eval ((i : ℕ) : ℤ)) =
      Matrix.of fun i j : Fin n =>
        (((i : ℕ) : ℤ) ^ 2 + c * ((i : ℕ) : ℤ) * ((j : ℕ) : ℤ) + d * ((j : ℕ) : ℤ) ^ 2) ^
          (n - 2) := by
    ext i j
    simp only [sunPoly, Matrix.of_apply, eval_pow, eval_add, eval_mul, eval_C, eval_X]
  rw [hentry] at hbridge
  have hn_dvd : (n : ℤ) ∣ ((n - 1).superFactorial : ℤ) :=
    Int.natCast_dvd_natCast.mpr (self_dvd_superFactorial_of_not_prime h4 hn)
  exact (pow_dvd_pow_of_dvd hn_dvd 2).trans hbridge

/-- Non-vacuity: `n = 4` satisfies the hypotheses of `sq_dvd_sunDet_of_not_prime`. -/
example : 4 ≤ 4 ∧ ¬ (4 : ℕ).Prime := ⟨le_rfl, by decide⟩

end SunDeterminantSuperfactorialBridge
