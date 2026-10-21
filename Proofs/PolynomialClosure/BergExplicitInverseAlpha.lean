/-
# Berg's explicit inverse of `(1 / C(i+j+α, α))` and the only-if half of Richardson's
# Conjecture 4.1

## Sources

* arXiv:math/9905079, Thomas M. Richardson, "The Filbert Matrix" (Fibonacci Quart. 39
  (2001)).  §4 defines `b_k(r) = C(k+r-1, r)` and the reciprocal Hankel matrix
  `R_n(a_k) = (1 / a_{i+j-1})_{1 ≤ i,j ≤ n}` and states, verbatim:

  > **Conjecture.** Suppose that $r$ is a positive integer.  The inverse of the matrix
  > $R_n(b_k(r))$ has integer entries if and only if $n\equiv 0 \pmod q$ or
  > $n\equiv 1 \pmod q$ for all prime powers $q$ that divide $r$.

  (Equivalently `r ∣ n(n-1)`.)
* arXiv:math/0609283, Christian Berg, "Fibonacci numbers and orthogonal polynomials"
  (Arab J. Math. Sci. 17 (2011)), §4, Theorem `cbthm:binomalpha` and the display after it,
  verbatim:

  > Let $\a\in\mathbb N$. The inverse of the matrix
  > $\left(\frac{1}{\a\binom{\a+i+j}{\a}}\right)_0^n$ has integer entries.
  > [...] $r_n^{(\a)}(1-x)=\sum_{k=0}^n (-1)^{n-k}\tbinom{n}{k}\tbinom{\a+n+k-1}{k}x^k$,
  > and it follows that the entries of the inverse of (\ref{eq:hankelbinom}) are given as
  > $(-1)^{i+j}\sum_{k=\max(i,j)}^n (\a+2k)\tbinom{k}{i}\tbinom{k}{j}
  > \tbinom{\a+k+i-1}{i}\tbinom{\a+k+j-1}{j}$.  This formula holds of course for any $\a>0$.

Recorded 2026-10-21.

## Target (workflow key a8-12)

For `H = (1/C(i+j+α, α))_{0 ≤ i,j < N}` with `α ∈ ℕ`, `α > 0`:
(i) `H` is invertible with `H⁻¹ = E = (1/α) Lᵀ diag(α+2k) L`, `L_{k,m} = c_k(m)`;
(ii) `α E` has integer entries;
(iii) `E_00 = N + N(N-1)/α`, so integrality of `H⁻¹` forces `α ∣ N(N-1)`
(the only-if half of Richardson's Conjecture 4.1).

## Status

Known result: (i)–(ii) are proved by Berg (via shifted Jacobi polynomials); (iii) is an
immediate consequence.  The if-half of Richardson's conjecture is not addressed here.

## Proof route (fully algebraic; no integrals)

* Off-diagonal orthogonality `∑_m c_k(m)/C(m+l+α, α) = 0` (`l < k`): the summand is
  `(-1)^(k+m) C(k,m)` times a polynomial of degree `k-1` in `m`; Mathlib's
  `Polynomial.fwdDiff_iter_eq_zero_of_degree_lt`.
* Diagonal value: one polynomial division by `X + (k+α)` plus the partial-fraction identity
  `∑_m (-1)^(k+m) C(k,m)/(x+m) = (-1)^k k!/∏_{i ≤ k}(x+i)`, proved by iterated forward
  differences on `ℕ`.
* Matrix algebra: `L H Lᵀ = diag(α/(α+2k))` gives `(Lᵀ diag((α+2k)/α) L) H = 1` via
  `mul_eq_one_comm` (no separate invertibility of `L` is needed).
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.BergExplicitInverseAlpha

open Finset Polynomial

/-- The `k`-th alternating binomial sum `∑_{m ≤ k} (-1)^(k+m) C(k,m) P(m)` of a
rational polynomial `P` of degree `< k` vanishes. -/
theorem alt_sum_eval_eq_zero (P : ℚ[X]) (k : ℕ) (hP : P.natDegree < k) :
    ∑ m ∈ range (k + 1), (-1 : ℚ) ^ (k + m) * (k.choose m : ℚ) * P.eval (m : ℚ) = 0 := by
  have h := congrFun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hP) 0
  rw [fwdDiff_iter_eq_sum_shift] at h
  rw [Pi.zero_apply] at h
  rw [← h]
  refine sum_congr rfl fun m hm => ?_
  have hmk : m ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hm)
  simp only [zsmul_eq_mul, nsmul_eq_mul, mul_one, zero_add, Int.cast_mul, Int.cast_pow,
    Int.cast_neg, Int.cast_one, Int.cast_natCast]
  congr 2
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmk
  rw [Nat.add_sub_cancel_left, show m + d + m = d + 2 * m by ring, pow_add, pow_mul]
  simp

/-- Factorial bookkeeping for the off-diagonal summand:
`C(m+l+α+r, m) (α+l+r)! = C(m+l+α, α) α! (m+1)^(l) (m+l+α+1)^(r)` (rising factorials). -/
theorem choose_mul_factorial_eq (α l r m : ℕ) :
    (m + l + α + r).choose m * (α + l + r).factorial =
      (m + l + α).choose α * α.factorial * (m + 1).ascFactorial l *
        (m + l + α + 1).ascFactorial r := by
  apply Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos m)
  have h1 := Nat.add_choose_mul_factorial_mul_factorial (α + l + r) m
  have h2 := Nat.add_choose_mul_factorial_mul_factorial (m + l) α
  have h3 := Nat.factorial_mul_ascFactorial m l
  have h4 := Nat.factorial_mul_ascFactorial (m + l + α) r
  have e1 : α + l + r + m = m + l + α + r := by ring
  rw [e1] at h1
  calc (m + l + α + r).choose m * (α + l + r).factorial * m.factorial
      = (m + l + α + r).factorial := by rw [← h1]
    _ = (m + l + α).factorial * (m + l + α + 1).ascFactorial r := by rw [h4]
    _ = (m + l + α).choose α * α.factorial * (m + 1).ascFactorial l *
          (m + l + α + 1).ascFactorial r * m.factorial := by
        rw [← h2, ← h3]; ring

/-- Berg's coefficient `c_k(m) = (-1)^(k-m) C(k,m) C(α+k+m-1, m)`: the coefficient of `x^m` in
the shifted Jacobi polynomial `r_k^(α)(1-x)` (sign written as `(-1)^(k+m)`). -/
def c (α k m : ℕ) : ℤ := (-1) ^ (k + m) * (k.choose m : ℤ) * ((α + k + m - 1).choose m : ℤ)

/-- `(ascPochhammer ℚ n)(X + a)` evaluated at a natural number `m` is the rising factorial
`(m+a)(m+a+1)⋯(m+a+n-1)`. -/
theorem ascPochhammer_comp_eval (n a m : ℕ) :
    ((ascPochhammer ℚ n).comp (X + C (a : ℚ))).eval (m : ℚ) = ((m + a).ascFactorial n : ℚ) := by
  rw [eval_comp, eval_add, eval_X, eval_C, ← ascPochhammer_nat_eq_ascFactorial,
    ascPochhammer_eval_cast, Nat.cast_add]

/-- The product of two shifted Pochhammer polynomials of lengths `l` and `r` has degree
at most `l + r`. -/
theorem natDegree_offDiagPoly (a b l r : ℕ) :
    ((ascPochhammer ℚ l).comp (X + C (a : ℚ)) *
      (ascPochhammer ℚ r).comp (X + C (b : ℚ))).natDegree ≤ l + r := by
  refine (natDegree_mul_le).trans (add_le_add ?_ ?_) <;>
  · rw [natDegree_comp, ascPochhammer_natDegree, natDegree_X_add_C, mul_one]

/-- Orthogonality, off-diagonal part: for `l < k`,
`∑_{m ≤ k} c_k(m) / C(m+l+α, α) = 0`. -/
theorem sum_c_div_choose_eq_zero (α k l : ℕ) (hlk : l < k) :
    ∑ m ∈ range (k + 1), (c α k m : ℚ) / ((m + l + α).choose α : ℚ) = 0 := by
  obtain ⟨r, rfl⟩ : ∃ r, k = l + 1 + r := ⟨k - l - 1, by omega⟩
  set P : ℚ[X] := (ascPochhammer ℚ l).comp (X + C ((1 : ℕ) : ℚ)) *
      (ascPochhammer ℚ r).comp (X + C ((l + α + 1 : ℕ) : ℚ)) with hP
  have hdeg : P.natDegree < l + 1 + r := by
    rw [hP]
    exact (natDegree_offDiagPoly 1 (l + α + 1) l r).trans_lt (by omega)
  have hterm : ∀ m : ℕ, (c α (l + 1 + r) m : ℚ) / ((m + l + α).choose α : ℚ) =
      (-1 : ℚ) ^ (l + 1 + r + m) * ((l + 1 + r).choose m : ℚ) * P.eval (m : ℚ) *
        ((α.factorial : ℚ) / ((α + l + r).factorial : ℚ)) := by
    intro m
    have hidx : α + (l + 1 + r) + m - 1 = m + l + α + r := by omega
    have hnat := choose_mul_factorial_eq α l r m
    have hcast : ((m + l + α + r).choose m : ℚ) * ((α + l + r).factorial : ℚ) =
        ((m + l + α).choose α : ℚ) * (α.factorial : ℚ) * ((m + 1).ascFactorial l : ℚ) *
          ((m + l + α + 1).ascFactorial r : ℚ) := by exact_mod_cast hnat
    have hC : ((m + l + α).choose α : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (by omega)).ne'
    have hF : ((α + l + r).factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    rw [hP, eval_mul, ascPochhammer_comp_eval, ascPochhammer_comp_eval, c, hidx]
    push_cast
    have hbig : ((m + l + α + r).choose m : ℚ) =
        ((m + l + α).choose α : ℚ) * (α.factorial : ℚ) * ((m + 1).ascFactorial l : ℚ) *
          ((m + l + α + 1).ascFactorial r : ℚ) / ((α + l + r).factorial : ℚ) := by
      rw [eq_div_iff hF]; exact hcast
    rw [hbig, show m + (l + α + 1) = m + l + α + 1 by ring]
    field_simp
  simp_rw [hterm]
  rw [← sum_mul, alt_sum_eval_eq_zero P _ hdeg, zero_mul]

open fwdDiff

/-- Forward difference of `y ↦ 1 / ∏_{i<n} (x+y+i)` on `ℕ` (for `x > 0`):
it equals `-n / ∏_{i<n+1} (x+y+i)`. -/
theorem fwdDiff_recipProd (x : ℚ) (hx : 0 < x) (n : ℕ) :
    Δ_[1] (fun y : ℕ => (∏ i ∈ range n, (x + y + i))⁻¹) =
      (-(n : ℚ)) • fun y : ℕ => (∏ i ∈ range (n + 1), (x + y + i))⁻¹ := by
  funext y
  have hpos : ∀ i : ℕ, 0 < x + (y : ℚ) + i := fun i => by positivity
  set A := ∏ i ∈ range n, (x + (y : ℚ) + i) with hA
  set B := ∏ i ∈ range n, (x + ((y + 1 : ℕ) : ℚ) + i) with hB
  have hA0 : A ≠ 0 := (prod_pos fun i _ => hpos i).ne'
  have hB0 : B ≠ 0 := (prod_pos fun i _ => by positivity).ne'
  have hD1 : ∏ i ∈ range (n + 1), (x + (y : ℚ) + i) = A * (x + y + n) := prod_range_succ _ _
  have hD2 : ∏ i ∈ range (n + 1), (x + (y : ℚ) + i) = B * (x + y) := by
    rw [prod_range_succ', hB]
    congr 1
    · refine prod_congr rfl fun i _ => ?_
      push_cast; ring
    · simp
  have hxy : x + (y : ℚ) ≠ 0 := by
    have h0 := hpos 0
    rw [Nat.cast_zero, add_zero] at h0
    exact h0.ne'
  have hxyn : x + (y : ℚ) + n ≠ 0 := (hpos n).ne'
  simp only [fwdDiff, Pi.smul_apply, smul_eq_mul]
  rw [← hA, ← hB]
  have hAB : A * (x + y + n) = B * (x + y) := hD1.symm.trans hD2
  rw [hD1]
  field_simp
  linear_combination hAB

/-- Iterated forward differences on `ℕ → ℚ` commute with scalar multiplication. -/
theorem fwdDiff_iter_const_smul' (r : ℚ) (f : ℕ → ℚ) (k : ℕ) :
    (fwdDiff (1 : ℕ))^[k] (r • f) = r • (fwdDiff (1 : ℕ))^[k] f := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      fwdDiff_const_smul]

/-- The `k`-th forward difference of `y ↦ 1 / ∏_{i<n} (x+y+i)` is
`(-1)^k n^(k) / ∏_{i<n+k} (x+y+i)` (rising factorial `n^(k)`). -/
theorem fwdDiff_iter_recipProd (x : ℚ) (hx : 0 < x) (k n : ℕ) :
    (fwdDiff (1 : ℕ))^[k] (fun y : ℕ => (∏ i ∈ range n, (x + y + i))⁻¹) =
      ((-1 : ℚ) ^ k * (n.ascFactorial k : ℚ)) •
        fun y : ℕ => (∏ i ∈ range (n + k), (x + y + i))⁻¹ := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, fwdDiff_recipProd x hx, fwdDiff_iter_const_smul', ih,
      smul_smul, show n + 1 + k = n + (k + 1) by ring]
    congr 1
    have h := Nat.succ_ascFactorial n k
    rw [Nat.ascFactorial_succ, ← h]
    push_cast
    ring

/-- Partial-fraction identity: for `x > 0`,
`∑_{m ≤ k} (-1)^(k+m) C(k,m) / (x+m) = (-1)^k k! / ∏_{i ≤ k} (x+i)`. -/
theorem sum_alt_choose_div (x : ℚ) (hx : 0 < x) (k : ℕ) :
    ∑ m ∈ range (k + 1), (-1 : ℚ) ^ (k + m) * (k.choose m : ℚ) / (x + m) =
      (-1 : ℚ) ^ k * (k.factorial : ℚ) / ∏ i ∈ range (k + 1), (x + i) := by
  have h := congrFun (fwdDiff_iter_recipProd x hx k 1) 0
  rw [fwdDiff_iter_eq_sum_shift] at h
  simp only [Pi.smul_apply, smul_eq_mul, Nat.one_ascFactorial, Nat.cast_zero, add_zero,
    zero_add, mul_one, prod_range_one] at h
  rw [show 1 + k = k + 1 by ring] at h
  rw [div_eq_mul_inv, ← h]
  refine sum_congr rfl fun m hm => ?_
  have hmk : m ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hm)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmk
  rw [Nat.add_sub_cancel_left, show m + d + m = d + 2 * m by ring, pow_add, pow_mul]
  simp [div_eq_mul_inv]

/-- Factorial bookkeeping for the diagonal summand (`α = a+1`, `l = k`):
`C(m+k+a, m) (k+a)! (m+k+a+1) = C(m+k+a+1, a+1) (a+1)! (m+1)^(k)`. -/
theorem choose_mul_factorial_diag (a k m : ℕ) :
    (m + k + a).choose m * (k + a).factorial * (m + k + a + 1) =
      (m + k + (a + 1)).choose (a + 1) * (a + 1).factorial * (m + 1).ascFactorial k := by
  apply Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos m)
  have h1 := Nat.add_choose_mul_factorial_mul_factorial (k + a) m
  have h2 := Nat.add_choose_mul_factorial_mul_factorial (m + k) (a + 1)
  have h3 := Nat.factorial_mul_ascFactorial m k
  rw [show k + a + m = m + k + a by ring] at h1
  rw [show m + k + (a + 1) = m + k + a + 1 by ring] at h2 ⊢
  calc (m + k + a).choose m * (k + a).factorial * (m + k + a + 1) * m.factorial
      = (m + k + a + 1) * (m + k + a).factorial := by rw [← h1]; ring
    _ = (m + k + a + 1).factorial := (Nat.factorial_succ _).symm
    _ = (m + k + a + 1).choose (a + 1) * (a + 1).factorial * (m + 1).ascFactorial k *
          m.factorial := by
        rw [← h2, ← h3]; ring

/-- Orthogonality, diagonal part (`α = a+1`):
`(∑_{m ≤ k} c_k(m) / C(m+k+α, α)) · c_k(k) = α / (α + 2k)`. -/
theorem sum_c_div_choose_diag (a k : ℕ) :
    (∑ m ∈ range (k + 1), (c (a + 1) k m : ℚ) / ((m + k + (a + 1)).choose (a + 1) : ℚ)) *
        (c (a + 1) k k : ℚ) = ((a + 1 : ℕ) : ℚ) / ((a + 1 + 2 * k : ℕ) : ℚ) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [div_self (by positivity)]
    simp [c]
  set x : ℚ := ((k + a + 1 : ℕ) : ℚ) with hx
  have hx0 : 0 < x := by rw [hx]; positivity
  set R : ℚ[X] := (ascPochhammer ℚ k).comp (X + C ((1 : ℕ) : ℚ)) with hR
  set Q : ℚ[X] := R /ₘ (X - C (-x)) with hQ
  have hRQ : ∀ y : ℚ, R.eval y = R.eval (-x) + (y + x) * Q.eval y := by
    intro y
    have h := modByMonic_add_div R (X - C (-x))
    rw [modByMonic_X_sub_C_eq_C_eval, ← hQ] at h
    conv_lhs => rw [← h]
    rw [eval_add, eval_C, eval_mul, eval_sub, eval_X, eval_C, sub_neg_eq_add]
  have hQdeg : Q.natDegree < k := by
    rw [hQ, natDegree_divByMonic _ (monic_X_sub_C _), natDegree_X_sub_C, hR, natDegree_comp,
      ascPochhammer_natDegree, natDegree_X_add_C]
    omega
  set K : ℚ := ((a + 1).factorial : ℚ) / ((k + a).factorial : ℚ) with hK
  have hterm : ∀ m ∈ range (k + 1),
      (c (a + 1) k m : ℚ) / ((m + k + (a + 1)).choose (a + 1) : ℚ) =
        K * ((-1 : ℚ) ^ (k + m) * (k.choose m : ℚ) * Q.eval (m : ℚ)) +
          K * R.eval (-x) * ((-1 : ℚ) ^ (k + m) * (k.choose m : ℚ) / (x + m)) := by
    intro m _
    have hnat := choose_mul_factorial_diag a k m
    rw [show m + k + (a + 1) = m + k + a + 1 by ring] at hnat ⊢
    have hnatQ : ((m + k + a).choose m : ℚ) * ((k + a).factorial : ℚ) * ((m + k + a + 1 : ℕ) : ℚ) =
        ((m + k + a + 1).choose (a + 1) : ℚ) * ((a + 1).factorial : ℚ) *
          ((m + 1).ascFactorial k : ℚ) := by exact_mod_cast hnat
    have hcast : ((m + k + a).choose m : ℚ) * ((k + a).factorial : ℚ) * ((m : ℚ) + x) =
        ((m + k + a + 1).choose (a + 1) : ℚ) * ((a + 1).factorial : ℚ) *
          ((m + 1).ascFactorial k : ℚ) := by
      rw [hx]; push_cast at hnatQ ⊢; linear_combination hnatQ
    have hRm := hRQ (m : ℚ)
    rw [hR, ascPochhammer_comp_eval] at hRm
    rw [← hR] at hRm
    have hC : ((m + k + a + 1).choose (a + 1) : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (by omega)).ne'
    have hF : ((k + a).factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    have hmx : (m : ℚ) + x ≠ 0 := by positivity
    have hidx : a + 1 + k + m - 1 = m + k + a := by omega
    rw [c, hidx, hK]
    push_cast
    rw [div_eq_iff hC]
    field_simp
    linear_combination (k.choose m : ℚ) * (hcast + ((m + k + a + 1).choose (a + 1) : ℚ) *
      ((a + 1).factorial : ℚ) * hRm)
  rw [sum_congr rfl hterm, sum_add_distrib, ← mul_sum, ← mul_sum, alt_sum_eval_eq_zero Q k hQdeg,
    mul_zero, zero_add, sum_alt_choose_div x hx0 k]
  have hRx : R.eval (-x) = (-1 : ℚ) ^ k * ((k + a).descFactorial k : ℚ) := by
    rw [hR, eval_comp, eval_add, eval_X, eval_C,
      show -x + ((1 : ℕ) : ℚ) = -((k + a : ℕ) : ℚ) by rw [hx]; push_cast; ring,
      ascPochhammer_eval_neg_eq_descPochhammer, descPochhammer_eval_eq_descFactorial]
  have hprod : ∏ i ∈ range (k + 1), (x + i) = ((k + a + 1).ascFactorial (k + 1) : ℚ) := by
    rw [Nat.ascFactorial_eq_prod_range, hx]
    push_cast
    rfl
  have hcc : (c (a + 1) k k : ℚ) = ((k + a + k).choose k : ℚ) := by
    rw [c, show a + 1 + k + k - 1 = k + a + k by omega, Nat.choose_self, ← two_mul, pow_mul]
    norm_num
  have f1 := Nat.factorial_mul_descFactorial (show k ≤ k + a by omega)
  rw [show k + a - k = a by omega] at f1
  have f2 := Nat.factorial_mul_ascFactorial (k + a) (k + 1)
  have f3 := Nat.add_choose_mul_factorial_mul_factorial (k + a) k
  have f4 : (k + a + (k + 1)).factorial = (k + a + k + 1) * (k + a + k).factorial :=
    Nat.factorial_succ _
  have f5 : (a + 1).factorial = (a + 1) * a.factorial := Nat.factorial_succ _
  have hFa : (a.factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hFka : ((k + a).factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hFk : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hF2 : ((k + a + k).factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hdF : ((k + a).descFactorial k : ℚ) = ((k + a).factorial : ℚ) / (a.factorial : ℚ) := by
    rw [eq_div_iff hFa, mul_comm]; exact_mod_cast f1
  have hAF : ((k + a + 1).ascFactorial (k + 1) : ℚ) =
      ((k + a + k + 1 : ℕ) : ℚ) * ((k + a + k).factorial : ℚ) / ((k + a).factorial : ℚ) := by
    rw [eq_div_iff hFka, mul_comm]; exact_mod_cast f2.trans f4
  have hCk : ((k + a + k).choose k : ℚ) =
      ((k + a + k).factorial : ℚ) / (((k + a).factorial : ℚ) * (k.factorial : ℚ)) := by
    rw [eq_div_iff (mul_ne_zero hFka hFk), ← mul_assoc]; exact_mod_cast f3
  have hFa1 : ((a + 1).factorial : ℚ) = ((a + 1 : ℕ) : ℚ) * (a.factorial : ℚ) := by
    exact_mod_cast f5
  have hsign : (-1 : ℚ) ^ k * (-1 : ℚ) ^ k = 1 := by rw [← mul_pow]; norm_num
  rw [hRx, hprod, hcc, hdF, hAF, hCk, hK, hFa1]
  have hden : ((a + 1 + 2 * k : ℕ) : ℚ) ≠ 0 := by positivity
  have hden' : ((k + a + k + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  rw [show ((k + a + k + 1 : ℕ) : ℚ) = ((a + 1 + 2 * k : ℕ) : ℚ) by push_cast; ring]
  field_simp
  linear_combination hsign

/-- The reciprocal binomial Hankel matrix `H = (1 / C(i+j+α, α))_{0 ≤ i,j < N}`; for `α = r`
this is Richardson's `R_N(b_k(r))`, `b_k(r) = C(k+r-1, r)`, reindexed from `0`. -/
def recipBinomHankel (α N : ℕ) : Matrix (Fin N) (Fin N) ℚ :=
  Matrix.of fun i j => 1 / (((i : ℕ) + (j : ℕ) + α).choose α : ℚ)

/-- Berg's explicit inverse `E_{ij} = (1/α) ∑_{k<N} (α+2k) c_k(i) c_k(j)`. -/
def bergInv (α N : ℕ) : Matrix (Fin N) (Fin N) ℚ :=
  Matrix.of fun i j =>
    (1 / (α : ℚ)) * ∑ k ∈ range N, ((α : ℚ) + 2 * k) * (c α k i : ℚ) * (c α k j : ℚ)

/-- The lower-triangular coefficient matrix `L_{k,m} = c_k(m)`. -/
def cMatrix (α N : ℕ) : Matrix (Fin N) (Fin N) ℚ := Matrix.of fun k m => (c α k m : ℚ)

/-- `c_k(m) = 0` for `m > k`, so `L` is lower triangular. -/
theorem c_eq_zero_of_lt (α k m : ℕ) (h : k < m) : c α k m = 0 := by
  simp [c, Nat.choose_eq_zero_of_lt h]

/-- The column sum `(L H)_{k,l} = ∑_{m ≤ k} c_k(m) / C(m+l+α, α)`. -/
def colSum (α k l : ℕ) : ℚ := ∑ m ∈ range (k + 1), (c α k m : ℚ) / ((m + l + α).choose α : ℚ)

/-- Entries of `L H` are the column sums `colSum α k l`. -/
theorem cMatrix_mul_apply (α N : ℕ) (k l : Fin N) :
    (cMatrix α N * recipBinomHankel α N) k l = colSum α k l := by
  rw [Matrix.mul_apply, colSum]
  simp only [cMatrix, recipBinomHankel, Matrix.of_apply, mul_one_div]
  rw [Fin.sum_univ_eq_sum_range (fun m => (c α k m : ℚ) / ((m + l + α).choose α : ℚ)) N]
  symm
  refine sum_subset (fun m hm => ?_) (fun m _ hm => ?_)
  · simp only [mem_range] at hm ⊢; omega
  · simp only [mem_range, not_lt] at hm
    rw [c_eq_zero_of_lt α k m (by omega)]
    simp

/-- Entries of `L H Lᵀ` as a single sum over `l < N`. -/
theorem triple_apply (α N : ℕ) (k k' : Fin N) :
    (cMatrix α N * recipBinomHankel α N * (cMatrix α N).transpose) k k' =
      ∑ l ∈ range N, colSum α k l * (c α k' l : ℚ) := by
  rw [Matrix.mul_apply]
  simp_rw [cMatrix_mul_apply]
  simp only [Matrix.transpose_apply, cMatrix, Matrix.of_apply]
  exact Fin.sum_univ_eq_sum_range (fun l => colSum α k l * (c α k' l : ℚ)) N

/-- `L H Lᵀ` vanishes strictly below the diagonal. -/
theorem triple_apply_of_lt (α N : ℕ) (k k' : Fin N) (h : (k' : ℕ) < k) :
    (cMatrix α N * recipBinomHankel α N * (cMatrix α N).transpose) k k' = 0 := by
  rw [triple_apply]
  refine sum_eq_zero fun l _ => ?_
  rcases le_or_gt l k' with hl | hl
  · rw [colSum, sum_c_div_choose_eq_zero α k l (by omega), zero_mul]
  · rw [c_eq_zero_of_lt α k' l hl]; simp

/-- `L H Lᵀ` is symmetric because `H` is. -/
theorem triple_symm (α N : ℕ) :
    (cMatrix α N * recipBinomHankel α N * (cMatrix α N).transpose).transpose =
      cMatrix α N * recipBinomHankel α N * (cMatrix α N).transpose := by
  have hH : (recipBinomHankel α N).transpose = recipBinomHankel α N := by
    ext i j
    simp only [recipBinomHankel, Matrix.transpose_apply, Matrix.of_apply, add_comm (j : ℕ)]
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hH,
    Matrix.mul_assoc]

/-- Orthogonality relations: `L H Lᵀ = diag(α / (α + 2k))` for `α > 0`. -/
theorem triple_eq_diagonal (α N : ℕ) (hα : 0 < α) :
    cMatrix α N * recipBinomHankel α N * (cMatrix α N).transpose =
      Matrix.diagonal fun k : Fin N => (α : ℚ) / ((α : ℚ) + 2 * (k : ℕ)) := by
  obtain ⟨a, rfl⟩ : ∃ a, α = a + 1 := ⟨α - 1, by omega⟩
  ext k k'
  rcases lt_trichotomy (k' : ℕ) k with h | h | h
  · rw [triple_apply_of_lt _ _ _ _ h, Matrix.diagonal_apply_ne _ (Fin.ne_of_lt h).symm]
  · have hkk : k = k' := Fin.ext h.symm
    subst hkk
    rw [triple_apply, Matrix.diagonal_apply_eq,
      sum_eq_single (k : ℕ) (fun l _ hl => ?_) (fun hk => absurd (mem_range.mpr k.isLt) hk)]
    · have := sum_c_div_choose_diag a k
      rw [colSum, this]
      push_cast; ring
    · rcases lt_or_gt_of_ne hl with hl | hl
      · rw [colSum, sum_c_div_choose_eq_zero _ k l hl, zero_mul]
      · rw [c_eq_zero_of_lt _ k l hl]; simp
  · rw [← triple_symm, Matrix.transpose_apply, triple_apply_of_lt _ _ _ _ h,
      Matrix.diagonal_apply_ne _ (Fin.ne_of_lt h)]

/-- Berg's inverse factors as `E = Lᵀ diag((α+2k)/α) L`. -/
theorem bergInv_eq_factor (α N : ℕ) :
    bergInv α N = (cMatrix α N).transpose *
      Matrix.diagonal (fun k : Fin N => ((α : ℚ) + 2 * (k : ℕ)) / α) * cMatrix α N := by
  ext i j
  rw [Matrix.mul_apply, bergInv, Matrix.of_apply, mul_sum]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, cMatrix, Matrix.of_apply]
  rw [← Fin.sum_univ_eq_sum_range (fun k => 1 / (α : ℚ) * (((α : ℚ) + 2 * k) *
    (c α k i : ℚ) * (c α k j : ℚ))) N]
  refine sum_congr rfl fun k _ => ?_
  ring

/-- (i) Berg's formula is a left inverse: `E H = 1` for `α > 0`. -/
theorem bergInv_mul_recipBinomHankel (α N : ℕ) (hα : 0 < α) :
    bergInv α N * recipBinomHankel α N = 1 := by
  set L := cMatrix α N
  set H := recipBinomHankel α N
  set D' := Matrix.diagonal (fun k : Fin N => ((α : ℚ) + 2 * (k : ℕ)) / α)
  have hD : D' * (L * H * L.transpose) = 1 := by
    rw [triple_eq_diagonal α N hα, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext k
    have h1 : (α : ℚ) ≠ 0 := by exact_mod_cast hα.ne'
    have h2 : (α : ℚ) + 2 * (k : ℕ) ≠ 0 := by positivity
    field_simp
  have h3 : (D' * L * H) * L.transpose = 1 := by
    rw [← hD]; simp only [Matrix.mul_assoc]
  have h4 : L.transpose * (D' * L * H) = 1 := mul_eq_one_comm.mp h3
  rw [bergInv_eq_factor, ← h4]
  simp only [Matrix.mul_assoc]
  rfl

/-- (i) Berg's formula is a right inverse: `H E = 1` for `α > 0`. -/
theorem recipBinomHankel_mul_bergInv (α N : ℕ) (hα : 0 < α) :
    recipBinomHankel α N * bergInv α N = 1 :=
  mul_eq_one_comm.mp (bergInv_mul_recipBinomHankel α N hα)

/-- (i) **Berg's explicit inverse** (Berg, arXiv math/0609283 §4): for `α > 0`,
`H⁻¹ = (1/α) Lᵀ diag(α+2k) L`, i.e. `H⁻¹_{ij} = (1/α) ∑_{k<N} (α+2k) c_k(i) c_k(j)`. -/
theorem recipBinomHankel_inv (α N : ℕ) (hα : 0 < α) :
    (recipBinomHankel α N)⁻¹ = bergInv α N :=
  Matrix.inv_eq_left_inv (bergInv_mul_recipBinomHankel α N hα)

/-- (i) `H` is invertible: its determinant is nonzero for `α > 0`. -/
theorem recipBinomHankel_det_ne_zero (α N : ℕ) (hα : 0 < α) :
    (recipBinomHankel α N).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (recipBinomHankel_mul_bergInv α N hα)
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

/-- (ii) `α H⁻¹` has integer entries (Berg, arXiv math/0609283, Theorem `cbthm:binomalpha`). -/
theorem alpha_mul_inv_integral (α N : ℕ) (hα : 0 < α) (i j : Fin N) :
    ∃ z : ℤ, (α : ℚ) * (recipBinomHankel α N)⁻¹ i j = z := by
  refine ⟨∑ k ∈ range N, ((α : ℤ) + 2 * k) * c α k i * c α k j, ?_⟩
  have h1 : (α : ℚ) ≠ 0 := by exact_mod_cast hα.ne'
  rw [recipBinomHankel_inv α N hα, bergInv, Matrix.of_apply, ← mul_assoc, mul_one_div_cancel h1,
    one_mul]
  push_cast
  rfl

/-- `c_k(0) = (-1)^k`. -/
theorem c_zero (α k : ℕ) : c α k 0 = (-1) ^ k := by simp [c]

/-- `∑_{k<N} (α + 2k) = Nα + N(N-1)`. -/
theorem sum_range_alpha_add_two_mul (α N : ℕ) :
    ∑ k ∈ range N, ((α : ℚ) + 2 * k) = N * α + N * ((N : ℚ) - 1) := by
  induction N with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

/-- (iii) The corner entry of the inverse: `H⁻¹_{00} = N + N(N-1)/α` for `α > 0`, `N > 0`. -/
theorem recipBinomHankel_inv_zero_zero (α N : ℕ) (hα : 0 < α) (hN : 0 < N) :
    (recipBinomHankel α N)⁻¹ ⟨0, hN⟩ ⟨0, hN⟩ = N + (N : ℚ) * ((N : ℚ) - 1) / α := by
  have h1 : (α : ℚ) ≠ 0 := by exact_mod_cast hα.ne'
  rw [recipBinomHankel_inv α N hα, bergInv, Matrix.of_apply]
  simp only [c_zero]
  have hsq : ∀ k : ℕ, ((α : ℚ) + 2 * k) * (((-1 : ℤ) ^ k : ℤ) : ℚ) * (((-1 : ℤ) ^ k : ℤ) : ℚ) =
      (α : ℚ) + 2 * k := by
    intro k; push_cast; rw [mul_assoc, ← mul_pow]; norm_num
  simp only [hsq, sum_range_alpha_add_two_mul]
  field_simp

/-- (iii) **Only-if half of Richardson's Conjecture 4.1** (arXiv math/9905079): if
`H⁻¹ = R_N(b_k(α))⁻¹` has integer entries then `α ∣ N(N-1)`, i.e. `N ≡ 0` or `1 (mod q)` for
every prime power `q ∣ α`. -/
theorem richardson_conj41_onlyIf (α N : ℕ) (hα : 0 < α)
    (h : ∀ i j : Fin N, ∃ z : ℤ, (recipBinomHankel α N)⁻¹ i j = z) :
    (α : ℤ) ∣ (N : ℤ) * ((N : ℤ) - 1) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  obtain ⟨z, hz⟩ := h ⟨0, hN⟩ ⟨0, hN⟩
  rw [recipBinomHankel_inv_zero_zero α N hα hN] at hz
  have h1 : (α : ℚ) ≠ 0 := by exact_mod_cast hα.ne'
  refine ⟨z - N, ?_⟩
  have hq : ((N : ℤ) * ((N : ℤ) - 1) : ℚ) = ((α * (z - N) : ℤ) : ℚ) := by
    push_cast
    rw [← hz]
    field_simp
    ring
  exact_mod_cast hq

/-- The `N × N` Hilbert matrix `(1 / (i + j + 1))_{0 ≤ i,j < N}`. -/
def hilbertMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℚ :=
  Matrix.of fun i j => 1 / ((i : ℚ) + (j : ℚ) + 1)

/-- The Hilbert matrix is the case `α = 1` of `recipBinomHankel`. -/
theorem hilbertMatrix_eq (N : ℕ) : hilbertMatrix N = recipBinomHankel 1 N := by
  ext i j
  simp [hilbertMatrix, recipBinomHankel]

/-- Corollary (`α = 1`, Choi): the inverse of the Hilbert matrix has integer entries. -/
theorem hilbertMatrix_inv_integral (N : ℕ) (i j : Fin N) :
    ∃ z : ℤ, (hilbertMatrix N)⁻¹ i j = z := by
  obtain ⟨z, hz⟩ := alpha_mul_inv_integral 1 N one_pos i j
  exact ⟨z, by rw [hilbertMatrix_eq, ← hz, Nat.cast_one, one_mul]⟩

/-! ## Ground truth on small instances -/

example : c 1 1 0 = -1 := by decide
example : c 1 1 1 = 2 := by decide
example : c 2 2 1 = -8 := by decide
example : c 2 1 1 = 3 := by decide

example : recipBinomHankel 2 2 0 1 = 1 / 3 := by
  norm_num [recipBinomHankel, Nat.choose]
example : recipBinomHankel 2 2 1 1 = 1 / 6 := by
  norm_num [recipBinomHankel, Nat.choose]

/-- `α = 2`, `N = 2`: `H = [[1, 1/3], [1/3, 1/6]]` and `H⁻¹ = [[3, -6], [-6, 18]]`. -/
example : bergInv 2 2 0 0 = 3 ∧ bergInv 2 2 0 1 = -6 ∧ bergInv 2 2 1 1 = 18 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [bergInv, c, sum_range_succ, Nat.choose]

/-- Non-vacuity of the integrality hypothesis of `richardson_conj41_onlyIf`: for `α = N = 2`
the inverse is integral. -/
example : ∀ i j : Fin 2, ∃ z : ℤ, (recipBinomHankel 2 2)⁻¹ i j = z := by
  intro i j
  rw [recipBinomHankel_inv 2 2 two_pos]
  fin_cases i <;> fin_cases j
  · exact ⟨3, by norm_num [bergInv, c, sum_range_succ, Nat.choose]⟩
  · exact ⟨-6, by norm_num [bergInv, c, sum_range_succ, Nat.choose]⟩
  · exact ⟨-6, by norm_num [bergInv, c, sum_range_succ, Nat.choose]⟩
  · exact ⟨18, by norm_num [bergInv, c, sum_range_succ, Nat.choose]⟩

/-- The contrapositive in action: for `α = 4`, `N = 3` (`4 ∤ 6`) the inverse is not integral. -/
example : ¬ ∀ i j : Fin 3, ∃ z : ℤ, (recipBinomHankel 4 3)⁻¹ i j = z := by
  intro h
  have := richardson_conj41_onlyIf 4 3 (by norm_num) h
  norm_num at this

end Candidates.BergExplicitInverseAlpha
