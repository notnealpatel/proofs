/-
# Rosinger, "Synthesizing Sums", Open Problem 2 (answered: no)

Elemér E. Rosinger, *Synthesizing Sums*, arXiv:math/0702605, §2,
Open Problem 2, equation (2.7).

Definitions in the paper (`ℕ₊ = {1, 2, 3, ...}`):

* (2.1)–(2.2) `PF_ℤ` is the set of all `f : ℕ₊ → ℕ₊` with `f(n) = p(n, n!)`,
  `n ∈ ℕ₊`, for a two-variable polynomial `p` with coefficients in `ℤ`;
* (2.3)–(2.4) `PF_ℚ` is the same with `q(x, y)` with coefficients in `ℚ`;
* (2.5)–(2.6) `SPF_ℤ` is the set of `f ∈ PF_ℤ` such that
  `∃ g ∈ PF_ℚ, ∀ n ∈ ℕ₊, f(1) + f(2) + ... + f(n) = g(n)`.

The answer is negative: `n ↦ n!` belongs to `PF_ℤ` but not `SPF_ℤ`, so
`SPF_ℤ ⊊ PF_ℤ`.

Proof outline.

1. (`eq_zero_of_eventually_evalEval_factorial`) `n` and `n!` are algebraically
   independent as sequences: if `P ∈ ℚ[x][y]` and `P(n, n!) = 0` for all large
   `n`, then `P = 0`.  Divide by `(n!)^m`, `m = deg_y P`: the leading
   coefficient `P_m(n)` tends to `0` because `poly(n) / n! → 0`; a nonzero
   polynomial does not tend to `0` along the naturals.
2. If `∑_{k=1}^n k! = q(n, n!)`, then `P(x, y) = q(x+1, (x+1) y) - q(x, y) - (x+1) y`
   vanishes at `(n, n!)` for `n ≥ 1`, hence `P = 0`.  Its `y¹`-coefficient
   gives `(x + 1) Q₁(x + 1) - Q₁(x) = x + 1`, impossible by degrees
   (`shift_mul_sub_ne`).

Convention: `Polynomial.evalEval x y p` evaluates the inner variable (`C X`)
at `x` and the outer variable (`X`) at `y`; so `p.evalEval n n!` is the
paper's `p(n, n!)` with `x` the inner and `y` the outer variable.
-/
import Mathlib

set_option autoImplicit false

open Polynomial Filter Topology

namespace Candidates.RosingerSumFactorialNotPolynomial

/-! ## Analytic part: `n` and `n!` are algebraically independent -/

/-- A real polynomial divided by `n!` tends to `0` along the naturals. -/
theorem tendsto_eval_div_factorial (f : ℝ[X]) :
    Tendsto (fun n : ℕ => f.eval (n : ℝ) / (n.factorial : ℝ)) atTop (𝓝 0) := by
  have hterm : ∀ i : ℕ, Tendsto (fun n : ℕ => f.coeff i * ((n : ℝ) ^ i / (n.factorial : ℝ)))
      atTop (𝓝 0) := by
    intro i
    have h1 := tendsto_pow_const_div_const_pow_of_one_lt i (r := 2) (by norm_num)
    have h2 := FloorSemiring.tendsto_pow_div_factorial_atTop (2 : ℝ)
    have h3 := (h1.mul h2).const_mul (f.coeff i)
    rw [mul_zero, mul_zero] at h3
    refine h3.congr' (Eventually.of_forall fun n => ?_)
    have hf : (n.factorial : ℝ) ≠ 0 := by positivity
    have h2n : (2 : ℝ) ^ n ≠ 0 := by positivity
    field_simp
  have hsum := tendsto_finsetSum (Finset.range (f.natDegree + 1)) (fun i _ => hterm i)
  rw [Finset.sum_const_zero] at hsum
  refine hsum.congr' (Eventually.of_forall fun n => ?_)
  simp only [eval_eq_sum_range, Finset.sum_div, mul_div_assoc]

/-- A real polynomial whose values at the naturals tend to `0` is zero. -/
theorem eq_zero_of_tendsto_eval_natCast (L : ℝ[X])
    (h : Tendsto (fun n : ℕ => L.eval (n : ℝ)) atTop (𝓝 0)) : L = 0 := by
  by_cases hdeg : 0 < L.degree
  · exfalso
    have habs : Tendsto (fun n : ℕ => |L.eval (n : ℝ)|) atTop atTop :=
      Polynomial.tendsto_abv_atTop (abv := abs) L hdeg (z := fun n : ℕ => (n : ℝ))
        (by simpa [Function.comp_def] using tendsto_natCast_atTop_atTop)
    have h0 : Tendsto (fun n : ℕ => |L.eval (n : ℝ)|) atTop (𝓝 0) := by
      simpa using h.abs
    exact not_tendsto_nhds_of_tendsto_atTop habs 0 h0
  · rw [not_lt] at hdeg
    rw [eq_C_of_degree_le_zero hdeg] at h ⊢
    simp only [eval_C] at h
    rw [tendsto_const_nhds_iff] at h
    rw [h, C_0]


/-- Expansion of `P(x, y) = ∑_j P_j(x) y^j` along the outer variable `y`. -/
theorem evalEval_eq_sum_range {R : Type*} [CommSemiring R] (P : R[X][X]) (x y : R) :
    P.evalEval x y = ∑ j ∈ Finset.range (P.natDegree + 1), (P.coeff j).eval x * y ^ j := by
  rw [evalEval, eval_eq_sum_range (p := P) (x := C y), eval_finsetSum]
  simp only [eval_mul, eval_pow, eval_C]

/-- Over `ℝ`: `n` and `n!` are algebraically independent as sequences: if
`P(n, n!) = 0` for all large `n`, then `P = 0`. -/
theorem eq_zero_of_eventually_evalEval_factorial_real (P : ℝ[X][X])
    (h : ∀ᶠ n : ℕ in atTop, P.evalEval (n : ℝ) (n.factorial : ℝ) = 0) : P = 0 := by
  by_contra hP
  set m := P.natDegree with hm
  have hL : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP
  -- each lower term, divided by `n! ^ m`, tends to `0`
  have hterm : ∀ j ∈ Finset.range m, Tendsto
      (fun n : ℕ => (P.coeff j).eval (n : ℝ) * (n.factorial : ℝ) ^ j / (n.factorial : ℝ) ^ m)
      atTop (𝓝 0) := by
    intro j hj
    obtain ⟨k, hk⟩ : ∃ k, m = j + k + 1 := ⟨m - j - 1, by rw [Finset.mem_range] at hj; omega⟩
    have hinv : Tendsto (fun n : ℕ => ((n.factorial : ℝ))⁻¹) atTop (𝓝 0) := by
      have := tendsto_eval_div_factorial 1
      simpa using this
    have h3 := (tendsto_eval_div_factorial (P.coeff j)).mul (hinv.pow k)
    rw [zero_mul] at h3
    refine h3.congr' (Eventually.of_forall fun n => ?_)
    have hf : (n.factorial : ℝ) ≠ 0 := by positivity
    rw [hk, inv_pow]
    field_simp
    ring
  have hsum := tendsto_finsetSum (Finset.range m) hterm
  rw [Finset.sum_const_zero] at hsum
  have hlead : Tendsto (fun n : ℕ => P.leadingCoeff.eval (n : ℝ)) atTop (𝓝 0) := by
    have hneg := hsum.neg
    rw [neg_zero] at hneg
    refine hneg.congr' (h.mono fun n hn => ?_)
    have hf : (n.factorial : ℝ) ^ m ≠ 0 := by positivity
    rw [evalEval_eq_sum_range, ← hm, Finset.sum_range_succ] at hn
    have hdiv := congrArg (fun t => t / (n.factorial : ℝ) ^ m) hn
    simp only [add_div, zero_div, Finset.sum_div] at hdiv
    rw [mul_div_assoc, div_self hf, mul_one] at hdiv
    rw [leadingCoeff]
    linarith
  exact hL (eq_zero_of_tendsto_eval_natCast _ hlead)


/-- **Independence lemma.** `n` and `n!` are algebraically independent as sequences:
if `P ∈ ℚ[x][y]` and `P(n, n!) = 0` for all large `n`, then `P = 0`. -/
theorem eq_zero_of_eventually_evalEval_factorial (P : ℚ[X][X])
    (h : ∀ᶠ n : ℕ in atTop, P.evalEval (n : ℚ) (n.factorial : ℚ) = 0) : P = 0 := by
  set Pr : ℝ[X][X] := P.map (mapRingHom (Rat.castHom ℝ)) with hPr
  have hr : ∀ᶠ n : ℕ in atTop, Pr.evalEval (n : ℝ) (n.factorial : ℝ) = 0 := by
    refine h.mono fun n hn => ?_
    have key := map_mapRingHom_evalEval (Rat.castHom ℝ) P (n : ℚ) (n.factorial : ℚ)
    simp only [eq_ratCast, Rat.cast_natCast] at key
    rw [hPr, key, hn, Rat.cast_zero]
  have hPr0 := eq_zero_of_eventually_evalEval_factorial_real Pr hr
  rw [hPr, Polynomial.map_eq_zero_iff (Polynomial.map_injective _ (Rat.castHom ℝ).injective)]
    at hPr0
  exact hPr0

/-! ## The coefficient comparison and the sum `∑ k!` -/

/-- No rational polynomial `Q` satisfies `(x + 1) Q(x + 1) - Q(x) = x + 1`. -/
theorem shift_mul_sub_ne (Q : ℚ[X]) : (X + 1) * Q.comp (X + 1) - Q ≠ X + 1 := by
  intro h
  by_cases hQ : Q = 0
  · rw [hQ] at h
    have h0 := congrArg (eval 0) h
    simp at h0
  · have hX1 : (X + 1 : ℚ[X]) ≠ 0 := X_add_C_ne_zero 1
    have hdX1 : (X + 1 : ℚ[X]).natDegree = 1 := natDegree_X_add_C 1
    have hcomp : (Q.comp (X + 1)).natDegree = Q.natDegree := by
      rw [natDegree_comp, hdX1, mul_one]
    have hcomp0 : Q.comp (X + 1) ≠ 0 := by
      intro hc
      have := congrArg (fun p : ℚ[X] => p.comp (X - 1)) hc
      simp only [comp_assoc, zero_comp] at this
      apply hQ
      simpa using this
    have hdeg : ((X + 1) * Q.comp (X + 1)).natDegree = 1 + Q.natDegree := by
      rw [natDegree_mul hX1 hcomp0, hdX1, hcomp]
    have hdeg' : ((X + 1) * Q.comp (X + 1) - Q).natDegree = 1 + Q.natDegree := by
      rw [natDegree_sub_eq_left_of_natDegree_lt (by omega), hdeg]
    rw [h, hdX1] at hdeg'
    have hQ0 : Q.natDegree = 0 := by omega
    rw [eq_C_of_natDegree_eq_zero hQ0] at h
    have h0 := congrArg (eval 0) h
    simp at h0


/-- Expansion of `P(x, y)` along the outer variable, over any range beyond the degree. -/
theorem evalEval_eq_sum_range' {R : Type*} [CommSemiring R] (P : R[X][X]) {N : ℕ}
    (hN : P.natDegree < N) (x y : R) :
    P.evalEval x y = ∑ j ∈ Finset.range N, (P.coeff j).eval x * y ^ j := by
  rw [evalEval, eval_eq_sum_range' hN, eval_finsetSum]
  simp only [eval_mul, eval_pow, eval_C]

/-- **Main computation.** There is no `q ∈ ℚ[x][y]` with `∑_{k=1}^n k! = q(n, n!)` for all
`n ≥ 1`; i.e. the partial sums of `k!` are not a polynomial in `n` and `n!`
(answering arXiv:math/0702605, Section 2, the remark before Open Problem 2). -/
theorem sum_factorial_ne_evalEval :
    ¬ ∃ q : ℚ[X][X], ∀ n : ℕ, 1 ≤ n →
      ∑ k ∈ Finset.Icc 1 n, (k.factorial : ℚ) = q.evalEval (n : ℚ) (n.factorial : ℚ) := by
  rintro ⟨q, hq⟩
  set N := q.natDegree + 2 with hNdef
  let R : ℕ → ℚ[X] := fun j =>
    (q.coeff j).comp (X + 1) * (X + 1) ^ j - q.coeff j - (if j = 1 then X + 1 else 0)
  let P : ℚ[X][X] := ∑ j ∈ Finset.range N, C (R j) * X ^ j
  have hstep : ∀ n : ℕ, 1 ≤ n →
      q.evalEval ((n + 1 : ℕ) : ℚ) ((n + 1).factorial : ℚ)
        - q.evalEval (n : ℚ) (n.factorial : ℚ) - ((n + 1).factorial : ℚ) = 0 := by
    intro n hn
    rw [← hq n hn, ← hq (n + 1) (by omega), Finset.sum_Icc_succ_top (by omega)]
    ring
  have hPeval : ∀ n : ℕ, P.evalEval (n : ℚ) (n.factorial : ℚ) =
      q.evalEval ((n + 1 : ℕ) : ℚ) ((n + 1).factorial : ℚ)
        - q.evalEval (n : ℚ) (n.factorial : ℚ) - ((n + 1).factorial : ℚ) := by
    intro n
    have hlt : q.natDegree < N := by omega
    rw [evalEval_eq_sum_range' q hlt, evalEval_eq_sum_range' q hlt]
    simp only [P, R, evalEval_finsetSum, evalEval_mul, evalEval_C, evalEval_pow, evalEval_X,
      eval_sub, eval_mul, eval_comp, eval_pow, eval_add, eval_X, eval_one, apply_ite (eval _),
      eval_zero]
    have h1 : (1 : ℕ) ∈ Finset.range N := Finset.mem_range.mpr (by omega)
    rw [Nat.factorial_succ]
    simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', h1,
      if_true]
    push_cast
    congr 1
    · congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_pow]
      ring
    · ring
  have hP : P = 0 := by
    apply eq_zero_of_eventually_evalEval_factorial
    rw [eventually_atTop]
    exact ⟨1, fun n hn => by rw [hPeval n, hstep n hn]⟩
  have hcoeff := congrArg (fun p : ℚ[X][X] => p.coeff 1) hP
  simp only [P, finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at hcoeff
  rw [Finset.sum_ite_eq (Finset.range N) 1 R, if_pos (Finset.mem_range.mpr (by omega))]
    at hcoeff
  simp only [R, if_true, pow_one] at hcoeff
  apply shift_mul_sub_ne (q.coeff 1)
  rw [mul_comm]
  exact sub_eq_zero.mp hcoeff


/-! ## The sets of the paper and Open Problem 2 -/

/-- `PF_ℤ` (math/0702605, (2.1)–(2.2)): the functions `f : ℕ₊ → ℕ₊` with
`f(n) = p(n, n!)` for all `n ∈ ℕ₊`, for some `p ∈ ℤ[x][y]`. -/
def PFZ : Set (ℕ+ → ℕ+) :=
  {f | ∃ p : ℤ[X][X], ∀ n : ℕ+,
    (((f n : ℕ) : ℤ)) = p.evalEval ((n : ℕ) : ℤ) (((n : ℕ).factorial : ℕ) : ℤ)}

/-- `PF_ℚ` (math/0702605, (2.3)–(2.4)): the functions `g : ℕ₊ → ℕ₊` with
`g(n) = q(n, n!)` for all `n ∈ ℕ₊`, for some `q ∈ ℚ[x][y]`. -/
def PFQ : Set (ℕ+ → ℕ+) :=
  {g | ∃ q : ℚ[X][X], ∀ n : ℕ+,
    (((g n : ℕ) : ℚ)) = q.evalEval ((n : ℕ) : ℚ) (((n : ℕ).factorial : ℕ) : ℚ)}

/-- `SPF_ℤ` (math/0702605, (2.5)–(2.6)): the `f ∈ PF_ℤ` such that some `g ∈ PF_ℚ`
satisfies `f(1) + ... + f(n) = g(n)` for all `n ∈ ℕ₊`. -/
def SPFZ : Set (ℕ+ → ℕ+) :=
  {f | f ∈ PFZ ∧ ∃ g ∈ PFQ, ∀ n : ℕ+, ∑ k ∈ Finset.Icc 1 n, (f k : ℕ) = (g n : ℕ)}

/-- The function `n ↦ n!` on `ℕ₊`. -/
def factorialPNat : ℕ+ → ℕ+ := fun n => ⟨(n : ℕ).factorial, Nat.factorial_pos _⟩

example : (factorialPNat 4 : ℕ) = 24 := by decide

example : (Finset.Icc (1 : ℕ+) 4).sum (fun k => (factorialPNat k : ℕ)) = 33 := by decide

/-- `n ↦ n!` lies in `PF_ℤ` (take `p(x, y) = y`). -/
theorem factorialPNat_mem_PFZ : factorialPNat ∈ PFZ :=
  ⟨X, fun n => by simp [factorialPNat]⟩

/-- A sum over `[1, n]` in `ℕ₊` equals the corresponding sum over `[1, n]` in `ℕ`. -/
theorem sum_Icc_pnat (f : ℕ+ → ℕ+) (n : ℕ+) :
    ∑ k ∈ Finset.Icc 1 n, (f k : ℕ) =
      ∑ k ∈ Finset.Icc 1 (n : ℕ), (f k.toPNat' : ℕ) := by
  refine Finset.sum_nbij' (fun k => (k : ℕ)) (fun k => k.toPNat') ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_Icc] at hk ⊢
    exact ⟨k.pos, hk.2⟩
  · intro k hk
    simp only [Finset.mem_Icc] at hk ⊢
    refine ⟨one_le, ?_⟩
    rw [← PNat.coe_le_coe, Nat.toPNat'_coe, if_pos (by omega)]
    exact hk.2
  · intro k _
    simp
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    simp only [Nat.toPNat'_coe, if_pos (show 0 < k by omega)]
  · intro k _
    simp

/-- `n ↦ n!` does not lie in `SPF_ℤ`. -/
theorem factorialPNat_not_mem_SPFZ : factorialPNat ∉ SPFZ := by
  rintro ⟨-, g, ⟨q, hq⟩, hsum⟩
  apply sum_factorial_ne_evalEval
  refine ⟨q, fun n hn => ?_⟩
  have h1 := hsum n.toPNat'
  have h2 := hq n.toPNat'
  have hn' : ((n.toPNat' : ℕ+) : ℕ) = n := by rw [Nat.toPNat'_coe, if_pos (by omega)]
  rw [sum_Icc_pnat, hn'] at h1
  rw [hn'] at h2
  rw [← h2, ← h1]
  push_cast
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk1 : 0 < k := by rw [Finset.mem_Icc] at hk; omega
  simp [factorialPNat, Nat.toPNat'_coe, hk1]

/-- **Open Problem 2 of arXiv:math/0702605 (answer: no).** The equality (2.7)
`SPF_ℤ = PF_ℤ` fails. -/
theorem SPFZ_ne_PFZ : SPFZ ≠ PFZ := by
  intro h
  apply factorialPNat_not_mem_SPFZ
  rw [h]
  exact factorialPNat_mem_PFZ


/-- `∑_{k=1}^n k · k! = (n+1)! - 1` (paper (1.3)). -/
theorem sum_mul_factorial (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, k * k.factorial = (n + 1).factorial - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    have hpos : 1 ≤ (n + 1).factorial := Nat.factorial_pos _
    rw [Nat.factorial_succ (n + 1)]
    zify [hpos, (by nlinarith : 1 ≤ (n + 1 + 1) * (n + 1).factorial)]
    ring

/-- The function `n ↦ n · n!` on `ℕ₊` (paper, before Open Problem 2). -/
def mulFactorialPNat : ℕ+ → ℕ+ := fun n =>
  ⟨(n : ℕ) * (n : ℕ).factorial, Nat.mul_pos n.pos (Nat.factorial_pos _)⟩

/-- The function `n ↦ (n+1)! - 1` on `ℕ₊` (positive since `(n+1)! ≥ 2`). -/
def succFactorialSubOne : ℕ+ → ℕ+ := fun n =>
  ⟨((n : ℕ) + 1).factorial - 1, by
    have h2 : 2 ≤ ((n : ℕ) + 1).factorial := by
      have := Nat.self_le_factorial ((n : ℕ) + 1)
      have := n.pos
      omega
    omega⟩

/-- Non-vacuity: the paper's example `n ↦ n · n!` lies in `SPF_ℤ`, witnessed by
`g(n) = (n + 1)! - 1 = q(n, n!)` with `q(x, y) = (x + 1) y - 1`. -/
theorem mulFactorialPNat_mem_SPFZ : mulFactorialPNat ∈ SPFZ := by
  refine ⟨⟨C X * X, fun n => by simp [mulFactorialPNat, evalEval_C]⟩,
    succFactorialSubOne, ⟨(C X + 1) * X - 1, fun n => ?_⟩, fun n => ?_⟩
  · have hpos : 1 ≤ ((n : ℕ) + 1).factorial := Nat.factorial_pos _
    simp only [succFactorialSubOne, PNat.mk_coe, evalEval_sub, evalEval_mul, evalEval_add,
      evalEval_C, evalEval_X, evalEval_one, eval_X]
    rw [Nat.cast_sub hpos, Nat.factorial_succ]
    push_cast
    ring
  · rw [sum_Icc_pnat]
    have hcongr : ∑ k ∈ Finset.Icc 1 (n : ℕ), (mulFactorialPNat k.toPNat' : ℕ) =
        ∑ k ∈ Finset.Icc 1 (n : ℕ), k * k.factorial := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk1 : 0 < k := by simp only [Finset.mem_Icc] at hk; omega
      simp [mulFactorialPNat, Nat.toPNat'_coe, hk1]
    rw [hcongr, sum_mul_factorial]
    rfl

example : (mulFactorialPNat 3 : ℕ) = 18 := by decide

example : (succFactorialSubOne 3 : ℕ) = 23 := by decide

/-- **Open Problem 2 of arXiv:math/0702605, strict form.** `SPF_ℤ ⊊ PF_ℤ`. -/
theorem SPFZ_ssubset_PFZ : SPFZ ⊂ PFZ :=
  ⟨fun _ hf => hf.1, fun h => factorialPNat_not_mem_SPFZ (h factorialPNat_mem_PFZ)⟩

end Candidates.RosingerSumFactorialNotPolynomial
