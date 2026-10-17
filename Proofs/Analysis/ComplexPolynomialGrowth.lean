import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Field

set_option autoImplicit false
open scoped BigOperators
open Finset Polynomial
namespace ComplexPolynomialGrowth

private theorem norm_nat_sub (a b : ℕ) (h : b ≤ a) :
    ‖(a : ℂ) - (b : ℂ)‖ = (a : ℝ) - (b : ℝ) := by
  rw [← Nat.cast_sub h, Complex.norm_natCast, Nat.cast_sub h]

private theorem prod_norm_sub_last (n : ℕ) :
    (∏ k ∈ range n, ‖(n : ℂ) - (k : ℂ)‖) = (n.factorial : ℝ) := by
  calc
    _ = ∏ k ∈ range n, ((n - k : ℕ) : ℝ) := by
      apply prod_congr rfl
      intro k hk
      rw [norm_nat_sub n k (Nat.le_of_lt (mem_range.mp hk)), Nat.cast_sub (Nat.le_of_lt (mem_range.mp hk))]
    _ = ∏ k ∈ range n, ((k + 1 : ℕ) : ℝ) := by
      rw [← prod_range_reflect (fun k : ℕ => ((k + 1 : ℕ) : ℝ)) n]
      apply prod_congr rfl
      intro k hk
      have hkn : k < n := mem_range.mp hk
      congr 1
      omega
    _ = (n.factorial : ℝ) := by
      rw [Nat.factorial_eq_prod_range_add_one, Nat.cast_prod]

private theorem prod_norm_sub (n j : ℕ) (hj : j < n) :
    (∏ k ∈ (range n).erase j, ‖(j : ℂ) - (k : ℂ)‖) =
      (j.factorial : ℝ) * ((n - 1 - j).factorial : ℝ) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : j = n
    · subst j
      rw [range_add_one, erase_insert (by simp), prod_norm_sub_last]
      simp
    · have hjn : j < n := by omega
      have hne : n ≠ j := Ne.symm he
      rw [range_add_one, erase_insert_of_ne hne, prod_insert (by simp), ih hjn]
      rw [norm_sub_rev, norm_nat_sub n j (Nat.le_of_lt hjn)]
      have hn : n - j = (n - 1 - j) + 1 := by omega
      have hn' : n + 1 - 1 - j = n - j := by omega
      rw [hn', hn, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      have hc : (n : ℝ) - (j : ℝ) = (n - 1 - j : ℕ) + 1 := by
        rw [← Nat.cast_sub (Nat.le_of_lt hjn), hn, Nat.cast_add, Nat.cast_one]
      rw [hc]
      ring

private theorem node_denominator (d j : ℕ) (hj : j ∈ range (d + 1)) :
    ‖∏ k ∈ (range (d + 1)).erase j,
      ((j : ℂ) / (d + 1) - (k : ℂ) / (d + 1))‖ =
      ((j.factorial : ℝ) * ((d - j).factorial : ℝ)) / (d + 1 : ℝ) ^ d := by
  have hcard : ((range (d + 1)).erase j).card = d := by
    rw [card_erase_of_mem hj, card_range]
    omega
  simp_rw [← sub_div, Complex.norm_prod, norm_div]
  rw [prod_div_distrib, prod_const, hcard, prod_norm_sub (d + 1) j (mem_range.mp hj)]
  simp only [Nat.add_sub_cancel]
  rw [show ‖(d + 1 : ℂ)‖ = (d + 1 : ℝ) by
    simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (d + 1)]

private theorem sum_reciprocal_factorials (d : ℕ) :
    (∑ j ∈ range (d + 1), 1 / ((j.factorial : ℝ) * ((d - j).factorial : ℝ))) =
      (2 : ℝ) ^ d / (d.factorial : ℝ) := by
  have hterm : ∀ j ∈ range (d + 1),
      1 / ((j.factorial : ℝ) * ((d - j).factorial : ℝ)) =
        (d.choose j : ℝ) / (d.factorial : ℝ) := by
    intro j hj
    rw [Nat.cast_choose ℝ (Nat.le_of_lt_succ (mem_range.mp hj))]
    have hd : (d.factorial : ℝ) ≠ 0 := by positivity
    have hjf : (j.factorial : ℝ) ≠ 0 := by positivity
    have hdf : ((d - j).factorial : ℝ) ≠ 0 := by positivity
    field_simp
  rw [sum_congr rfl hterm, ← sum_div, ← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]

private theorem node_mem (d j : ℕ) (hj : j ∈ range (d + 1)) :
    (j : ℝ) / (d + 1) ∈ Set.Icc (0 : ℝ) 1 := by
  have hpos : (0 : ℝ) < d + 1 := by positivity
  constructor
  · positivity
  · apply (div_le_one hpos).mpr
    exact_mod_cast (Nat.le_of_lt (mem_range.mp hj) : j ≤ d + 1)

private theorem lagrange_bound (d : ℕ) (R M : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (p : ℂ[X]) (hd : p.natDegree ≤ d)
    (hp : ∀ t : ℝ, t ∈ Set.Icc 0 1 → ‖p.eval (t : ℂ)‖ ≤ M)
    (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖p.eval z‖ ≤ M * (R + 1) ^ d * (d + 1 : ℝ) ^ d * (2 ^ d / (d.factorial : ℝ)) := by
  let v : ℕ → ℂ := fun j => (j : ℂ) / (d + 1)
  have hdn : (d + 1 : ℂ) ≠ 0 := by
    exact_mod_cast (show d + 1 ≠ 0 by omega)
  have hv : Set.InjOn v (range (d + 1)) := by
    intro i hi j hj hij
    dsimp [v] at hij
    have he : (i : ℂ) = (j : ℂ) := (div_left_inj' hdn).mp hij
    exact_mod_cast he
  have hdegree : p.degree < ((range (d + 1)).card : WithBot ℕ) := by
    apply lt_of_le_of_lt p.degree_le_natDegree
    rw [card_range]
    exact_mod_cast (hd.trans_lt (Nat.lt_succ_self d))
  have hinterp := Lagrange.eq_interpolate hv hdegree
  have heval : p.eval z = ∑ j ∈ range (d + 1),
      (p.eval (v j) / ∏ k ∈ (range (d + 1)).erase j, (v j - v k)) *
        ∏ k ∈ (range (d + 1)).erase j, (z - v k) := by
    conv_lhs => rw [hinterp, Lagrange.interpolate_eq_sum]
    simp only [eval_finsetSum, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
  have hnode : ∀ j ∈ range (d + 1), ‖p.eval (v j)‖ ≤ M := by
    intro j hj
    have he : (((j : ℝ) / (d + 1) : ℝ) : ℂ) = v j := by
      simp [v]
    rw [← he]
    exact hp _ (node_mem d j hj)
  have hvnorm : ∀ k ∈ range (d + 1), ‖v k‖ ≤ 1 := by
    intro k hk
    have hmem := node_mem d k hk
    simpa only [v, norm_div, Complex.norm_natCast, show ‖(d + 1 : ℂ)‖ = (d + 1 : ℝ) by
      rw [← Nat.cast_add_one, Complex.norm_natCast, Nat.cast_add, Nat.cast_one]] using hmem.2
  have hnum : ∀ j ∈ range (d + 1),
      ‖∏ k ∈ (range (d + 1)).erase j, (z - v k)‖ ≤ (R + 1) ^ d := by
    intro j hj
    rw [Complex.norm_prod]
    have hcard : ((range (d + 1)).erase j).card = d := by
      rw [card_erase_of_mem hj, card_range]; omega
    calc
      _ ≤ ∏ _k ∈ (range (d + 1)).erase j, (R + 1) := by
        apply prod_le_prod (fun _ _ => norm_nonneg _)
        intro k hk
        exact (norm_sub_le z (v k)).trans (add_le_add hz (hvnorm k (mem_of_mem_erase hk)))
      _ = (R + 1) ^ d := by rw [prod_const, hcard]
  have hterm : ∀ j ∈ range (d + 1),
      ‖(p.eval (v j) / ∏ k ∈ (range (d + 1)).erase j, (v j - v k)) *
        ∏ k ∈ (range (d + 1)).erase j, (z - v k)‖ ≤
        (M * (R + 1) ^ d * (d + 1 : ℝ) ^ d) *
          (1 / ((j.factorial : ℝ) * ((d - j).factorial : ℝ))) := by
    intro j hj
    rw [norm_mul, norm_div]
    calc
      _ ≤ (M / ‖∏ k ∈ (range (d + 1)).erase j, (v j - v k)‖) * (R + 1) ^ d :=
        mul_le_mul (div_le_div_of_nonneg_right (hnode j hj) (norm_nonneg _))
          (hnum j hj) (norm_nonneg _) (div_nonneg hM (norm_nonneg _))
      _ = _ := by
        dsimp [v]
        rw [node_denominator d j hj]
        have hdp : (d + 1 : ℝ) ≠ 0 := by positivity
        have hjf : (j.factorial : ℝ) ≠ 0 := by positivity
        have hdf : ((d - j).factorial : ℝ) ≠ 0 := by positivity
        field_simp
  calc
    ‖p.eval z‖ ≤ ∑ j ∈ range (d + 1),
        ‖(p.eval (v j) / ∏ k ∈ (range (d + 1)).erase j, (v j - v k)) *
          ∏ k ∈ (range (d + 1)).erase j, (z - v k)‖ := by
      rw [heval]
      exact norm_sum_le _ _
    _ ≤ ∑ j ∈ range (d + 1), (M * (R + 1) ^ d * (d + 1 : ℝ) ^ d) *
        (1 / ((j.factorial : ℝ) * ((d - j).factorial : ℝ))) := sum_le_sum hterm
    _ = _ := by rw [← mul_sum, sum_reciprocal_factorials]

/-- A complex polynomial of degree at most `d`, bounded by `M` on the real unit
interval, has the stated exponential growth bound on the closed complex disk of radius `R`.
This includes degree zero and the zero polynomial. -/
theorem norm_eval_le (d : ℕ) (R M : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (p : ℂ[X]) (hd : p.natDegree ≤ d)
    (hp : ∀ t : ℝ, t ∈ Set.Icc 0 1 → ‖p.eval (t : ℂ)‖ ≤ M) :
    ∀ z : ℂ, ‖z‖ ≤ R →
      ‖p.eval z‖ ≤ M * (2 * (R + 1)) ^ d * Real.exp ((d : ℝ) + 1) := by
  intro z hz
  have hexp := Real.pow_div_factorial_le_exp ((d : ℝ) + 1) (by positivity) d
  calc
    ‖p.eval z‖ ≤ M * (R + 1) ^ d * (d + 1 : ℝ) ^ d * (2 ^ d / (d.factorial : ℝ)) :=
      lagrange_bound d R M hR hM p hd hp z hz
    _ = (M * (2 * (R + 1)) ^ d) * (((d : ℝ) + 1) ^ d / (d.factorial : ℝ)) := by
      rw [mul_pow]
      ring
    _ ≤ (M * (2 * (R + 1)) ^ d) * Real.exp ((d : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)

/-- Separate polynomial representations of degree at most `d` in each complex
coordinate turn a bound on the real unit square into a bound on a complex bidisk. -/
theorem norm_le_of_separately_polynomial (d : ℕ) (R M : ℝ)
    (hR : 0 ≤ R) (hM : 0 ≤ M) (b : ℂ → ℂ → ℂ)
    (hx : ∀ w : ℂ, ∃ p : ℂ[X], p.natDegree ≤ d ∧ ∀ z : ℂ, p.eval z = b z w)
    (hy : ∀ z : ℂ, ∃ q : ℂ[X], q.natDegree ≤ d ∧ ∀ w : ℂ, q.eval w = b z w)
    (hb : ∀ x y : ℝ, x ∈ Set.Icc 0 1 → y ∈ Set.Icc 0 1 →
      ‖b (x : ℂ) (y : ℂ)‖ ≤ M) :
    ∀ z w : ℂ, ‖z‖ ≤ R → ‖w‖ ≤ R →
      ‖b z w‖ ≤ M * (2 * (R + 1)) ^ (2 * d) *
        Real.exp (2 * ((d : ℝ) + 1)) := by
  intro z w hz hw
  have hreal : ∀ y : ℝ, y ∈ Set.Icc 0 1 →
      ‖b z (y : ℂ)‖ ≤ M * (2 * (R + 1)) ^ d * Real.exp ((d : ℝ) + 1) := by
    intro y hyreal
    obtain ⟨p, hpd, hp⟩ := hx (y : ℂ)
    rw [← hp z]
    apply norm_eval_le d R M hR hM p hpd _ z hz
    intro x hxreal
    rw [hp]
    exact hb x y hxreal hyreal
  obtain ⟨q, hqd, hq⟩ := hy z
  have hbound : ‖q.eval w‖ ≤
      (M * (2 * (R + 1)) ^ d * Real.exp ((d : ℝ) + 1)) *
        (2 * (R + 1)) ^ d * Real.exp ((d : ℝ) + 1) := by
    apply norm_eval_le d R _ hR (by positivity) q hqd _ w hw
    intro y hyreal
    rw [hq]
    exact hreal y hyreal
  rw [hq] at hbound
  calc
    ‖b z w‖ ≤ _ := hbound
    _ = M * (2 * (R + 1)) ^ (2 * d) * Real.exp (2 * ((d : ℝ) + 1)) := by
      rw [show 2 * d = d + d by omega, pow_add,
        show 2 * ((d : ℝ) + 1) = ((d : ℝ) + 1) + ((d : ℝ) + 1) by ring]
      simp only [Real.exp_add]
      ring

example :
    (0 : ℝ) ≤ 1 ∧ (0 : ℝ) ≤ 1 ∧ (C (1 : ℂ)).natDegree ≤ 2 ∧
      (∀ t : ℝ, t ∈ Set.Icc 0 1 → ‖(C (1 : ℂ)).eval (t : ℂ)‖ ≤ 1) := by
  norm_num

example :
    (0 : ℝ) ≤ 1 ∧ (0 : ℝ) ≤ 1 ∧
    (∀ _w : ℂ, ∃ p : ℂ[X], p.natDegree ≤ 2 ∧ ∀ z : ℂ, p.eval z = (1 : ℂ)) ∧
    (∀ _z : ℂ, ∃ q : ℂ[X], q.natDegree ≤ 2 ∧ ∀ w : ℂ, q.eval w = (1 : ℂ)) ∧
    (∀ x y : ℝ, x ∈ Set.Icc 0 1 → y ∈ Set.Icc 0 1 → ‖(1 : ℂ)‖ ≤ (1 : ℝ)) := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_⟩
  · intro w
    exact ⟨C 1, by simp, by simp⟩
  · intro z
    exact ⟨C 1, by simp, by simp⟩
  · intros
    norm_num

end ComplexPolynomialGrowth
