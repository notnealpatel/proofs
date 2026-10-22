/-
# Generalized Tamarkin conjecture: refutation at `p = 5`

Darij Grinberg, MathOverflow question 66959, “Generalization of
Tamarkin’s ARO 1993, final round, problem 10/8: still a conjecture?”,
https://mathoverflow.net/questions/66959 .
A sequence is `p`-average-integral when all iterates of the length-`p`
averaging operator are integer-valued. The proposed closure under
pointwise `p`-th powers fails at `p = 5`: zeb's witness `1+n⁶` is
average-integral but `(1+n⁶)⁵` is not. The thread gives counterexamples
for every prime `p > 3`; only `p = 5` is formalized here.
Sequences are rational-valued rather than real-valued; all values
in this witness are rational.

Write `D f = Δ⁴ f / 5` (`quartOp`).  Pointwise
`F_5 f (n) = f(n+1) - f(n+2) + f(n+3) + D f (n)`.

* Positive part: the class of `h` with `h` and `D h` integer-valued and
  `D (D h) = 0` is closed under `F_5`, and contains `1 + n^6`
  (`D (1 + n^6) = 72 n^2 + 288 n + 312`).
* Negative part: the class of `h` with all `F_5`-iterates integer-valued is
  closed under `D` (an integer combination of `F_5` and shifts).  So
  `D^6 ((1+n^6)^5) (0) = Δ^24 ((1+n^6)^5) (0) / 5^6` would be an integer,
  but `Δ^24 ((1+n^6)^5) (0) ≡ 5^5 (mod 5^6)`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.TamarkinAverageIntegralRefutation

/-! ## Definitions mirroring the source -/

/-- Grinberg's averaging operator `F_p`:
`(F_p f)(n) = (f(n) + f(n+1) + ... + f(n+p-1)) / p`, on `ℚ`-valued sequences
(the source uses `ℝ`; every value involved is rational). -/
def avgOp (p : ℕ) (f : ℤ → ℚ) : ℤ → ℚ :=
  fun n => (∑ i ∈ Finset.range p, f (n + i)) / p

/-- An integer sequence `f` is `p`-*average-integral* if `F_p^k f` is
integer-valued for every `k ≥ 0`. -/
def AvgIntegral (p : ℕ) (f : ℤ → ℤ) : Prop :=
  ∀ k : ℕ, ∀ n : ℤ, ∃ m : ℤ, (avgOp p)^[k] (fun x => (f x : ℚ)) n = m

/-! ### Examples -/

example : avgOp 5 (fun n => (n : ℚ)) 0 = 2 := by
  simp only [avgOp, zero_add, Int.cast_natCast, Finset.sum_range_succ, Finset.range_one,
    Finset.sum_singleton, CharP.cast_eq_zero, Nat.cast_one, Nat.cast_ofNat]
  norm_num

example : avgOp 2 (fun n => (n : ℚ) ^ 2) 0 = 1 / 2 := by
  simp [avgOp, Finset.sum_range_succ]

/-- `n ↦ n^2` is not `2`-average-integral: `F_2 (n^2) (0) = 1/2`. -/
example : ¬ AvgIntegral 2 (fun n => n ^ 2) := by
  intro h
  obtain ⟨m, hm⟩ := h 1 0
  simp only [Int.cast_pow, Function.iterate_one, avgOp, zero_add, Int.cast_natCast,
    Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, CharP.cast_eq_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Nat.cast_one, one_pow, Nat.cast_ofNat,
    one_div] at hm
  have h2 : (1 : ℚ) = 2 * m := by linarith
  have h2' : (1 : ℤ) = 2 * m := by exact_mod_cast h2
  omega

/-- A constant sequence is average-integral (each `F_p`, `p ≠ 0`, fixes it). -/
example : AvgIntegral 3 (fun _ => 7) := by
  intro k
  have hfix : avgOp 3 (fun _ => ((7 : ℤ) : ℚ)) = fun _ => ((7 : ℤ) : ℚ) := by
    funext n
    simp [avgOp]
  intro n
  refine ⟨7, ?_⟩
  rw [Function.iterate_fixed hfix]

/-! ## The operator `D = Δ⁴ / 5` -/

/-- The operator `D f = Δ⁴ f / 5`, written out with binomial coefficients. -/
def quartOp (f : ℤ → ℚ) : ℤ → ℚ :=
  fun n => (f (n + 4) - 4 * f (n + 3) + 6 * f (n + 2) - 4 * f (n + 1) + f n) / 5

/-- `D` agrees with `(1/5) • Δ⁴` for Mathlib's forward difference. -/
theorem quartOp_eq_smul_fwdDiff_iter (f : ℤ → ℚ) :
    quartOp f = (1 / 5 : ℚ) • (fwdDiff (1 : ℤ))^[4] f := by
  funext n
  rw [Pi.smul_apply, fwdDiff_iter_eq_sum_shift]
  simp only [quartOp, one_div, Nat.reduceAdd, Int.reduceNeg, Int.nsmul_eq_mul, mul_one,
    zsmul_eq_mul, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast,
    Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, tsub_zero, Nat.choose,
    Nat.cast_one, CharP.cast_eq_zero, add_zero, Nat.add_one_sub_one, Nat.cast_ofNat,
    Nat.reduceSub, even_two, Even.neg_pow, one_pow, one_mul, pow_one, neg_mul, tsub_self,
    pow_zero, smul_eq_mul]
  ring_nf

/-- Iterating `D` gives `(1/5)^k • Δ^(4k)`. -/
theorem quartOp_iterate (f : ℤ → ℚ) (k : ℕ) :
    quartOp^[k] f = (1 / 5 : ℚ) ^ k • (fwdDiff (1 : ℤ))^[4 * k] f := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, quartOp_eq_smul_fwdDiff_iter,
      fwdDiff_iter_const_smul, smul_smul, ← Function.iterate_add_apply, pow_succ,
      mul_comm ((1 / 5 : ℚ) ^ k)]
    congr 2
    ring

/-- Pointwise decomposition `F_5 f (n) = f(n+1) - f(n+2) + f(n+3) + D f (n)`. -/
theorem avgOp_five_eq (f : ℤ → ℚ) (n : ℤ) :
    avgOp 5 f n = f (n + 1) - f (n + 2) + f (n + 3) + quartOp f n := by
  simp only [avgOp, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
    CharP.cast_eq_zero, add_zero, Nat.cast_one, Nat.cast_ofNat, quartOp]
  ring

/-- `D` commutes with `F_5`, written pointwise through `avgOp_five_eq`:
`D (F_5 h) (n) = D h (n+1) - D h (n+2) + D h (n+3) + D (D h) (n)`. -/
theorem quartOp_avgOp_five (h : ℤ → ℚ) (n : ℤ) :
    quartOp (avgOp 5 h) n = quartOp h (n + 1) - quartOp h (n + 2) + quartOp h (n + 3)
      + quartOp (quartOp h) n := by
  simp only [quartOp, avgOp, Finset.sum_range_succ, Finset.sum_range_zero, add_assoc]
  norm_num
  ring

/-- `D` applied to the shift combination `g(n+1) - g(n+2) + g(n+3)`. -/
theorem quartOp_shiftComb (g : ℤ → ℚ) (n : ℤ) :
    quartOp (fun x => g (x + 1) - g (x + 2) + g (x + 3)) n
      = quartOp g (n + 1) - quartOp g (n + 2) + quartOp g (n + 3) := by
  simp only [quartOp, add_assoc]
  norm_num
  ring

/-! ## Positive part: `1 + n^6` is `5`-average-integral -/

/-- A rational sequence is integer-valued. -/
def IsIntValued (h : ℤ → ℚ) : Prop :=
  ∀ n : ℤ, ∃ m : ℤ, h n = m

/-- Integer-valuedness is preserved by the combination
`n ↦ g(n+1) - g(n+2) + g(n+3) + d(n)`. -/
theorem isIntValued_comb {g d : ℤ → ℚ} (hg : IsIntValued g) (hd : IsIntValued d) :
    IsIntValued (fun n => g (n + 1) - g (n + 2) + g (n + 3) + d n) := by
  intro n
  obtain ⟨a, ha⟩ := hg (n + 1)
  obtain ⟨b, hb⟩ := hg (n + 2)
  obtain ⟨c, hc⟩ := hg (n + 3)
  obtain ⟨e, he⟩ := hd n
  exact ⟨a - b + c + e, by simp only [ha, hb, hc, he]; push_cast; ring⟩

/-- The `F_5`-invariant class: `h` and `D h` are integer-valued and `D (D h) = 0`. -/
def GoodClass (h : ℤ → ℚ) : Prop :=
  IsIntValued h ∧ IsIntValued (quartOp h) ∧ quartOp (quartOp h) = 0

/-- `GoodClass` is closed under `F_5`. -/
theorem GoodClass.avgOp_five {h : ℤ → ℚ} (hh : GoodClass h) : GoodClass (avgOp 5 h) := by
  obtain ⟨hint, hDint, hDD⟩ := hh
  have hF : avgOp 5 h = fun n => h (n + 1) - h (n + 2) + h (n + 3) + quartOp h n := by
    funext n
    exact avgOp_five_eq h n
  have hDF : quartOp (avgOp 5 h)
      = fun n => quartOp h (n + 1) - quartOp h (n + 2) + quartOp h (n + 3) := by
    funext n
    rw [quartOp_avgOp_five, hDD]
    simp
  refine ⟨?_, ?_, ?_⟩
  · rw [hF]
    exact isIntValued_comb hint hDint
  · rw [hDF]
    have hzero : IsIntValued (fun _ => (0 : ℚ)) := fun _ => ⟨0, by simp⟩
    simpa using isIntValued_comb hDint hzero
  · rw [hDF]
    funext n
    rw [quartOp_shiftComb, hDD]
    simp

/-- Every `F_5`-iterate of a `GoodClass` sequence is integer-valued. -/
theorem GoodClass.isIntValued_iterate {h : ℤ → ℚ} (hh : GoodClass h) (k : ℕ) :
    IsIntValued ((avgOp 5)^[k] h) := by
  have hgood : GoodClass ((avgOp 5)^[k] h) := by
    induction k with
    | zero => simpa using hh
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact ih.avgOp_five
  exact hgood.1

/-- `D (1 + n^6) = 72 n^2 + 288 n + 312`. -/
theorem quartOp_one_add_pow_six :
    quartOp (fun x => (((1 + x ^ 6 : ℤ)) : ℚ))
      = fun n : ℤ => 72 * (n : ℚ) ^ 2 + 288 * n + 312 := by
  funext n
  simp only [quartOp]
  push_cast
  ring

/-- `1 + n^6` lies in the `F_5`-invariant class. -/
theorem goodClass_one_add_pow_six : GoodClass (fun x => (((1 + x ^ 6 : ℤ)) : ℚ)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact fun n => ⟨1 + n ^ 6, rfl⟩
  · rw [quartOp_one_add_pow_six]
    exact fun n => ⟨72 * n ^ 2 + 288 * n + 312, by push_cast; ring⟩
  · rw [quartOp_one_add_pow_six]
    funext n
    simp only [quartOp, Pi.zero_apply]
    push_cast
    ring

/-- **Positive part.** `n ↦ 1 + n^6` is `5`-average-integral. -/
theorem avgIntegral_five_one_add_pow_six : AvgIntegral 5 (fun n => 1 + n ^ 6) :=
  fun k => goodClass_one_add_pow_six.isIntValued_iterate k

/-! ## Negative part: `(1 + n^6)^5` is not `5`-average-integral -/

/-- `F_p` commutes with the shift by `c`. -/
theorem avgOp_comp_add (p : ℕ) (h : ℤ → ℚ) (c : ℤ) :
    avgOp p (fun x => h (x + c)) = fun x => avgOp p h (x + c) := by
  funext n
  simp only [avgOp, add_right_comm]

/-- `F_p` is additive. -/
theorem avgOp_add (p : ℕ) (g h : ℤ → ℚ) : avgOp p (g + h) = avgOp p g + avgOp p h := by
  funext n
  simp only [avgOp, Pi.add_apply, Finset.sum_add_distrib, add_div]

/-- `F_p` commutes with subtraction. -/
theorem avgOp_sub (p : ℕ) (g h : ℤ → ℚ) : avgOp p (g - h) = avgOp p g - avgOp p h := by
  funext n
  simp only [avgOp, Pi.sub_apply, Finset.sum_sub_distrib, sub_div]

/-- Iterates of `F_p` commute with shifts. -/
theorem avgOp_iterate_comp_add (p : ℕ) (h : ℤ → ℚ) (c : ℤ) (k : ℕ) :
    (avgOp p)^[k] (fun x => h (x + c)) = fun x => (avgOp p)^[k] h (x + c) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, avgOp_comp_add, ← Function.iterate_succ_apply' (avgOp p)]

/-- Iterates of `F_p` are additive. -/
theorem avgOp_iterate_add (p : ℕ) (g h : ℤ → ℚ) (k : ℕ) :
    (avgOp p)^[k] (g + h) = (avgOp p)^[k] g + (avgOp p)^[k] h := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, avgOp_add,
      Function.iterate_succ_apply', Function.iterate_succ_apply']

/-- Iterates of `F_p` commute with subtraction. -/
theorem avgOp_iterate_sub (p : ℕ) (g h : ℤ → ℚ) (k : ℕ) :
    (avgOp p)^[k] (g - h) = (avgOp p)^[k] g - (avgOp p)^[k] h := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, avgOp_sub,
      Function.iterate_succ_apply', Function.iterate_succ_apply']

/-- All `F_5`-iterates of `h` are integer-valued. -/
def IterIntValued (h : ℤ → ℚ) : Prop :=
  ∀ k : ℕ, IsIntValued ((avgOp 5)^[k] h)

/-- `D` as an integer combination of `F_5` and shifts:
`D h = F_5 h - h(·+1) + h(·+2) - h(·+3)`. -/
theorem quartOp_eq_avgOp_sub (h : ℤ → ℚ) :
    quartOp h = avgOp 5 h - (fun x => h (x + 1)) + (fun x => h (x + 2))
      - (fun x => h (x + 3)) := by
  funext n
  simp only [Pi.add_apply, Pi.sub_apply, avgOp_five_eq]
  ring

/-- The class of sequences with all `F_5`-iterates integer-valued is closed under `D`. -/
theorem IterIntValued.quartOp {h : ℤ → ℚ} (hh : IterIntValued h) :
    IterIntValued (quartOp h) := by
  intro k n
  rw [quartOp_eq_avgOp_sub, avgOp_iterate_sub, avgOp_iterate_add, avgOp_iterate_sub,
    avgOp_iterate_comp_add, avgOp_iterate_comp_add, avgOp_iterate_comp_add,
    ← Function.iterate_succ_apply]
  obtain ⟨a, ha⟩ := hh (k + 1) n
  obtain ⟨b, hb⟩ := hh k (n + 1)
  obtain ⟨c, hc⟩ := hh k (n + 2)
  obtain ⟨d, hd⟩ := hh k (n + 3)
  refine ⟨a - b + c - d, ?_⟩
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [ha, hb, hc, hd]
  push_cast
  ring

/-- The 24th forward difference of `(1 + n^6)^5` at `0`; its `5`-adic valuation is `5`. -/
theorem fwdDiff_iter_24_one_add_pow_six_pow_five :
    (fwdDiff (1 : ℤ))^[24] (fun x => (((1 + x ^ 6) ^ 5 : ℤ) : ℚ)) 0
      = 1338667115787133020121634950348800000 := by
  rw [fwdDiff_iter_eq_sum_shift]
  simp only [Nat.reduceAdd, Int.reduceNeg, Int.nsmul_eq_mul, mul_one, zero_add, Int.cast_pow,
    Int.cast_add, Int.cast_one, Int.cast_natCast, zsmul_eq_mul, Int.cast_mul, Int.cast_neg,
    Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, tsub_zero, zero_le,
    Nat.choose_eq_factorial_div_factorial, Nat.factorial, Nat.succ_eq_add_one, Nat.reduceMul,
    one_mul, Nat.ofNat_pos, Nat.div_self, Nat.cast_one, CharP.cast_eq_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, one_pow, Nat.add_one_sub_one,
    Nat.one_le_ofNat, Nat.reduceDiv, Nat.cast_ofNat, Nat.reduceSub, Nat.reduceLeDiff, even_two,
    Even.neg_pow, Nat.factorial_two, pow_one, neg_mul, tsub_self,
    pow_zero]
  norm_num

/-- **Negative part.** `n ↦ (1 + n^6)^5` is not `5`-average-integral:
`D^6` of it at `0` equals `Δ^24 (0) / 5^6`, which is not an integer. -/
theorem not_avgIntegral_five_one_add_pow_six_pow_five :
    ¬ AvgIntegral 5 (fun n => (1 + n ^ 6) ^ 5) := by
  intro hav
  have hiter : IterIntValued (fun x => (((1 + x ^ 6) ^ 5 : ℤ) : ℚ)) := hav
  have hDj : ∀ j : ℕ,
      IterIntValued (quartOp^[j] (fun x => (((1 + x ^ 6) ^ 5 : ℤ) : ℚ))) := by
    intro j
    induction j with
    | zero => exact hiter
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact ih.quartOp
  obtain ⟨m, hm⟩ := hDj 6 0 0
  rw [Function.iterate_zero_apply, quartOp_iterate, Pi.smul_apply,
    fwdDiff_iter_24_one_add_pow_six_pow_five] at hm
  have hq : (1338667115787133020121634950348800000 : ℚ) = 15625 * m := by
    norm_num at hm
    linarith
  have hz : (1338667115787133020121634950348800000 : ℤ) = 15625 * m := by
    exact_mod_cast hq
  omega

/-- **Generalized Tamarkin conjecture fails at `p = 5`.**  Zeb's witness from
MathOverflow 66959: `f(n) = 1 + n^6` is `5`-average-integral, but `f^5` is not. -/
theorem tamarkin_generalization_false_five :
    AvgIntegral 5 (fun n => 1 + n ^ 6) ∧ ¬ AvgIntegral 5 (fun n => (1 + n ^ 6) ^ 5) :=
  ⟨avgIntegral_five_one_add_pow_six, not_avgIntegral_five_one_add_pow_six_pow_five⟩

/-- **Refutation of Grinberg's conjecture (MathOverflow 66959).**  It is not true
that for every prime `p` and every `p`-average-integral `f : ℤ → ℤ`, the
pointwise power `n ↦ f(n)^p` is again `p`-average-integral. -/
theorem not_generalized_tamarkin :
    ¬ ∀ p : ℕ, p.Prime → ∀ f : ℤ → ℤ, AvgIntegral p f → AvgIntegral p (fun n => f n ^ p) :=
  fun h => not_avgIntegral_five_one_add_pow_six_pow_five
    (h 5 Nat.prime_five _ avgIntegral_five_one_add_pow_six)

end Candidates.TamarkinAverageIntegralRefutation
