/-
# Generalized Tamarkin conjecture at `p = 3`: the cube of a `3`-average-integral
# sequence is `3`-average-integral

Darij Grinberg, MathOverflow question 66959, *Generalization of Tamarkin's
ARO 1993, final round, problem 10/8: still a conjecture?*
(<https://mathoverflow.net/questions/66959>), asks whether `p`-average-integral
integer sequences are closed under pointwise `p`-th powers.
The averaging operator is `(F_p f)(n) = (f(n)+⋯+f(n+p-1))/p`;
average-integrality requires every nonnegative iterate to be integer-valued.

This module proves the case `p = 3` for arbitrary integer sequences, asserted
in Grinberg's question via an unpublished computation. Gjergji Zaimi's answer
gives a binomial-basis criterion for polynomials and discusses closure for
`p ∈ {2,3}`. The general claim for `p > 3` is false (zeb, same thread; see
`TamarkinAverageIntegralRefutation`).

## Proof route

* Characterization (`avgIntegral_three_iff`): with `D = Δ² / 3`,
  `F_3 = S + D` (`S` the unit shift), and `D`, `F_3` commute, so `f` is
  `3`-average-integral iff every `D^j f` is integer-valued iff
  `3^⌊k/2⌋ ∣ Δ^k f (n)` for all `k, n`.
* Newton expansion (`fwdDiff_iter_cube_eq`): with `b_i = Δ^i f (n)`,
  `Δ^K (f³) (n) = Σ_{i,j,l ≤ K} b_i b_j b_l c^K_{i,j,l}`, where `c^K_{i,j,l}`
  vanishes for `K > i + j + l`.
* Rotation (`three_pow_dvd_sum_cube`): the valuation deficit of each term is
  at most `1`; non-constant triples come in cyclic orbits of size `3`; on the
  diagonal Fermat gives `c^K_{i,i,i} ≡ [K = i] (mod 3)`.
-/
import Mathlib

set_option autoImplicit false

open Finset

namespace Candidates.TamarkinAverageIntegralCube

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

example : avgOp 3 (fun n => (n : ℚ) ^ 2) 0 = 5 / 3 := by
  simp only [avgOp, zero_add, Int.cast_natCast, sum_range_succ, range_one, sum_singleton,
      CharP.cast_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Nat.cast_one,
      one_pow, Nat.cast_ofNat, div_left_inj']
  norm_num

/-- `n ↦ n^2` is not `3`-average-integral: `F_3 (n^2) (0) = 5/3`. -/
example : ¬ AvgIntegral 3 (fun n => n ^ 2) := by
  intro h
  obtain ⟨m, hm⟩ := h 1 0
  simp only [Int.cast_pow, Function.iterate_one, avgOp, zero_add, Int.cast_natCast, sum_range_succ,
      range_one, sum_singleton, CharP.cast_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, Nat.cast_one, one_pow, Nat.cast_ofNat] at hm
  norm_num at hm
  have h2 : (5 : ℚ) = 3 * m := by linarith
  have h2' : (5 : ℤ) = 3 * m := by exact_mod_cast h2
  omega

/-- The identity sequence is `3`-average-integral: `F_3^k (n) = n + k`. -/
theorem avgIntegral_three_id : AvgIntegral 3 (fun n => n) := by
  have hstep : ∀ c : ℤ,
      avgOp 3 (fun x => ((x + c : ℤ) : ℚ)) = fun x => ((x + (c + 1) : ℤ) : ℚ) := by
    intro c
    funext n
    simp only [avgOp, Int.cast_add, Int.cast_natCast, sum_range_succ, range_one, sum_singleton,
        CharP.cast_eq_zero, add_zero, Nat.cast_one, Nat.cast_ofNat, Int.cast_one]
    ring
  have hk : ∀ k : ℕ, (avgOp 3)^[k] (fun x => ((x : ℤ) : ℚ)) = fun x => ((x + (k : ℤ) : ℤ) : ℚ) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, hstep]
      push_cast
      rfl
  intro k n
  exact ⟨n + k, by rw [hk k]⟩

/-! ## Characterization through `D = Δ² / 3` -/

/-- The operator `D f = Δ² f / 3`, written out with binomial coefficients;
`F_3 = S + D` with `S` the unit shift. -/
def sqOp (f : ℤ → ℚ) : ℤ → ℚ :=
  fun n => (f (n + 2) - 2 * f (n + 1) + f n) / 3

/-- A rational sequence is integer-valued. -/
def IsIntValued (h : ℤ → ℚ) : Prop :=
  ∀ n : ℤ, ∃ m : ℤ, h n = m

/-- `D` agrees with `(1/3) • Δ²` for Mathlib's forward difference. -/
theorem sqOp_eq_smul_fwdDiff_iter (f : ℤ → ℚ) :
    sqOp f = (1 / 3 : ℚ) • (fwdDiff (1 : ℤ))^[2] f := by
  funext n
  rw [Pi.smul_apply, fwdDiff_iter_eq_sum_shift]
  simp only [sqOp, one_div, Nat.reduceAdd, Int.reduceNeg, Int.nsmul_eq_mul, mul_one, zsmul_eq_mul,
      Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast, sum_range_succ,
      range_one, sum_singleton, tsub_zero, even_two, Even.neg_pow, one_pow, Nat.choose_zero_right,
      Nat.cast_one, CharP.cast_eq_zero, add_zero, one_mul, Nat.add_one_sub_one, pow_one,
      Nat.choose_succ_self_right, Nat.cast_ofNat, neg_mul, tsub_self, pow_zero, Nat.choose_self,
      smul_eq_mul]
  ring_nf

/-- Iterating `D` gives `(1/3)^k • Δ^(2k)`. -/
theorem sqOp_iterate (f : ℤ → ℚ) (k : ℕ) :
    sqOp^[k] f = (1 / 3 : ℚ) ^ k • (fwdDiff (1 : ℤ))^[2 * k] f := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, sqOp_eq_smul_fwdDiff_iter,
      fwdDiff_iter_const_smul, smul_smul, ← Function.iterate_add_apply, pow_succ,
      mul_comm ((1 / 3 : ℚ) ^ k)]
    congr 2
    ring

/-- Forward differences commute with the cast `ℤ → ℚ`. -/
theorem fwdDiff_iter_intCast (f : ℤ → ℤ) (k : ℕ) (n : ℤ) :
    (fwdDiff (1 : ℤ))^[k] (fun x => (f x : ℚ)) n = (((fwdDiff (1 : ℤ))^[k] f n : ℤ) : ℚ) := by
  rw [fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift]
  push_cast
  simp [zsmul_eq_mul]

/-- Pointwise decomposition `F_3 f (n) = f(n+1) + D f (n)`. -/
theorem avgOp_three_eq (f : ℤ → ℚ) (n : ℤ) : avgOp 3 f n = f (n + 1) + sqOp f n := by
  simp only [avgOp, sum_range_succ, range_one, sum_singleton, CharP.cast_eq_zero, add_zero,
      Nat.cast_one, Nat.cast_ofNat, sqOp]
  ring

/-- `D` commutes with `F_3`. -/
theorem sqOp_avgOp_three (h : ℤ → ℚ) : sqOp (avgOp 3 h) = avgOp 3 (sqOp h) := by
  funext n
  simp only [sqOp, avgOp, Finset.sum_range_succ, Finset.sum_range_zero, add_assoc]
  push_cast
  ring_nf

/-- `D` and `F_3` commute as self-maps of `ℤ → ℚ`. -/
theorem commute_sqOp_avgOp_three : Function.Commute sqOp (avgOp 3) := sqOp_avgOp_three

/-- If `g` and `D g` are integer-valued, so is `F_3 g`. -/
theorem IsIntValued.avgOp_three {g : ℤ → ℚ} (hg : IsIntValued g) (hd : IsIntValued (sqOp g)) :
    IsIntValued (avgOp 3 g) := by
  intro n
  obtain ⟨a, ha⟩ := hg (n + 1)
  obtain ⟨c, hc⟩ := hd n
  exact ⟨a + c, by rw [avgOp_three_eq, ha, hc]; push_cast; ring⟩

/-- If every `D`-iterate of `f` is integer-valued, then `f` is `3`-average-integral:
the class `{h | ∀ j, D^j h integer-valued}` is closed under `F_3`. -/
theorem avgIntegral_three_of_sqOp {f : ℤ → ℤ}
    (hf : ∀ j : ℕ, IsIntValued (sqOp^[j] (fun x => (f x : ℚ)))) : AvgIntegral 3 f := by
  have hstep : ∀ h : ℤ → ℚ, (∀ j : ℕ, IsIntValued (sqOp^[j] h)) →
      ∀ j : ℕ, IsIntValued (sqOp^[j] (avgOp 3 h)) := by
    intro h hh j
    rw [commute_sqOp_avgOp_three.iterate_left j h]
    refine (hh j).avgOp_three ?_
    rw [← Function.iterate_succ_apply' sqOp j h]
    exact hh (j + 1)
  have hall : ∀ k : ℕ, ∀ j : ℕ,
      IsIntValued (sqOp^[j] ((avgOp 3)^[k] (fun x => (f x : ℚ)))) := by
    intro k
    induction k with
    | zero => exact hf
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact hstep _ ih
  intro k n
  exact hall k 0 n

/-- If `f` is `3`-average-integral, every `D`-iterate of `f` is integer-valued:
`D h = F_3 h - h(·+1)` and `D` commutes with `F_3`. -/
theorem sqOp_iterate_isIntValued_of_avgIntegral_three {f : ℤ → ℤ} (hf : AvgIntegral 3 f)
    (j : ℕ) : IsIntValued (sqOp^[j] (fun x => (f x : ℚ))) := by
  have hstep : ∀ h : ℤ → ℚ, (∀ k : ℕ, IsIntValued ((avgOp 3)^[k] h)) →
      ∀ k : ℕ, IsIntValued ((avgOp 3)^[k] (sqOp h)) := by
    intro h hh k n
    rw [commute_sqOp_avgOp_three.symm.iterate_left k h]
    obtain ⟨a, ha⟩ := hh (k + 1) n
    obtain ⟨c, hc⟩ := hh k (n + 1)
    refine ⟨a - c, ?_⟩
    have e := avgOp_three_eq ((avgOp 3)^[k] h) n
    rw [← Function.iterate_succ_apply' (avgOp 3) k h, ha, hc] at e
    push_cast
    linarith
  have hall : ∀ j : ℕ, ∀ k : ℕ, IsIntValued ((avgOp 3)^[k] (sqOp^[j] (fun x => (f x : ℚ)))) := by
    intro j
    induction j with
    | zero => exact hf
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact hstep _ ih
  exact hall j 0

/-- `D^j f` is integer-valued iff `3^j ∣ Δ^(2j) f (n)` for every `n`. -/
theorem isIntValued_sqOp_iterate_iff (f : ℤ → ℤ) (j : ℕ) :
    IsIntValued (sqOp^[j] (fun x => (f x : ℚ)))
      ↔ ∀ n : ℤ, (3 : ℤ) ^ j ∣ (fwdDiff (1 : ℤ))^[2 * j] f n := by
  have hval : ∀ n : ℤ, sqOp^[j] (fun x => (f x : ℚ)) n
      = (1 / 3 : ℚ) ^ j * (((fwdDiff (1 : ℤ))^[2 * j] f n : ℤ) : ℚ) := by
    intro n
    rw [sqOp_iterate, Pi.smul_apply, fwdDiff_iter_intCast, smul_eq_mul]
  have h3 : (3 : ℚ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
  constructor
  · intro h n
    obtain ⟨m, hm⟩ := h n
    rw [hval] at hm
    refine ⟨m, ?_⟩
    have hq : (((fwdDiff (1 : ℤ))^[2 * j] f n : ℤ) : ℚ) = (3 : ℚ) ^ j * m := by
      rw [← hm, ← mul_assoc, one_div, inv_pow, mul_inv_cancel₀ h3, one_mul]
    exact_mod_cast hq
  · intro h n
    obtain ⟨m, hm⟩ := h n
    refine ⟨m, ?_⟩
    rw [hval, hm]
    push_cast
    rw [← mul_assoc, one_div, inv_pow, inv_mul_cancel₀ h3, one_mul]

/-- **Characterization.** An integer sequence `f` is `3`-average-integral iff
`3^⌊k/2⌋ ∣ Δ^k f (n)` for all `k ≥ 0` and all `n ∈ ℤ`. -/
theorem avgIntegral_three_iff (f : ℤ → ℤ) :
    AvgIntegral 3 f ↔ ∀ k : ℕ, ∀ n : ℤ, (3 : ℤ) ^ (k / 2) ∣ (fwdDiff (1 : ℤ))^[k] f n := by
  constructor
  · intro hf k n
    have hj := (isIntValued_sqOp_iterate_iff f (k / 2)).1
      (sqOp_iterate_isIntValued_of_avgIntegral_three hf (k / 2))
    rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
    · have e : 2 * j / 2 = j := by omega
      rw [e] at hj ⊢
      exact hj n
    · have e : (2 * j + 1) / 2 = j := by omega
      rw [e] at hj ⊢
      rw [Function.iterate_succ_apply']
      exact dvd_sub (hj (n + 1)) (hj n)
  · intro h
    refine avgIntegral_three_of_sqOp fun j => (isIntValued_sqOp_iterate_iff f j).2 fun n => ?_
    have e : 2 * j / 2 = j := by omega
    simpa [e] using h (2 * j) n

/-! ## The cube: Newton expansion and the rotation argument -/

/-- The coefficient `c^K_{i,j,l} = Σ_{t=0}^{K} (-1)^(K-t) C(K,t) C(t,i) C(t,j) C(t,l)`,
i.e. `Δ^K` at `0` of `t ↦ C(t,i) C(t,j) C(t,l)`.  With `b_i = Δ^i f (n)`,
`Δ^K (f³) (n) = Σ_{i,j,l ≤ K} b_i b_j b_l c^K_{i,j,l}` (`fwdDiff_iter_cube_eq`). -/
def cubeCoeff (K i j l : ℕ) : ℤ :=
  ∑ t ∈ range (K + 1), (-1 : ℤ) ^ (K - t) * K.choose t * (t.choose i * t.choose j * t.choose l)

/-- `Δ² (t³) (0) = 6`, `Δ³ (t³) (0) = 6`, `Δ⁴ (t³) (0) = 0`, and
`Δ² (t · C(t,2)²) (0) = 2`. -/
example : cubeCoeff 2 1 1 1 = 6 ∧ cubeCoeff 3 1 1 1 = 6 ∧ cubeCoeff 4 1 1 1 = 0
    ∧ cubeCoeff 2 1 2 2 = 2 := by
  decide

/-- `c^K_{i,j,l} = 0` when `i + j + l < K`: it is the `K`-th difference of a
polynomial of degree `i + j + l` (times `i! j! l!`). -/
theorem cubeCoeff_eq_zero {K i j l : ℕ} (h : i + j + l < K) : cubeCoeff K i j l = 0 := by
  let P : Polynomial ℤ := descPochhammer ℤ i * descPochhammer ℤ j * descPochhammer ℤ l
  have hdeg : P.natDegree < K := by
    have h1 : P.natDegree ≤ i + j + l := by
      refine Polynomial.natDegree_mul_le.trans ?_
      refine add_le_add (Polynomial.natDegree_mul_le.trans ?_) ?_
      · simp [descPochhammer_natDegree]
      · simp [descPochhammer_natDegree]
    omega
  have h0 := congrFun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hdeg) 0
  rw [fwdDiff_iter_eq_sum_shift] at h0
  have key : ∀ t : ℕ, P.eval ((0 : ℤ) + t • (1 : ℤ))
      = (i.factorial * j.factorial * l.factorial : ℤ) * (t.choose i * t.choose j * t.choose l) := by
    intro t
    simp only [P, zero_add, nsmul_eq_mul, mul_one, Polynomial.eval_mul,
      descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    ring
  simp only [key, smul_eq_mul, Pi.zero_apply] at h0
  have hfac : (i.factorial * j.factorial * l.factorial : ℤ) ≠ 0 := by positivity
  have : (i.factorial * j.factorial * l.factorial : ℤ) * cubeCoeff K i j l = 0 := by
    rw [← h0, cubeCoeff, mul_sum]
    refine sum_congr rfl fun t _ => ?_
    ring
  exact (mul_eq_zero.1 this).resolve_left hfac

/-- Fermat at `p = 3`: `3 ∣ x³ - x`. -/
theorem three_dvd_cube_sub (x : ℤ) : (3 : ℤ) ∣ x ^ 3 - x := by
  have h : ((x ^ 3 - x : ℤ) : ZMod 3) = 0 := by
    push_cast
    rw [ZMod.pow_card, sub_self]
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd (x ^ 3 - x) 3).1 h

/-- Diagonal coefficients: `c^K_{i,i,i} ≡ [K = i] (mod 3)`, so `3 ∣ c^K_{i,i,i}`
when `K ≠ i` (Fermat, `C(t,i)³ ≡ C(t,i)`). -/
theorem three_dvd_cubeCoeff_diag {K i : ℕ} (h : K ≠ i) : (3 : ℤ) ∣ cubeCoeff K i i i := by
  have h1 := fwdDiff_iter_choose_zero i K
  rw [fwdDiff_iter_eq_sum_shift, if_neg h] at h1
  simp only [zero_add, smul_eq_mul, mul_one] at h1
  have h2 : cubeCoeff K i i i = cubeCoeff K i i i - ∑ k ∈ range (K + 1),
      (-1 : ℤ) ^ (K - k) * (K.choose k) * ((k.choose i : ℕ) : ℤ) := by
    rw [h1, sub_zero]
  rw [h2, cubeCoeff, ← sum_sub_distrib]
  refine dvd_sum fun t _ => ?_
  have h3 : (-1 : ℤ) ^ (K - t) * K.choose t * (t.choose i * t.choose i * t.choose i)
      - (-1 : ℤ) ^ (K - t) * K.choose t * ((t.choose i : ℕ) : ℤ)
      = (-1 : ℤ) ^ (K - t) * K.choose t * (((t.choose i : ℕ) : ℤ) ^ 3 - (t.choose i : ℕ)) := by
    ring
  rw [h3]
  exact dvd_mul_of_dvd_right (three_dvd_cube_sub _) _

/-- `c^K_{i,j,l}` is invariant under cyclic rotation of `(i, j, l)`. -/
theorem cubeCoeff_rotate (K i j l : ℕ) : cubeCoeff K i j l = cubeCoeff K j l i := by
  unfold cubeCoeff
  refine sum_congr rfl fun t _ => ?_
  ring

/-- The cube of a finite sum as a triple sum. -/
theorem sum_pow_three (s : Finset ℕ) (a : ℕ → ℤ) :
    (∑ i ∈ s, a i) ^ 3 = ∑ i ∈ s, ∑ j ∈ s, ∑ l ∈ s, a i * a j * a l := by
  rw [pow_three, sum_mul]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_mul_sum, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun l _ => ?_
  ring

/-- Newton expansion: `Δ^K (f³) (n) = Σ_{i,j,l ≤ K} b_i b_j b_l c^K_{i,j,l}` with
`b_i = Δ^i f (n)`. -/
theorem fwdDiff_iter_cube_eq (f : ℤ → ℤ) (K : ℕ) (n : ℤ) :
    (fwdDiff (1 : ℤ))^[K] (fun x => f x ^ 3) n = ∑ i ∈ range (K + 1), ∑ j ∈ range (K + 1),
      ∑ l ∈ range (K + 1), (fwdDiff (1 : ℤ))^[i] f n * (fwdDiff (1 : ℤ))^[j] f n
        * (fwdDiff (1 : ℤ))^[l] f n * cubeCoeff K i j l := by
  have hshift : ∀ t ∈ range (K + 1), f (n + t • (1 : ℤ))
      = ∑ j ∈ range (K + 1), (t.choose j : ℤ) * (fwdDiff (1 : ℤ))^[j] f n := by
    intro t ht
    rw [shift_eq_sum_fwdDiff_iter (1 : ℤ) f t n]
    have hsub : range (t + 1) ⊆ range (K + 1) := by
      have : t < K + 1 := mem_range.1 ht
      exact range_subset_range.2 (by omega)
    rw [sum_subset hsub]
    · exact sum_congr rfl fun j _ => nsmul_eq_mul _ _
    · intro j hj hjt
      have hlt : t < j := by
        simp only [mem_range] at hj hjt
        omega
      simp [Nat.choose_eq_zero_of_lt hlt]
  rw [fwdDiff_iter_eq_sum_shift, sum_congr rfl fun t ht => by rw [hshift t ht]]
  simp only [sum_pow_three, smul_eq_mul, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun l _ => ?_
  unfold cubeCoeff
  rw [mul_sum]
  refine sum_congr rfl fun t _ => ?_
  ring

/-- Off-diagonal estimate: if `3^⌊i/2⌋ ∣ b_i` for all `i`, then
`3^⌊K/2⌋ ∣ 3 · b_i b_j b_l c^K_{i,j,l}` for every triple; the valuation deficit
is at most `1`. -/
theorem three_pow_dvd_mul_three (b : ℕ → ℤ) (hb : ∀ i, (3 : ℤ) ^ (i / 2) ∣ b i)
    (K i j l : ℕ) : (3 : ℤ) ^ (K / 2) ∣ 3 * (b i * b j * b l * cubeCoeff K i j l) := by
  by_cases h : i + j + l < K
  · simp [cubeCoeff_eq_zero h]
  · have hd : (3 : ℤ) ^ (i / 2 + j / 2 + l / 2) ∣ b i * b j * b l := by
      rw [pow_add, pow_add]
      exact mul_dvd_mul (mul_dvd_mul (hb i) (hb j)) (hb l)
    have hle : (3 : ℤ) ^ (K / 2) ∣ 3 ^ (i / 2 + j / 2 + l / 2 + 1) := pow_dvd_pow 3 (by omega)
    refine hle.trans ?_
    rw [pow_succ']
    exact mul_dvd_mul_left 3 (dvd_mul_of_dvd_left hd _)

/-- Diagonal estimate: if `3^⌊i/2⌋ ∣ b_i` for all `i`, then
`3^⌊K/2⌋ ∣ b_i³ c^K_{i,i,i}`.  The deficit `1` occurs only for odd `i` and
`K ∈ {3i-1, 3i}`, where `3 ∣ c^K_{i,i,i}` supplies the missing factor. -/
theorem three_pow_dvd_diag (b : ℕ → ℤ) (hb : ∀ i, (3 : ℤ) ^ (i / 2) ∣ b i)
    (K i : ℕ) : (3 : ℤ) ^ (K / 2) ∣ b i * b i * b i * cubeCoeff K i i i := by
  have hd : (3 : ℤ) ^ (i / 2 + i / 2 + i / 2) ∣ b i * b i * b i := by
    rw [pow_add, pow_add]
    exact mul_dvd_mul (mul_dvd_mul (hb i) (hb i)) (hb i)
  by_cases h : i + i + i < K
  · simp [cubeCoeff_eq_zero h]
  by_cases h2 : K / 2 ≤ i / 2 + i / 2 + i / 2
  · exact (pow_dvd_pow 3 h2).trans (dvd_mul_of_dvd_left hd _)
  · have hKi : K ≠ i := by omega
    have hle : (3 : ℤ) ^ (K / 2) ∣ 3 ^ (i / 2 + i / 2 + i / 2 + 1) := pow_dvd_pow 3 (by omega)
    refine hle.trans ?_
    rw [pow_succ]
    exact mul_dvd_mul hd (three_dvd_cubeCoeff_diag hKi)

/-- **Core divisibility.** If `3^⌊i/2⌋ ∣ b_i` for all `i`, then
`3^⌊K/2⌋ ∣ Σ_{i,j,l ≤ K} b_i b_j b_l c^K_{i,j,l}`.  Non-constant triples split
into three cyclic copies of the fundamental domain `{i < j ∧ i ≤ l}`, which
supplies a factor `3`. -/
theorem three_pow_dvd_sum_cube (b : ℕ → ℤ) (hb : ∀ i, (3 : ℤ) ^ (i / 2) ∣ b i) (K : ℕ) :
    (3 : ℤ) ^ (K / 2) ∣ ∑ i ∈ range (K + 1), ∑ j ∈ range (K + 1), ∑ l ∈ range (K + 1),
      b i * b j * b l * cubeCoeff K i j l := by
  set s := range (K + 1) with hs
  let T : ℕ → ℕ → ℕ → ℤ := fun i j l => b i * b j * b l * cubeCoeff K i j l
  have hrot : ∀ i j l, T i j l = T j l i := by
    intro i j l
    simp only [T]
    rw [cubeCoeff_rotate]
    ring
  let D : ℕ → ℕ → ℕ → ℤ := fun i j l => if i = j ∧ j = l then T i j l else 0
  let G : ℕ → ℕ → ℕ → ℤ := fun i j l => if i < j ∧ i ≤ l then T i j l else 0
  have hsplit : ∀ i j l, T i j l = D i j l + G i j l + G j l i + G l i j := by
    intro i j l
    simp only [D, G]
    rw [← hrot i j l, hrot l i j]
    split_ifs <;> omega
  have e : ∑ i ∈ s, ∑ j ∈ s, ∑ l ∈ s, T i j l
      = ∑ i ∈ s, ∑ j ∈ s, ∑ l ∈ s, D i j l + ∑ i ∈ s, ∑ j ∈ s, ∑ l ∈ s, G i j l
        + ∑ i ∈ s, ∑ j ∈ s, ∑ l ∈ s, G j l i + ∑ i ∈ s, ∑ j ∈ s, ∑ l ∈ s, G l i j := by
    simp only [← sum_add_distrib]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun l _ => hsplit i j l
  have e1 : ∑ i ∈ s, ∑ j ∈ s, ∑ l ∈ s, G j l i = ∑ i ∈ s, ∑ j ∈ s, ∑ l ∈ s, G i j l := by
    refine sum_comm.trans ?_
    exact sum_congr rfl fun j _ => sum_comm
  have e2 : ∑ i ∈ s, ∑ j ∈ s, ∑ l ∈ s, G l i j = ∑ i ∈ s, ∑ j ∈ s, ∑ l ∈ s, G i j l := by
    refine (sum_congr rfl fun i _ => sum_comm).trans ?_
    exact sum_comm
  have hD : (3 : ℤ) ^ (K / 2) ∣ ∑ i ∈ s, ∑ j ∈ s, ∑ l ∈ s, D i j l := by
    refine dvd_sum fun i _ => dvd_sum fun j _ => dvd_sum fun l _ => ?_
    simp only [D]
    split_ifs with hijl
    · obtain ⟨rfl, rfl⟩ := hijl
      exact three_pow_dvd_diag b hb K i
    · exact dvd_zero _
  have hG : (3 : ℤ) ^ (K / 2) ∣ 3 * ∑ i ∈ s, ∑ j ∈ s, ∑ l ∈ s, G i j l := by
    simp only [mul_sum]
    refine dvd_sum fun i _ => dvd_sum fun j _ => dvd_sum fun l _ => ?_
    simp only [G]
    split_ifs
    · exact three_pow_dvd_mul_three b hb K i j l
    · simp
  change (3 : ℤ) ^ (K / 2) ∣ ∑ i ∈ s, ∑ j ∈ s, ∑ l ∈ s, T i j l
  rw [e, e1, e2]
  have e3 : ∑ i ∈ s, ∑ j ∈ s, ∑ l ∈ s, D i j l + ∑ i ∈ s, ∑ j ∈ s, ∑ l ∈ s, G i j l
      + ∑ i ∈ s, ∑ j ∈ s, ∑ l ∈ s, G i j l + ∑ i ∈ s, ∑ j ∈ s, ∑ l ∈ s, G i j l
      = ∑ i ∈ s, ∑ j ∈ s, ∑ l ∈ s, D i j l + 3 * ∑ i ∈ s, ∑ j ∈ s, ∑ l ∈ s, G i j l := by ring
  rw [e3]
  exact dvd_add hD hG

/-- If `3^⌊k/2⌋ ∣ Δ^k f (n)` for all `k, n`, the same holds for `f³`. -/
theorem three_pow_dvd_fwdDiff_iter_cube {f : ℤ → ℤ}
    (hf : ∀ k n, (3 : ℤ) ^ (k / 2) ∣ (fwdDiff (1 : ℤ))^[k] f n) (K : ℕ) (n : ℤ) :
    (3 : ℤ) ^ (K / 2) ∣ (fwdDiff (1 : ℤ))^[K] (fun x => f x ^ 3) n := by
  rw [fwdDiff_iter_cube_eq]
  exact three_pow_dvd_sum_cube (fun i => (fwdDiff (1 : ℤ))^[i] f n) (fun i => hf i n) K

/-! ## Main theorem -/

/-- **Tamarkin-type closure at `p = 3`** (MathOverflow 66959, Grinberg's
conjecture at `p = 3`, asserted there via an unpublished computation): if
`f : ℤ → ℤ` is `3`-average-integral, then so is `n ↦ f(n)³`. -/
theorem avgIntegral_three_pow_three {f : ℤ → ℤ} (hf : AvgIntegral 3 f) :
    AvgIntegral 3 (fun n => f n ^ 3) :=
  (avgIntegral_three_iff _).2
    (three_pow_dvd_fwdDiff_iter_cube ((avgIntegral_three_iff f).1 hf))

/-- Non-vacuity of the hypothesis of `avgIntegral_three_pow_three`: the identity
sequence satisfies it, giving that `n ↦ n³` is `3`-average-integral. -/
example : AvgIntegral 3 (fun n => n ^ 3) := avgIntegral_three_pow_three avgIntegral_three_id

end Candidates.TamarkinAverageIntegralCube
