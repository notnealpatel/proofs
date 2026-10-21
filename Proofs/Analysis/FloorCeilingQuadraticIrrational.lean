/-
# Bényi–Ćurgus, Conjecture 4.5 for quadratic irrationals

## Source

Árpád Bényi and Branko Ćurgus, *Floor, ceiling and the space between*,
arXiv:2507.14244, Section 4.2.  For `α > 0` the paper defines
`f_α : ℕ → ℤ`, `f_α(n) = ⌊α² n⌋ - ⌊α ⌊α n⌋⌋` (equation (1.2)), with
`ℕ` the positive integers and `Range(f_α) = {f_α(n) : n ∈ ℕ}`.

Conjecture 4.5 (verbatim): "For all irrational numbers α ∈ (0, 1) we have
Range(f_α) = {0, 1}."  Remark 4.1: by Corollary 2.2 this is equivalent to
`1 ∈ Range(f_α)`.

## Status

Conjecture 4.5 is open in the paper (recorded 2026-10-21); the paper proves
only the partial result Proposition 4.6 (right neighbourhoods of
square-root rationals).  This module proves the special case where `α`
satisfies a rational quadratic relation `α² = u α + v` with `u v : ℚ`,
which covers every quadratic irrational in `(0, 1)` (and every `α` with
`α²` rational).  The argument is ours, not the paper's.

## Argument

Pick `D ≥ 1` with `D u = a` and `D v = b` integers, so `D α² = a α + b`.
Put `w = a - α D`, which is nonzero because `α` is irrational.  For
`n = D m + 1` and `s = m α - k` (`k` an integer) one computes

* `α n = D k + (D s + α)`,
* `α² n = (a k + b m) + (a s + α²)`,
* `α ⌊α n⌋ = (a k + b m) + s w` whenever `⌊α n⌋ = D k`.

So if `s` is small with `s w < 0`, then `f_α(n) = 1`.  Such `s` exist
on either side of `0` by Dirichlet's approximation theorem and the
irrationality of `α` (one-dimensional density of `m α mod 1`).
-/
import Mathlib

set_option autoImplicit false

namespace FloorCeilingQuadraticIrrational

/-- The Bényi–Ćurgus function `f_α(n) = ⌊α² n⌋ - ⌊α ⌊α n⌋⌋`
(arXiv:2507.14244, equation (1.2)). -/
noncomputable def f (α : ℝ) (n : ℕ) : ℤ := ⌊α ^ 2 * n⌋ - ⌊α * ⌊α * n⌋⌋

/-- Ground truth: `f_{3/2}(1) = ⌊9/4⌋ - ⌊3/2 · ⌊3/2⌋⌋ = 2 - 1 = 1`. -/
example : f (3 / 2) 1 = 1 := by
  have h1 : ⌊(3 / 2 : ℝ) ^ 2 * ((1 : ℕ) : ℝ)⌋ = 2 := by
    rw [Int.floor_eq_iff]; norm_num
  have h2 : ⌊(3 / 2 : ℝ) * ((1 : ℕ) : ℝ)⌋ = 1 := by
    rw [Int.floor_eq_iff]; norm_num
  have h3 : ⌊(3 / 2 : ℝ) * ((1 : ℤ) : ℝ)⌋ = 1 := by
    rw [Int.floor_eq_iff]; norm_num
  rw [f, h1, h2, h3]; norm_num

/-- Ground truth: `f_{3/2}(2) = ⌊9/2⌋ - ⌊3/2 · ⌊3⌋⌋ = 4 - 4 = 0`. -/
example : f (3 / 2) 2 = 0 := by
  have h1 : ⌊(3 / 2 : ℝ) ^ 2 * ((2 : ℕ) : ℝ)⌋ = 4 := by
    rw [Int.floor_eq_iff]; norm_num
  have h2 : ⌊(3 / 2 : ℝ) * ((2 : ℕ) : ℝ)⌋ = 3 := by
    rw [Int.floor_eq_iff]; norm_num
  have h3 : ⌊(3 / 2 : ℝ) * ((3 : ℤ) : ℝ)⌋ = 4 := by
    rw [Int.floor_eq_iff]; norm_num
  rw [f, h1, h2, h3]; norm_num

/-- Reduction: `f_α(n) = ⌈α {α n} - {α² n}⌉`, with `{x}` the fractional
part. -/
theorem f_eq_ceil (α : ℝ) (n : ℕ) :
    f α n = ⌈α * Int.fract (α * n) - Int.fract (α ^ 2 * n)⌉ := by
  have hrw : α * Int.fract (α * n) - Int.fract (α ^ 2 * n) =
      (⌊α ^ 2 * (n : ℝ)⌋ : ℝ) + -(α * (⌊α * (n : ℝ)⌋ : ℝ)) := by
    rw [Int.fract, Int.fract]; ring
  rw [hrw, Int.ceil_intCast_add, Int.ceil_neg, f]
  ring

/-- Dirichlet plus irrationality: for every `δ > 0` some positive multiple
`k α` lies within `δ` of an integer `j` without being equal to it. -/
theorem exists_mul_sub_ne_zero_abs_lt {α : ℝ} (hα : Irrational α) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ k : ℕ, 0 < k ∧ ∃ j : ℤ, (k : ℝ) * α - j ≠ 0 ∧ |(k : ℝ) * α - j| < δ := by
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  obtain ⟨k, hk0, -, hk⟩ :=
    Real.exists_nat_abs_mul_sub_round_le α (Nat.succ_pos N)
  refine ⟨k, hk0, round ((k : ℝ) * α), ?_, ?_⟩
  · intro h
    exact (hα.natCast_mul hk0.ne').ne_int _ (sub_eq_zero.mp h)
  · refine lt_of_le_of_lt hk (lt_of_le_of_lt ?_ hN)
    gcongr
    linarith

/-- From a multiple `k β` slightly above an integer one gets a multiple
`m β` slightly below an integer: take `m = q k` with `q = ⌈1/e⌉ - 1`. -/
theorem exists_mul_sub_mem_Ioo_neg {β δ : ℝ} (hδ1 : δ ≤ 1) {k : ℕ} (hk : 0 < k)
    {j : ℤ} (he0 : 0 < (k : ℝ) * β - j) (heδ : (k : ℝ) * β - j < δ) :
    ∃ m : ℕ, 0 < m ∧ ∃ i : ℤ, -δ < (m : ℝ) * β - i ∧ (m : ℝ) * β - i < 0 := by
  set e : ℝ := (k : ℝ) * β - j with he
  have he1 : e < 1 := lt_of_lt_of_le heδ hδ1
  have hinv : 1 < 1 / e := by rw [lt_div_iff₀ he0]; linarith
  set c : ℕ := ⌈1 / e⌉₊ with hc
  have hc_ge : 1 / e ≤ c := Nat.le_ceil _
  have hc_lt : (c : ℝ) < 1 / e + 1 := Nat.ceil_lt_add_one (by positivity)
  have hc2 : 2 ≤ c := by
    have : (1 : ℝ) < c := lt_of_lt_of_le hinv hc_ge
    exact_mod_cast this
  set q : ℕ := c - 1 with hq
  have hqR : (q : ℝ) = c - 1 := by
    rw [hq, Nat.cast_sub (by omega), Nat.cast_one]
  have hq_lt : (q : ℝ) * e < 1 := by
    have : (q : ℝ) < 1 / e := by linarith
    rw [lt_div_iff₀ he0] at this
    exact this
  have hq_ge : 1 - e ≤ (q : ℝ) * e := by
    have : 1 / e - 1 ≤ (q : ℝ) := by linarith
    have h' : (1 / e - 1) * e ≤ (q : ℝ) * e := mul_le_mul_of_nonneg_right this he0.le
    rwa [sub_mul, one_div, inv_mul_cancel₀ he0.ne', one_mul] at h'
  refine ⟨q * k, Nat.mul_pos (by omega) hk, q * j + 1, ?_, ?_⟩
  · have hid : ((q * k : ℕ) : ℝ) * β - ((q * j + 1 : ℤ) : ℝ) = (q : ℝ) * e - 1 := by
      rw [he]; push_cast; ring
    rw [hid]; linarith
  · have hid : ((q * k : ℕ) : ℝ) * β - ((q * j + 1 : ℤ) : ℝ) = (q : ℝ) * e - 1 := by
      rw [he]; push_cast; ring
    rw [hid]; linarith

/-- Two-sided one-dimensional density of `m α mod 1` over positive `m`:
for `δ > 0` there are positive multiples of an irrational `α` lying in
`(i, i + δ)` and in `(i - δ, i)` for suitable integers `i`. -/
theorem exists_mul_sub_mem_Ioo {α : ℝ} (hα : Irrational α) {δ : ℝ} (hδ : 0 < δ) :
    (∃ m : ℕ, 0 < m ∧ ∃ i : ℤ, 0 < (m : ℝ) * α - i ∧ (m : ℝ) * α - i < δ) ∧
    (∃ m : ℕ, 0 < m ∧ ∃ i : ℤ, -δ < (m : ℝ) * α - i ∧ (m : ℝ) * α - i < 0) := by
  set δ' : ℝ := min δ 1 with hδ'
  have hδ'0 : 0 < δ' := lt_min hδ one_pos
  have hδ'δ : δ' ≤ δ := min_le_left _ _
  have hδ'1 : δ' ≤ 1 := min_le_right _ _
  obtain ⟨k, hk, j, hne, habs⟩ := exists_mul_sub_ne_zero_abs_lt hα hδ'0
  rcases hne.lt_or_gt with hneg | hpos
  · -- `k α` lies just below `j`; flip using `-α`.
    have h0 : 0 < (k : ℝ) * (-α) - ((-j : ℤ) : ℝ) := by push_cast; linarith
    have h1 : (k : ℝ) * (-α) - ((-j : ℤ) : ℝ) < δ' := by
      push_cast; linarith [neg_abs_le ((k : ℝ) * α - j)]
    obtain ⟨m, hm, i, hi1, hi2⟩ := exists_mul_sub_mem_Ioo_neg hδ'1 hk h0 h1
    refine ⟨⟨m, hm, -i, ?_, ?_⟩, ⟨k, hk, j, ?_, hneg⟩⟩
    · push_cast; linarith
    · push_cast; linarith
    · linarith [neg_abs_le ((k : ℝ) * α - j)]
  · -- `k α` lies just above `j`.
    have h1 : (k : ℝ) * α - j < δ' := lt_of_le_of_lt (le_abs_self _) habs
    obtain ⟨m, hm, i, hi1, hi2⟩ := exists_mul_sub_mem_Ioo_neg hδ'1 hk hpos h1
    exact ⟨⟨k, hk, j, hpos, by linarith⟩, ⟨m, hm, i, by linarith, hi2⟩⟩

/-- Core computation.  Let `D α² = a α + b` with `a b` integers, `w = a - α D`,
and `s = m α - k`.  If `s` is small (the three bounds below) and `s w < 0`,
then `f_α(D m + 1) = 1`. -/
theorem f_eq_one_of_approx {α : ℝ} (h0 : 0 < α) (h1 : α < 1) {D : ℕ} {a b : ℤ}
    (hD : (D : ℝ) * α ^ 2 = a * α + b) (m : ℕ) (k : ℤ)
    (hs1 : -α ≤ D * ((m : ℝ) * α - k)) (hs2 : D * ((m : ℝ) * α - k) < 1 - α)
    (hs3 : -α ^ 2 ≤ a * ((m : ℝ) * α - k))
    (hs5 : ((m : ℝ) * α - k) * (a - α * D) < 0) :
    f α (D * m + 1) = 1 := by
  generalize hs : (m : ℝ) * α - k = s at hs1 hs2 hs3 hs5
  have hmα : (m : ℝ) * α = s + k := by rw [← hs]; ring
  have hfl1 : ⌊α * ((D * m + 1 : ℕ) : ℝ)⌋ = D * k := by
    have hid : α * ((D * m + 1 : ℕ) : ℝ) = ((D * k : ℤ) : ℝ) + (D * s + α) := by
      push_cast
      linear_combination (D : ℝ) * hmα
    rw [Int.floor_eq_iff, hid]
    constructor <;> linarith
  have hkey : α * (D * s + α) < 1 := by
    have : α * (D * s + α) < α * 1 := mul_lt_mul_of_pos_left (by linarith) h0
    linarith
  have hfl2 : ⌊α ^ 2 * ((D * m + 1 : ℕ) : ℝ)⌋ = a * k + b * m := by
    have hid : α ^ 2 * ((D * m + 1 : ℕ) : ℝ) =
        ((a * k + b * m : ℤ) : ℝ) + (a * s + α ^ 2) := by
      push_cast
      linear_combination (m : ℝ) * hD + (a : ℝ) * hmα
    have hsplit : a * s + α ^ 2 = α * (D * s + α) + s * (a - α * D) := by ring
    rw [Int.floor_eq_iff, hid]
    constructor <;> linarith
  have hfl3 : ⌊α * ((D * k : ℤ) : ℝ)⌋ = a * k + b * m - 1 := by
    have hid : α * ((D * k : ℤ) : ℝ) = ((a * k + b * m - 1 : ℤ) : ℝ) + (1 + s * (a - α * D)) := by
      push_cast
      linear_combination (m : ℝ) * hD + ((a : ℝ) - α * D) * hmα
    rw [Int.floor_eq_iff, hid]
    constructor <;> linarith
  rw [f, hfl1, hfl2, hfl3]
  ring

/-- Integer form of the quadratic relation: if `α² = u α + v` with `u v : ℚ`,
then `D α² = a α + b` for the positive integer `D = den u · den v` and
integers `a = num u · den v`, `b = num v · den u`. -/
theorem exists_int_relation {α : ℝ} {u v : ℚ} (huv : α ^ 2 = u * α + v) :
    ∃ D : ℕ, 0 < D ∧ ∃ a b : ℤ, (D : ℝ) * α ^ 2 = a * α + b := by
  have hu : (u : ℝ) * (u.den : ℝ) = (u.num : ℝ) := by
    have h := congrArg (fun x : ℚ => (x : ℝ)) (Rat.mul_den_eq_num u)
    push_cast at h
    exact h
  have hv : (v : ℝ) * (v.den : ℝ) = (v.num : ℝ) := by
    have h := congrArg (fun x : ℚ => (x : ℝ)) (Rat.mul_den_eq_num v)
    push_cast at h
    exact h
  refine ⟨u.den * v.den, Nat.mul_pos u.den_pos v.den_pos, u.num * v.den,
    v.num * u.den, ?_⟩
  rw [huv]
  push_cast
  linear_combination (v.den : ℝ) * α * hu + (u.den : ℝ) * hv

/-- **Conjecture 4.5 of Bényi–Ćurgus (arXiv:2507.14244), quadratic case,
`1 ∈ Range(f_α)` form (Remark 4.1).**  If `α ∈ (0, 1)` is irrational and
`α² = u α + v` for some rationals `u, v`, then `f_α(n) = 1` for some
positive integer `n`. -/
theorem exists_f_eq_one {α : ℝ} (hα : Irrational α) (h0 : 0 < α) (h1 : α < 1)
    (u v : ℚ) (huv : α ^ 2 = u * α + v) : ∃ n : ℕ, 0 < n ∧ f α n = 1 := by
  obtain ⟨D, hD0, a, b, hD⟩ := exists_int_relation huv
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD0
  set w : ℝ := (a : ℝ) - α * D with hw
  have hw0 : w ≠ 0 := by
    intro h
    have hαD : α * (D : ℝ) = a := by linarith
    exact (hα.mul_natCast hD0.ne').ne_int a hαD
  have hA : (0 : ℝ) < |(a : ℝ)| + 1 := by positivity
  set δ : ℝ := min (min (α / D) ((1 - α) / D)) (α ^ 2 / (|(a : ℝ)| + 1)) with hδ
  have hδ0 : 0 < δ := by
    have h1α : 0 < 1 - α := by linarith
    positivity
  have key : ∀ (m : ℕ) (k : ℤ), |(m : ℝ) * α - k| < δ →
      ((m : ℝ) * α - k) * w < 0 → f α (D * m + 1) = 1 := by
    intro m k hsδ hsw
    set s : ℝ := (m : ℝ) * α - k with hs
    have hs0 : 0 ≤ |s| := abs_nonneg s
    have hb1 : |s| ≤ α / D :=
      hsδ.le.trans ((min_le_left _ _).trans (min_le_left _ _))
    have hb2 : |s| < (1 - α) / D :=
      hsδ.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    have hb3 : |s| ≤ α ^ 2 / (|(a : ℝ)| + 1) := hsδ.le.trans (min_le_right _ _)
    rw [le_div_iff₀ hDR] at hb1
    rw [lt_div_iff₀ hDR] at hb2
    rw [le_div_iff₀ hA] at hb3
    have hDs : |(D : ℝ) * s| = |s| * D := by
      rw [abs_mul, Nat.abs_cast, mul_comm]
    have has : |(a : ℝ) * s| ≤ α ^ 2 := by
      rw [abs_mul]; nlinarith [abs_nonneg (a : ℝ)]
    refine f_eq_one_of_approx h0 h1 hD m k ?_ ?_ ?_ hsw
    · linarith [neg_abs_le ((D : ℝ) * s)]
    · linarith [le_abs_self ((D : ℝ) * s)]
    · exact (abs_le.mp has).1
  rcases hw0.lt_or_gt with hneg | hpos
  · obtain ⟨m, -, k, hk1, hk2⟩ := (exists_mul_sub_mem_Ioo hα hδ0).1
    refine ⟨D * m + 1, Nat.succ_pos _, key m k ?_ (mul_neg_of_pos_of_neg hk1 hneg)⟩
    rw [abs_lt]; constructor <;> linarith
  · obtain ⟨m, -, k, hk1, hk2⟩ := (exists_mul_sub_mem_Ioo hα hδ0).2
    refine ⟨D * m + 1, Nat.succ_pos _, key m k ?_ (mul_neg_of_neg_of_pos hk2 hpos)⟩
    rw [abs_lt]; constructor <;> linarith

/-- For `α ∈ (0, 1)` every value of `f_α` is `0` or `1`
(the case `⌈α⌉ = 1` of Proposition 2.1 of arXiv:2507.14244). -/
theorem f_eq_zero_or_eq_one {α : ℝ} (h0 : 0 < α) (h1 : α < 1) (n : ℕ) :
    f α n = 0 ∨ f α n = 1 := by
  rw [f_eq_ceil]
  set y : ℝ := Int.fract (α * n) with hy
  set z : ℝ := Int.fract (α ^ 2 * n) with hz
  have hy0 : 0 ≤ y := Int.fract_nonneg _
  have hy1 : y < 1 := Int.fract_lt_one _
  have hz0 : 0 ≤ z := Int.fract_nonneg _
  have hz1 : z < 1 := Int.fract_lt_one _
  have hαy0 : 0 ≤ α * y := mul_nonneg h0.le hy0
  have hαy1 : α * y < 1 := by nlinarith
  have hle : ⌈α * y - z⌉ ≤ 1 := by
    rw [Int.ceil_le]; push_cast; linarith
  have hgt : -1 < ⌈α * y - z⌉ := by
    rw [Int.lt_ceil]; push_cast; linarith
  omega

/-- `f_α(1) = 0` for `α ∈ (0, 1)`. -/
theorem f_one_eq_zero {α : ℝ} (h0 : 0 < α) (h1 : α < 1) : f α 1 = 0 := by
  have hα2 : ⌊α ^ 2 * ((1 : ℕ) : ℝ)⌋ = 0 := by
    rw [Int.floor_eq_iff]; push_cast; constructor <;> nlinarith
  have hα1 : ⌊α * ((1 : ℕ) : ℝ)⌋ = 0 := by
    rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
  rw [f, hα2, hα1]
  simp

/-- **Conjecture 4.5 of Bényi–Ćurgus (arXiv:2507.14244), quadratic case.**
If `α ∈ (0, 1)` is irrational and satisfies `α² = u α + v` with `u v : ℚ`
(in particular, if `α` is a quadratic irrational), then
`Range(f_α) = {f_α(n) : n a positive integer} = {0, 1}`. -/
theorem range_f_eq_of_quadratic {α : ℝ} (hα : Irrational α) (h0 : 0 < α)
    (h1 : α < 1) (u v : ℚ) (huv : α ^ 2 = u * α + v) :
    {k : ℤ | ∃ n : ℕ, 0 < n ∧ f α n = k} = {0, 1} := by
  ext k
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨n, -, rfl⟩
    exact f_eq_zero_or_eq_one h0 h1 n
  · rintro (rfl | rfl)
    · exact ⟨1, one_pos, f_one_eq_zero h0 h1⟩
    · exact exists_f_eq_one hα h0 h1 u v huv

/-- Non-vacuity: `α = √2 - 1` is irrational, lies in `(0, 1)` and satisfies
`α² = -2 α + 1`, so `Range(f_{√2 - 1}) = {0, 1}`. -/
theorem range_f_sqrt_two_sub_one :
    {k : ℤ | ∃ n : ℕ, 0 < n ∧ f (√2 - 1) n = k} = {0, 1} := by
  have hirr : Irrational (√2 - 1) := by
    have h := irrational_sqrt_two.sub_intCast 1
    simpa using h
  have hsq : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hlo : 1 < √2 := by
    rw [show (1 : ℝ) = √1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hhi : √2 < 2 := by nlinarith
  refine range_f_eq_of_quadratic hirr (by linarith) (by linarith) (-2) 1 ?_
  push_cast
  linear_combination hsq

end FloorCeilingQuadraticIrrational
