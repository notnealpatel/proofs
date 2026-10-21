/-
# A Markov-type equation `x² + y² + z² + 2yz = kxyz`

## Source

Zhichao Chen and Yimin Huang, *Mutation-preserving generalized cluster
algebras and Laurent mutation invariants*, arXiv:2608.10551, Section 4
("A Markov-type Diophantine equation with multiple orbits"):
Proposition `prop: k larger than 5`, Theorem `thm: main`,
Theorem `thm: 12345`.  Recorded 2026-10-21.

Verbatim (Theorem `thm: 12345`, first sentence):

> There exist positive integer solutions to the Diophantine equations
> `x^2+y^2+z^2+2yz=kxyz` if and only if `k=1,2,3,4,5`.

Verbatim (Proposition `prop: k larger than 5`):

> Let `k ∈ ℕ` and the Diophantine equation be as follows:
> `x^2+y^2+z^2+2yz=kxyz`.  Then, if `k ≥ 6`, there is no positive
> integer solution.

## Status

Proved in the paper.  The existence half uses explicit solutions; the
nonexistence half (`k ≥ 6`) is a Vieta-jumping descent on the maximal
coordinate with the generalized mutations
`x ↦ (y+z)²/x = kyz - x` and `y ↦ (x²+z²)/y = kxz - 2z - y`.
The second sentence of `thm: 12345` (orbit structure) is not formalized
here.

Note on the source proof: in the case `B ≥ C ≥ A` the paper writes
`H_k(C) = 2C² + A² + 2AC - kAC²`; the correct value is
`H_k(C) = 4C² + A² - kAC²`.  The bound `H_k(C) ≤ 5C² - 6C² < 0` used
there still holds (it needs `A ≤ C`), so the argument is unaffected.
The formal proof below uses the corrected expression.

Witnesses used here (each checked by `decide` below):
`k = 1 : (5,5,5)`, `k = 2 : (4,2,2)`, `k = 3 : (3,2,1)`,
`k = 4 : (2,1,1)`, `k = 5 : (1,1,1)`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.MarkovTypeEquation

/-! ## Definition layer -/

/-- `IsPosSol k x y z` says that `(x, y, z)` is a positive integer solution of the
Markov-type equation `x² + y² + z² + 2yz = kxyz` of Chen–Huang (arXiv:2608.10551, §4). -/
def IsPosSol (k x y z : ℕ) : Prop :=
  0 < x ∧ 0 < y ∧ 0 < z ∧ x ^ 2 + y ^ 2 + z ^ 2 + 2 * y * z = k * x * y * z

instance (k x y z : ℕ) : Decidable (IsPosSol k x y z) := by
  unfold IsPosSol; infer_instance

/-! ### Ground truth: the witnesses, a solution from the paper's comments, and non-solutions -/

example : IsPosSol 1 5 5 5 := by decide
example : IsPosSol 1 9 6 3 := by decide
example : IsPosSol 2 4 2 2 := by decide
example : IsPosSol 3 3 2 1 := by decide
example : IsPosSol 4 2 1 1 := by decide
example : IsPosSol 4 2 1 5 := by decide
example : IsPosSol 5 1 1 1 := by decide
example : ¬ IsPosSol 6 1 1 1 := by decide
example : ¬ IsPosSol 0 0 0 0 := by decide
example : ¬ IsPosSol 5 2 1 1 := by decide

/-! ## Descent steps (over `ℤ`) -/

/-- Mutation at `x` (the generalized mutation `μ̂₁`): if `(x, y, z)` is a positive solution
with `k ≥ 6` and `z ≤ y ≤ x`, then `x' = kyz - x = (y+z)²/x` gives a positive solution
`(x', y, z)` with `x' < x`. -/
theorem x_step (k x y z : ℤ) (hk : 6 ≤ k) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hzy : z ≤ y) (hyx : y ≤ x)
    (h : x ^ 2 + y ^ 2 + z ^ 2 + 2 * y * z = k * x * y * z) :
    0 < k * y * z - x ∧ k * y * z - x < x ∧
      (k * y * z - x) ^ 2 + y ^ 2 + z ^ 2 + 2 * y * z = k * (k * y * z - x) * y * z := by
  set x' := k * y * z - x with hx'
  have hprod : x * x' = (y + z) ^ 2 := by rw [hx']; linear_combination -h
  have hpos : 0 < x' := by
    have hxx' : 0 < x * x' := by rw [hprod]; positivity
    exact pos_of_mul_pos_right hxx' hx.le
  -- `G_k(y) = (y - x)(y - x') < 0`
  have hG : (y - x) * (y - x') < 0 := by
    have hyz : 0 < y ^ 2 * z := by positivity
    have e : (y - x) * (y - x') = y ^ 2 - k * y * z * y + (y + z) ^ 2 := by
      rw [hx']; linear_combination -h
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_right hk hyz.le, mul_le_mul_of_nonneg_left hz (sq_nonneg y)]
  have hlt : x' < y := by
    by_contra hc
    rw [not_lt] at hc
    nlinarith [mul_nonneg (sub_nonneg.mpr hyx) (sub_nonneg.mpr hc)]
  refine ⟨hpos, by omega, ?_⟩
  rw [hx']; linear_combination h

/-- Mutation at `y` (the generalized mutation `μ̂₂`): if `(x, y, z)` is a positive solution
with `k ≥ 6` and `y` maximal, then `y' = kxz - 2z - y = (x²+z²)/y` gives a positive solution
`(x, y', z)` with `y' < y`. -/
theorem y_step (k x y z : ℤ) (hk : 6 ≤ k) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy : x ≤ y) (hzy : z ≤ y)
    (h : x ^ 2 + y ^ 2 + z ^ 2 + 2 * y * z = k * x * y * z) :
    0 < k * x * z - 2 * z - y ∧ k * x * z - 2 * z - y < y ∧
      x ^ 2 + (k * x * z - 2 * z - y) ^ 2 + z ^ 2 + 2 * (k * x * z - 2 * z - y) * z =
        k * x * (k * x * z - 2 * z - y) * z := by
  set y' := k * x * z - 2 * z - y with hy'
  have hprod : y * y' = x ^ 2 + z ^ 2 := by rw [hy']; linear_combination -h
  have hpos : 0 < y' := by
    have hyy' : 0 < y * y' := by rw [hprod]; positivity
    exact pos_of_mul_pos_right hyy' hy.le
  -- `H_k(t) = (t - y)(t - y')`
  have hH : ∀ t : ℤ, (t - y) * (t - y') = t ^ 2 + (2 * z - k * x * z) * t + x ^ 2 + z ^ 2 := by
    intro t; rw [hy']; linear_combination -h
  -- `H_k(max x z) < 0`
  have key : ∃ m : ℤ, m ≤ y ∧ (m - y) * (m - y') < 0 := by
    rcases le_total z x with hzx | hxz
    · refine ⟨x, hxy, ?_⟩
      rw [hH]
      have hxz : 0 < x ^ 2 * z := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hk hxz.le, mul_le_mul_of_nonneg_left hz (sq_nonneg x),
        mul_le_mul_of_nonneg_left hzx hx.le]
    · refine ⟨z, hzy, ?_⟩
      rw [hH]
      have hxz' : 0 < x * z ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hk hxz'.le, mul_le_mul_of_nonneg_left hx (sq_nonneg z),
        mul_le_mul_of_nonneg_left hxz hx.le, mul_le_mul_of_nonneg_left hxz hz.le]
  obtain ⟨m, hmy, hm⟩ := key
  have hlt : y' < m := by
    by_contra hc
    rw [not_lt] at hc
    nlinarith [mul_nonneg (sub_nonneg.mpr hmy) (sub_nonneg.mpr hc)]
  refine ⟨hpos, by omega, ?_⟩
  rw [hy']; linear_combination h

/-- One descent step: for `k ≥ 6`, every positive integer solution `(x, y, z)` of
`x² + y² + z² + 2yz = kxyz` yields another positive solution with strictly smaller
coordinate sum (mutate at a maximal coordinate). -/
theorem exists_smaller (k x y z : ℤ) (hk : 6 ≤ k) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x ^ 2 + y ^ 2 + z ^ 2 + 2 * y * z = k * x * y * z) :
    ∃ a b c : ℤ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a + b + c < x + y + z ∧
      a ^ 2 + b ^ 2 + c ^ 2 + 2 * b * c = k * a * b * c := by
  by_cases hxm : y ≤ x ∧ z ≤ x
  · rcases le_total z y with hzy | hyz
    · obtain ⟨h1, h2, h3⟩ := x_step k x y z hk hx hy hz hzy hxm.1 h
      exact ⟨_, y, z, h1, hy, hz, by omega, h3⟩
    · have h' : x ^ 2 + z ^ 2 + y ^ 2 + 2 * z * y = k * x * z * y := by linear_combination h
      obtain ⟨h1, h2, h3⟩ := x_step k x z y hk hx hz hy hyz hxm.2 h'
      exact ⟨_, y, z, h1, hy, hz, by omega, by linear_combination h3⟩
  · by_cases hym : x ≤ y ∧ z ≤ y
    · obtain ⟨h1, h2, h3⟩ := y_step k x y z hk hx hy hz hym.1 hym.2 h
      exact ⟨x, _, z, hx, h1, hz, by omega, h3⟩
    · have hxz : x ≤ z := by omega
      have hyz : y ≤ z := by omega
      have h' : x ^ 2 + z ^ 2 + y ^ 2 + 2 * z * y = k * x * z * y := by linear_combination h
      obtain ⟨h1, h2, h3⟩ := y_step k x z y hk hx hz hy hxz hyz h'
      exact ⟨x, y, _, hx, hy, h1, by omega, by linear_combination h3⟩

/-- Nonexistence over `ℤ` (Chen–Huang, arXiv:2608.10551, Proposition `prop: k larger than 5`):
for `k ≥ 6` the equation `x² + y² + z² + 2yz = kxyz` has no solution in positive integers. -/
theorem no_pos_sol_int (k : ℤ) (hk : 6 ≤ k) (x y z : ℤ) (hx : 0 < x) (hy : 0 < y)
    (hz : 0 < z) : x ^ 2 + y ^ 2 + z ^ 2 + 2 * y * z ≠ k * x * y * z := by
  suffices H : ∀ n : ℕ, ∀ x y z : ℤ, x + y + z = n → 0 < x → 0 < y → 0 < z →
      x ^ 2 + y ^ 2 + z ^ 2 + 2 * y * z ≠ k * x * y * z from
    H (x + y + z).toNat x y z (by omega) hx hy hz
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x y z hn hx hy hz h
    obtain ⟨a, b, c, ha, hb, hc, hlt, habc⟩ := exists_smaller k x y z hk hx hy hz h
    exact ih (a + b + c).toNat (by omega) a b c (by omega) ha hb hc habc

/-- Nonexistence over `ℕ` (Chen–Huang, arXiv:2608.10551, Proposition `prop: k larger than 5`):
if `6 ≤ k` then `x² + y² + z² + 2yz = kxyz` has no positive integer solution. -/
theorem not_isPosSol_of_six_le {k : ℕ} (hk : 6 ≤ k) (x y z : ℕ) : ¬ IsPosSol k x y z := by
  rintro ⟨hx, hy, hz, h⟩
  have hZ : (x : ℤ) ^ 2 + (y : ℤ) ^ 2 + (z : ℤ) ^ 2 + 2 * (y : ℤ) * (z : ℤ) =
      (k : ℤ) * (x : ℤ) * (y : ℤ) * (z : ℤ) := by exact_mod_cast h
  exact no_pos_sol_int (k : ℤ) (by exact_mod_cast hk) x y z (by exact_mod_cast hx)
    (by exact_mod_cast hy) (by exact_mod_cast hz) hZ

/-- For `k = 0` there is no positive solution: the left side is positive. -/
theorem not_isPosSol_zero (x y z : ℕ) : ¬ IsPosSol 0 x y z := by
  rintro ⟨hx, -, -, h⟩
  have hx2 : 0 < x ^ 2 := by positivity
  simp only [zero_mul] at h
  omega

/-- **Chen–Huang, arXiv:2608.10551, Theorem `thm: 12345` (existence criterion).**
The Diophantine equation `x² + y² + z² + 2yz = kxyz` has a solution in positive integers
if and only if `k ∈ {1, 2, 3, 4, 5}`, i.e. `1 ≤ k ≤ 5`. -/
theorem exists_isPosSol_iff (k : ℕ) : (∃ x y z : ℕ, IsPosSol k x y z) ↔ 1 ≤ k ∧ k ≤ 5 := by
  constructor
  · rintro ⟨x, y, z, hsol⟩
    refine ⟨?_, ?_⟩
    · rcases Nat.eq_zero_or_pos k with rfl | hpos
      · exact absurd hsol (not_isPosSol_zero x y z)
      · exact hpos
    · by_contra hc
      exact not_isPosSol_of_six_le (by omega) x y z hsol
  · rintro ⟨h1, h5⟩
    interval_cases k
    · exact ⟨5, 5, 5, by decide⟩
    · exact ⟨4, 2, 2, by decide⟩
    · exact ⟨3, 2, 1, by decide⟩
    · exact ⟨2, 1, 1, by decide⟩
    · exact ⟨1, 1, 1, by decide⟩

end Candidates.MarkovTypeEquation
