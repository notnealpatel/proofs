/-
# Legendre's three-square theorem

## Source

* A.-M. Legendre, *Essai sur la théorie des nombres* (1798), first statement
  (with an incomplete proof).
* C. F. Gauss, *Disquisitiones Arithmeticae* (1801), art. 291, first complete
  proof via ternary quadratic forms.
* N. C. Ankeny, "Sums of three squares", Proc. Amer. Math. Soc. 8 (1957)
  316–319: short proof via Dirichlet's theorem on primes in arithmetic
  progressions and Minkowski's convex body theorem.

## Informal statement (verbatim from the target spec)

> A natural number n is a sum of three squares of integers if and only if n is
> not of the form 4^a (8b + 7).

Date: 2026-10-21.

## Status of this module

* Necessity (`not_isSumOfThreeSquares_of_isLegendreExceptional`): proved.
  Squares mod 8 lie in `{0, 1, 4}`, so `x² + y² + z² ≢ 7 (mod 8)`; and
  `4 ∣ x² + y² + z²` forces `x, y, z` even, which gives a descent on `a`.
* Sufficiency (`isSumOfThreeSquares_of_not_isLegendreExceptional`): reduced,
  with proved helpers, to the single residual
  `isSumOfThreeSquares_of_squarefree` (squarefree `s` with `s % 8 ≠ 7`),
  which is the deep part (Gauss / Ankeny) and remains `sorry`.

Mathlib absence check (2026-10-21, `leandoc`): queries "three squares",
"sum of three squares Legendre", exact `Nat.sum_three_sq`,
`Nat.sum_three_squares`; grep for "three squares" in Mathlib: no hit.
Mathlib has only `Nat.sum_four_squares` and the two-square theory.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.LegendreThreeSquare

/-! ## Definitions -/

/-- `n` is a sum of three squares of natural numbers (equivalently, of
integers, since `(-x)² = x²`). -/
def IsSumOfThreeSquares (n : ℕ) : Prop :=
  ∃ x y z : ℕ, n = x ^ 2 + y ^ 2 + z ^ 2

/-- `n` is of Legendre's exceptional form `4^a (8b + 7)`. -/
def IsLegendreExceptional (n : ℕ) : Prop :=
  ∃ a b : ℕ, n = 4 ^ a * (8 * b + 7)

/-! ## Ground-truth checks -/

example : IsSumOfThreeSquares 0 := ⟨0, 0, 0, rfl⟩
example : IsSumOfThreeSquares 3 := ⟨1, 1, 1, rfl⟩
example : IsSumOfThreeSquares 6 := ⟨2, 1, 1, rfl⟩
example : IsSumOfThreeSquares 14 := ⟨3, 2, 1, rfl⟩
example : IsLegendreExceptional 7 := ⟨0, 0, rfl⟩
example : IsLegendreExceptional 15 := ⟨0, 1, rfl⟩
example : IsLegendreExceptional 28 := ⟨1, 0, rfl⟩
example : IsLegendreExceptional 112 := ⟨2, 0, rfl⟩

/-! ## Necessity -/

/-- Squares mod 8: no sum of three squares is `≡ 7 (mod 8)`. -/
theorem sum_three_sq_mod_eight_ne_seven (x y z : ℕ) :
    (x ^ 2 + y ^ 2 + z ^ 2) % 8 ≠ 7 := by
  have key : ∀ a b c : ZMod 8, a ^ 2 + b ^ 2 + c ^ 2 ≠ 7 := by decide
  intro h
  apply key x y z
  have hcast : ((x ^ 2 + y ^ 2 + z ^ 2 : ℕ) : ZMod 8) = ((7 : ℕ) : ZMod 8) := by
    rw [ZMod.natCast_eq_natCast_iff']
    exact h
  push_cast at hcast
  exact hcast

/-- If `4 ∣ x² + y² + z²` then `x`, `y`, `z` are all even. -/
theorem even_of_four_dvd_sum_three_sq {x y z : ℕ} (h : 4 ∣ x ^ 2 + y ^ 2 + z ^ 2) :
    2 ∣ x ∧ 2 ∣ y ∧ 2 ∣ z := by
  obtain ⟨i, hi | hi⟩ := Nat.even_or_odd' x <;>
  obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' y <;>
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' z <;>
  subst hi hj hk <;>
  · ring_nf at h
    omega

/-- Descent: if `4m` is a sum of three squares, so is `m`. -/
theorem isSumOfThreeSquares_of_four_mul {m : ℕ} (h : IsSumOfThreeSquares (4 * m)) :
    IsSumOfThreeSquares m := by
  obtain ⟨x, y, z, hxyz⟩ := h
  obtain ⟨⟨x', rfl⟩, ⟨y', rfl⟩, ⟨z', rfl⟩⟩ :=
    even_of_four_dvd_sum_three_sq (hxyz ▸ dvd_mul_right 4 m)
  refine ⟨x', y', z', ?_⟩
  have h4 : 4 * m = 4 * (x' ^ 2 + y' ^ 2 + z' ^ 2) := by rw [hxyz]; ring
  omega

/-- **Legendre, necessity.** No number of the form `4^a (8b + 7)` is a sum of
three squares. -/
theorem not_isSumOfThreeSquares_of_isLegendreExceptional {n : ℕ}
    (h : IsLegendreExceptional n) : ¬ IsSumOfThreeSquares n := by
  obtain ⟨a, b, rfl⟩ := h
  induction a with
  | zero =>
    rintro ⟨x, y, z, hxyz⟩
    apply sum_three_sq_mod_eight_ne_seven x y z
    omega
  | succ a ih =>
    intro hs
    apply ih
    apply isSumOfThreeSquares_of_four_mul
    rw [pow_succ] at hs
    convert hs using 1
    ring

/-! ## Sufficiency -/

/-- Scaling: if `m` is a sum of three squares, so is `k² m`. -/
theorem IsSumOfThreeSquares.sq_mul {m : ℕ} (h : IsSumOfThreeSquares m) (k : ℕ) :
    IsSumOfThreeSquares (k ^ 2 * m) := by
  obtain ⟨x, y, z, rfl⟩ := h
  exact ⟨k * x, k * y, k * z, by ring⟩

/-- **Residual (deep part: Gauss 1801, Ankeny 1957).** Every squarefree `s`
with `s % 8 ≠ 7` is a sum of three squares. -/
theorem isSumOfThreeSquares_of_squarefree {s : ℕ} (hs : Squarefree s) (h7 : s % 8 ≠ 7) :
    IsSumOfThreeSquares s := by
  -- Remaining goal: `IsSumOfThreeSquares s` for squarefree `s` with `s % 8 ≠ 7`.
  -- Ankeny's route: Dirichlet's theorem (`Nat.forall_exists_prime_gt_and_modEq`)
  -- to pick an auxiliary prime with Jacobi-symbol conditions, a rank-3 lattice
  -- of determinant `s` (or `2s`), and Minkowski's convex body theorem
  -- (`MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`).
  sorry

/-- An odd square is `≡ 1 (mod 8)`. -/
theorem sq_mod_eight_of_odd {k : ℕ} (hk : ¬ 2 ∣ k) : k ^ 2 % 8 = 1 := by
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' k
  · omega
  · have hsq : (2 * i + 1) ^ 2 = 4 * (i * (i + 1)) + 1 := by ring
    have hev : 2 ∣ i * (i + 1) := (Nat.even_mul_succ_self i).two_dvd
    omega

/-- Reduction: a number `m` not divisible by `4` with `m % 8 ≠ 7` is a sum of
three squares (assuming the squarefree residual). -/
theorem isSumOfThreeSquares_of_not_four_dvd {m : ℕ} (h4 : ¬ 4 ∣ m) (h7 : m % 8 ≠ 7) :
    IsSumOfThreeSquares m := by
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · exact absurd (dvd_zero 4) h4
    · exact hpos
  obtain ⟨s, k, -, -, rfl, hsf⟩ := Nat.sq_mul_squarefree_of_pos hm
  have hk : ¬ 2 ∣ k := by
    rintro ⟨j, rfl⟩
    exact h4 ⟨j ^ 2 * s, by ring⟩
  have hk8 : k ^ 2 % 8 = 1 := sq_mod_eight_of_odd hk
  have hs8 : s % 8 = k ^ 2 * s % 8 := by
    rw [Nat.mul_mod, hk8, one_mul, Nat.mod_mod]
  exact (isSumOfThreeSquares_of_squarefree hsf (hs8 ▸ h7)).sq_mul k

/-- **Legendre, sufficiency.** Every number not of the form `4^a (8b + 7)` is a
sum of three squares. -/
theorem isSumOfThreeSquares_of_not_isLegendreExceptional {n : ℕ}
    (h : ¬ IsLegendreExceptional n) : IsSumOfThreeSquares n := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exact ⟨0, 0, 0, rfl⟩
  obtain ⟨a, m, h4, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hpos.ne' 4 (by norm_num)
  have h7 : m % 8 ≠ 7 := by
    intro h7
    exact h ⟨a, m / 8, by rw [← h7, Nat.div_add_mod]⟩
  have hpow : (4 : ℕ) ^ a = (2 ^ a) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [hpow]
  exact (isSumOfThreeSquares_of_not_four_dvd h4 h7).sq_mul (2 ^ a)

/-- **Legendre's three-square theorem** (Legendre 1798; Gauss, *Disq. Arith.*
art. 291). A natural number `n` is a sum of three squares if and only if `n`
is not of the form `4^a (8b + 7)`. -/
theorem isSumOfThreeSquares_iff (n : ℕ) :
    IsSumOfThreeSquares n ↔ ¬ IsLegendreExceptional n :=
  ⟨fun hs he => not_isSumOfThreeSquares_of_isLegendreExceptional he hs,
    isSumOfThreeSquares_of_not_isLegendreExceptional⟩

/-- Unfolded form of `isSumOfThreeSquares_iff`, matching the target spec. -/
theorem sum_three_sq_iff (n : ℕ) :
    (∃ x y z : ℕ, n = x ^ 2 + y ^ 2 + z ^ 2) ↔ ¬ ∃ a b : ℕ, n = 4 ^ a * (8 * b + 7) :=
  isSumOfThreeSquares_iff n

/-- Ground truth for the necessity direction: `7` is not a sum of three squares. -/
example : ¬ IsSumOfThreeSquares 7 :=
  not_isSumOfThreeSquares_of_isLegendreExceptional ⟨0, 0, rfl⟩

end Candidates.LegendreThreeSquare
