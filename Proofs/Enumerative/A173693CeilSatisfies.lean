/-
# A ceiling recurrence for A173693

Source: R. J. Mathar's OEIS A173693 formula and A107293 program (Feb 18 2016).
The sequence `ceil(A107293(n)/2)` satisfies the stated order-36 recurrence
for `n ≥ 36`. Twice the ceiling is `A107293(n)` plus its parity indicator;
the latter is 31-periodic by the five-term state recurrence modulo 2.
The claimed characteristic polynomial factors as
`(x^5-x^4-x^3+x²-1)(x^31-1)`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A173693CeilSatisfies

/-- `A107293`: `b(0..4) = 0,0,0,0,1` and
`b(n) = b(n-1) + b(n-2) - b(n-3) + b(n-5)` for `n ≥ 5`. -/
def b : ℕ → ℤ
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 1
  | n + 5 => b (n + 4) + b (n + 3) - b (n + 2) + b n

/-- `A173693`: `a(n) = ceiling(A107293(n)/2)`, with the division taken in `ℚ`. -/
def a (n : ℕ) : ℤ := ⌈(b n : ℚ) / 2⌉

/-- The first 46 listed terms of A107293. -/
example : (List.range 46).map b = [0, 0, 0, 0, 1, 1, 2, 2, 3, 4, 6, 9, 13, 19, 27, 39, 56,
    81, 117, 169, 244, 352, 508, 733, 1058, 1527, 2204, 3181, 4591, 6626, 9563, 13802, 19920,
    28750, 41494, 59887, 86433, 124746, 180042, 259849, 375032, 541272, 781201, 1127483,
    1627261, 2348575] := by
  decide +kernel

/-- All 48 listed terms of A173693. -/
example : (List.range 48).map a = [0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 3, 5, 7, 10, 14, 20, 28,
    41, 59, 85, 122, 176, 254, 367, 529, 764, 1102, 1591, 2296, 3313, 4782, 6901, 9960, 14375,
    20747, 29944, 43217, 62373, 90021, 129925, 187516, 270636, 390601, 563742, 813631, 1174288,
    1694813, 2446070] := by
  decide +kernel

/-- The defining recurrence of `A107293`, shifted to start at index `0`. -/
theorem b_add_five (n : ℕ) : b (n + 5) = b (n + 4) + b (n + 3) - b (n + 2) + b n := rfl

/-- For an integer `z`, `ceiling(z/2) = ⌊(z + 1)/2⌋` (integer floor division). -/
theorem ceil_intCast_div_two (z : ℤ) : ⌈(z : ℚ) / 2⌉ = (z + 1) / 2 := by
  rw [Int.ceil_eq_iff]
  constructor
  · rw [lt_div_iff₀ (by norm_num)]
    have hlt : (((z + 1) / 2 : ℤ) - 1) * 2 < z := by omega
    exact_mod_cast hlt
  · rw [div_le_iff₀ (by norm_num)]
    have hle : z ≤ ((z + 1) / 2 : ℤ) * 2 := by omega
    exact_mod_cast hle

/-- `A107293 mod 2` is periodic with period `31`. -/
theorem b_add_thirtyOne_modEq (n : ℕ) : b (n + 31) ≡ b n [ZMOD 2] := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => decide +kernel
    | 1, _ => decide +kernel
    | 2, _ => decide +kernel
    | 3, _ => decide +kernel
    | 4, _ => decide +kernel
    | m + 5, ih =>
      rw [show m + 5 + 31 = (m + 31) + 5 by omega, b_add_five, b_add_five]
      have h4 := ih (m + 4) (by omega)
      have h3 := ih (m + 3) (by omega)
      have h2 := ih (m + 2) (by omega)
      have h0 := ih m (by omega)
      rw [show m + 4 + 31 = m + 31 + 4 by omega] at h4
      rw [show m + 3 + 31 = m + 31 + 3 by omega] at h3
      rw [show m + 2 + 31 = m + 31 + 2 by omega] at h2
      exact ((h4.add h3).sub h2).add h0

/-- `2 a(n) = A107293(n) + (A107293(n) mod 2)`. -/
theorem two_mul_a (n : ℕ) : 2 * a n = b n + b n % 2 := by
  rw [a, ceil_intCast_div_two]
  omega

/-- Mathar's recurrence for `A173693`, shifted to start at index `0`. -/
theorem a_add_thirtySix (n : ℕ) :
    a (n + 36) = a (n + 35) + a (n + 34) - a (n + 33) + a (n + 31) + a (n + 5)
      - a (n + 4) - a (n + 3) + a (n + 2) - a n := by
  have p5 : b (n + 36) % 2 = b (n + 5) % 2 := b_add_thirtyOne_modEq (n + 5)
  have p4 : b (n + 35) % 2 = b (n + 4) % 2 := b_add_thirtyOne_modEq (n + 4)
  have p3 : b (n + 34) % 2 = b (n + 3) % 2 := b_add_thirtyOne_modEq (n + 3)
  have p2 : b (n + 33) % 2 = b (n + 2) % 2 := b_add_thirtyOne_modEq (n + 2)
  have p0 : b (n + 31) % 2 = b n % 2 := b_add_thirtyOne_modEq n
  have r1 : b (n + 36) = b (n + 35) + b (n + 34) - b (n + 33) + b (n + 31) :=
    b_add_five (n + 31)
  have r0 : b (n + 5) = b (n + 4) + b (n + 3) - b (n + 2) + b n := b_add_five n
  have e36 := two_mul_a (n + 36)
  have e35 := two_mul_a (n + 35)
  have e34 := two_mul_a (n + 34)
  have e33 := two_mul_a (n + 33)
  have e31 := two_mul_a (n + 31)
  have e5 := two_mul_a (n + 5)
  have e4 := two_mul_a (n + 4)
  have e3 := two_mul_a (n + 3)
  have e2 := two_mul_a (n + 2)
  have e0 := two_mul_a n
  linarith

/-- Mathar's order-36 recurrence for `ceil(A107293(n)/2)`.
The guard `36 ≤ n` makes every natural index subtraction exact. -/
theorem mathar_conjecture (n : ℕ) (hn : 36 ≤ n) :
    a n = a (n - 1) + a (n - 2) - a (n - 3) + a (n - 5) + a (n - 31) - a (n - 32)
      - a (n - 33) + a (n - 34) - a (n - 36) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have hrec := a_add_thirtySix m
  simp only [show m + 36 - 1 = m + 35 by omega, show m + 36 - 2 = m + 34 by omega,
    show m + 36 - 3 = m + 33 by omega, show m + 36 - 5 = m + 31 by omega,
    show m + 36 - 31 = m + 5 by omega, show m + 36 - 32 = m + 4 by omega,
    show m + 36 - 33 = m + 3 by omega, show m + 36 - 34 = m + 2 by omega,
    show m + 36 - 36 = m by omega]
  linarith

/-- Non-vacuity: the hypothesis of `mathar_conjecture` is met at `n = 36`, where
the instance reads `43217 = 29944 + 20747 - 14375 + 6901 + 1 - 1 - 0 + 0 - 0`. -/
example : a 36 = a 35 + a 34 - a 33 + a 31 + a 5 - a 4 - a 3 + a 2 - a 0 :=
  mathar_conjecture 36 le_rfl

end Candidates.A173693CeilSatisfies
