/-
# A295475 — Bala: the half-index Gamma ratio `a(n/2)` is an integer

OEIS A295475, Peter Bala (2026): `a(n/2)` is an integer for every natural
`n`, where `a(n) = (20n)!(3n)! / ((10n)!(9n)!(4n)!)` and `x! = Γ(x+1)`.
The entry also gives binomial-coefficient formulas by Chai Wah Wu (2026).

## Proof outline

* Odd `n`: `Γ(k/2 + 1) = k! √π / (2^k ⌊k/2⌋!)` for odd `k`
  (`Candidates.A295431BalaGamma.gamma_half_of_odd`), so the ratio equals
  `2^(6n) (10n)! (3n)! ⌊9n/2⌋! / ((5n)! (2n)! (9n)! ⌊3n/2⌋!)`. Landau's
  criterion shows that the factorial quotient without the power of two is
  already an integer: with `j = ⌊180x⌋` the step function
  `⌊10x⌋ + ⌊3x⌋ + ⌊9x/2⌋ - ⌊5x⌋ - ⌊2x⌋ - ⌊9x⌋ - ⌊3x/2⌋` is
  `⌊j/18⌋ + ⌊j/60⌋ + ⌊j/40⌋ - ⌊j/36⌋ - ⌊j/90⌋ - ⌊j/20⌋ - ⌊j/120⌋ ≥ 0`,
  a finite check over `j < 360`.
* Even `n = 2m`: the ratio is `a(m)`, integral by Landau's criterion with
  `j = ⌊180y⌋` and `⌊j/9⌋ + ⌊j/60⌋ - ⌊j/18⌋ - ⌊j/20⌋ - ⌊j/45⌋ ≥ 0`.
-/
import Mathlib
import Combinatorics.A295431BalaGamma
import Combinatorics.A295470Bala

set_option autoImplicit false

namespace Candidates.A295475Bala

open Candidates.A295431BalaGamma (landau_list div_div_eq_of_mul_eq gamma_half_of_odd)
open Candidates.A295470Bala (step_of_period)

/-! ## Definition layer -/

/-- The OEIS sequence A295475:
`a(n) = (20n)! (3n)! / ((10n)! (9n)! (4n)!)`. The truncating `Nat` division is
exact; see `a295475_mul`. -/
def a295475 (n : ℕ) : ℕ :=
  (20 * n).factorial * (3 * n).factorial /
    ((10 * n).factorial * (9 * n).factorial * (4 * n).factorial)

/-- Bala's half-index value `a(n/2)`:
`(10n)! Γ(3n/2 + 1) / ((5n)! Γ(9n/2 + 1) (2n)!)`. Here `(3n/2)! := Γ(3n/2 + 1)`
and `(9n/2)! := Γ(9n/2 + 1)` as in the entry. The denominator is positive
(`balaRatio_denom_pos`), so the real division never takes its junk value. -/
noncomputable def balaRatio (n : ℕ) : ℝ :=
  ((10 * n).factorial : ℝ) * Real.Gamma (3 * (n : ℝ) / 2 + 1) /
    (((5 * n).factorial : ℝ) * Real.Gamma (9 * (n : ℝ) / 2 + 1) * ((2 * n).factorial : ℝ))

/-- The denominator of `balaRatio n` is positive. -/
theorem balaRatio_denom_pos (n : ℕ) :
    0 < ((5 * n).factorial : ℝ) * Real.Gamma (9 * (n : ℝ) / 2 + 1) *
      ((2 * n).factorial : ℝ) := by
  have hG : 0 < Real.Gamma (9 * (n : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
  positivity

/-! ## The step-function inequalities -/

set_option maxRecDepth 20000 in
/-- The odd-case step inequality in the variable `j = ⌊180x⌋`:
`⌊j/36⌋ + ⌊j/90⌋ + ⌊j/20⌋ + ⌊j/120⌋ ≤ ⌊j/18⌋ + ⌊j/60⌋ + ⌊j/40⌋`, i.e.
`⌊5x⌋ + ⌊2x⌋ + ⌊9x⌋ + ⌊3x/2⌋ ≤ ⌊10x⌋ + ⌊3x⌋ + ⌊9x/2⌋`. -/
theorem step_odd (j : ℕ) :
    j / 36 + j / 90 + j / 20 + j / 120 ≤ j / 18 + j / 60 + j / 40 := by
  have h := step_of_period 360 (by norm_num) [18, 60, 40] [36, 90, 20, 120] (by decide)
    (by decide) (by decide) (by decide) j
  simpa [add_assoc] using h

set_option maxRecDepth 20000 in
/-- The even-case step inequality in the variable `j = ⌊180y⌋`:
`⌊j/18⌋ + ⌊j/20⌋ + ⌊j/45⌋ ≤ ⌊j/9⌋ + ⌊j/60⌋`, i.e.
`⌊10y⌋ + ⌊9y⌋ + ⌊4y⌋ ≤ ⌊20y⌋ + ⌊3y⌋`. -/
theorem step_even (j : ℕ) : j / 18 + j / 20 + j / 45 ≤ j / 9 + j / 60 := by
  have h := step_of_period 180 (by norm_num) [9, 60] [18, 20, 45] (by decide) (by decide)
    (by decide) (by decide) j
  simpa [add_assoc] using h

/-- The odd-case Landau term inequality, valid for every `n` and `q`:
`⌊5n/q⌋ + ⌊2n/q⌋ + ⌊9n/q⌋ + ⌊⌊3n/2⌋/q⌋ ≤ ⌊10n/q⌋ + ⌊3n/q⌋ + ⌊⌊9n/2⌋/q⌋`. -/
theorem term_odd (n q : ℕ) :
    5 * n / q + 2 * n / q + 9 * n / q + 3 * n / 2 / q ≤
      10 * n / q + 3 * n / q + 9 * n / 2 / q := by
  have h := step_odd (180 * n / q)
  rw [div_div_eq_of_mul_eq 180 n q 5 36 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 180 n q 2 90 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 180 n q 9 20 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 180 n q 3 120 2 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 180 n q 10 18 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 180 n q 3 60 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 180 n q 9 40 2 (by norm_num) (by norm_num) (by norm_num)] at h
  simp only [one_mul] at h
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
  exact h

/-- The even-case Landau term inequality, valid for every `m` and `q`:
`⌊10m/q⌋ + ⌊9m/q⌋ + ⌊4m/q⌋ ≤ ⌊20m/q⌋ + ⌊3m/q⌋`. -/
theorem term_even (m q : ℕ) :
    10 * m / q + 9 * m / q + 4 * m / q ≤ 20 * m / q + 3 * m / q := by
  have h := step_even (180 * m / q)
  rw [div_div_eq_of_mul_eq 180 m q 10 18 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 180 m q 9 20 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 180 m q 4 45 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 180 m q 20 9 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 180 m q 3 60 1 (by norm_num) (by norm_num) (by norm_num)] at h
  simpa only [one_mul] using h

/-! ## Factorial divisibilities -/

/-- For every `n`, `(5n)! (2n)! (9n)! ⌊3n/2⌋!` divides `(10n)! (3n)! ⌊9n/2⌋!`.
For odd `n` this is stronger than needed: the factor `2^(6n)` of Bala's ratio
is not used. -/
theorem factorial_dvd_odd_form (n : ℕ) :
    (5 * n).factorial * (2 * n).factorial * (9 * n).factorial * (3 * n / 2).factorial ∣
      (10 * n).factorial * (3 * n).factorial * (9 * n / 2).factorial := by
  have h := landau_list [10 * n, 3 * n, 9 * n / 2] [5 * n, 2 * n, 9 * n, 3 * n / 2] (10 * n)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun q => by
      have := term_odd n q
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      omega)
  simpa [mul_assoc] using h

/-- Integrality of A295475: `(10m)! (9m)! (4m)!` divides `(20m)! (3m)!`. -/
theorem factorial_dvd_a295475 (m : ℕ) :
    (10 * m).factorial * (9 * m).factorial * (4 * m).factorial ∣
      (20 * m).factorial * (3 * m).factorial := by
  have h := landau_list [20 * m, 3 * m] [10 * m, 9 * m, 4 * m] (20 * m)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun q => by
      have := term_even m q
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      omega)
  simpa [mul_assoc] using h

/-- The exact-division identity behind `a295475`. -/
theorem a295475_mul (m : ℕ) :
    (10 * m).factorial * (9 * m).factorial * (4 * m).factorial * a295475 m =
      (20 * m).factorial * (3 * m).factorial :=
  Nat.mul_div_cancel' (factorial_dvd_a295475 m)

/-! ## The Gamma bridge -/

/-- For odd `n`, suppose `(10n)! (3n)! ⌊9n/2⌋! = (5n)! (2n)! (9n)! ⌊3n/2⌋! c`.
Then Bala's ratio equals `2^(6n) c`. -/
theorem balaRatio_of_odd {n c : ℕ} (hn : Odd n)
    (hc : (10 * n).factorial * (3 * n).factorial * (9 * n / 2).factorial =
      (5 * n).factorial * (2 * n).factorial * (9 * n).factorial * (3 * n / 2).factorial * c) :
    balaRatio n = 2 ^ (6 * n) * (c : ℝ) := by
  have h3 : 3 * (n : ℝ) = ((3 * n : ℕ) : ℝ) := by push_cast; ring
  have h9 : 9 * (n : ℝ) = ((9 * n : ℕ) : ℝ) := by push_cast; ring
  have hG3 := gamma_half_of_odd (Odd.mul (by decide : Odd 3) hn)
  have hG9 := gamma_half_of_odd (Odd.mul (by decide : Odd 9) hn)
  have hcR : ((10 * n).factorial : ℝ) * (3 * n).factorial * (9 * n / 2).factorial =
      (5 * n).factorial * (2 * n).factorial * (9 * n).factorial * (3 * n / 2).factorial * c := by
    exact_mod_cast hc
  have hpi : 0 < √Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hpos3 : (0 : ℝ) < (3 * n / 2).factorial := by positivity
  have hpos9 : (0 : ℝ) < (9 * n / 2).factorial := by positivity
  unfold balaRatio
  rw [h3, h9, hG3, hG9]
  field_simp
  linear_combination (2 ^ (9 * n) : ℝ) * hcR

/-- For even `n = 2m`, Bala's ratio is the sequence term `a(m)`. -/
theorem balaRatio_two_mul (m : ℕ) : balaRatio (2 * m) = (a295475 m : ℝ) := by
  have hG3 : Real.Gamma (3 * ((2 * m : ℕ) : ℝ) / 2 + 1) = ((3 * m).factorial : ℝ) := by
    rw [← Real.Gamma_nat_eq_factorial]
    congr 1
    push_cast; ring
  have hG9 : Real.Gamma (9 * ((2 * m : ℕ) : ℝ) / 2 + 1) = ((9 * m).factorial : ℝ) := by
    rw [← Real.Gamma_nat_eq_factorial]
    congr 1
    push_cast; ring
  have hmul : (((10 * m).factorial * (9 * m).factorial * (4 * m).factorial *
      a295475 m : ℕ) : ℝ) = (((20 * m).factorial * (3 * m).factorial : ℕ) : ℝ) := by
    rw [a295475_mul]
  push_cast at hmul
  unfold balaRatio
  rw [hG3, hG9, show 10 * (2 * m) = 20 * m by ring, show 5 * (2 * m) = 10 * m by ring,
    show 2 * (2 * m) = 4 * m by ring]
  have h10 : (0 : ℝ) < (10 * m).factorial := by positivity
  have h9 : (0 : ℝ) < (9 * m).factorial := by positivity
  have h4 : (0 : ℝ) < (4 * m).factorial := by positivity
  rw [div_eq_iff (by positivity)]
  linear_combination -hmul

/-! ## Examples -/

example : a295475 0 = 1 := by decide
example : a295475 1 = 461890 := by decide
example : a295475 2 = 935387159850 := by decide

/-- Bala's ratio at `n = 1`: `10! Γ(5/2) / (5! Γ(11/2) 2!) = 384`. -/
theorem balaRatio_one : balaRatio 1 = 384 := by
  rw [balaRatio_of_odd (c := 6) (by decide) (by decide)]
  norm_num

/-- Bala's ratio at `n = 2` is `a(1) = 461890`. -/
example : balaRatio 2 = 461890 := by
  have h := balaRatio_two_mul 1
  rw [show (461890 : ℝ) = (a295475 1 : ℝ) by norm_num [show a295475 1 = 461890 by decide]]
  simpa using h

/-! ## The conjecture -/

/-- **Bala's conjecture, odd case (A295475, Peter Bala, Jul 31 2026).** For
every odd `n`, `(10n)! Γ(3n/2 + 1) / ((5n)! Γ(9n/2 + 1) (2n)!)` is an
integer. -/
theorem bala_integrality_of_odd (n : ℕ) (hn : Odd n) : ∃ z : ℤ, balaRatio n = z := by
  obtain ⟨c, hc⟩ := factorial_dvd_odd_form n
  refine ⟨2 ^ (6 * n) * c, ?_⟩
  rw [balaRatio_of_odd hn hc]
  push_cast
  ring

/-- **Bala's conjecture (A295475, Peter Bala, Jul 31 2026).**
For every natural `n`, `balaRatio n` (the value `a(n/2)`) is an integer, with
fractional factorials interpreted as `x! = Γ(x+1)`. -/
theorem bala_integrality (n : ℕ) : ∃ z : ℤ, balaRatio n = z := by
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | hn
  · refine ⟨a295475 m, ?_⟩
    rw [← two_mul, balaRatio_two_mul]
    push_cast
    rfl
  · exact bala_integrality_of_odd n hn

end Candidates.A295475Bala
