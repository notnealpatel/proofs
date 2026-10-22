/-
# A295479 — Bala: the half-index Gamma ratio `a(n/2)` is an integer

Peter Bala's conjecture in OEIS A295479 (July 31, 2026) asserts integrality
of `a(n/2)` for every natural `n`, where
`a(n) = (24n)! (4n)! n! / ((12n)! (8n)! (7n)! (2n)!)`
and `x! = Γ(x+1)` for fractional `x`.

* Odd `n`: `Γ(k/2 + 1) = k! √π / (2^k ⌊k/2⌋!)` for odd `k`
  (`Candidates.A295431BalaGamma.gamma_half_of_odd`), so the ratio equals
  `2^(6n) (12n)! (2n)! ⌊7n/2⌋! / ((6n)! (4n)! (7n)! ⌊n/2⌋!)`. Landau's
  criterion shows that the factorial quotient without the power of two is
  already an integer: with `j = ⌊84x⌋` the step function
  `⌊12x⌋ + ⌊2x⌋ + ⌊7x/2⌋ - ⌊6x⌋ - ⌊4x⌋ - ⌊7x⌋ - ⌊x/2⌋` is
  `⌊j/7⌋ + ⌊j/42⌋ + ⌊j/24⌋ - ⌊j/14⌋ - ⌊j/21⌋ - ⌊j/12⌋ - ⌊j/168⌋ ≥ 0`,
  a finite check over `j < 168`.
* Even `n = 2m`: the ratio is `a(m)`, integral by Landau's criterion with
  `j = ⌊168y⌋` and
  `⌊j/7⌋ + ⌊j/42⌋ + ⌊j/168⌋ - ⌊j/14⌋ - ⌊j/21⌋ - ⌊j/24⌋ - ⌊j/84⌋ ≥ 0`.
-/
import Mathlib
import Combinatorics.A295431BalaGamma
import Combinatorics.A295470Bala

set_option autoImplicit false

namespace Candidates.A295479Bala

open Candidates.A295431BalaGamma (landau_list div_div_eq_of_mul_eq gamma_half_of_odd)
open Candidates.A295470Bala (step_of_period)

/-! ## Definition layer -/

/-- The OEIS sequence A295479:
`a(n) = (24n)! (4n)! n! / ((12n)! (8n)! (7n)! (2n)!)`. The truncating `Nat`
division is exact; see `a295479_mul`. -/
def a295479 (n : ℕ) : ℕ :=
  (24 * n).factorial * (4 * n).factorial * n.factorial /
    ((12 * n).factorial * (8 * n).factorial * (7 * n).factorial * (2 * n).factorial)

/-- Bala's half-index value `a(n/2)`:
`(12n)! (2n)! Γ(n/2 + 1) / ((6n)! (4n)! Γ(7n/2 + 1) n!)`. Here
`(n/2)! := Γ(n/2 + 1)` and `(7n/2)! := Γ(7n/2 + 1)` as in the entry. The
denominator is positive (`balaRatio_denom_pos`), so the real division never
takes its junk value. -/
noncomputable def balaRatio (n : ℕ) : ℝ :=
  ((12 * n).factorial : ℝ) * ((2 * n).factorial : ℝ) * Real.Gamma ((n : ℝ) / 2 + 1) /
    (((6 * n).factorial : ℝ) * ((4 * n).factorial : ℝ) * Real.Gamma (7 * (n : ℝ) / 2 + 1) *
      (n.factorial : ℝ))

/-- The denominator of `balaRatio n` is positive. -/
theorem balaRatio_denom_pos (n : ℕ) :
    0 < ((6 * n).factorial : ℝ) * ((4 * n).factorial : ℝ) * Real.Gamma (7 * (n : ℝ) / 2 + 1) *
      (n.factorial : ℝ) := by
  have hG : 0 < Real.Gamma (7 * (n : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
  positivity

/-! ## The step-function inequalities -/

set_option maxRecDepth 20000 in
/-- The odd-case step inequality in the variable `j = ⌊84x⌋`:
`⌊j/14⌋ + ⌊j/21⌋ + ⌊j/12⌋ + ⌊j/168⌋ ≤ ⌊j/7⌋ + ⌊j/42⌋ + ⌊j/24⌋`, i.e.
`⌊6x⌋ + ⌊4x⌋ + ⌊7x⌋ + ⌊x/2⌋ ≤ ⌊12x⌋ + ⌊2x⌋ + ⌊7x/2⌋`. -/
theorem step_odd (j : ℕ) :
    j / 14 + j / 21 + j / 12 + j / 168 ≤ j / 7 + j / 42 + j / 24 := by
  have h := step_of_period 168 (by norm_num) [7, 42, 24] [14, 21, 12, 168] (by decide)
    (by decide) (by decide) (by decide) j
  simpa [add_assoc] using h

set_option maxRecDepth 20000 in
/-- The even-case step inequality in the variable `j = ⌊168y⌋`:
`⌊j/14⌋ + ⌊j/21⌋ + ⌊j/24⌋ + ⌊j/84⌋ ≤ ⌊j/7⌋ + ⌊j/42⌋ + ⌊j/168⌋`, i.e.
`⌊12y⌋ + ⌊8y⌋ + ⌊7y⌋ + ⌊2y⌋ ≤ ⌊24y⌋ + ⌊4y⌋ + ⌊y⌋`. -/
theorem step_even (j : ℕ) :
    j / 14 + j / 21 + j / 24 + j / 84 ≤ j / 7 + j / 42 + j / 168 := by
  have h := step_of_period 168 (by norm_num) [7, 42, 168] [14, 21, 24, 84] (by decide)
    (by decide) (by decide) (by decide) j
  simpa [add_assoc] using h

/-- The odd-case Landau term inequality, valid for every `n` and `q`:
`⌊6n/q⌋ + ⌊4n/q⌋ + ⌊7n/q⌋ + ⌊⌊n/2⌋/q⌋ ≤ ⌊12n/q⌋ + ⌊2n/q⌋ + ⌊⌊7n/2⌋/q⌋`. -/
theorem term_odd (n q : ℕ) :
    6 * n / q + 4 * n / q + 7 * n / q + n / 2 / q ≤
      12 * n / q + 2 * n / q + 7 * n / 2 / q := by
  have h := step_odd (84 * n / q)
  rw [div_div_eq_of_mul_eq 84 n q 6 14 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 84 n q 4 21 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 84 n q 7 12 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 84 n q 1 168 2 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 84 n q 12 7 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 84 n q 2 42 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 84 n q 7 24 2 (by norm_num) (by norm_num) (by norm_num)] at h
  simp only [one_mul] at h
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
  exact h

/-- The even-case Landau term inequality, valid for every `m` and `q`:
`⌊12m/q⌋ + ⌊8m/q⌋ + ⌊7m/q⌋ + ⌊2m/q⌋ ≤ ⌊24m/q⌋ + ⌊4m/q⌋ + ⌊m/q⌋`. -/
theorem term_even (m q : ℕ) :
    12 * m / q + 8 * m / q + 7 * m / q + 2 * m / q ≤ 24 * m / q + 4 * m / q + m / q := by
  have h := step_even (168 * m / q)
  rw [div_div_eq_of_mul_eq 168 m q 12 14 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 168 m q 8 21 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 168 m q 7 24 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 168 m q 2 84 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 168 m q 24 7 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 168 m q 4 42 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 168 m q 1 168 1 (by norm_num) (by norm_num) (by norm_num)] at h
  simpa only [one_mul] using h

/-! ## Factorial divisibilities -/

/-- For every `n`, `(6n)! (4n)! (7n)! ⌊n/2⌋!` divides `(12n)! (2n)! ⌊7n/2⌋!`.
For odd `n` this is stronger than needed: the factor `2^(6n)` of Bala's ratio
is not used. -/
theorem factorial_dvd_odd_form (n : ℕ) :
    (6 * n).factorial * (4 * n).factorial * (7 * n).factorial * (n / 2).factorial ∣
      (12 * n).factorial * (2 * n).factorial * (7 * n / 2).factorial := by
  have h := landau_list [12 * n, 2 * n, 7 * n / 2] [6 * n, 4 * n, 7 * n, n / 2] (12 * n)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun q => by
      have := term_odd n q
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      omega)
  simpa [mul_assoc] using h

/-- Integrality of A295479: `(12m)! (8m)! (7m)! (2m)!` divides
`(24m)! (4m)! m!`. -/
theorem factorial_dvd_a295479 (m : ℕ) :
    (12 * m).factorial * (8 * m).factorial * (7 * m).factorial * (2 * m).factorial ∣
      (24 * m).factorial * (4 * m).factorial * m.factorial := by
  have h := landau_list [24 * m, 4 * m, m] [12 * m, 8 * m, 7 * m, 2 * m] (24 * m)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun q => by
      have := term_even m q
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      omega)
  simpa [mul_assoc] using h

/-- The exact-division identity behind `a295479`. -/
theorem a295479_mul (m : ℕ) :
    (12 * m).factorial * (8 * m).factorial * (7 * m).factorial * (2 * m).factorial *
        a295479 m =
      (24 * m).factorial * (4 * m).factorial * m.factorial :=
  Nat.mul_div_cancel' (factorial_dvd_a295479 m)

/-! ## The Gamma bridge -/

/-- For odd `n`, suppose `(12n)! (2n)! ⌊7n/2⌋! = (6n)! (4n)! (7n)! ⌊n/2⌋! c`.
Then Bala's ratio equals `2^(6n) c`. -/
theorem balaRatio_of_odd {n c : ℕ} (hn : Odd n)
    (hc : (12 * n).factorial * (2 * n).factorial * (7 * n / 2).factorial =
      (6 * n).factorial * (4 * n).factorial * (7 * n).factorial * (n / 2).factorial * c) :
    balaRatio n = 2 ^ (6 * n) * (c : ℝ) := by
  have h7 : 7 * (n : ℝ) = ((7 * n : ℕ) : ℝ) := by push_cast; ring
  have hG1 := gamma_half_of_odd hn
  have hG7 := gamma_half_of_odd (Odd.mul (by decide : Odd 7) hn)
  have hcR : ((12 * n).factorial : ℝ) * (2 * n).factorial * (7 * n / 2).factorial =
      (6 * n).factorial * (4 * n).factorial * (7 * n).factorial * (n / 2).factorial * c := by
    exact_mod_cast hc
  have hpi : 0 < √Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hpos : (0 : ℝ) < (7 * n / 2).factorial := by positivity
  unfold balaRatio
  rw [h7, hG1, hG7]
  field_simp
  linear_combination (2 ^ (7 * n) : ℝ) * hcR

/-- For even `n = 2m`, Bala's ratio is the sequence term `a(m)`. -/
theorem balaRatio_two_mul (m : ℕ) : balaRatio (2 * m) = (a295479 m : ℝ) := by
  have hG1 : Real.Gamma (((2 * m : ℕ) : ℝ) / 2 + 1) = (m.factorial : ℝ) := by
    rw [← Real.Gamma_nat_eq_factorial]
    congr 1
    push_cast; ring
  have hG7 : Real.Gamma (7 * ((2 * m : ℕ) : ℝ) / 2 + 1) = ((7 * m).factorial : ℝ) := by
    rw [← Real.Gamma_nat_eq_factorial]
    congr 1
    push_cast; ring
  have hmul : (((12 * m).factorial * (8 * m).factorial * (7 * m).factorial *
      (2 * m).factorial * a295479 m : ℕ) : ℝ) =
      (((24 * m).factorial * (4 * m).factorial * m.factorial : ℕ) : ℝ) := by
    rw [a295479_mul]
  push_cast at hmul
  unfold balaRatio
  rw [hG1, hG7, show 12 * (2 * m) = 24 * m by ring, show 2 * (2 * m) = 4 * m by ring,
    show 6 * (2 * m) = 12 * m by ring, show 4 * (2 * m) = 8 * m by ring]
  have h12 : (0 : ℝ) < (12 * m).factorial := by positivity
  have h8 : (0 : ℝ) < (8 * m).factorial := by positivity
  have h7 : (0 : ℝ) < (7 * m).factorial := by positivity
  have h2 : (0 : ℝ) < (2 * m).factorial := by positivity
  rw [div_eq_iff (by positivity)]
  linear_combination -hmul

/-! ## Examples -/

example : a295479 0 = 1 := by decide
example : a295479 1 = 76488984 := by decide

/-- Bala's ratio at `n = 1`: `12! 2! Γ(3/2) / (6! 4! Γ(9/2) 1!) = 4224`. -/
theorem balaRatio_one : balaRatio 1 = 4224 := by
  rw [balaRatio_of_odd (c := 66) (by decide) (by decide)]
  norm_num

/-- Bala's ratio at `n = 2` is `a(1) = 76488984`. -/
example : balaRatio 2 = 76488984 := by
  have h := balaRatio_two_mul 1
  rw [show (76488984 : ℝ) = (a295479 1 : ℝ) by norm_num [show a295479 1 = 76488984 by decide]]
  simpa using h

/-! ## The conjecture -/

/-- **Bala's conjecture, odd case (A295479, Peter Bala, Jul 31 2026).** For
every odd `n`, `(12n)! (2n)! Γ(n/2 + 1) / ((6n)! (4n)! Γ(7n/2 + 1) n!)` is an
integer. -/
theorem bala_integrality_of_odd (n : ℕ) (hn : Odd n) : ∃ z : ℤ, balaRatio n = z := by
  obtain ⟨c, hc⟩ := factorial_dvd_odd_form n
  refine ⟨2 ^ (6 * n) * c, ?_⟩
  rw [balaRatio_of_odd hn hc]
  push_cast
  ring

/-- Bala's conjecture (OEIS A295479, July 31, 2026):
`balaRatio n = a(n/2)` is an integer for every natural `n`,
interpreting fractional factorials as `x! = Γ(x+1)`. -/
theorem bala_integrality (n : ℕ) : ∃ z : ℤ, balaRatio n = z := by
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | hn
  · refine ⟨a295479 m, ?_⟩
    rw [← two_mul, balaRatio_two_mul]
    push_cast
    rfl
  · exact bala_integrality_of_odd n hn

end Candidates.A295479Bala
