/-
# A295454 — Bala: the half-index Gamma ratio `a(n/2)` is an integer

## OEIS source (retrieved with `oeis show A295454`, 2026-10-21)

```
NAME:     a(n) = (30*n)!*(9*n)!*(5*n)!/((18*n)!*(15*n)!*(10*n)!*n!).
TERMS:    1,380190,402651263238,481367742667183020,...
FORMULA:  a(n) = binomial(30*n,12*n)*binomial(5*n,2*n)*binomial(2*n,n)/
          (binomial(15*n,3*n)*binomial(10*n,n)). - _Chai Wah Wu_, Feb 15 2026
COMMENT (the conjecture):
  Conjecture: for n >= 0, a(n/2) = (15*n)!*(9*n/2)!*(5*n/2)!/((9*n)!*
  (15*n/2)!*(5*n)!*(n/2)!) is an integer, where fractional factorials are
  defined using the Gamma function; for example, (9*n/2)! :=
  Gamma(9*n/2 + 1). - _Peter Bala_, Jun 13 2026
```

## Literature status (triage)

Open: no proof in the entry or in the literature as far as the triage could
tell. The even case `n = 2m` is the integrality of `a(m)` itself, which is
classical (Landau's criterion). Triage evidence: integral for `n ≤ 300`.
Re-validated here (Python, exact integers, 2026-10-21): for odd `n ≤ 699` the
odd form below is integral even without its power of two, and `a(m)` is
integral for `m ≤ 399`.

## Result of this module

The conjecture is proved for every `n`, with no remaining `sorry`.

* Odd `n`: `Γ(k/2 + 1) = k! √π / (2^k ⌊k/2⌋!)` for odd `k`
  (`Candidates.A295431BalaGamma.gamma_half_of_odd`), so the ratio equals
  `2^(2n) ⌊15n/2⌋! ⌊n/2⌋! / (⌊9n/2⌋! ⌊5n/2⌋! n!)`. Landau's criterion shows
  that the factorial quotient without the power of two is already an integer:
  with `y = n/(2q)` and `j = ⌊90y⌋` the step function
  `⌊15y⌋ + ⌊y⌋ - ⌊9y⌋ - ⌊5y⌋ - ⌊2y⌋` is
  `⌊j/6⌋ + ⌊j/90⌋ - ⌊j/10⌋ - ⌊j/18⌋ - ⌊j/45⌋ ≥ 0`, a finite check over
  `j < 90`.
* Even `n = 2m`: the ratio is `a(m)`, integral by Landau's criterion with
  `j = ⌊90y⌋` and
  `⌊j/3⌋ + ⌊j/10⌋ + ⌊j/18⌋ - ⌊j/5⌋ - ⌊j/6⌋ - ⌊j/9⌋ - ⌊j/90⌋ ≥ 0`.
-/
import Mathlib
import Combinatorics.A295431BalaGamma
import Combinatorics.A295468Bala

set_option autoImplicit false

namespace Candidates.A295454Bala

open Candidates.A295431BalaGamma (landau_list div_div_eq_of_mul_eq gamma_half_of_odd)
open Candidates.A295468Bala (step_of_period)

/-! ## Definition layer -/

/-- The OEIS sequence A295454:
`a(n) = (30n)! (9n)! (5n)! / ((18n)! (15n)! (10n)! n!)`. The truncating `Nat`
division is exact; see `a295454_mul`. -/
def a295454 (n : ℕ) : ℕ :=
  (30 * n).factorial * (9 * n).factorial * (5 * n).factorial /
    ((18 * n).factorial * (15 * n).factorial * (10 * n).factorial * n.factorial)

/-- Bala's half-index value `a(n/2)`:
`(15n)! Γ(9n/2 + 1) Γ(5n/2 + 1) / ((9n)! Γ(15n/2 + 1) (5n)! Γ(n/2 + 1))`.
Here `(k/2)! := Γ(k/2 + 1)` as in the entry. The denominator is positive
(`balaRatio_denom_pos`), so the real division never takes its junk value. -/
noncomputable def balaRatio (n : ℕ) : ℝ :=
  ((15 * n).factorial : ℝ) * Real.Gamma (9 * (n : ℝ) / 2 + 1) *
      Real.Gamma (5 * (n : ℝ) / 2 + 1) /
    (((9 * n).factorial : ℝ) * Real.Gamma (15 * (n : ℝ) / 2 + 1) * ((5 * n).factorial : ℝ) *
      Real.Gamma ((n : ℝ) / 2 + 1))

/-- The denominator of `balaRatio n` is positive. -/
theorem balaRatio_denom_pos (n : ℕ) :
    0 < ((9 * n).factorial : ℝ) * Real.Gamma (15 * (n : ℝ) / 2 + 1) *
      ((5 * n).factorial : ℝ) * Real.Gamma ((n : ℝ) / 2 + 1) := by
  have hG15 : 0 < Real.Gamma (15 * (n : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
  have hG1 : 0 < Real.Gamma ((n : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
  positivity

/-! ## The step-function inequalities -/

/-- The odd-case step inequality in the variable `j = ⌊90y⌋`:
`⌊j/10⌋ + ⌊j/18⌋ + ⌊j/45⌋ ≤ ⌊j/6⌋ + ⌊j/90⌋`, i.e.
`⌊9y⌋ + ⌊5y⌋ + ⌊2y⌋ ≤ ⌊15y⌋ + ⌊y⌋`. -/
theorem step_odd (j : ℕ) : j / 10 + j / 18 + j / 45 ≤ j / 6 + j / 90 := by
  have h := step_of_period 90 (by norm_num) [6, 90] [10, 18, 45] (by decide) (by decide)
    (by decide) (by decide) j
  simpa [add_assoc] using h

/-- The even-case step inequality in the variable `j = ⌊90y⌋`:
`⌊j/5⌋ + ⌊j/6⌋ + ⌊j/9⌋ + ⌊j/90⌋ ≤ ⌊j/3⌋ + ⌊j/10⌋ + ⌊j/18⌋`, i.e.
`⌊18y⌋ + ⌊15y⌋ + ⌊10y⌋ + ⌊y⌋ ≤ ⌊30y⌋ + ⌊9y⌋ + ⌊5y⌋`. -/
theorem step_even (j : ℕ) :
    j / 5 + j / 6 + j / 9 + j / 90 ≤ j / 3 + j / 10 + j / 18 := by
  have h := step_of_period 90 (by norm_num) [3, 10, 18] [5, 6, 9, 90]
    (by decide) (by decide) (by decide) (by decide) j
  simpa [add_assoc] using h

/-- The odd-case Landau term inequality, valid for every `n` and `q`:
`⌊⌊9n/2⌋/q⌋ + ⌊⌊5n/2⌋/q⌋ + ⌊n/q⌋ ≤ ⌊⌊15n/2⌋/q⌋ + ⌊⌊n/2⌋/q⌋`. -/
theorem term_odd (n q : ℕ) :
    9 * n / 2 / q + 5 * n / 2 / q + n / q ≤ 15 * n / 2 / q + n / 2 / q := by
  have h := step_odd (45 * n / q)
  rw [div_div_eq_of_mul_eq 45 n q 9 10 2 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 45 n q 5 18 2 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 45 n q 1 45 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 45 n q 15 6 2 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 45 n q 1 90 2 (by norm_num) (by norm_num) (by norm_num)] at h
  simp only [one_mul] at h
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul,
    Nat.div_div_eq_div_mul]
  exact h

/-- The even-case Landau term inequality, valid for every `m` and `q`:
`⌊18m/q⌋ + ⌊15m/q⌋ + ⌊10m/q⌋ + ⌊m/q⌋ ≤ ⌊30m/q⌋ + ⌊9m/q⌋ + ⌊5m/q⌋`. -/
theorem term_even (m q : ℕ) :
    18 * m / q + 15 * m / q + 10 * m / q + m / q ≤ 30 * m / q + 9 * m / q + 5 * m / q := by
  have h := step_even (90 * m / q)
  rw [div_div_eq_of_mul_eq 90 m q 18 5 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 90 m q 15 6 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 90 m q 10 9 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 90 m q 1 90 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 90 m q 30 3 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 90 m q 9 10 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 90 m q 5 18 1 (by norm_num) (by norm_num) (by norm_num)] at h
  simpa only [one_mul] using h

/-! ## Factorial divisibilities -/

/-- For every `n`, `⌊9n/2⌋! ⌊5n/2⌋! n!` divides `⌊15n/2⌋! ⌊n/2⌋!`. For odd
`n` this is stronger than needed: the factor `2^(2n)` of Bala's ratio is not
used. -/
theorem factorial_dvd_odd_form (n : ℕ) :
    (9 * n / 2).factorial * (5 * n / 2).factorial * n.factorial ∣
      (15 * n / 2).factorial * (n / 2).factorial := by
  have h := landau_list [15 * n / 2, n / 2] [9 * n / 2, 5 * n / 2, n] (15 * n)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun q => by
      have := term_odd n q
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      omega)
  simpa [mul_assoc] using h

/-- Integrality of A295454: `(18m)! (15m)! (10m)! m!` divides
`(30m)! (9m)! (5m)!`. -/
theorem factorial_dvd_a295454 (m : ℕ) :
    (18 * m).factorial * (15 * m).factorial * (10 * m).factorial * m.factorial ∣
      (30 * m).factorial * (9 * m).factorial * (5 * m).factorial := by
  have h := landau_list [30 * m, 9 * m, 5 * m] [18 * m, 15 * m, 10 * m, m] (30 * m)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun q => by
      have := term_even m q
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      omega)
  simpa [mul_assoc] using h

/-- The exact-division identity behind `a295454`. -/
theorem a295454_mul (m : ℕ) :
    (18 * m).factorial * (15 * m).factorial * (10 * m).factorial * m.factorial * a295454 m =
      (30 * m).factorial * (9 * m).factorial * (5 * m).factorial :=
  Nat.mul_div_cancel' (factorial_dvd_a295454 m)

/-! ## The Gamma bridge -/

/-- For odd `n`, suppose `⌊15n/2⌋! ⌊n/2⌋! = ⌊9n/2⌋! ⌊5n/2⌋! n! c`. Then
Bala's ratio equals `2^(2n) c`. -/
theorem balaRatio_of_odd {n c : ℕ} (hn : Odd n)
    (hc : (15 * n / 2).factorial * (n / 2).factorial =
      (9 * n / 2).factorial * (5 * n / 2).factorial * n.factorial * c) :
    balaRatio n = 2 ^ (2 * n) * (c : ℝ) := by
  have h9 : 9 * (n : ℝ) = ((9 * n : ℕ) : ℝ) := by push_cast; ring
  have h5 : 5 * (n : ℝ) = ((5 * n : ℕ) : ℝ) := by push_cast; ring
  have h15 : 15 * (n : ℝ) = ((15 * n : ℕ) : ℝ) := by push_cast; ring
  have hG1 := gamma_half_of_odd hn
  have hG9 := gamma_half_of_odd (Odd.mul (by decide : Odd 9) hn)
  have hG5 := gamma_half_of_odd (Odd.mul (by decide : Odd 5) hn)
  have hG15 := gamma_half_of_odd (Odd.mul (by decide : Odd 15) hn)
  have hcR : ((15 * n / 2).factorial : ℝ) * (n / 2).factorial =
      (9 * n / 2).factorial * (5 * n / 2).factorial * n.factorial * c := by
    exact_mod_cast hc
  have hpi : 0 < √Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hpos9 : (0 : ℝ) < (9 * n / 2).factorial := by positivity
  have hpos5 : (0 : ℝ) < (5 * n / 2).factorial := by positivity
  unfold balaRatio
  rw [h9, h5, h15, hG1, hG9, hG5, hG15]
  field_simp
  linear_combination (2 ^ (16 * n) : ℝ) * hcR


/-- For even `n = 2m`, Bala's ratio is the sequence term `a(m)`. -/
theorem balaRatio_two_mul (m : ℕ) : balaRatio (2 * m) = (a295454 m : ℝ) := by
  have hG1 : Real.Gamma (((2 * m : ℕ) : ℝ) / 2 + 1) = (m.factorial : ℝ) := by
    rw [← Real.Gamma_nat_eq_factorial]
    congr 1
    push_cast; ring
  have hG9 : Real.Gamma (9 * ((2 * m : ℕ) : ℝ) / 2 + 1) = ((9 * m).factorial : ℝ) := by
    rw [← Real.Gamma_nat_eq_factorial]
    congr 1
    push_cast; ring
  have hG5 : Real.Gamma (5 * ((2 * m : ℕ) : ℝ) / 2 + 1) = ((5 * m).factorial : ℝ) := by
    rw [← Real.Gamma_nat_eq_factorial]
    congr 1
    push_cast; ring
  have hG15 : Real.Gamma (15 * ((2 * m : ℕ) : ℝ) / 2 + 1) = ((15 * m).factorial : ℝ) := by
    rw [← Real.Gamma_nat_eq_factorial]
    congr 1
    push_cast; ring
  have hmul : (((18 * m).factorial * (15 * m).factorial * (10 * m).factorial *
      m.factorial * a295454 m : ℕ) : ℝ) =
      (((30 * m).factorial * (9 * m).factorial * (5 * m).factorial : ℕ) : ℝ) := by
    rw [a295454_mul]
  push_cast at hmul
  unfold balaRatio
  rw [hG1, hG9, hG5, hG15, show 15 * (2 * m) = 30 * m by ring,
    show 9 * (2 * m) = 18 * m by ring, show 5 * (2 * m) = 10 * m by ring]
  have h18 : (0 : ℝ) < (18 * m).factorial := by positivity
  have h15 : (0 : ℝ) < (15 * m).factorial := by positivity
  have h10 : (0 : ℝ) < (10 * m).factorial := by positivity
  have h1 : (0 : ℝ) < m.factorial := by positivity
  rw [div_eq_iff (by positivity)]
  linear_combination -hmul

/-! ## Ground truth -/

example : a295454 0 = 1 := by decide
example : a295454 1 = 380190 := by decide
example : a295454 2 = 402651263238 := by decide

/-- Bala's ratio at `n = 1`:
`15! Γ(11/2) Γ(7/2) / (9! Γ(17/2) 5! Γ(3/2)) = 2^2 · 105 = 420`. -/
theorem balaRatio_one : balaRatio 1 = 420 := by
  rw [balaRatio_of_odd (c := 105) (by decide) (by decide)]
  norm_num

/-- Bala's ratio at `n = 2` is `a(1) = 380190`. -/
example : balaRatio 2 = 380190 := by
  have h := balaRatio_two_mul 1
  rw [show (380190 : ℝ) = (a295454 1 : ℝ) by
    norm_num [show a295454 1 = 380190 by decide]]
  simpa using h

/-! ## The conjecture -/

/-- **Bala's conjecture, odd case (A295454, Peter Bala, Jun 13 2026).** For
every odd `n`,
`(15n)! Γ(9n/2 + 1) Γ(5n/2 + 1) / ((9n)! Γ(15n/2 + 1) (5n)! Γ(n/2 + 1))`
is an integer. -/
theorem bala_integrality_of_odd (n : ℕ) (hn : Odd n) : ∃ z : ℤ, balaRatio n = z := by
  obtain ⟨c, hc⟩ := factorial_dvd_odd_form n
  refine ⟨2 ^ (2 * n) * c, ?_⟩
  rw [balaRatio_of_odd hn hc]
  push_cast
  ring

/-- **Bala's conjecture (A295454, Peter Bala, Jun 13 2026).** Verbatim:
"Conjecture: for n >= 0, a(n/2) = (15*n)!*(9*n/2)!*(5*n/2)!/((9*n)!*
(15*n/2)!*(5*n)!*(n/2)!) is an integer, where fractional factorials are
defined using the Gamma function; for example, (9*n/2)! := Gamma(9*n/2 + 1)."
Here `balaRatio n` is `a(n/2)`. -/
theorem bala_integrality (n : ℕ) : ∃ z : ℤ, balaRatio n = z := by
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | hn
  · refine ⟨a295454 m, ?_⟩
    rw [← two_mul, balaRatio_two_mul]
    push_cast
    rfl
  · exact bala_integrality_of_odd n hn

end Candidates.A295454Bala
