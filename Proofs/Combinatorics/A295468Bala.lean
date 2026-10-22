/-
# A295468 — integrality of Bala's half-index Gamma ratio

Peter Bala (OEIS A295468, Jul 30 2026) conjectured integrality of `a(n/2)`
for every natural `n`, where `a(n) = (30n)! (5n)! (3n)! (2n)! /
((15n)! (10n)! (8n)! (6n)! n!)` and `x! = Γ(x+1)`.
Chai Wah Wu (Feb 16 2026) also gave a binomial-quotient formula for `a(n)`.

* Odd `n`: `Γ(k/2 + 1) = k! √π / (2^k ⌊k/2⌋!)` for odd `k`
  (`Candidates.A295431BalaGamma.gamma_half_of_odd`), so the ratio equals
  `2^(8n) ⌊15n/2⌋! ⌊n/2⌋! / (⌊5n/2⌋! ⌊3n/2⌋! (4n)!)`. Landau's criterion shows
  that the factorial quotient without the power of two is already an integer:
  with `y = n/(2q)` and `j = ⌊120y⌋` the step function
  `⌊15y⌋ + ⌊y⌋ - ⌊5y⌋ - ⌊3y⌋ - ⌊8y⌋` is
  `⌊j/8⌋ + ⌊j/120⌋ - ⌊j/24⌋ - ⌊j/40⌋ - ⌊j/15⌋ ≥ 0`, a finite check over
  `j < 120`.
* Even `n = 2m`: the ratio is `a(m)`, integral by Landau's criterion with
  `j = ⌊120y⌋` and
  `⌊j/4⌋ + ⌊j/24⌋ + ⌊j/40⌋ + ⌊j/60⌋ - ⌊j/8⌋ - ⌊j/12⌋ - ⌊j/15⌋ - ⌊j/20⌋ -
  ⌊j/120⌋ ≥ 0`.
-/
import Mathlib
import Combinatorics.A295431BalaGamma

set_option autoImplicit false

namespace Candidates.A295468Bala

open Candidates.A295431BalaGamma (landau_list div_div_eq_of_mul_eq gamma_half_of_odd)

/-! ## Definitions -/

/-- The OEIS sequence A295468:
`a(n) = (30n)! (5n)! (3n)! (2n)! / ((15n)! (10n)! (8n)! (6n)! n!)`. The
truncating `Nat` division is exact; see `a295468_mul`. -/
def a295468 (n : ℕ) : ℕ :=
  (30 * n).factorial * (5 * n).factorial * (3 * n).factorial * (2 * n).factorial /
    ((15 * n).factorial * (10 * n).factorial * (8 * n).factorial * (6 * n).factorial *
      n.factorial)

/-- Bala's half-index value `a(n/2)`:
`(15n)! Γ(5n/2 + 1) Γ(3n/2 + 1) n! / (Γ(15n/2 + 1) (5n)! (4n)! (3n)! Γ(n/2 + 1))`.
Here `(k/2)! := Γ(k/2 + 1)` as in the entry. The denominator is positive
(`balaRatio_denom_pos`), so the real division never takes its junk value. -/
noncomputable def balaRatio (n : ℕ) : ℝ :=
  ((15 * n).factorial : ℝ) * Real.Gamma (5 * (n : ℝ) / 2 + 1) *
      Real.Gamma (3 * (n : ℝ) / 2 + 1) * (n.factorial : ℝ) /
    (Real.Gamma (15 * (n : ℝ) / 2 + 1) * ((5 * n).factorial : ℝ) * ((4 * n).factorial : ℝ) *
      ((3 * n).factorial : ℝ) * Real.Gamma ((n : ℝ) / 2 + 1))

/-- The denominator of `balaRatio n` is positive. -/
theorem balaRatio_denom_pos (n : ℕ) :
    0 < Real.Gamma (15 * (n : ℝ) / 2 + 1) * ((5 * n).factorial : ℝ) *
      ((4 * n).factorial : ℝ) * ((3 * n).factorial : ℝ) * Real.Gamma ((n : ℝ) / 2 + 1) := by
  have hG15 : 0 < Real.Gamma (15 * (n : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
  have hG1 : 0 < Real.Gamma ((n : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
  positivity

/-! ## The step-function inequalities -/

/-- Shifting by a multiple of `P` shifts the quotient by a divisor `d` of `P`
linearly. -/
theorem add_mul_div_of_dvd (P s t d : ℕ) (hd : d ∣ P) (hd0 : 0 < d) :
    (s + P * t) / d = s / d + P / d * t := by
  obtain ⟨k, hk⟩ := hd
  have hkd : P / d = k := by rw [hk, Nat.mul_div_cancel_left _ hd0]
  rw [hkd, hk, mul_assoc, Nat.add_mul_div_left _ _ hd0]

/-- Reduce a floor inequality to a single period `P`. Assume that
`∑_{d ∈ ds} ⌊s/d⌋ ≤ ∑_{d ∈ cs} ⌊s/d⌋` for every residue `s < P`, that every
`d` divides `P`, and that the linear parts agree. Then the inequality holds
for all `j`. -/
theorem step_of_period (P : ℕ) (hP : 0 < P) (cs ds : List ℕ) (hcs : ∀ d ∈ cs, d ∣ P ∧ 0 < d)
    (hds : ∀ d ∈ ds, d ∣ P ∧ 0 < d)
    (hlin : (ds.map (P / ·)).sum = (cs.map (P / ·)).sum)
    (hsmall : ∀ s < P, (ds.map (s / ·)).sum ≤ (cs.map (s / ·)).sum) (j : ℕ) :
    (ds.map (j / ·)).sum ≤ (cs.map (j / ·)).sum := by
  have hshift : ∀ (l : List ℕ), (∀ d ∈ l, d ∣ P ∧ 0 < d) → ∀ s t : ℕ,
      (l.map ((s + P * t) / ·)).sum = (l.map (s / ·)).sum + (l.map (P / ·)).sum * t := by
    intro l hl s t
    induction l with
    | nil => simp
    | cons d l ih =>
      have hd := hl d (List.mem_cons_self ..)
      simp only [List.map_cons, List.sum_cons]
      rw [add_mul_div_of_dvd P s t d hd.1 hd.2, ih fun e he => hl e (List.mem_cons_of_mem _ he)]
      ring
  have hj : j = j % P + P * (j / P) := (Nat.mod_add_div j P).symm
  rw [hj, hshift cs hcs, hshift ds hds, hlin]
  have hs := hsmall (j % P) (Nat.mod_lt _ hP)
  omega

/-- The odd-case step inequality in the variable `j = ⌊120y⌋`:
`⌊j/24⌋ + ⌊j/40⌋ + ⌊j/15⌋ ≤ ⌊j/8⌋ + ⌊j/120⌋`, i.e.
`⌊5y⌋ + ⌊3y⌋ + ⌊8y⌋ ≤ ⌊15y⌋ + ⌊y⌋`. -/
theorem step_odd (j : ℕ) : j / 24 + j / 40 + j / 15 ≤ j / 8 + j / 120 := by
  have h := step_of_period 120 (by norm_num) [8, 120] [24, 40, 15] (by decide) (by decide)
    (by decide) (by decide) j
  simpa [add_assoc] using h

/-- The even-case step inequality in the variable `j = ⌊120y⌋`:
`⌊j/8⌋ + ⌊j/12⌋ + ⌊j/15⌋ + ⌊j/20⌋ + ⌊j/120⌋ ≤ ⌊j/4⌋ + ⌊j/24⌋ + ⌊j/40⌋ + ⌊j/60⌋`,
i.e. `⌊15y⌋ + ⌊10y⌋ + ⌊8y⌋ + ⌊6y⌋ + ⌊y⌋ ≤ ⌊30y⌋ + ⌊5y⌋ + ⌊3y⌋ + ⌊2y⌋`. -/
theorem step_even (j : ℕ) :
    j / 8 + j / 12 + j / 15 + j / 20 + j / 120 ≤ j / 4 + j / 24 + j / 40 + j / 60 := by
  have h := step_of_period 120 (by norm_num) [4, 24, 40, 60] [8, 12, 15, 20, 120]
    (by decide) (by decide) (by decide) (by decide) j
  simpa [add_assoc] using h

/-- The odd-case Landau term inequality, valid for every `n` and `q`:
`⌊⌊5n/2⌋/q⌋ + ⌊⌊3n/2⌋/q⌋ + ⌊4n/q⌋ ≤ ⌊⌊15n/2⌋/q⌋ + ⌊⌊n/2⌋/q⌋`. -/
theorem term_odd (n q : ℕ) :
    5 * n / 2 / q + 3 * n / 2 / q + 4 * n / q ≤ 15 * n / 2 / q + n / 2 / q := by
  have h := step_odd (60 * n / q)
  rw [div_div_eq_of_mul_eq 60 n q 5 24 2 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 60 n q 3 40 2 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 60 n q 4 15 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 60 n q 15 8 2 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 60 n q 1 120 2 (by norm_num) (by norm_num) (by norm_num)] at h
  simp only [one_mul] at h
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul,
    Nat.div_div_eq_div_mul]
  exact h

/-- The even-case Landau term inequality, valid for every `m` and `q`:
`⌊15m/q⌋ + ⌊10m/q⌋ + ⌊8m/q⌋ + ⌊6m/q⌋ + ⌊m/q⌋ ≤ ⌊30m/q⌋ + ⌊5m/q⌋ + ⌊3m/q⌋ + ⌊2m/q⌋`. -/
theorem term_even (m q : ℕ) :
    15 * m / q + 10 * m / q + 8 * m / q + 6 * m / q + m / q ≤
      30 * m / q + 5 * m / q + 3 * m / q + 2 * m / q := by
  have h := step_even (120 * m / q)
  rw [div_div_eq_of_mul_eq 120 m q 15 8 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 120 m q 10 12 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 120 m q 8 15 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 120 m q 6 20 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 120 m q 1 120 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 120 m q 30 4 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 120 m q 5 24 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 120 m q 3 40 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 120 m q 2 60 1 (by norm_num) (by norm_num) (by norm_num)] at h
  simpa only [one_mul] using h

/-! ## Factorial divisibilities -/

/-- For every `n`, `⌊5n/2⌋! ⌊3n/2⌋! (4n)!` divides `⌊15n/2⌋! ⌊n/2⌋!`. For odd
`n` this is stronger than needed: the factor `2^(8n)` of Bala's ratio is not
used. -/
theorem factorial_dvd_odd_form (n : ℕ) :
    (5 * n / 2).factorial * (3 * n / 2).factorial * (4 * n).factorial ∣
      (15 * n / 2).factorial * (n / 2).factorial := by
  have h := landau_list [15 * n / 2, n / 2] [5 * n / 2, 3 * n / 2, 4 * n] (15 * n)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun q => by
      have := term_odd n q
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      omega)
  simpa [mul_assoc] using h

/-- Integrality of A295468: `(15m)! (10m)! (8m)! (6m)! m!` divides
`(30m)! (5m)! (3m)! (2m)!`. -/
theorem factorial_dvd_a295468 (m : ℕ) :
    (15 * m).factorial * (10 * m).factorial * (8 * m).factorial * (6 * m).factorial *
        m.factorial ∣
      (30 * m).factorial * (5 * m).factorial * (3 * m).factorial * (2 * m).factorial := by
  have h := landau_list [30 * m, 5 * m, 3 * m, 2 * m] [15 * m, 10 * m, 8 * m, 6 * m, m] (30 * m)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun q => by
      have := term_even m q
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      omega)
  simpa [mul_assoc] using h

/-- The exact-division identity behind `a295468`. -/
theorem a295468_mul (m : ℕ) :
    (15 * m).factorial * (10 * m).factorial * (8 * m).factorial * (6 * m).factorial *
        m.factorial * a295468 m =
      (30 * m).factorial * (5 * m).factorial * (3 * m).factorial * (2 * m).factorial :=
  Nat.mul_div_cancel' (factorial_dvd_a295468 m)

/-! ## The Gamma bridge -/

/-- For odd `n`, suppose `⌊15n/2⌋! ⌊n/2⌋! = ⌊5n/2⌋! ⌊3n/2⌋! (4n)! c`. Then
Bala's ratio equals `2^(8n) c`. -/
theorem balaRatio_of_odd {n c : ℕ} (hn : Odd n)
    (hc : (15 * n / 2).factorial * (n / 2).factorial =
      (5 * n / 2).factorial * (3 * n / 2).factorial * (4 * n).factorial * c) :
    balaRatio n = 2 ^ (8 * n) * (c : ℝ) := by
  have h5 : 5 * (n : ℝ) = ((5 * n : ℕ) : ℝ) := by push_cast; ring
  have h3 : 3 * (n : ℝ) = ((3 * n : ℕ) : ℝ) := by push_cast; ring
  have h15 : 15 * (n : ℝ) = ((15 * n : ℕ) : ℝ) := by push_cast; ring
  have hG1 := gamma_half_of_odd hn
  have hG3 := gamma_half_of_odd (Odd.mul (by decide : Odd 3) hn)
  have hG5 := gamma_half_of_odd (Odd.mul (by decide : Odd 5) hn)
  have hG15 := gamma_half_of_odd (Odd.mul (by decide : Odd 15) hn)
  have hcR : ((15 * n / 2).factorial : ℝ) * (n / 2).factorial =
      (5 * n / 2).factorial * (3 * n / 2).factorial * (4 * n).factorial * c := by
    exact_mod_cast hc
  have hpi : 0 < √Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hpos5 : (0 : ℝ) < (5 * n / 2).factorial := by positivity
  have hpos3 : (0 : ℝ) < (3 * n / 2).factorial := by positivity
  unfold balaRatio
  rw [h5, h3, h15, hG1, hG3, hG5, hG15]
  field_simp
  linear_combination (2 ^ (16 * n) : ℝ) * hcR

/-- For even `n = 2m`, Bala's ratio is the sequence term `a(m)`. -/
theorem balaRatio_two_mul (m : ℕ) : balaRatio (2 * m) = (a295468 m : ℝ) := by
  have hG1 : Real.Gamma (((2 * m : ℕ) : ℝ) / 2 + 1) = (m.factorial : ℝ) := by
    rw [← Real.Gamma_nat_eq_factorial]
    congr 1
    push_cast; ring
  have hG3 : Real.Gamma (3 * ((2 * m : ℕ) : ℝ) / 2 + 1) = ((3 * m).factorial : ℝ) := by
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
  have hmul : (((15 * m).factorial * (10 * m).factorial * (8 * m).factorial *
      (6 * m).factorial * m.factorial * a295468 m : ℕ) : ℝ) =
      (((30 * m).factorial * (5 * m).factorial * (3 * m).factorial *
        (2 * m).factorial : ℕ) : ℝ) := by
    rw [a295468_mul]
  push_cast at hmul
  unfold balaRatio
  rw [hG1, hG3, hG5, hG15, show 15 * (2 * m) = 30 * m by ring,
    show 5 * (2 * m) = 10 * m by ring, show 4 * (2 * m) = 8 * m by ring,
    show 3 * (2 * m) = 6 * m by ring]
  have h15 : (0 : ℝ) < (15 * m).factorial := by positivity
  have h10 : (0 : ℝ) < (10 * m).factorial := by positivity
  have h8 : (0 : ℝ) < (8 * m).factorial := by positivity
  have h6 : (0 : ℝ) < (6 * m).factorial := by positivity
  have h1 : (0 : ℝ) < m.factorial := by positivity
  rw [div_eq_iff (by positivity)]
  linear_combination -hmul

/-! ## Examples -/

example : a295468 0 = 1 := by decide
example : a295468 1 = 2772725670 := by decide
example : a295468 2 = 40337629723514950470 := by decide

/-- Bala's ratio at `n = 1`:
`15! Γ(7/2) Γ(5/2) 1! / (Γ(17/2) 5! 4! 3! Γ(3/2)) = 2^8 · 105 = 26880`. -/
theorem balaRatio_one : balaRatio 1 = 26880 := by
  rw [balaRatio_of_odd (c := 105) (by decide) (by decide)]
  norm_num

/-- Bala's ratio at `n = 2` is `a(1) = 2772725670`. -/
example : balaRatio 2 = 2772725670 := by
  have h := balaRatio_two_mul 1
  rw [show (2772725670 : ℝ) = (a295468 1 : ℝ) by
    norm_num [show a295468 1 = 2772725670 by decide]]
  simpa using h

/-! ## The conjecture -/

/-- **Bala's conjecture, odd case (A295468, Peter Bala, Jul 30 2026).** For
every odd `n`,
`(15n)! Γ(5n/2 + 1) Γ(3n/2 + 1) n! / (Γ(15n/2 + 1) (5n)! (4n)! (3n)! Γ(n/2 + 1))`
is an integer. -/
theorem bala_integrality_of_odd (n : ℕ) (hn : Odd n) : ∃ z : ℤ, balaRatio n = z := by
  obtain ⟨c, hc⟩ := factorial_dvd_odd_form n
  refine ⟨2 ^ (8 * n) * c, ?_⟩
  rw [balaRatio_of_odd hn hc]
  push_cast
  ring

/-- Bala's conjecture (OEIS A295468, Peter Bala, Jul 30 2026):
`balaRatio n = a(n/2)` is integral for every natural `n`, with fractional
factorials interpreted as `x! = Γ(x+1)`. -/
theorem bala_integrality (n : ℕ) : ∃ z : ℤ, balaRatio n = z := by
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | hn
  · refine ⟨a295468 m, ?_⟩
    rw [← two_mul, balaRatio_two_mul]
    push_cast
    rfl
  · exact bala_integrality_of_odd n hn

end Candidates.A295468Bala
