/-
# A295471 — Bala: the half-index Gamma ratio `a(n/2)` is an integer

Peter Bala's conjecture in OEIS A295471 (July 30, 2026) asserts integrality
of `a(n/2)` for every natural `n`, where
`a(n) = (20n)! n! / ((10n)! (8n)! (3n)!)` and `x! = Γ(x+1)`
for fractional `x`.

* Odd `n`: `Γ(k/2 + 1) = k! √π / (2^k ⌊k/2⌋!)` for odd `k`
  (`Candidates.A295431BalaGamma.gamma_half_of_odd`), so the ratio equals
  `2^(2n) (10n)! n! ⌊3n/2⌋! / ((5n)! (4n)! (3n)! ⌊n/2⌋!)`. Landau's criterion
  shows that the factorial quotient without the power of two is already an
  integer: with `j = ⌊60x⌋` the step function
  `⌊10x⌋ + ⌊x⌋ + ⌊3x/2⌋ - ⌊5x⌋ - ⌊4x⌋ - ⌊3x⌋ - ⌊x/2⌋` is
  `⌊j/6⌋ + ⌊j/60⌋ + ⌊j/40⌋ - ⌊j/12⌋ - ⌊j/15⌋ - ⌊j/20⌋ - ⌊j/120⌋ ≥ 0`, a finite
  check over `j < 120`.
* Even `n = 2m`: the ratio is `a(m)`, integral by Landau's criterion with
  `j = ⌊120y⌋` and `⌊j/6⌋ + ⌊j/120⌋ - ⌊j/12⌋ - ⌊j/15⌋ - ⌊j/40⌋ ≥ 0`.
-/
import Mathlib
import Combinatorics.A295431BalaGamma

set_option autoImplicit false

namespace Candidates.A295471Bala

open Candidates.A295431BalaGamma (landau_list div_div_eq_of_mul_eq gamma_half_of_odd)

/-! ## Definition layer -/

/-- The OEIS sequence A295471: `a(n) = (20n)! n! / ((10n)! (8n)! (3n)!)`. The
truncating `Nat` division is exact; see `a295471_mul`. -/
def a295471 (n : ℕ) : ℕ :=
  (20 * n).factorial * n.factorial / ((10 * n).factorial * (8 * n).factorial * (3 * n).factorial)

/-- Bala's half-index value `a(n/2)`:
`(10n)! Γ(n/2 + 1) / ((5n)! (4n)! Γ(3n/2 + 1))`. Here `(n/2)! := Γ(n/2 + 1)`
and `(3n/2)! := Γ(3n/2 + 1)` as in the entry. The denominator is positive
(`balaRatio_denom_pos`), so the real division never takes its junk value. -/
noncomputable def balaRatio (n : ℕ) : ℝ :=
  ((10 * n).factorial : ℝ) * Real.Gamma ((n : ℝ) / 2 + 1) /
    (((5 * n).factorial : ℝ) * ((4 * n).factorial : ℝ) * Real.Gamma (3 * (n : ℝ) / 2 + 1))

/-- The denominator of `balaRatio n` is positive. -/
theorem balaRatio_denom_pos (n : ℕ) :
    0 < ((5 * n).factorial : ℝ) * ((4 * n).factorial : ℝ) * Real.Gamma (3 * (n : ℝ) / 2 + 1) := by
  have hG : 0 < Real.Gamma (3 * (n : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
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

/-- The odd-case step inequality in the variable `j = ⌊60x⌋`:
`⌊j/12⌋ + ⌊j/15⌋ + ⌊j/20⌋ + ⌊j/120⌋ ≤ ⌊j/6⌋ + ⌊j/60⌋ + ⌊j/40⌋`, i.e.
`⌊5x⌋ + ⌊4x⌋ + ⌊3x⌋ + ⌊x/2⌋ ≤ ⌊10x⌋ + ⌊x⌋ + ⌊3x/2⌋`. -/
theorem step_odd (j : ℕ) : j / 12 + j / 15 + j / 20 + j / 120 ≤ j / 6 + j / 60 + j / 40 := by
  have h := step_of_period 120 (by norm_num) [6, 60, 40] [12, 15, 20, 120] (by decide)
    (by decide) (by decide) (by decide) j
  simpa [add_assoc] using h

/-- The even-case step inequality in the variable `j = ⌊120y⌋`:
`⌊j/12⌋ + ⌊j/15⌋ + ⌊j/40⌋ ≤ ⌊j/6⌋ + ⌊j/120⌋`, i.e.
`⌊10y⌋ + ⌊8y⌋ + ⌊3y⌋ ≤ ⌊20y⌋ + ⌊y⌋`. -/
theorem step_even (j : ℕ) : j / 12 + j / 15 + j / 40 ≤ j / 6 + j / 120 := by
  have h := step_of_period 120 (by norm_num) [6, 120] [12, 15, 40] (by decide) (by decide)
    (by decide) (by decide) j
  simpa [add_assoc] using h

/-- The odd-case Landau term inequality, valid for every `n` and `q`:
`⌊5n/q⌋ + ⌊4n/q⌋ + ⌊3n/q⌋ + ⌊⌊n/2⌋/q⌋ ≤ ⌊10n/q⌋ + ⌊n/q⌋ + ⌊⌊3n/2⌋/q⌋`. -/
theorem term_odd (n q : ℕ) :
    5 * n / q + 4 * n / q + 3 * n / q + n / 2 / q ≤ 10 * n / q + n / q + 3 * n / 2 / q := by
  have h := step_odd (60 * n / q)
  rw [div_div_eq_of_mul_eq 60 n q 5 12 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 60 n q 4 15 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 60 n q 3 20 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 60 n q 1 120 2 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 60 n q 10 6 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 60 n q 1 60 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 60 n q 3 40 2 (by norm_num) (by norm_num) (by norm_num)] at h
  simp only [one_mul] at h
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
  exact h

/-- The even-case Landau term inequality, valid for every `m` and `q`:
`⌊10m/q⌋ + ⌊8m/q⌋ + ⌊3m/q⌋ ≤ ⌊20m/q⌋ + ⌊m/q⌋`. -/
theorem term_even (m q : ℕ) :
    10 * m / q + 8 * m / q + 3 * m / q ≤ 20 * m / q + m / q := by
  have h := step_even (120 * m / q)
  rw [div_div_eq_of_mul_eq 120 m q 10 12 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 120 m q 8 15 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 120 m q 3 40 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 120 m q 20 6 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 120 m q 1 120 1 (by norm_num) (by norm_num) (by norm_num)] at h
  simpa only [one_mul] using h

/-! ## Factorial divisibilities -/

/-- For every `n`, `(5n)! (4n)! (3n)! ⌊n/2⌋!` divides `(10n)! n! ⌊3n/2⌋!`.
For odd `n` this is stronger than needed: the factor `2^(2n)` of Bala's ratio
is not used. -/
theorem factorial_dvd_odd_form (n : ℕ) :
    (5 * n).factorial * (4 * n).factorial * (3 * n).factorial * (n / 2).factorial ∣
      (10 * n).factorial * n.factorial * (3 * n / 2).factorial := by
  have h := landau_list [10 * n, n, 3 * n / 2] [5 * n, 4 * n, 3 * n, n / 2] (10 * n)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun q => by
      have := term_odd n q
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      omega)
  simpa [mul_assoc] using h

/-- Integrality of A295471: `(10m)! (8m)! (3m)!` divides `(20m)! m!`. -/
theorem factorial_dvd_a295471 (m : ℕ) :
    (10 * m).factorial * (8 * m).factorial * (3 * m).factorial ∣
      (20 * m).factorial * m.factorial := by
  have h := landau_list [20 * m, m] [10 * m, 8 * m, 3 * m] (20 * m)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun q => by
      have := term_even m q
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      omega)
  simpa [mul_assoc] using h

/-- The exact-division identity behind `a295471`. -/
theorem a295471_mul (m : ℕ) :
    (10 * m).factorial * (8 * m).factorial * (3 * m).factorial * a295471 m =
      (20 * m).factorial * m.factorial :=
  Nat.mul_div_cancel' (factorial_dvd_a295471 m)

/-! ## The Gamma bridge -/

/-- For odd `n`, suppose `(10n)! n! ⌊3n/2⌋! = (5n)! (4n)! (3n)! ⌊n/2⌋! c`.
Then Bala's ratio equals `2^(2n) c`. -/
theorem balaRatio_of_odd {n c : ℕ} (hn : Odd n)
    (hc : (10 * n).factorial * n.factorial * (3 * n / 2).factorial =
      (5 * n).factorial * (4 * n).factorial * (3 * n).factorial * (n / 2).factorial * c) :
    balaRatio n = 2 ^ (2 * n) * (c : ℝ) := by
  have h3 : 3 * (n : ℝ) = ((3 * n : ℕ) : ℝ) := by push_cast; ring
  have hG1 := gamma_half_of_odd hn
  have hG3 := gamma_half_of_odd (Odd.mul (by decide : Odd 3) hn)
  have hcR : ((10 * n).factorial : ℝ) * n.factorial * (3 * n / 2).factorial =
      (5 * n).factorial * (4 * n).factorial * (3 * n).factorial * (n / 2).factorial * c := by
    exact_mod_cast hc
  have hpi : 0 < √Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hpos : (0 : ℝ) < (3 * n / 2).factorial := by positivity
  unfold balaRatio
  rw [h3, hG1, hG3]
  field_simp
  linear_combination (2 ^ (3 * n) : ℝ) * hcR

/-- For even `n = 2m`, Bala's ratio is the sequence term `a(m)`. -/
theorem balaRatio_two_mul (m : ℕ) : balaRatio (2 * m) = (a295471 m : ℝ) := by
  have hG1 : Real.Gamma (((2 * m : ℕ) : ℝ) / 2 + 1) = (m.factorial : ℝ) := by
    rw [← Real.Gamma_nat_eq_factorial]
    congr 1
    push_cast; ring
  have hG3 : Real.Gamma (3 * ((2 * m : ℕ) : ℝ) / 2 + 1) = ((3 * m).factorial : ℝ) := by
    rw [← Real.Gamma_nat_eq_factorial]
    congr 1
    push_cast; ring
  have hmul : (((10 * m).factorial * (8 * m).factorial * (3 * m).factorial * a295471 m : ℕ) : ℝ) =
      (((20 * m).factorial * m.factorial : ℕ) : ℝ) := by
    rw [a295471_mul]
  push_cast at hmul
  unfold balaRatio
  rw [hG1, hG3, show 10 * (2 * m) = 20 * m by ring, show 5 * (2 * m) = 10 * m by ring,
    show 4 * (2 * m) = 8 * m by ring]
  have h10 : (0 : ℝ) < (10 * m).factorial := by positivity
  have h8 : (0 : ℝ) < (8 * m).factorial := by positivity
  have h3 : (0 : ℝ) < (3 * m).factorial := by positivity
  rw [div_eq_iff (by positivity)]
  linear_combination -hmul

/-! ## Examples -/

example : a295471 0 = 1 := by decide
example : a295471 1 = 2771340 := by decide
example : a295471 2 = 44524428808860 := by decide

/-- Bala's ratio at `n = 1`: `10! Γ(3/2) / (5! 4! Γ(5/2)) = 840`. -/
theorem balaRatio_one : balaRatio 1 = 840 := by
  rw [balaRatio_of_odd (c := 210) (by decide) (by decide)]
  norm_num

/-- Bala's ratio at `n = 2` is `a(1) = 2771340`. -/
example : balaRatio 2 = 2771340 := by
  have h := balaRatio_two_mul 1
  rw [show (2771340 : ℝ) = (a295471 1 : ℝ) by norm_num [show a295471 1 = 2771340 by decide]]
  simpa using h

/-! ## The conjecture -/

/-- **Bala's conjecture, odd case (A295471, Peter Bala, Jul 30 2026).** For
every odd `n`, `(10n)! Γ(n/2 + 1) / ((5n)! (4n)! Γ(3n/2 + 1))` is an integer. -/
theorem bala_integrality_of_odd (n : ℕ) (hn : Odd n) : ∃ z : ℤ, balaRatio n = z := by
  obtain ⟨c, hc⟩ := factorial_dvd_odd_form n
  refine ⟨2 ^ (2 * n) * c, ?_⟩
  rw [balaRatio_of_odd hn hc]
  push_cast
  ring

/-- Bala's conjecture (OEIS A295471, July 30, 2026):
`balaRatio n = a(n/2)` is an integer for every natural `n`,
interpreting fractional factorials as `x! = Γ(x+1)`. -/
theorem bala_integrality (n : ℕ) : ∃ z : ℤ, balaRatio n = z := by
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | hn
  · refine ⟨a295471 m, ?_⟩
    rw [← two_mul, balaRatio_two_mul]
    push_cast
    rfl
  · exact bala_integrality_of_odd n hn

end Candidates.A295471Bala
