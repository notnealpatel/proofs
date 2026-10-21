/-
# A295470 — Bala: the half-index Gamma ratio `a(n/2)` is an integer

## OEIS source (retrieved with `oeis show A295470`, 2026-10-21)

```
NAME:     a(n) = (20*n)!*(6*n)!*n!/((12*n)!*(10*n)!*(3*n)!*(2*n)!).
TERMS:    1,83980,29966636700,12398706131799988,5447952226877283703580,...
FORMULA:  a(n) = binomial(20*n,8*n)*binomial(6*n,3*n)*binomial(3*n,n)/
          (binomial(10*n,2*n)*binomial(2*n,n)). - _Chai Wah Wu_, Feb 16 2026
COMMENT (the conjecture):
  Conjecture: for n >= 0, a(n/2) = (10*n)!*(3*n)!*(n/2)! / ((6*n)!*(5*n)!*
  (3*n/2)!*n!) is an integer, where fractional factorials are defined using
  the Gamma function - for example, (3*n/2)! := Gamma(3*n/2 + 1).
  - _Peter Bala_, Jul 30 2026
```

## Literature status (triage)

Open: no proof in the entry or in the literature as far as the triage could
tell. The even case `n = 2m` is the integrality of `a(m)` itself, which is
classical (Landau's criterion). Triage evidence: integral for `n ≤ 300`.
Re-validated here (Python, exact integers, 2026-10-21) for `n ≤ 400`.

## Result of this module

The conjecture is proved for every `n`, with no remaining `sorry`.

* Odd `n`: `Γ(k/2 + 1) = k! √π / (2^k ⌊k/2⌋!)` for odd `k`
  (`Candidates.A295431BalaGamma.gamma_half_of_odd`), so the ratio equals
  `2^(2n) (10n)! ⌊3n/2⌋! / ((6n)! (5n)! ⌊n/2⌋!)`. Landau's criterion shows that
  the factorial quotient without the power of two is already an integer: with
  `j = ⌊30x⌋` the step function
  `⌊10x⌋ + ⌊3x/2⌋ - ⌊6x⌋ - ⌊5x⌋ - ⌊x/2⌋` is
  `⌊j/3⌋ + ⌊j/20⌋ - ⌊j/5⌋ - ⌊j/6⌋ - ⌊j/60⌋ ≥ 0`, a finite check over `j < 60`.
* Even `n = 2m`: the ratio is `a(m)`, integral by Landau's criterion with
  `j = ⌊60y⌋` and
  `⌊j/3⌋ + ⌊j/10⌋ + ⌊j/60⌋ - ⌊j/5⌋ - ⌊j/6⌋ - ⌊j/20⌋ - ⌊j/30⌋ ≥ 0`.
-/
import Mathlib
import Combinatorics.A295431BalaGamma

set_option autoImplicit false

namespace Candidates.A295470Bala

open Candidates.A295431BalaGamma (landau_list div_div_eq_of_mul_eq gamma_half_of_odd)

/-! ## Definition layer -/

/-- The OEIS sequence A295470:
`a(n) = (20n)! (6n)! n! / ((12n)! (10n)! (3n)! (2n)!)`. The truncating `Nat`
division is exact; see `a295470_mul`. -/
def a295470 (n : ℕ) : ℕ :=
  (20 * n).factorial * (6 * n).factorial * n.factorial /
    ((12 * n).factorial * (10 * n).factorial * (3 * n).factorial * (2 * n).factorial)

/-- Bala's half-index value `a(n/2)`:
`(10n)! (3n)! Γ(n/2 + 1) / ((6n)! (5n)! Γ(3n/2 + 1) n!)`. Here
`(n/2)! := Γ(n/2 + 1)` and `(3n/2)! := Γ(3n/2 + 1)` as in the entry. The
denominator is positive (`balaRatio_denom_pos`), so the real division never
takes its junk value. -/
noncomputable def balaRatio (n : ℕ) : ℝ :=
  ((10 * n).factorial : ℝ) * ((3 * n).factorial : ℝ) * Real.Gamma ((n : ℝ) / 2 + 1) /
    (((6 * n).factorial : ℝ) * ((5 * n).factorial : ℝ) * Real.Gamma (3 * (n : ℝ) / 2 + 1) *
      (n.factorial : ℝ))

/-- The denominator of `balaRatio n` is positive. -/
theorem balaRatio_denom_pos (n : ℕ) :
    0 < ((6 * n).factorial : ℝ) * ((5 * n).factorial : ℝ) * Real.Gamma (3 * (n : ℝ) / 2 + 1) *
      (n.factorial : ℝ) := by
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

/-- The odd-case step inequality in the variable `j = ⌊30x⌋`:
`⌊j/5⌋ + ⌊j/6⌋ + ⌊j/60⌋ ≤ ⌊j/3⌋ + ⌊j/20⌋`, i.e.
`⌊6x⌋ + ⌊5x⌋ + ⌊x/2⌋ ≤ ⌊10x⌋ + ⌊3x/2⌋`. -/
theorem step_odd (j : ℕ) : j / 5 + j / 6 + j / 60 ≤ j / 3 + j / 20 := by
  have h := step_of_period 60 (by norm_num) [3, 20] [5, 6, 60] (by decide) (by decide)
    (by decide) (by decide) j
  simpa [add_assoc] using h

/-- The even-case step inequality in the variable `j = ⌊60y⌋`:
`⌊j/5⌋ + ⌊j/6⌋ + ⌊j/20⌋ + ⌊j/30⌋ ≤ ⌊j/3⌋ + ⌊j/10⌋ + ⌊j/60⌋`, i.e.
`⌊12y⌋ + ⌊10y⌋ + ⌊3y⌋ + ⌊2y⌋ ≤ ⌊20y⌋ + ⌊6y⌋ + ⌊y⌋`. -/
theorem step_even (j : ℕ) : j / 5 + j / 6 + j / 20 + j / 30 ≤ j / 3 + j / 10 + j / 60 := by
  have h := step_of_period 60 (by norm_num) [3, 10, 60] [5, 6, 20, 30] (by decide) (by decide)
    (by decide) (by decide) j
  simpa [add_assoc] using h

/-- The odd-case Landau term inequality, valid for every `n` and `q`:
`⌊6n/q⌋ + ⌊5n/q⌋ + ⌊⌊n/2⌋/q⌋ ≤ ⌊10n/q⌋ + ⌊⌊3n/2⌋/q⌋`. -/
theorem term_odd (n q : ℕ) :
    6 * n / q + 5 * n / q + n / 2 / q ≤ 10 * n / q + 3 * n / 2 / q := by
  have h := step_odd (30 * n / q)
  rw [div_div_eq_of_mul_eq 30 n q 6 5 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 30 n q 5 6 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 30 n q 1 60 2 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 30 n q 10 3 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 30 n q 3 20 2 (by norm_num) (by norm_num) (by norm_num)] at h
  simp only [one_mul] at h
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
  exact h

/-- The even-case Landau term inequality, valid for every `m` and `q`:
`⌊12m/q⌋ + ⌊10m/q⌋ + ⌊3m/q⌋ + ⌊2m/q⌋ ≤ ⌊20m/q⌋ + ⌊6m/q⌋ + ⌊m/q⌋`. -/
theorem term_even (m q : ℕ) :
    12 * m / q + 10 * m / q + 3 * m / q + 2 * m / q ≤ 20 * m / q + 6 * m / q + m / q := by
  have h := step_even (60 * m / q)
  rw [div_div_eq_of_mul_eq 60 m q 12 5 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 60 m q 10 6 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 60 m q 3 20 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 60 m q 2 30 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 60 m q 20 3 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 60 m q 6 10 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 60 m q 1 60 1 (by norm_num) (by norm_num) (by norm_num)] at h
  simpa only [one_mul] using h

/-! ## Factorial divisibilities -/

/-- For every `n`, `(6n)! (5n)! ⌊n/2⌋!` divides `(10n)! ⌊3n/2⌋!`. For odd `n`
this is stronger than needed: the factor `2^(2n)` of Bala's ratio is not
used. -/
theorem factorial_dvd_odd_form (n : ℕ) :
    (6 * n).factorial * (5 * n).factorial * (n / 2).factorial ∣
      (10 * n).factorial * (3 * n / 2).factorial := by
  have h := landau_list [10 * n, 3 * n / 2] [6 * n, 5 * n, n / 2] (10 * n)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun q => by
      have := term_odd n q
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      omega)
  simpa [mul_assoc] using h

/-- Integrality of A295470: `(12m)! (10m)! (3m)! (2m)!` divides
`(20m)! (6m)! m!`. -/
theorem factorial_dvd_a295470 (m : ℕ) :
    (12 * m).factorial * (10 * m).factorial * (3 * m).factorial * (2 * m).factorial ∣
      (20 * m).factorial * (6 * m).factorial * m.factorial := by
  have h := landau_list [20 * m, 6 * m, m] [12 * m, 10 * m, 3 * m, 2 * m] (20 * m)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun q => by
      have := term_even m q
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      omega)
  simpa [mul_assoc] using h

/-- The exact-division identity behind `a295470`. -/
theorem a295470_mul (m : ℕ) :
    (12 * m).factorial * (10 * m).factorial * (3 * m).factorial * (2 * m).factorial *
        a295470 m =
      (20 * m).factorial * (6 * m).factorial * m.factorial :=
  Nat.mul_div_cancel' (factorial_dvd_a295470 m)

/-! ## The Gamma bridge -/

/-- For odd `n`, suppose `(10n)! ⌊3n/2⌋! = (6n)! (5n)! ⌊n/2⌋! c`. Then Bala's
ratio equals `2^(2n) c`. -/
theorem balaRatio_of_odd {n c : ℕ} (hn : Odd n)
    (hc : (10 * n).factorial * (3 * n / 2).factorial =
      (6 * n).factorial * (5 * n).factorial * (n / 2).factorial * c) :
    balaRatio n = 2 ^ (2 * n) * (c : ℝ) := by
  have h3 : 3 * (n : ℝ) = ((3 * n : ℕ) : ℝ) := by push_cast; ring
  have hG1 := gamma_half_of_odd hn
  have hG3 := gamma_half_of_odd (Odd.mul (by decide : Odd 3) hn)
  have hcR : ((10 * n).factorial : ℝ) * (3 * n / 2).factorial =
      (6 * n).factorial * (5 * n).factorial * (n / 2).factorial * c := by
    exact_mod_cast hc
  have hpi : 0 < √Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hpos : (0 : ℝ) < (3 * n / 2).factorial := by positivity
  unfold balaRatio
  rw [h3, hG1, hG3]
  field_simp
  linear_combination (2 ^ (3 * n) : ℝ) * hcR

/-- For even `n = 2m`, Bala's ratio is the sequence term `a(m)`. -/
theorem balaRatio_two_mul (m : ℕ) : balaRatio (2 * m) = (a295470 m : ℝ) := by
  have hG1 : Real.Gamma (((2 * m : ℕ) : ℝ) / 2 + 1) = (m.factorial : ℝ) := by
    rw [← Real.Gamma_nat_eq_factorial]
    congr 1
    push_cast; ring
  have hG3 : Real.Gamma (3 * ((2 * m : ℕ) : ℝ) / 2 + 1) = ((3 * m).factorial : ℝ) := by
    rw [← Real.Gamma_nat_eq_factorial]
    congr 1
    push_cast; ring
  have hmul : (((12 * m).factorial * (10 * m).factorial * (3 * m).factorial *
      (2 * m).factorial * a295470 m : ℕ) : ℝ) =
      (((20 * m).factorial * (6 * m).factorial * m.factorial : ℕ) : ℝ) := by
    rw [a295470_mul]
  push_cast at hmul
  unfold balaRatio
  rw [hG1, hG3, show 10 * (2 * m) = 20 * m by ring, show 3 * (2 * m) = 6 * m by ring,
    show 6 * (2 * m) = 12 * m by ring, show 5 * (2 * m) = 10 * m by ring]
  have h12 : (0 : ℝ) < (12 * m).factorial := by positivity
  have h10 : (0 : ℝ) < (10 * m).factorial := by positivity
  have h3 : (0 : ℝ) < (3 * m).factorial := by positivity
  have h2 : (0 : ℝ) < (2 * m).factorial := by positivity
  rw [div_eq_iff (by positivity)]
  linear_combination -hmul

/-! ## Ground truth -/

example : a295470 0 = 1 := by decide
example : a295470 1 = 83980 := by decide
example : a295470 2 = 29966636700 := by decide

/-- Bala's ratio at `n = 1`: `10! 3! Γ(3/2) / (6! 5! Γ(5/2) 1!) = 168`. -/
theorem balaRatio_one : balaRatio 1 = 168 := by
  rw [balaRatio_of_odd (c := 42) (by decide) (by decide)]
  norm_num

/-- Bala's ratio at `n = 2` is `a(1) = 83980`. -/
example : balaRatio 2 = 83980 := by
  have h := balaRatio_two_mul 1
  rw [show (83980 : ℝ) = (a295470 1 : ℝ) by norm_num [show a295470 1 = 83980 by decide]]
  simpa using h

/-! ## The conjecture -/

/-- **Bala's conjecture, odd case (A295470, Peter Bala, Jul 30 2026).** For
every odd `n`, `(10n)! (3n)! Γ(n/2 + 1) / ((6n)! (5n)! Γ(3n/2 + 1) n!)` is an
integer. -/
theorem bala_integrality_of_odd (n : ℕ) (hn : Odd n) : ∃ z : ℤ, balaRatio n = z := by
  obtain ⟨c, hc⟩ := factorial_dvd_odd_form n
  refine ⟨2 ^ (2 * n) * c, ?_⟩
  rw [balaRatio_of_odd hn hc]
  push_cast
  ring

/-- **Bala's conjecture (A295470, Peter Bala, Jul 30 2026).** Verbatim:
"Conjecture: for n >= 0, a(n/2) = (10*n)!*(3*n)!*(n/2)! / ((6*n)!*(5*n)!*
(3*n/2)!*n!) is an integer, where fractional factorials are defined using the
Gamma function - for example, (3*n/2)! := Gamma(3*n/2 + 1)." Here
`balaRatio n` is `a(n/2)`. -/
theorem bala_integrality (n : ℕ) : ∃ z : ℤ, balaRatio n = z := by
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | hn
  · refine ⟨a295470 m, ?_⟩
    rw [← two_mul, balaRatio_two_mul]
    push_cast
    rfl
  · exact bala_integrality_of_odd n hn

end Candidates.A295470Bala
