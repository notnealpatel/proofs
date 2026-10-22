/-
# A295433 — integrality of Bala's half-index Gamma ratio

Peter Bala (OEIS A295433, Jun 13 2026) conjectured that `a(n/2)`,
also A347856(n), is integral for every natural `n`, with fractional
factorials interpreted as `x! = Γ(x+1)`. The sequence is
`a(n) = (12n)! n! / ((8n)! (3n)! (2n)!)`.
The proof uses the Landau-criterion framework of `Combinatorics.A295431BalaGamma`.

* Odd `n`: `Γ(k/2 + 1) = k! √π / (2^k ⌊k/2⌋!)` for odd `k`, so the ratio
  equals `2^(2n) (6n)! ⌊3n/2⌋! / ((4n)! (3n)! ⌊n/2⌋!)`. The factorial quotient
  without the power of two is already an integer by Landau's criterion: the step
  function `⌊6x⌋ + ⌊3x/2⌋ - ⌊4x⌋ - ⌊3x⌋ - ⌊x/2⌋` is nonnegative. With
  `j = ⌊12x⌋` every term is `⌊j/d⌋` for a divisor `d` of `24`, so a finite
  `decide` over `j < 24` closes it.
* Even `n = 2m`: the ratio is `a(m)`, integral by Landau's criterion with
  `⌊12y⌋ + ⌊y⌋ - ⌊8y⌋ - ⌊3y⌋ - ⌊2y⌋ ≥ 0` (period `24` in `j = ⌊24y⌋`).
-/
import Mathlib
import Combinatorics.A295431BalaGamma

set_option autoImplicit false

namespace Candidates.A295433BalaJunGamma

open Candidates.A295431BalaGamma (landau_list div_div_eq_of_mul_eq gamma_half_of_odd)

/-! ## Definitions -/

/-- The OEIS sequence A295433: `a(n) = (12n)! n! / ((8n)! (3n)! (2n)!)`. The
truncating `Nat` division is exact; see `a295433_mul`. -/
def a295433 (n : ℕ) : ℕ :=
  (12 * n).factorial * n.factorial / ((8 * n).factorial * (3 * n).factorial * (2 * n).factorial)

/-- Bala's half-index value `a(n/2) = A347856(n)`:
`(6n)! Γ(n/2 + 1) / ((4n)! Γ(3n/2 + 1) n!)`. Here `(n/2)! := Γ(n/2 + 1)` as in
the entry. The denominator is positive (`balaRatio_denom_pos`), so the real
division never takes its junk value. -/
noncomputable def balaRatio (n : ℕ) : ℝ :=
  ((6 * n).factorial : ℝ) * Real.Gamma ((n : ℝ) / 2 + 1) /
    (((4 * n).factorial : ℝ) * Real.Gamma (3 * (n : ℝ) / 2 + 1) * (n.factorial : ℝ))

/-- The denominator of `balaRatio n` is positive. -/
theorem balaRatio_denom_pos (n : ℕ) :
    0 < ((4 * n).factorial : ℝ) * Real.Gamma (3 * (n : ℝ) / 2 + 1) * (n.factorial : ℝ) := by
  have hG : 0 < Real.Gamma (3 * (n : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
  positivity

/-! ## The step-function inequalities (period `24`) -/

/-- Shifting by a multiple of `P` shifts the quotient by a divisor `d` of `P`
linearly. -/
theorem add_mul_div_of_dvd (P s t d : ℕ) (hd : d ∣ P) (hd0 : 0 < d) :
    (s + P * t) / d = s / d + P / d * t := by
  obtain ⟨k, hk⟩ := hd
  have hkd : P / d = k := by rw [hk, Nat.mul_div_cancel_left _ hd0]
  rw [hkd, hk, mul_assoc, Nat.add_mul_div_left _ _ hd0]

/-- Reduce a floor inequality to a single period `P`. Assume that
`∑_{d ∈ ds} ⌊s/d⌋ ≤ ∑_{d ∈ cs} ⌊s/d⌋` for every residue `s < P`, that every `d`
divides `P`, and that the linear parts agree. Then the inequality holds for all
`j`. -/
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

/-- The odd-case step inequality in the variable `j = ⌊12x⌋`:
`⌊j/3⌋ + ⌊j/4⌋ + ⌊j/24⌋ ≤ ⌊j/2⌋ + ⌊j/8⌋`, i.e.
`⌊4x⌋ + ⌊3x⌋ + ⌊x/2⌋ ≤ ⌊6x⌋ + ⌊3x/2⌋`. -/
theorem step_odd (j : ℕ) : j / 3 + j / 4 + j / 24 ≤ j / 2 + j / 8 := by
  have h := step_of_period 24 (by norm_num) [2, 8] [3, 4, 24] (by decide) (by decide)
    (by decide) (by decide) j
  simpa [add_assoc] using h

/-- The even-case step inequality in the variable `j = ⌊24y⌋`:
`⌊j/3⌋ + ⌊j/8⌋ + ⌊j/12⌋ ≤ ⌊j/2⌋ + ⌊j/24⌋`, i.e.
`⌊8y⌋ + ⌊3y⌋ + ⌊2y⌋ ≤ ⌊12y⌋ + ⌊y⌋`. -/
theorem step_even (j : ℕ) : j / 3 + j / 8 + j / 12 ≤ j / 2 + j / 24 := by
  have h := step_of_period 24 (by norm_num) [2, 24] [3, 8, 12] (by decide) (by decide)
    (by decide) (by decide) j
  simpa [add_assoc] using h

/-- The odd-case Landau term inequality, valid for every `n` and `q`:
`⌊4n/q⌋ + ⌊3n/q⌋ + ⌊⌊n/2⌋/q⌋ ≤ ⌊6n/q⌋ + ⌊⌊3n/2⌋/q⌋`. -/
theorem term_odd (n q : ℕ) :
    4 * n / q + 3 * n / q + n / 2 / q ≤ 6 * n / q + 3 * n / 2 / q := by
  have h := step_odd (12 * n / q)
  rw [div_div_eq_of_mul_eq 12 n q 4 3 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 12 n q 3 4 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 12 n q 1 24 2 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 12 n q 6 2 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 12 n q 3 8 2 (by norm_num) (by norm_num) (by norm_num)] at h
  simp only [one_mul] at h
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
  exact h

/-- The even-case Landau term inequality, valid for every `m` and `q`:
`⌊8m/q⌋ + ⌊3m/q⌋ + ⌊2m/q⌋ ≤ ⌊12m/q⌋ + ⌊m/q⌋`. -/
theorem term_even (m q : ℕ) :
    8 * m / q + 3 * m / q + 2 * m / q ≤ 12 * m / q + m / q := by
  have h := step_even (24 * m / q)
  rw [div_div_eq_of_mul_eq 24 m q 8 3 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 24 m q 3 8 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 24 m q 2 12 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 24 m q 12 2 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 24 m q 1 24 1 (by norm_num) (by norm_num) (by norm_num)] at h
  simpa only [one_mul] using h

/-! ## Factorial divisibilities -/

/-- For every `n`, `(4n)! (3n)! ⌊n/2⌋!` divides `(6n)! ⌊3n/2⌋!`. For odd `n`
this is stronger than needed: the factor `2^(2n)` of Bala's ratio is not used. -/
theorem factorial_dvd_odd_form (n : ℕ) :
    (4 * n).factorial * (3 * n).factorial * (n / 2).factorial ∣
      (6 * n).factorial * (3 * n / 2).factorial := by
  have h := landau_list [6 * n, 3 * n / 2] [4 * n, 3 * n, n / 2] (6 * n)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun q => by simpa [add_assoc] using term_odd n q)
  simpa [mul_assoc] using h

/-- Integrality of A295433: `(8m)! (3m)! (2m)!` divides `(12m)! m!`. -/
theorem factorial_dvd_a295433 (m : ℕ) :
    (8 * m).factorial * (3 * m).factorial * (2 * m).factorial ∣
      (12 * m).factorial * m.factorial := by
  have h := landau_list [12 * m, m] [8 * m, 3 * m, 2 * m] (12 * m)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun q => by
      have := term_even m q
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      omega)
  simpa [mul_assoc] using h

/-- The exact-division identity behind `a295433`. -/
theorem a295433_mul (m : ℕ) :
    (8 * m).factorial * (3 * m).factorial * (2 * m).factorial * a295433 m =
      (12 * m).factorial * m.factorial :=
  Nat.mul_div_cancel' (factorial_dvd_a295433 m)

/-! ## The Gamma bridge -/

/-- For odd `n`, suppose `(6n)! ⌊3n/2⌋! = (4n)! (3n)! ⌊n/2⌋! c`. Then Bala's
ratio equals `2^(2n) c`. -/
theorem balaRatio_of_odd {n c : ℕ} (hn : Odd n)
    (hc : (6 * n).factorial * (3 * n / 2).factorial =
      (4 * n).factorial * (3 * n).factorial * (n / 2).factorial * c) :
    balaRatio n = 2 ^ (2 * n) * (c : ℝ) := by
  have h3 : 3 * (n : ℝ) = ((3 * n : ℕ) : ℝ) := by push_cast; ring
  have hG1 := gamma_half_of_odd hn
  have hG3 := gamma_half_of_odd (Odd.mul (by decide : Odd 3) hn)
  have hcR : ((6 * n).factorial : ℝ) * (3 * n / 2).factorial =
      (4 * n).factorial * (3 * n).factorial * (n / 2).factorial * c := by
    exact_mod_cast hc
  have hpi : 0 < √Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hpos : (0 : ℝ) < (3 * n / 2).factorial := by positivity
  unfold balaRatio
  rw [h3, hG1, hG3]
  field_simp
  linear_combination (2 ^ (3 * n) : ℝ) * hcR

/-- For even `n = 2m`, Bala's ratio is the sequence term `a(m)`. -/
theorem balaRatio_two_mul (m : ℕ) : balaRatio (2 * m) = (a295433 m : ℝ) := by
  have hG1 : Real.Gamma (((2 * m : ℕ) : ℝ) / 2 + 1) = (m.factorial : ℝ) := by
    rw [← Real.Gamma_nat_eq_factorial]
    congr 1
    push_cast; ring
  have hG3 : Real.Gamma (3 * ((2 * m : ℕ) : ℝ) / 2 + 1) = ((3 * m).factorial : ℝ) := by
    rw [← Real.Gamma_nat_eq_factorial]
    congr 1
    push_cast; ring
  have hmul : (((8 * m).factorial * (3 * m).factorial * (2 * m).factorial * a295433 m : ℕ) : ℝ) =
      (((12 * m).factorial * m.factorial : ℕ) : ℝ) := by
    rw [a295433_mul]
  push_cast at hmul
  unfold balaRatio
  rw [hG1, hG3, show 6 * (2 * m) = 12 * m by ring, show 4 * (2 * m) = 8 * m by ring]
  have h8 : (0 : ℝ) < (8 * m).factorial := by positivity
  have h3 : (0 : ℝ) < (3 * m).factorial := by positivity
  have h2 : (0 : ℝ) < (2 * m).factorial := by positivity
  rw [div_eq_iff (by positivity)]
  linear_combination -hmul

/-! ## Examples -/

example : a295433 0 = 1 := by decide
example : a295433 1 = 990 := by decide
example : a295433 2 = 3432198 := by decide

/-- Bala's ratio at `n = 1`: `6! Γ(3/2) / (4! Γ(5/2) 1!) = 20 = A347856(1)`. -/
theorem balaRatio_one : balaRatio 1 = 20 := by
  rw [balaRatio_of_odd (c := 5) (by decide) (by decide)]
  norm_num

/-- Bala's ratio at `n = 3`: `18! Γ(5/2) / (12! Γ(11/2) 3!) = 56576 = A347856(3)`. -/
theorem balaRatio_three : balaRatio 3 = 56576 := by
  rw [balaRatio_of_odd (c := 884) (by decide) (by decide)]
  norm_num

/-- Bala's ratio at `n = 2` is `a(1) = 990 = A347856(2)`. -/
example : balaRatio 2 = 990 := by
  have h := balaRatio_two_mul 1
  rw [show (990 : ℝ) = (a295433 1 : ℝ) by norm_num [show a295433 1 = 990 by decide]]
  simpa using h

/-! ## The conjecture -/

/-- **Bala's conjecture, odd case (A295433, Peter Bala, Jun 13 2026).** For every
odd `n`, `(6n)! Γ(n/2 + 1) / ((4n)! Γ(3n/2 + 1) n!)` is a natural number; in
fact it equals `2^(2n) c` with `c = (6n)! ⌊3n/2⌋! / ((4n)! (3n)! ⌊n/2⌋!)`. -/
theorem bala_integrality_of_odd (n : ℕ) (hn : Odd n) : ∃ k : ℕ, balaRatio n = k := by
  obtain ⟨c, hc⟩ := factorial_dvd_odd_form n
  refine ⟨2 ^ (2 * n) * c, ?_⟩
  rw [balaRatio_of_odd hn hc]
  push_cast
  ring

/-- Bala's conjecture (OEIS A295433, Peter Bala, Jun 13 2026):
`balaRatio n` is a natural number for every natural `n`, with fractional
factorials interpreted as `x! = Γ(x+1)`. -/
theorem bala_integrality (n : ℕ) : ∃ k : ℕ, balaRatio n = k := by
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | hn
  · exact ⟨a295433 m, by rw [← two_mul, balaRatio_two_mul]⟩
  · exact bala_integrality_of_odd n hn

end Candidates.A295433BalaJunGamma
