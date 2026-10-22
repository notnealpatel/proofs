/-
# A295431 — Bala: the half-index Gamma ratio `a(n/2)` is an integer

Peter Bala's conjecture in OEIS A295431 (June 9, 2026) asserts integrality
of both `a(n/2)` and `a(n/3)`, interpreting `x!` as `Γ(x+1)`.
Here `a(n) = (12n)! n! / ((6n)! (4n)! (3n)!)`.
This file proves the integrality of the half-index ratio `a(n/2)`;
the third-index assertion is not formalized.

* Odd `n`: `Γ(k/2 + 1) = k! √π / (2^k ⌊k/2⌋!)` for odd `k`, so the ratio
  equals `2^(2n) (6n)! n! ⌊3n/2⌋! / ((3n)! (2n)! (3n)! ⌊n/2⌋!)`. Landau's
  criterion shows that the factorial quotient without the power of two is
  already an integer. The step function behind it is
  `⌊6x⌋ + ⌊x⌋ + ⌊3x/2⌋ - 2⌊3x⌋ - ⌊2x⌋ - ⌊x/2⌋`. With `j = ⌊6x⌋` every term
  is `⌊j/d⌋` for a divisor `d` of `12`, so a finite `decide` over `j < 12`
  closes it.
* Even `n = 2m`: the ratio is `a(m)`, integral by Landau's criterion with
  `⌊12y⌋ + ⌊y⌋ - ⌊6y⌋ - ⌊4y⌋ - ⌊3y⌋ ≥ 0`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A295431BalaGamma

/-! ## Definition layer -/

/-- The OEIS sequence A295431: `a(n) = (12n)! n! / ((6n)! (4n)! (3n)!)`. The
truncating `Nat` division is exact; see `a295431_mul`. -/
def a295431 (n : ℕ) : ℕ :=
  (12 * n).factorial * n.factorial / ((6 * n).factorial * (4 * n).factorial * (3 * n).factorial)

/-- Bala's half-index value `a(n/2)`: `(6n)! Γ(n/2 + 1) / ((3n)! (2n)! Γ(3n/2 + 1))`.
Here `(n/2)! := Γ(n/2 + 1)` as in the entry. The denominator is positive
(`balaRatio_denom_pos`), so the real division never takes its junk value. -/
noncomputable def balaRatio (n : ℕ) : ℝ :=
  ((6 * n).factorial : ℝ) * Real.Gamma ((n : ℝ) / 2 + 1) /
    (((3 * n).factorial : ℝ) * ((2 * n).factorial : ℝ) * Real.Gamma (3 * (n : ℝ) / 2 + 1))

/-- The denominator of `balaRatio n` is positive. -/
theorem balaRatio_denom_pos (n : ℕ) :
    0 < ((3 * n).factorial : ℝ) * ((2 * n).factorial : ℝ) * Real.Gamma (3 * (n : ℝ) / 2 + 1) := by
  have hG : 0 < Real.Gamma (3 * (n : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
  positivity

/-! ## Landau's criterion for products of factorials -/

/-- Legendre's formula for a product of factorials. Let `p` be prime and let
`b` exceed `log_p x` for every `x ∈ l`. Then
`v_p(∏_{x ∈ l} x!) = ∑_{1 ≤ i < b} ∑_{x ∈ l} ⌊x / p^i⌋`. -/
theorem factorization_prod_factorial {p : ℕ} (hp : p.Prime) (b : ℕ) :
    ∀ l : List ℕ, (∀ x ∈ l, Nat.log p x < b) →
      (l.map Nat.factorial).prod.factorization p =
        ∑ i ∈ Finset.Ico 1 b, (l.map (· / p ^ i)).sum
  | [], _ => by simp
  | x :: l, hl => by
    have hx : Nat.log p x < b := hl x (List.mem_cons_self ..)
    have ih := factorization_prod_factorial hp b l fun y hy => hl y (List.mem_cons_of_mem _ hy)
    have hne : (l.map Nat.factorial).prod ≠ 0 := by simp [Nat.factorial_ne_zero]
    rw [List.map_cons, List.prod_cons, Nat.factorization_mul (Nat.factorial_ne_zero x) hne,
      Finsupp.add_apply, ih, Nat.factorization_factorial hp hx, ← Finset.sum_add_distrib]
    simp

/-- Landau's criterion (the sufficient direction) for lists of naturals. Suppose
`∑_{y ∈ bs} ⌊y/q⌋ ≤ ∑_{x ∈ as} ⌊x/q⌋` for every `q`. Then `∏_{y ∈ bs} y!`
divides `∏_{x ∈ as} x!`. The bound `M` only supplies a common range for
Legendre's formula. -/
theorem landau_list (as bs : List ℕ) (M : ℕ) (has : ∀ x ∈ as, x ≤ M) (hbs : ∀ x ∈ bs, x ≤ M)
    (hterm : ∀ q : ℕ, (bs.map (· / q)).sum ≤ (as.map (· / q)).sum) :
    (bs.map Nat.factorial).prod ∣ (as.map Nat.factorial).prod := by
  have hne : ∀ l : List ℕ, (l.map Nat.factorial).prod ≠ 0 := fun l => by
    simp [Nat.factorial_ne_zero]
  rw [← Nat.factorization_le_iff_dvd (hne bs) (hne as), Finsupp.le_def]
  intro p
  by_cases hp : p.Prime
  · have hb : ∀ x ≤ M, Nat.log p x < M + 1 := fun x hx =>
      Nat.lt_succ_of_le ((Nat.log_le_self p x).trans hx)
    rw [factorization_prod_factorial hp (M + 1) bs fun x hx => hb x (hbs x hx),
      factorization_prod_factorial hp (M + 1) as fun x hx => hb x (has x hx)]
    exact Finset.sum_le_sum fun i _ => hterm (p ^ i)
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

/-! ## The step-function inequalities -/

/-- Shifting by a multiple of `12` shifts the quotient by a divisor `d` of `12`
linearly. -/
theorem add_mul_12_div (s t d : ℕ) (hd : d ∣ 12) (hd0 : 0 < d) :
    (s + 12 * t) / d = s / d + 12 / d * t := by
  obtain ⟨k, hk⟩ := hd
  have hkd : 12 / d = k := by rw [hk, Nat.mul_div_cancel_left _ hd0]
  rw [hkd, hk, mul_assoc, Nat.add_mul_div_left _ _ hd0]

/-- Reduce a floor inequality to a single period. Assume that
`∑_{d ∈ ds} ⌊s/d⌋ ≤ ∑_{d ∈ cs} ⌊s/d⌋` for every residue `s < 12`. Assume also
that every `d` divides `12` and the linear parts agree. Then the inequality
holds for all `j`. -/
theorem step_of_period (cs ds : List ℕ) (hcs : ∀ d ∈ cs, d ∣ 12 ∧ 0 < d)
    (hds : ∀ d ∈ ds, d ∣ 12 ∧ 0 < d)
    (hlin : (ds.map (12 / ·)).sum = (cs.map (12 / ·)).sum)
    (hsmall : ∀ s < 12, (ds.map (s / ·)).sum ≤ (cs.map (s / ·)).sum) (j : ℕ) :
    (ds.map (j / ·)).sum ≤ (cs.map (j / ·)).sum := by
  have hshift : ∀ (l : List ℕ), (∀ d ∈ l, d ∣ 12 ∧ 0 < d) → ∀ s t : ℕ,
      (l.map ((s + 12 * t) / ·)).sum = (l.map (s / ·)).sum + (l.map (12 / ·)).sum * t := by
    intro l hl s t
    induction l with
    | nil => simp
    | cons d l ih =>
      have hd := hl d (List.mem_cons_self ..)
      simp only [List.map_cons, List.sum_cons]
      rw [add_mul_12_div s t d hd.1 hd.2, ih fun e he => hl e (List.mem_cons_of_mem _ he)]
      ring
  have hj : j = j % 12 + 12 * (j / 12) := (Nat.mod_add_div j 12).symm
  rw [hj, hshift cs hcs, hshift ds hds, hlin]
  have hs := hsmall (j % 12) (Nat.mod_lt _ (by norm_num))
  omega

/-- The odd-case step inequality in the variable `j = ⌊6x⌋`:
`⌊j/2⌋ + ⌊j/2⌋ + ⌊j/3⌋ + ⌊j/12⌋ ≤ ⌊j/1⌋ + ⌊j/6⌋ + ⌊j/4⌋`, i.e.
`2⌊3x⌋ + ⌊2x⌋ + ⌊x/2⌋ ≤ ⌊6x⌋ + ⌊x⌋ + ⌊3x/2⌋`. -/
theorem step_odd (j : ℕ) : j / 2 + j / 2 + j / 3 + j / 12 ≤ j / 1 + j / 6 + j / 4 := by
  have h := step_of_period [1, 6, 4] [2, 2, 3, 12] (by decide) (by decide) (by decide)
    (by decide) j
  simpa [add_assoc] using h

/-- The even-case step inequality in the variable `j = ⌊12y⌋`:
`⌊j/2⌋ + ⌊j/3⌋ + ⌊j/4⌋ ≤ ⌊j/1⌋ + ⌊j/12⌋`, i.e.
`⌊6y⌋ + ⌊4y⌋ + ⌊3y⌋ ≤ ⌊12y⌋ + ⌊y⌋`. -/
theorem step_even (j : ℕ) : j / 2 + j / 3 + j / 4 ≤ j / 1 + j / 12 := by
  have h := step_of_period [1, 12] [2, 3, 4] (by decide) (by decide) (by decide)
    (by decide) j
  simpa [add_assoc] using h

/-- Floors of rational multiples factor through `⌊K a / q⌋`. If `c d = K e` and
`0 < d`, `0 < e`, then `⌊⌊K a / q⌋ / d⌋ = ⌊c a / (e q)⌋`. -/
theorem div_div_eq_of_mul_eq (K a q c d e : ℕ) (hd : 0 < d) (he : 0 < e) (h : c * d = K * e) :
    (K * a / q) / d = c * a / (e * q) := by
  rw [Nat.div_div_eq_div_mul, ← Nat.mul_div_mul_left (c * a) (e * q) hd,
    ← Nat.mul_div_mul_left (K * a) (q * d) he]
  congr 1
  · calc e * (K * a) = (c * d) * a := by rw [h]; ring
      _ = d * (c * a) := by ring
  · ring

/-- The odd-case Landau term inequality, valid for every `n` and `q`:
`⌊3n/q⌋ + ⌊3n/q⌋ + ⌊2n/q⌋ + ⌊⌊n/2⌋/q⌋ ≤ ⌊6n/q⌋ + ⌊n/q⌋ + ⌊⌊3n/2⌋/q⌋`. -/
theorem term_odd (n q : ℕ) :
    3 * n / q + 3 * n / q + 2 * n / q + n / 2 / q ≤ 6 * n / q + n / q + 3 * n / 2 / q := by
  have h := step_odd (6 * n / q)
  rw [div_div_eq_of_mul_eq 6 n q 3 2 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 6 n q 2 3 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 6 n q 1 12 2 (by norm_num) (by norm_num) (by norm_num),
    Nat.div_one,
    div_div_eq_of_mul_eq 6 n q 1 6 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 6 n q 3 4 2 (by norm_num) (by norm_num) (by norm_num)] at h
  simp only [one_mul] at h
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
  exact h

/-- The even-case Landau term inequality, valid for every `m` and `q`:
`⌊6m/q⌋ + ⌊4m/q⌋ + ⌊3m/q⌋ ≤ ⌊12m/q⌋ + ⌊m/q⌋`. -/
theorem term_even (m q : ℕ) :
    6 * m / q + 4 * m / q + 3 * m / q ≤ 12 * m / q + m / q := by
  have h := step_even (12 * m / q)
  rw [div_div_eq_of_mul_eq 12 m q 6 2 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 12 m q 4 3 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 12 m q 3 4 1 (by norm_num) (by norm_num) (by norm_num),
    Nat.div_one,
    div_div_eq_of_mul_eq 12 m q 1 12 1 (by norm_num) (by norm_num) (by norm_num)] at h
  simpa only [one_mul] using h

/-! ## Factorial divisibilities -/

/-- For every `n`, `(3n)! (3n)! (2n)! ⌊n/2⌋!` divides `(6n)! n! ⌊3n/2⌋!`. For
odd `n` this is stronger than needed: the factor `2^(2n)` of Bala's ratio is
not used. -/
theorem factorial_dvd_odd_form (n : ℕ) :
    (3 * n).factorial * (3 * n).factorial * (2 * n).factorial * (n / 2).factorial ∣
      (6 * n).factorial * n.factorial * (3 * n / 2).factorial := by
  have h := landau_list [6 * n, n, 3 * n / 2] [3 * n, 3 * n, 2 * n, n / 2] (6 * n)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun q => by simpa [add_assoc] using term_odd n q)
  simpa [mul_assoc] using h

/-- Integrality of A295431: `(6m)! (4m)! (3m)!` divides `(12m)! m!`. -/
theorem factorial_dvd_a295431 (m : ℕ) :
    (6 * m).factorial * (4 * m).factorial * (3 * m).factorial ∣
      (12 * m).factorial * m.factorial := by
  have h := landau_list [12 * m, m] [6 * m, 4 * m, 3 * m] (12 * m)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun q => by
      have := term_even m q
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      omega)
  simpa [mul_assoc] using h

/-- The exact-division identity behind `a295431`. -/
theorem a295431_mul (m : ℕ) :
    (6 * m).factorial * (4 * m).factorial * (3 * m).factorial * a295431 m =
      (12 * m).factorial * m.factorial :=
  Nat.mul_div_cancel' (factorial_dvd_a295431 m)

/-! ## The Gamma bridge -/

/-- `Γ((2j+1)/2 + 1) = (2j+1)! √π / (2^(2j+1) j!)`. -/
theorem gamma_odd_half (j : ℕ) :
    Real.Gamma (((2 * j + 1 : ℕ) : ℝ) / 2 + 1) =
      ((2 * j + 1).factorial : ℝ) * √Real.pi / (2 ^ (2 * j + 1) * (j.factorial : ℝ)) := by
  have harg : ((2 * j + 1 : ℕ) : ℝ) / 2 + 1 = ((j + 1 : ℕ) : ℝ) + 1 / 2 := by
    push_cast; ring
  have hfact : (2 * j + 1).factorial = (2 * j + 1).doubleFactorial * (2 ^ j * j.factorial) := by
    rw [Nat.factorial_eq_mul_doubleFactorial, Nat.doubleFactorial_two_mul]
  rw [harg, Real.Gamma_nat_add_half, show 2 * (j + 1) - 1 = 2 * j + 1 by omega, hfact]
  push_cast
  field_simp
  ring

/-- For odd `k`, `Γ(k/2 + 1) = k! √π / (2^k ⌊k/2⌋!)`. -/
theorem gamma_half_of_odd {k : ℕ} (hk : Odd k) :
    Real.Gamma ((k : ℝ) / 2 + 1) =
      (k.factorial : ℝ) * √Real.pi / (2 ^ k * ((k / 2).factorial : ℝ)) := by
  obtain ⟨j, rfl⟩ := hk
  rw [show (2 * j + 1) / 2 = j by omega]
  exact gamma_odd_half j

/-- For odd `n`, suppose `(6n)! n! ⌊3n/2⌋! = (3n)! (3n)! (2n)! ⌊n/2⌋! c`.
Then Bala's ratio equals `2^(2n) c`. -/
theorem balaRatio_of_odd {n c : ℕ} (hn : Odd n)
    (hc : (6 * n).factorial * n.factorial * (3 * n / 2).factorial =
      (3 * n).factorial * (3 * n).factorial * (2 * n).factorial * (n / 2).factorial * c) :
    balaRatio n = 2 ^ (2 * n) * (c : ℝ) := by
  have h3 : 3 * (n : ℝ) = ((3 * n : ℕ) : ℝ) := by push_cast; ring
  have hG1 := gamma_half_of_odd hn
  have hG3 := gamma_half_of_odd (Odd.mul (by decide : Odd 3) hn)
  have hcR : ((6 * n).factorial : ℝ) * n.factorial * (3 * n / 2).factorial =
      (3 * n).factorial * (3 * n).factorial * (2 * n).factorial * (n / 2).factorial * c := by
    exact_mod_cast hc
  have hpi : 0 < √Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hpos : (0 : ℝ) < (3 * n / 2).factorial := by positivity
  unfold balaRatio
  rw [h3, hG1, hG3]
  field_simp
  linear_combination (2 ^ (3 * n) : ℝ) * hcR

/-- For even `n = 2m`, Bala's ratio is the sequence term `a(m)`. -/
theorem balaRatio_two_mul (m : ℕ) : balaRatio (2 * m) = (a295431 m : ℝ) := by
  have hG1 : Real.Gamma (((2 * m : ℕ) : ℝ) / 2 + 1) = (m.factorial : ℝ) := by
    rw [← Real.Gamma_nat_eq_factorial]
    congr 1
    push_cast; ring
  have hG3 : Real.Gamma (3 * ((2 * m : ℕ) : ℝ) / 2 + 1) = ((3 * m).factorial : ℝ) := by
    rw [← Real.Gamma_nat_eq_factorial]
    congr 1
    push_cast; ring
  have hmul : (((6 * m).factorial * (4 * m).factorial * (3 * m).factorial * a295431 m : ℕ) : ℝ) =
      (((12 * m).factorial * m.factorial : ℕ) : ℝ) := by
    rw [a295431_mul]
  push_cast at hmul
  unfold balaRatio
  rw [hG1, hG3, show 6 * (2 * m) = 12 * m by ring, show 3 * (2 * m) = 6 * m by ring,
    show 2 * (2 * m) = 4 * m by ring]
  have h6 : (0 : ℝ) < (6 * m).factorial := by positivity
  have h4 : (0 : ℝ) < (4 * m).factorial := by positivity
  have h3 : (0 : ℝ) < (3 * m).factorial := by positivity
  rw [div_eq_iff (by positivity)]
  linear_combination -hmul

/-! ## Examples -/

example : a295431 0 = 1 := by decide
example : a295431 1 = 4620 := by decide
example : a295431 2 = 89237148 := by decide

/-- Bala's ratio at `n = 1`: `6! Γ(3/2) / (3! 2! Γ(5/2)) = 40 = A347854(1)`. -/
theorem balaRatio_one : balaRatio 1 = 40 := by
  rw [balaRatio_of_odd (c := 10) (by decide) (by decide)]
  norm_num

/-- Bala's ratio at `n = 3`: `18! Γ(5/2) / (9! 6! Γ(11/2)) = 622336 = A347854(3)`. -/
theorem balaRatio_three : balaRatio 3 = 622336 := by
  rw [balaRatio_of_odd (c := 9724) (by decide) (by decide)]
  norm_num

/-- Bala's ratio at `n = 2` is `a(1) = 4620 = A347854(2)`. -/
example : balaRatio 2 = 4620 := by
  have h := balaRatio_two_mul 1
  rw [show (4620 : ℝ) = (a295431 1 : ℝ) by norm_num [show a295431 1 = 4620 by decide]]
  simpa using h

/-! ## The conjecture -/

/-- **Bala's conjecture, odd case (A295431, Peter Bala, Jun 09 2026).** For every
odd `n`, `(6n)! Γ(n/2 + 1) / ((3n)! (2n)! Γ(3n/2 + 1))` is an integer. -/
theorem bala_integrality_of_odd (n : ℕ) (hn : Odd n) : ∃ z : ℤ, balaRatio n = z := by
  obtain ⟨c, hc⟩ := factorial_dvd_odd_form n
  refine ⟨2 ^ (2 * n) * c, ?_⟩
  rw [balaRatio_of_odd hn hc]
  push_cast
  ring

/-- Bala's conjecture (OEIS A295431, June 9, 2026), half-index part:
`balaRatio n = a(n/2)` is an integer for every natural `n`, with
fractional factorials interpreted as `x! = Γ(x+1)`.
The companion third-index assertion is not part of this theorem. -/
theorem bala_integrality (n : ℕ) : ∃ z : ℤ, balaRatio n = z := by
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | hn
  · refine ⟨a295431 m, ?_⟩
    rw [← two_mul, balaRatio_two_mul]
    push_cast
    rfl
  · exact bala_integrality_of_odd n hn

end Candidates.A295431BalaGamma
