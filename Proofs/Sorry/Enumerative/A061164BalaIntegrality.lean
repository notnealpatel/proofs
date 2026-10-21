/-
# A061164 — Bala: half-integer factorial ratio is an integer

## OEIS source (retrieved with `oeis show A061164`, 2026-10-21)

```
NAME:     a(n) = (20*n)!*n!/((10*n)!*(7*n)!*(4*n)!).
TERMS:    1,5542680,190818980609400,7691041400616850556280,...
COMMENT (the conjecture):
  Conjecture: for n >= 0, a(n/2) = (10*n)!*(n/2)! / ((5*n)!*(7*n/2)!*(2*n)!)
  is an integer, where fractional factorials are defined using the Gamma
  function - for example, (n/2)! := Gamma(n/2 + 1). - _Peter Bala_, Jul 31 2026
COMMENT (context):
  One of the 52 sporadic integral factorial ratio sequences found by
  V. I. Vasyunin (see Bober, Table 2, Entry 43). - _Peter Bala_, Apr 10 2012
```

## Literature status (triage)

Open: no proof in the entry or in the literature as far as the triage could
tell (the cited arXiv:2608.11941 of Adamczewski does not cover it). The even
case `n = 2m` is the integrality of `a(m)` itself (Vasyunin, Bober). Same-day
sibling conjectures by Bala sit in A295475, A295477, A295479 and A295481.

## Result of this module

The conjecture is proved for every `n`, with no remaining `sorry`.

* Odd `n`: `Γ(k/2 + 1) = k! √π / (2^k ⌊k/2⌋!)` for odd `k`, so the ratio
  equals `2^(6n) (10n)! n! ⌊7n/2⌋! / ((5n)! (2n)! (7n)! ⌊n/2⌋!)`. Landau's
  criterion shows that the factorial quotient without the power of two is
  already an integer. The step function behind it is
  `⌊10x⌋ + ⌊x⌋ + ⌊7x/2⌋ - ⌊5x⌋ - ⌊2x⌋ - ⌊7x⌋ - ⌊x/2⌋`. It is constant on
  intervals `[j/70, (j+1)/70)` and has period `2`. Writing `j = ⌊70x⌋` reduces
  it to a finite `decide` over `j < 140`.
* Even `n = 2m`: the ratio is `a(m)`. Its integrality follows from the same
  Landau argument with the step function
  `⌊20y⌋ + ⌊y⌋ - ⌊10y⌋ - ⌊7y⌋ - ⌊4y⌋`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A061164BalaIntegrality

/-! ## Definition layer -/

/-- The OEIS sequence A061164: `a(n) = (20n)! n! / ((10n)! (7n)! (4n)!)`. The
truncating `Nat` division is exact; see `a061164_mul`. -/
def a061164 (n : ℕ) : ℕ :=
  (20 * n).factorial * n.factorial / ((10 * n).factorial * (7 * n).factorial * (4 * n).factorial)

/-- Bala's half-index value `a(n/2)`: `(10n)! Γ(n/2 + 1) / ((5n)! Γ(7n/2 + 1) (2n)!)`.
Here `(n/2)! := Γ(n/2 + 1)` as in the entry. The denominator is positive
(`balaRatio_denom_pos`), so the real division never takes its junk value. -/
noncomputable def balaRatio (n : ℕ) : ℝ :=
  ((10 * n).factorial : ℝ) * Real.Gamma ((n : ℝ) / 2 + 1) /
    (((5 * n).factorial : ℝ) * Real.Gamma (7 * (n : ℝ) / 2 + 1) * ((2 * n).factorial : ℝ))

/-- The denominator of `balaRatio n` is positive. -/
theorem balaRatio_denom_pos (n : ℕ) :
    0 < ((5 * n).factorial : ℝ) * Real.Gamma (7 * (n : ℝ) / 2 + 1) * ((2 * n).factorial : ℝ) := by
  have hG : 0 < Real.Gamma (7 * (n : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
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

/-- Shifting by a multiple of `140` shifts the quotient by a divisor `d` of `140`
linearly. -/
theorem add_mul_140_div (s t d : ℕ) (hd : d ∣ 140) (hd0 : 0 < d) :
    (s + 140 * t) / d = s / d + 140 / d * t := by
  obtain ⟨k, hk⟩ := hd
  have hkd : 140 / d = k := by rw [hk, Nat.mul_div_cancel_left _ hd0]
  rw [hkd, hk, mul_assoc, Nat.add_mul_div_left _ _ hd0]

/-- Reduce a floor inequality to a single period. Assume that
`∑_{d ∈ ds} ⌊s/d⌋ ≤ ∑_{d ∈ cs} ⌊s/d⌋` for every residue `s < 140`. Assume also
that every `d` divides `140` and the linear parts agree. Then the inequality
holds for all `j`. -/
theorem step_of_period (cs ds : List ℕ) (hcs : ∀ d ∈ cs, d ∣ 140 ∧ 0 < d)
    (hds : ∀ d ∈ ds, d ∣ 140 ∧ 0 < d)
    (hlin : (ds.map (140 / ·)).sum = (cs.map (140 / ·)).sum)
    (hsmall : ∀ s < 140, (ds.map (s / ·)).sum ≤ (cs.map (s / ·)).sum) (j : ℕ) :
    (ds.map (j / ·)).sum ≤ (cs.map (j / ·)).sum := by
  have hshift : ∀ (l : List ℕ), (∀ d ∈ l, d ∣ 140 ∧ 0 < d) → ∀ s t : ℕ,
      (l.map ((s + 140 * t) / ·)).sum = (l.map (s / ·)).sum + (l.map (140 / ·)).sum * t := by
    intro l hl s t
    induction l with
    | nil => simp
    | cons d l ih =>
      have hd := hl d (List.mem_cons_self ..)
      simp only [List.map_cons, List.sum_cons]
      rw [add_mul_140_div s t d hd.1 hd.2, ih fun e he => hl e (List.mem_cons_of_mem _ he)]
      ring
  have hj : j = j % 140 + 140 * (j / 140) := (Nat.mod_add_div j 140).symm
  rw [hj, hshift cs hcs, hshift ds hds, hlin]
  have hs := hsmall (j % 140) (Nat.mod_lt _ (by norm_num))
  omega

/-- The odd-case step inequality in the variable `j = ⌊70x⌋`:
`⌊j/14⌋ + ⌊j/35⌋ + ⌊j/10⌋ + ⌊j/140⌋ ≤ ⌊j/7⌋ + ⌊j/70⌋ + ⌊j/20⌋`, i.e.
`⌊5x⌋ + ⌊2x⌋ + ⌊7x⌋ + ⌊x/2⌋ ≤ ⌊10x⌋ + ⌊x⌋ + ⌊7x/2⌋`. -/
theorem step_odd (j : ℕ) : j / 14 + j / 35 + j / 10 + j / 140 ≤ j / 7 + j / 70 + j / 20 := by
  have h := step_of_period [7, 70, 20] [14, 35, 10, 140] (by decide) (by decide) (by decide)
    (by decide) j
  simpa [add_assoc] using h

/-- The even-case step inequality in the variable `j = ⌊140y⌋`:
`⌊j/14⌋ + ⌊j/35⌋ + ⌊j/20⌋ ≤ ⌊j/7⌋ + ⌊j/140⌋`, i.e.
`⌊10y⌋ + ⌊4y⌋ + ⌊7y⌋ ≤ ⌊20y⌋ + ⌊y⌋`. -/
theorem step_even (j : ℕ) : j / 14 + j / 35 + j / 20 ≤ j / 7 + j / 140 := by
  have h := step_of_period [7, 140] [14, 35, 20] (by decide) (by decide) (by decide)
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
`⌊5n/q⌋ + ⌊2n/q⌋ + ⌊7n/q⌋ + ⌊⌊n/2⌋/q⌋ ≤ ⌊10n/q⌋ + ⌊n/q⌋ + ⌊⌊7n/2⌋/q⌋`. -/
theorem term_odd (n q : ℕ) :
    5 * n / q + 2 * n / q + 7 * n / q + n / 2 / q ≤ 10 * n / q + n / q + 7 * n / 2 / q := by
  have h := step_odd (70 * n / q)
  rw [div_div_eq_of_mul_eq 70 n q 5 14 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 70 n q 2 35 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 70 n q 7 10 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 70 n q 1 140 2 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 70 n q 10 7 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 70 n q 1 70 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 70 n q 7 20 2 (by norm_num) (by norm_num) (by norm_num)] at h
  simp only [one_mul] at h
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
  exact h

/-- The even-case Landau term inequality, valid for every `m` and `q`:
`⌊10m/q⌋ + ⌊4m/q⌋ + ⌊7m/q⌋ ≤ ⌊20m/q⌋ + ⌊m/q⌋`. -/
theorem term_even (m q : ℕ) :
    10 * m / q + 4 * m / q + 7 * m / q ≤ 20 * m / q + m / q := by
  have h := step_even (140 * m / q)
  rw [div_div_eq_of_mul_eq 140 m q 10 14 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 140 m q 4 35 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 140 m q 7 20 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 140 m q 20 7 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 140 m q 1 140 1 (by norm_num) (by norm_num) (by norm_num)] at h
  simpa only [one_mul] using h

/-! ## Factorial divisibilities -/

/-- For every `n`, `(5n)! (2n)! (7n)! ⌊n/2⌋!` divides `(10n)! n! ⌊7n/2⌋!`. For
odd `n` this is stronger than Bala's integer form: the factor `2^(6n)` is not
needed. -/
theorem factorial_dvd_odd_form (n : ℕ) :
    (5 * n).factorial * (2 * n).factorial * (7 * n).factorial * (n / 2).factorial ∣
      (10 * n).factorial * n.factorial * (7 * n / 2).factorial := by
  have h := landau_list [10 * n, n, 7 * n / 2] [5 * n, 2 * n, 7 * n, n / 2] (10 * n)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun q => by simpa [add_assoc] using term_odd n q)
  simpa [mul_assoc] using h

/-- Integrality of A061164: `(10m)! (7m)! (4m)!` divides `(20m)! m!`. This is
Vasyunin's sporadic factorial ratio (Bober, Table 2, Entry 43). -/
theorem factorial_dvd_a061164 (m : ℕ) :
    (10 * m).factorial * (7 * m).factorial * (4 * m).factorial ∣
      (20 * m).factorial * m.factorial := by
  have h := landau_list [20 * m, m] [10 * m, 7 * m, 4 * m] (20 * m)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun q => by
      have := term_even m q
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      omega)
  simpa [mul_assoc] using h

/-- The exact-division identity behind `a061164`. -/
theorem a061164_mul (m : ℕ) :
    (10 * m).factorial * (7 * m).factorial * (4 * m).factorial * a061164 m =
      (20 * m).factorial * m.factorial :=
  Nat.mul_div_cancel' (factorial_dvd_a061164 m)

/-- **Bala's integer form (triage restatement).** For odd `n`,
`(5n)! (7n)! (2n)! ((n-1)/2)!` divides `2^(6n) (10n)! n! ((7n-1)/2)!`. The
natural subtractions are guarded by oddness (`1 ≤ n`). -/
theorem integer_form_of_odd (n : ℕ) (hn : Odd n) :
    (5 * n).factorial * (7 * n).factorial * (2 * n).factorial * ((n - 1) / 2).factorial ∣
      2 ^ (6 * n) * (10 * n).factorial * n.factorial * ((7 * n - 1) / 2).factorial := by
  obtain ⟨k, rfl⟩ := hn
  have h1 : (2 * k + 1 - 1) / 2 = (2 * k + 1) / 2 := by omega
  have h7 : (7 * (2 * k + 1) - 1) / 2 = 7 * (2 * k + 1) / 2 := by omega
  rw [h1, h7, mul_assoc (2 ^ _), mul_assoc (2 ^ _)]
  refine Dvd.dvd.mul_left ?_ _
  have h := factorial_dvd_odd_form (2 * k + 1)
  calc (5 * (2 * k + 1)).factorial * (7 * (2 * k + 1)).factorial * (2 * (2 * k + 1)).factorial *
        ((2 * k + 1) / 2).factorial
      = (5 * (2 * k + 1)).factorial * (2 * (2 * k + 1)).factorial *
          (7 * (2 * k + 1)).factorial * ((2 * k + 1) / 2).factorial := by ring
    _ ∣ _ := h

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

/-- For odd `n`, suppose `(10n)! n! ⌊7n/2⌋! = (5n)! (2n)! (7n)! ⌊n/2⌋! c`.
Then Bala's ratio equals `2^(6n) c`. -/
theorem balaRatio_of_odd {n c : ℕ} (hn : Odd n)
    (hc : (10 * n).factorial * n.factorial * (7 * n / 2).factorial =
      (5 * n).factorial * (2 * n).factorial * (7 * n).factorial * (n / 2).factorial * c) :
    balaRatio n = 2 ^ (6 * n) * (c : ℝ) := by
  have h7 : 7 * (n : ℝ) = ((7 * n : ℕ) : ℝ) := by push_cast; ring
  have hG1 := gamma_half_of_odd hn
  have hG7 := gamma_half_of_odd (Odd.mul (by decide : Odd 7) hn)
  have hcR : ((10 * n).factorial : ℝ) * n.factorial * (7 * n / 2).factorial =
      (5 * n).factorial * (2 * n).factorial * (7 * n).factorial * (n / 2).factorial * c := by
    exact_mod_cast hc
  have hpi : 0 < √Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hpos : (0 : ℝ) < (7 * n / 2).factorial := by positivity
  unfold balaRatio
  rw [h7, hG1, hG7]
  field_simp
  linear_combination (2 ^ (7 * n) : ℝ) * hcR

/-- For even `n = 2m`, Bala's ratio is the sequence term `a(m)`. -/
theorem balaRatio_two_mul (m : ℕ) : balaRatio (2 * m) = (a061164 m : ℝ) := by
  have hG1 : Real.Gamma (((2 * m : ℕ) : ℝ) / 2 + 1) = (m.factorial : ℝ) := by
    rw [← Real.Gamma_nat_eq_factorial]
    congr 1
    push_cast; ring
  have hG7 : Real.Gamma (7 * ((2 * m : ℕ) : ℝ) / 2 + 1) = ((7 * m).factorial : ℝ) := by
    rw [← Real.Gamma_nat_eq_factorial]
    congr 1
    push_cast; ring
  have hmul : (((10 * m).factorial * (7 * m).factorial * (4 * m).factorial * a061164 m : ℕ) : ℝ) =
      (((20 * m).factorial * m.factorial : ℕ) : ℝ) := by
    rw [a061164_mul]
  push_cast at hmul
  unfold balaRatio
  rw [hG1, hG7, show 10 * (2 * m) = 20 * m by ring, show 5 * (2 * m) = 10 * m by ring,
    show 2 * (2 * m) = 4 * m by ring]
  have h10 : (0 : ℝ) < (10 * m).factorial := by positivity
  have h7m : (0 : ℝ) < (7 * m).factorial := by positivity
  have h4 : (0 : ℝ) < (4 * m).factorial := by positivity
  rw [div_eq_iff (by positivity)]
  linear_combination -hmul

/-! ## Ground truth -/

example : a061164 0 = 1 := by decide
example : a061164 1 = 5542680 := by decide
example : a061164 2 = 190818980609400 := by decide

/-- Bala's ratio at `n = 1`: `10! Γ(3/2) / (5! Γ(9/2) 2!) = 1152`. -/
theorem balaRatio_one : balaRatio 1 = 1152 := by
  rw [balaRatio_of_odd (c := 18) (by decide) (by decide)]
  norm_num

/-- Bala's ratio at `n = 3`: `30! Γ(5/2) / (15! Γ(23/2) 6!) = 31473008640`. -/
theorem balaRatio_three : balaRatio 3 = 31473008640 := by
  rw [balaRatio_of_odd (c := 120060) (by decide) (by decide)]
  norm_num

/-- Bala's ratio at `n = 2` is `a(1) = 5542680`. -/
example : balaRatio 2 = 5542680 := by
  have h := balaRatio_two_mul 1
  rw [show (5542680 : ℝ) = (a061164 1 : ℝ) by norm_num [show a061164 1 = 5542680 by decide]]
  simpa using h

/-! ## The conjecture -/

/-- **Bala's conjecture, odd case (A061164, Peter Bala, Jul 31 2026).** For every
odd `n`, `(10n)! Γ(n/2 + 1) / ((5n)! Γ(7n/2 + 1) (2n)!)` is an integer. -/
theorem bala_integrality_of_odd (n : ℕ) (hn : Odd n) : ∃ z : ℤ, balaRatio n = z := by
  obtain ⟨c, hc⟩ := factorial_dvd_odd_form n
  refine ⟨2 ^ (6 * n) * c, ?_⟩
  rw [balaRatio_of_odd hn hc]
  push_cast
  ring

/-- **Bala's conjecture (A061164, Peter Bala, Jul 31 2026), full form.** Verbatim:
"Conjecture: for n >= 0, a(n/2) = (10*n)!*(n/2)! / ((5*n)!*(7*n/2)!*(2*n)!) is
an integer, where fractional factorials are defined using the Gamma function -
for example, (n/2)! := Gamma(n/2 + 1)." Here `balaRatio n` is that value. -/
theorem bala_integrality (n : ℕ) : ∃ z : ℤ, balaRatio n = z := by
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | hn
  · refine ⟨a061164 m, ?_⟩
    rw [← two_mul, balaRatio_two_mul]
    push_cast
    rfl
  · exact bala_integrality_of_odd n hn

end Candidates.A061164BalaIntegrality
