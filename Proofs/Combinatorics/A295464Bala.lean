/-
# A295464 — Bala: the half-index Gamma ratio `a(n/2)` is an integer

OEIS A295464, Peter Bala (2026): `a(n/2)` is an integer for every natural
`n`, where `a(n) = (30n)!(5n)!(3n)! / ((15n)!(10n)!(7n)!(6n)!)` and
`x! = Γ(x+1)`. The entry also gives a binomial-coefficient formula by
Chai Wah Wu (2026).

## Proof outline

* Odd `n`: `Γ(k/2 + 1) = k! √π / (2^k ⌊k/2⌋!)` for odd `k`, so the ratio
  equals `2^(14n) ⌊15n/2⌋! ⌊7n/2⌋! / (⌊5n/2⌋! ⌊3n/2⌋! (7n)!)`. Landau's
  criterion shows that the factorial quotient without the power of two is
  already an integer: the step function
  `⌊15y⌋ + ⌊7y⌋ - ⌊5y⌋ - ⌊3y⌋ - ⌊14y⌋` (with `y = n/(2q)`) is nonnegative.
  With `j = ⌊210y⌋` every term is `⌊j/d⌋` for a divisor `d` of `210`, so a
  finite `decide` over `j < 210` closes it.
* Even `n = 2m`: the ratio is `a(m)`, integral by Landau's criterion with
  `⌊30x⌋ + ⌊5x⌋ + ⌊3x⌋ - ⌊15x⌋ - ⌊10x⌋ - ⌊7x⌋ - ⌊6x⌋ ≥ 0`.

The Landau and Gamma-bridge lemmas follow
`Proofs/Combinatorics/A295431BalaGamma.lean` (copied, with the period `12`
generalized to an arbitrary period).
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A295464Bala

/-! ## Definition layer -/

/-- The OEIS sequence A295464: `a(n) = (30n)! (5n)! (3n)! / ((15n)! (10n)! (7n)! (6n)!)`.
The truncating `Nat` division is exact; see `a295464_mul`. -/
def a295464 (n : ℕ) : ℕ :=
  (30 * n).factorial * (5 * n).factorial * (3 * n).factorial /
    ((15 * n).factorial * (10 * n).factorial * (7 * n).factorial * (6 * n).factorial)

/-- Bala's half-index value `a(n/2)`:
`(15n)! Γ(5n/2 + 1) Γ(3n/2 + 1) / (Γ(15n/2 + 1) (5n)! Γ(7n/2 + 1) (3n)!)`.
Here `(x)! := Γ(x + 1)` for fractional `x`, as in the entry. The denominator is
positive (`balaRatio_denom_pos`), so the real division never takes its junk value. -/
noncomputable def balaRatio (n : ℕ) : ℝ :=
  ((15 * n).factorial : ℝ) * Real.Gamma (5 * (n : ℝ) / 2 + 1) *
      Real.Gamma (3 * (n : ℝ) / 2 + 1) /
    (Real.Gamma (15 * (n : ℝ) / 2 + 1) * ((5 * n).factorial : ℝ) *
      Real.Gamma (7 * (n : ℝ) / 2 + 1) * ((3 * n).factorial : ℝ))

/-- The denominator of `balaRatio n` is positive. -/
theorem balaRatio_denom_pos (n : ℕ) :
    0 < Real.Gamma (15 * (n : ℝ) / 2 + 1) * ((5 * n).factorial : ℝ) *
      Real.Gamma (7 * (n : ℝ) / 2 + 1) * ((3 * n).factorial : ℝ) := by
  have h15 : 0 < Real.Gamma (15 * (n : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
  have h7 : 0 < Real.Gamma (7 * (n : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
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

/-- Shifting by a multiple of the period `N` shifts the quotient by a divisor
`d` of `N` linearly. -/
theorem add_mul_div_of_dvd (N s t d : ℕ) (hd : d ∣ N) (hd0 : 0 < d) :
    (s + N * t) / d = s / d + N / d * t := by
  obtain ⟨k, hk⟩ := hd
  have hkd : N / d = k := by rw [hk, Nat.mul_div_cancel_left _ hd0]
  rw [hkd, hk, mul_assoc, Nat.add_mul_div_left _ _ hd0]

/-- Reduce a floor inequality to a single period `N > 0`. Assume that
`∑_{d ∈ ds} ⌊s/d⌋ ≤ ∑_{d ∈ cs} ⌊s/d⌋` for every residue `s < N`, that every
`d` divides `N`, and that the linear parts agree. Then the inequality holds for
all `j`. -/
theorem step_of_period (N : ℕ) (hN : 0 < N) (cs ds : List ℕ)
    (hcs : ∀ d ∈ cs, d ∣ N ∧ 0 < d) (hds : ∀ d ∈ ds, d ∣ N ∧ 0 < d)
    (hlin : (ds.map (N / ·)).sum = (cs.map (N / ·)).sum)
    (hsmall : ∀ s < N, (ds.map (s / ·)).sum ≤ (cs.map (s / ·)).sum) (j : ℕ) :
    (ds.map (j / ·)).sum ≤ (cs.map (j / ·)).sum := by
  have hshift : ∀ (l : List ℕ), (∀ d ∈ l, d ∣ N ∧ 0 < d) → ∀ s t : ℕ,
      (l.map ((s + N * t) / ·)).sum = (l.map (s / ·)).sum + (l.map (N / ·)).sum * t := by
    intro l hl s t
    induction l with
    | nil => simp
    | cons d l ih =>
      have hd := hl d (List.mem_cons_self ..)
      simp only [List.map_cons, List.sum_cons]
      rw [add_mul_div_of_dvd N s t d hd.1 hd.2, ih fun e he => hl e (List.mem_cons_of_mem _ he)]
      ring
  have hj : j = j % N + N * (j / N) := (Nat.mod_add_div j N).symm
  rw [hj, hshift cs hcs, hshift ds hds, hlin]
  have hs := hsmall (j % N) (Nat.mod_lt _ hN)
  omega

set_option maxRecDepth 10000 in
/-- The odd-case step inequality in the variable `j = ⌊210y⌋`:
`⌊j/42⌋ + ⌊j/70⌋ + ⌊j/15⌋ ≤ ⌊j/14⌋ + ⌊j/30⌋`, i.e.
`⌊5y⌋ + ⌊3y⌋ + ⌊14y⌋ ≤ ⌊15y⌋ + ⌊7y⌋`. -/
theorem step_odd (j : ℕ) : j / 42 + j / 70 + j / 15 ≤ j / 14 + j / 30 := by
  have h := step_of_period 210 (by norm_num) [14, 30] [42, 70, 15] (by decide) (by decide)
    (by decide) (by decide) j
  simpa [add_assoc] using h

set_option maxRecDepth 10000 in
/-- The even-case step inequality in the variable `j = ⌊210x⌋`:
`⌊j/14⌋ + ⌊j/21⌋ + ⌊j/30⌋ + ⌊j/35⌋ ≤ ⌊j/7⌋ + ⌊j/42⌋ + ⌊j/70⌋`, i.e.
`⌊15x⌋ + ⌊10x⌋ + ⌊7x⌋ + ⌊6x⌋ ≤ ⌊30x⌋ + ⌊5x⌋ + ⌊3x⌋`. -/
theorem step_even (j : ℕ) : j / 14 + j / 21 + j / 30 + j / 35 ≤ j / 7 + j / 42 + j / 70 := by
  have h := step_of_period 210 (by norm_num) [7, 42, 70] [14, 21, 30, 35] (by decide)
    (by decide) (by decide) (by decide) j
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
`⌊⌊5n/2⌋/q⌋ + ⌊⌊3n/2⌋/q⌋ + ⌊7n/q⌋ ≤ ⌊⌊15n/2⌋/q⌋ + ⌊⌊7n/2⌋/q⌋`. -/
theorem term_odd (n q : ℕ) :
    5 * n / 2 / q + 3 * n / 2 / q + 7 * n / q ≤ 15 * n / 2 / q + 7 * n / 2 / q := by
  have h := step_odd (105 * n / q)
  rw [div_div_eq_of_mul_eq 105 n q 5 42 2 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 105 n q 3 70 2 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 105 n q 7 15 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 105 n q 15 14 2 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 105 n q 7 30 2 (by norm_num) (by norm_num) (by norm_num)] at h
  simp only [one_mul] at h
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul,
    Nat.div_div_eq_div_mul]
  exact h

/-- The even-case Landau term inequality, valid for every `m` and `q`:
`⌊15m/q⌋ + ⌊10m/q⌋ + ⌊7m/q⌋ + ⌊6m/q⌋ ≤ ⌊30m/q⌋ + ⌊5m/q⌋ + ⌊3m/q⌋`. -/
theorem term_even (m q : ℕ) :
    15 * m / q + 10 * m / q + 7 * m / q + 6 * m / q ≤ 30 * m / q + 5 * m / q + 3 * m / q := by
  have h := step_even (210 * m / q)
  rw [div_div_eq_of_mul_eq 210 m q 15 14 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 210 m q 10 21 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 210 m q 7 30 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 210 m q 6 35 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 210 m q 30 7 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 210 m q 5 42 1 (by norm_num) (by norm_num) (by norm_num),
    div_div_eq_of_mul_eq 210 m q 3 70 1 (by norm_num) (by norm_num) (by norm_num)] at h
  simpa only [one_mul] using h

/-! ## Factorial divisibilities -/

/-- For every `n`, `⌊5n/2⌋! ⌊3n/2⌋! (7n)!` divides `⌊15n/2⌋! ⌊7n/2⌋!`. For odd
`n` this is stronger than needed: the factor `2^(14n)` of Bala's ratio is not
used. -/
theorem factorial_dvd_odd_form (n : ℕ) :
    (5 * n / 2).factorial * (3 * n / 2).factorial * (7 * n).factorial ∣
      (15 * n / 2).factorial * (7 * n / 2).factorial := by
  have h := landau_list [15 * n / 2, 7 * n / 2] [5 * n / 2, 3 * n / 2, 7 * n] (15 * n)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun q => by simpa [add_assoc] using term_odd n q)
  simpa [mul_assoc] using h

/-- Integrality of A295464: `(15m)! (10m)! (7m)! (6m)!` divides `(30m)! (5m)! (3m)!`. -/
theorem factorial_dvd_a295464 (m : ℕ) :
    (15 * m).factorial * (10 * m).factorial * (7 * m).factorial * (6 * m).factorial ∣
      (30 * m).factorial * (5 * m).factorial * (3 * m).factorial := by
  have h := landau_list [30 * m, 5 * m, 3 * m] [15 * m, 10 * m, 7 * m, 6 * m] (30 * m)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
    (fun q => by
      have := term_even m q
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      omega)
  simpa [mul_assoc] using h

/-- The exact-division identity behind `a295464`. -/
theorem a295464_mul (m : ℕ) :
    (15 * m).factorial * (10 * m).factorial * (7 * m).factorial * (6 * m).factorial *
        a295464 m =
      (30 * m).factorial * (5 * m).factorial * (3 * m).factorial :=
  Nat.mul_div_cancel' (factorial_dvd_a295464 m)

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

/-- For odd `n`, suppose `⌊15n/2⌋! ⌊7n/2⌋! = ⌊5n/2⌋! ⌊3n/2⌋! (7n)! c`.
Then Bala's ratio equals `2^(14n) c`. -/
theorem balaRatio_of_odd {n c : ℕ} (hn : Odd n)
    (hc : (15 * n / 2).factorial * (7 * n / 2).factorial =
      (5 * n / 2).factorial * (3 * n / 2).factorial * (7 * n).factorial * c) :
    balaRatio n = 2 ^ (14 * n) * (c : ℝ) := by
  have hcast : ∀ a : ℕ, (a : ℝ) * (n : ℝ) = ((a * n : ℕ) : ℝ) := fun a => by push_cast; ring
  have hG15 := gamma_half_of_odd (Odd.mul (by decide : Odd 15) hn)
  have hG5 := gamma_half_of_odd (Odd.mul (by decide : Odd 5) hn)
  have hG7 := gamma_half_of_odd (Odd.mul (by decide : Odd 7) hn)
  have hG3 := gamma_half_of_odd (Odd.mul (by decide : Odd 3) hn)
  have hcR : ((15 * n / 2).factorial : ℝ) * (7 * n / 2).factorial =
      (5 * n / 2).factorial * (3 * n / 2).factorial * (7 * n).factorial * c := by
    exact_mod_cast hc
  have hpi : 0 < √Real.pi := Real.sqrt_pos.2 Real.pi_pos
  unfold balaRatio
  rw [show (15 : ℝ) = ((15 : ℕ) : ℝ) by norm_num, show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num,
    show (7 : ℝ) = ((7 : ℕ) : ℝ) by norm_num, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
    hcast 15, hcast 5, hcast 7, hcast 3, hG15, hG5, hG7, hG3]
  field_simp
  linear_combination (2 ^ (22 * n) : ℝ) * hcR

/-- For even `n = 2m`, Bala's ratio is the sequence term `a(m)`. -/
theorem balaRatio_two_mul (m : ℕ) : balaRatio (2 * m) = (a295464 m : ℝ) := by
  have hfacR : ∀ a : ℕ, ∀ x : ℝ, x = (a : ℝ) → Real.Gamma (x + 1) = (a.factorial : ℝ) :=
    fun a x hx => by rw [hx, Real.Gamma_nat_eq_factorial]
  have hG5 : Real.Gamma (5 * ((2 * m : ℕ) : ℝ) / 2 + 1) = ((5 * m).factorial : ℝ) :=
    hfacR _ _ (by push_cast; ring)
  have hG3 : Real.Gamma (3 * ((2 * m : ℕ) : ℝ) / 2 + 1) = ((3 * m).factorial : ℝ) :=
    hfacR _ _ (by push_cast; ring)
  have hG15 : Real.Gamma (15 * ((2 * m : ℕ) : ℝ) / 2 + 1) = ((15 * m).factorial : ℝ) :=
    hfacR _ _ (by push_cast; ring)
  have hG7 : Real.Gamma (7 * ((2 * m : ℕ) : ℝ) / 2 + 1) = ((7 * m).factorial : ℝ) :=
    hfacR _ _ (by push_cast; ring)
  have hmul : (((15 * m).factorial * (10 * m).factorial * (7 * m).factorial *
      (6 * m).factorial * a295464 m : ℕ) : ℝ) =
      (((30 * m).factorial * (5 * m).factorial * (3 * m).factorial : ℕ) : ℝ) := by
    rw [a295464_mul]
  push_cast at hmul
  unfold balaRatio
  rw [hG5, hG3, hG15, hG7, show 15 * (2 * m) = 30 * m by ring,
    show 5 * (2 * m) = 10 * m by ring, show 3 * (2 * m) = 6 * m by ring]
  have h15 : (0 : ℝ) < (15 * m).factorial := by positivity
  have h10 : (0 : ℝ) < (10 * m).factorial := by positivity
  have h7 : (0 : ℝ) < (7 * m).factorial := by positivity
  have h6 : (0 : ℝ) < (6 * m).factorial := by positivity
  rw [div_eq_iff (by positivity)]
  linear_combination -hmul

/-! ## Examples -/

example : a295464 0 = 1 := by decide
example : a295464 1 = 11090902680 := by decide
example : a295464 2 = 806752594470299009400 := by decide

/-- Bala's ratio at `n = 1`:
`15! Γ(7/2) Γ(5/2) / (Γ(17/2) 5! Γ(9/2) 3!) = 49152 = 2^14 · 3`. -/
theorem balaRatio_one : balaRatio 1 = 49152 := by
  rw [balaRatio_of_odd (c := 3) (by decide) (by decide)]
  norm_num

/-- Bala's ratio at `n = 3`: `2902710697328640 = 2^42 · 660`. -/
theorem balaRatio_three : balaRatio 3 = 2902710697328640 := by
  rw [balaRatio_of_odd (c := 660) (by decide) (by decide)]
  norm_num

/-- Bala's ratio at `n = 2` is `a(1) = 11090902680`. -/
example : balaRatio 2 = 11090902680 := by
  have h := balaRatio_two_mul 1
  rw [show (11090902680 : ℝ) = (a295464 1 : ℝ) by
    norm_num [show a295464 1 = 11090902680 by decide]]
  simpa using h

/-! ## The conjecture -/

/-- **Bala's conjecture, odd case (A295464, Peter Bala, Aug 03 2026).** For every
odd `n`, `(15n)! Γ(5n/2 + 1) Γ(3n/2 + 1) / (Γ(15n/2 + 1) (5n)! Γ(7n/2 + 1) (3n)!)`
is an integer (indeed `2^(14n)` times an integer). -/
theorem bala_integrality_of_odd (n : ℕ) (hn : Odd n) : ∃ z : ℤ, balaRatio n = z := by
  obtain ⟨c, hc⟩ := factorial_dvd_odd_form n
  refine ⟨2 ^ (14 * n) * c, ?_⟩
  rw [balaRatio_of_odd hn hc]
  push_cast
  ring

/-- **Bala's conjecture (A295464, Peter Bala, Aug 03 2026).**
For every natural `n`, `balaRatio n` (the value `a(n/2)`) is an integer, with
fractional factorials interpreted as `x! = Γ(x+1)`. -/
theorem bala_integrality (n : ℕ) : ∃ z : ℤ, balaRatio n = z := by
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | hn
  · refine ⟨a295464 m, ?_⟩
    rw [← two_mul, balaRatio_two_mul]
    push_cast
    rfl
  · exact bala_integrality_of_odd n hn

end Candidates.A295464Bala
