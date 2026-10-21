/-
# A352654 — Bala: the binomial sum is a coefficient of 1/(1 - x - xy - yz - xz - xyz)

## OEIS source (retrieved with `oeis show A352654` and https://oeis.org/A352654, 2026-10-21)

```
NAME:     a(0) = 0, a(n) = [x^n] P(n-1,(1 + x)/(1 - x)) for n >= 1, where P(n,x)
          denotes the n-th Legendre polynomial.
TERMS:    0,0,2,18,162,1500,14240,137886,1356194,13507416,135916002,...
AUTHOR:   Peter Bala, Apr 14 2022
FORMULA (first):
  a(n) = Sum_{k = 1..n-1} binomial(n-1,k)*binomial(n-1,k-1)*binomial(n+k-1,k).
FORMULA (the conjecture, unsigned, hence the author's, Peter Bala, Apr 14 2022):
  Conjecture: a(n) = [(x*y)^(n-1)*z^n] 1/(1 - x - x*y - y*z - x*z - x*y*z) =
  [(x*z)^(n-1)*y^n] 1/(1 - x - x*y - y*z - x*z - x*y*z) for n >= 1.
```

## Status

Triage: open (no proof in the entry or found in the literature).  This file
proves both equalities, with `a(n)` given by the entry's first formula.

Proof (three-step coefficient extraction).  The denominator factors as
`(1 - yz) - x(1+y)(1+z)`, so the `x^a` slice of its inverse is
`V a = (1+y)^a (1+z)^a (1-yz)^{-(a+1)}`; this is checked by verifying that the
series `G` with slices `V a` satisfies `denom * G = 1` coefficientwise
(`denom_mul_G`), using only `(1-yz) V 0 = 1` and `(1-yz) V (a+1) = (1+y)(1+z) V a`.
The series `(1-yz)^{-(k+1)} = ∑_j C(k+j,k) (yz)^j` is given explicitly (`W`) and
its recurrence is Pascal's rule.  Expanding `(1+y)^a (1+z)^a` binomially and
reading off `y^a z^(a+1)` (resp. `y^(a+1) z^a`) gives
`∑_{i<a} C(a,i) C(a,i+1) C(2a-i,a)`, which the substitution `k = a - i` turns
into the first formula.

Definitional-fidelity note.  The entry's NAME defines `a(n)` through Legendre
polynomials; this file defines `a352654` by the entry's first FORMULA line,
which is the sum named in the triaged conjecture.  The equality of the NAME
and the first FORMULA is the entry's own (unproved here) claim; the
ground-truth examples check `a352654` against the listed terms.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A352654SumCoefficientXyz

open MvPowerSeries

/-- The exponent vector of the monomial `x^a y^b z^c`, with `x = X 0`, `y = X 1`,
`z = X 2`. -/
noncomputable def expo (a b c : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.single 0 a + Finsupp.single 1 b + Finsupp.single 2 c

/-- The monomial `x^a y^b z^c` with coefficient `1` in `ℚ[[x, y, z]]`. -/
noncomputable def mon (a b c : ℕ) : MvPowerSeries (Fin 3) ℚ :=
  monomial (expo a b c) 1

/-- The `x`-exponent of `expo a b c`. -/
@[simp] lemma expo_zero (a b c : ℕ) : expo a b c 0 = a := by simp [expo]
/-- The `y`-exponent of `expo a b c`. -/
@[simp] lemma expo_one (a b c : ℕ) : expo a b c 1 = b := by simp [expo]
/-- The `z`-exponent of `expo a b c`. -/
@[simp] lemma expo_two (a b c : ℕ) : expo a b c 2 = c := by simp [expo]

/-- Every exponent vector on `Fin 3` is of the form `expo a b c`. -/
lemma expo_eta (e : Fin 3 →₀ ℕ) : expo (e 0) (e 1) (e 2) = e := by
  ext i; fin_cases i <;> simp

/-- Exponent vectors compare coordinatewise. -/
lemma expo_le_expo {i j k a b c : ℕ} :
    expo i j k ≤ expo a b c ↔ i ≤ a ∧ j ≤ b ∧ k ≤ c := by
  rw [Finsupp.le_def]
  constructor
  · intro h
    exact ⟨by simpa using h 0, by simpa using h 1, by simpa using h 2⟩
  · rintro ⟨h0, h1, h2⟩ t
    fin_cases t <;> simpa

/-- Truncated subtraction of exponent vectors is coordinatewise. -/
lemma expo_sub_expo (i j k a b c : ℕ) :
    expo a b c - expo i j k = expo (a - i) (b - j) (c - k) := by
  ext t; fin_cases t <;> simp

/-- Addition of exponent vectors is coordinatewise. -/
lemma expo_add_expo (i j k a b c : ℕ) :
    expo a b c + expo i j k = expo (a + i) (b + j) (c + k) := by
  ext t; fin_cases t <;> simp

/-- Coefficient of `x^a y^b z^c` in `x^i y^j z^k * φ`. -/
lemma coeff_mon_mul (i j k a b c : ℕ) (φ : MvPowerSeries (Fin 3) ℚ) :
    coeff (expo a b c) (mon i j k * φ) =
      if i ≤ a ∧ j ≤ b ∧ k ≤ c then coeff (expo (a - i) (b - j) (c - k)) φ else 0 := by
  rw [mon, coeff_monomial_mul, expo_sub_expo, one_mul]
  exact if_congr expo_le_expo rfl rfl

/-- Monomials multiply by adding exponents. -/
lemma mon_mul_mon (i j k a b c : ℕ) : mon a b c * mon i j k = mon (a + i) (b + j) (c + k) := by
  rw [mon, mon, monomial_mul_monomial, expo_add_expo, one_mul, mon]

/-- `x` as a monomial. -/
lemma X0_eq : (X 0 : MvPowerSeries (Fin 3) ℚ) = mon 1 0 0 := by
  rw [X, mon]; congr 1; simp [expo]
/-- `y` as a monomial. -/
lemma X1_eq : (X 1 : MvPowerSeries (Fin 3) ℚ) = mon 0 1 0 := by
  rw [X, mon]; congr 1; simp [expo]
/-- `z` as a monomial. -/
lemma X2_eq : (X 2 : MvPowerSeries (Fin 3) ℚ) = mon 0 0 1 := by
  rw [X, mon]; congr 1; simp [expo]
/-- `1` as a monomial. -/
lemma one_eq : (1 : MvPowerSeries (Fin 3) ℚ) = mon 0 0 0 := by
  rw [mon, ← MvPowerSeries.monomial_zero_one]; congr 1; simp [expo]

/-- Coefficient of `x^a y^b z^c` in the constant `1`. -/
lemma coeff_expo_one (a b c : ℕ) :
    coeff (expo a b c) (1 : MvPowerSeries (Fin 3) ℚ) = if a = 0 ∧ b = 0 ∧ c = 0 then 1 else 0 := by
  rw [one_eq, mon, coeff_monomial]
  refine if_congr ⟨fun h => ?_, fun h => ?_⟩ rfl rfl
  · exact ⟨by simpa using congrArg (· 0) h, by simpa using congrArg (· 1) h,
      by simpa using congrArg (· 2) h⟩
  · obtain ⟨rfl, rfl, rfl⟩ := h; rfl

/-- The series `(1 - yz)^{-(k+1)} = ∑_j C(k+j, k) (yz)^j`, given by its coefficients. -/
noncomputable def W (k : ℕ) : MvPowerSeries (Fin 3) ℚ :=
  fun e => if e 0 = 0 ∧ e 1 = e 2 then ((k + e 1).choose k : ℚ) else 0
/-- Coefficient of `x^a y^b z^c` in `W k`. -/
lemma coeff_W (k a b c : ℕ) :
    coeff (expo a b c) (W k) = if a = 0 ∧ b = c then ((k + b).choose k : ℚ) else 0 := by
  show W k (expo a b c) = _
  simp [W]

/-- `(1 - yz) W 0 = 1`. -/
lemma W_zero_mul : (mon 0 0 0 - mon 0 1 1) * W 0 = 1 := by
  ext e
  rw [← expo_eta e]
  generalize e 0 = a, e 1 = b, e 2 = c
  rw [sub_mul, map_sub, coeff_mon_mul, coeff_mon_mul, coeff_W, coeff_W, coeff_expo_one]
  rcases b with _ | b <;> rcases c with _ | c <;> simp

/-- `(1 - yz) W (k+1) = W k`, Pascal's rule. -/
lemma W_succ_mul (k : ℕ) : (mon 0 0 0 - mon 0 1 1) * W (k + 1) = W k := by
  ext e
  rw [← expo_eta e]
  generalize e 0 = a, e 1 = b, e 2 = c
  rw [sub_mul, map_sub, coeff_mon_mul, coeff_mon_mul, coeff_W, coeff_W, coeff_W]
  rcases b with _ | b <;> rcases c with _ | c
  · simp
  · simp
  · simp
  · by_cases ha : a = 0
    · by_cases hbc : b = c
      · subst hbc
        simp only [ha, zero_le, le_add_iff_nonneg_left, and_self, Nat.sub_zero,
          add_tsub_cancel_right, if_true]
        have h := Nat.choose_succ_succ' (k + (b + 1)) k
        rw [show k + 1 + (b + 1) = k + (b + 1) + 1 by ring, show k + 1 + b = k + (b + 1) by ring, h]
        push_cast; ring
      · simp [ha, hbc]
    · simp [ha]

/-- The denominator `1 - x - xy - yz - xz - xyz` in `ℚ[[x, y, z]]`, with `x = X 0`,
`y = X 1`, `z = X 2`. -/
noncomputable def denom : MvPowerSeries (Fin 3) ℚ :=
  1 - X 0 - X 0 * X 1 - X 1 * X 2 - X 0 * X 2 - X 0 * X 1 * X 2

/-- The denominator written as a signed sum of monomials. -/
lemma denom_eq : denom =
    mon 0 0 0 - mon 1 0 0 - mon 1 1 0 - mon 0 1 1 - mon 1 0 1 - mon 1 1 1 := by
  simp only [denom, X0_eq, X1_eq, X2_eq, one_eq, mon_mul_mon]

/-- The slice series `V a = (1+y)^a (1+z)^a (1-yz)^{-(a+1)}`, the coefficient of `x^a`
in `1 / denom`. -/
noncomputable def V (a : ℕ) : MvPowerSeries (Fin 3) ℚ :=
  (mon 0 1 0 + 1) ^ a * (mon 0 0 1 + 1) ^ a * W a
/-- `(1 - yz) V 0 = 1`. -/
lemma V_zero_mul : (mon 0 0 0 - mon 0 1 1) * V 0 = 1 := by
  rw [V, pow_zero, pow_zero, one_mul, one_mul, W_zero_mul]

/-- The slice recurrence `(1 - yz) V (a+1) = (1+y)(1+z) V a`. -/
lemma V_succ_mul (a : ℕ) : (mon 0 0 0 - mon 0 1 1) * V (a + 1) =
    (mon 0 0 0 + mon 0 1 0 + mon 0 0 1 + mon 0 1 1) * V a := by
  have hP : mon 0 0 0 + mon 0 1 0 + mon 0 0 1 + mon 0 1 1 =
      (mon 0 1 0 + 1) * (mon 0 0 1 + 1) := by
    simp only [add_mul, mul_add, mon_mul_mon, one_eq]
    simp only [add_zero, zero_add]
    abel
  calc (mon 0 0 0 - mon 0 1 1) * V (a + 1)
      = (mon 0 1 0 + 1) ^ (a + 1) * (mon 0 0 1 + 1) ^ (a + 1) *
          ((mon 0 0 0 - mon 0 1 1) * W (a + 1)) := by rw [V]; ring
    _ = (mon 0 0 0 + mon 0 1 0 + mon 0 0 1 + mon 0 1 1) * V a := by
          rw [W_succ_mul, hP, V]; ring

/-- The candidate inverse: its `x^a y^b z^c` coefficient is the `y^b z^c` coefficient
of `V a`. -/
noncomputable def G : MvPowerSeries (Fin 3) ℚ :=
  fun e => coeff (expo 0 (e 1) (e 2)) (V (e 0))
/-- Coefficient of `x^a y^b z^c` in `G`. -/
lemma coeff_G (a b c : ℕ) : coeff (expo a b c) G = coeff (expo 0 b c) (V a) := by
  show G (expo a b c) = _
  simp [G]
/-- `denom * G = 1`: `G` satisfies the defining recurrence of `1 / denom`. -/
lemma denom_mul_G : denom * G = 1 := by
  ext e
  rw [← expo_eta e]
  generalize e 0 = a, e 1 = b, e 2 = c
  rw [denom_eq]
  simp only [sub_mul, map_sub, coeff_mon_mul, coeff_G, coeff_expo_one]
  rcases a with _ | a
  · have h0 := congrArg (coeff (expo 0 b c)) V_zero_mul
    simp only [sub_mul, map_sub, coeff_mon_mul, coeff_expo_one] at h0
    simp only [Nat.zero_le, true_and, Nat.sub_zero, Nat.sub_self, nonpos_iff_eq_zero,
      one_ne_zero, false_and, if_false, if_true, sub_zero, and_true] at h0 ⊢
    exact h0
  · have h1 := congrArg (coeff (expo 0 b c)) (V_succ_mul a)
    simp only [sub_mul, add_mul, map_sub, map_add, coeff_mon_mul] at h1
    simp only [Nat.zero_le, true_and, Nat.sub_zero, Nat.sub_self, le_add_iff_nonneg_left,
      Nat.add_sub_cancel, if_true, Nat.add_eq_zero_iff, one_ne_zero, and_false, false_and,
      if_false] at h1 ⊢
    linear_combination h1


/-- `1 / denom = G`. -/
lemma denom_inv : denom⁻¹ = G := by
  have h : constantCoeff denom ≠ 0 := by simp [denom]
  rw [MvPowerSeries.inv_eq_iff_mul_eq_one h, mul_comm, denom_mul_G]

/-- The coefficient of `x^a y^b z^c` in `1 / denom` is the `y^b z^c` coefficient of
`V a = (1+y)^a (1+z)^a (1-yz)^{-(a+1)}`. -/
lemma coeff_denom_inv (a b c : ℕ) :
    coeff (expo a b c) denom⁻¹ = coeff (expo 0 b c) (V a) := by
  rw [denom_inv, coeff_G]
/-- Powers of monomials. -/
lemma mon_pow (a b c m : ℕ) : mon a b c ^ m = mon (m * a) (m * b) (m * c) := by
  induction m with
  | zero => simp [one_eq]
  | succ m ih => rw [pow_succ, ih, mon_mul_mon]; congr 1 <;> ring

/-- Binomial expansion of `(1+y)^a`. -/
lemma one_add_y_pow (a : ℕ) : (mon 0 1 0 + 1) ^ a =
    ∑ i ∈ Finset.range (a + 1), C ((a.choose i : ℕ) : ℚ) * mon 0 i 0 := by
  rw [add_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [one_pow, mul_one, mon_pow, map_natCast, mul_comm]
  simp

/-- Binomial expansion of `(1+z)^a`. -/
lemma one_add_z_pow (a : ℕ) : (mon 0 0 1 + 1) ^ a =
    ∑ l ∈ Finset.range (a + 1), C ((a.choose l : ℕ) : ℚ) * mon 0 0 l := by
  rw [add_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [one_pow, mul_one, mon_pow, map_natCast, mul_comm]
  simp

/-- Closed form of the `y^b z^c` coefficient of `V a`:
`∑_{i,l ≤ a, b-i = c-l} C(a,i) C(a,l) C(a + (b-i), a)`. -/
lemma coeff_V (a b c : ℕ) : coeff (expo 0 b c) (V a) =
    ∑ i ∈ Finset.range (a + 1), ∑ l ∈ Finset.range (a + 1),
      if i ≤ b ∧ l ≤ c ∧ b - i = c - l then
        ((a.choose i : ℕ) : ℚ) * (a.choose l : ℕ) * ((a + (b - i)).choose a : ℕ) else 0 := by
  rw [V, one_add_y_pow, one_add_z_pow, Finset.sum_mul_sum, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hreorg : C ((a.choose i : ℕ) : ℚ) * mon 0 i 0 * (C ((a.choose l : ℕ) : ℚ) * mon 0 0 l) * W a
      = C (((a.choose i : ℕ) : ℚ) * (a.choose l : ℕ)) * (mon 0 i l * W a) := by
    have hm : mon 0 i l = mon 0 i 0 * mon 0 0 l := by
      rw [mon_mul_mon, add_zero, add_zero, zero_add]
    rw [map_mul, hm]; ring
  rw [hreorg, coeff_C_mul, coeff_mon_mul, coeff_W]
  by_cases h : i ≤ b ∧ l ≤ c ∧ b - i = c - l
  · rw [if_pos ⟨Nat.zero_le 0, h.1, h.2.1⟩, if_pos ⟨Nat.sub_self 0, h.2.2⟩, if_pos h]
  · rw [if_neg h]
    split_ifs with h1 h2
    · exact absurd ⟨h1.2.1, h1.2.2, h2.2⟩ h
    · rw [mul_zero]
    · rw [mul_zero]


/-- A352654 via the entry's first formula:
`a(n) = ∑_{k=1}^{n-1} C(n-1,k) C(n-1,k-1) C(n+k-1,k)` (empty sum for `n ≤ 1`). -/
def a352654 (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 (n - 1), (n - 1).choose k * (n - 1).choose (k - 1) * (n + k - 1).choose k

/-- Reindexing `k = a - i` turns the extracted sum into the entry's formula. -/
lemma sum_reflect (a : ℕ) :
    ∑ i ∈ Finset.range a,
      ((a.choose i : ℕ) : ℚ) * (a.choose (i + 1) : ℕ) * ((a + (a - i)).choose a : ℕ) =
      (a352654 (a + 1) : ℚ) := by
  rw [a352654, Nat.add_sub_cancel, Nat.cast_sum]
  refine Finset.sum_nbij' (fun i => a - i) (fun k => a - k) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_range] at hi
    rw [Finset.mem_Icc]
    omega
  · intro k hk
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_range]
    omega
  · intro i hi
    rw [Finset.mem_range] at hi
    omega
  · intro k hk
    rw [Finset.mem_Icc] at hk
    omega
  · intro i hi
    rw [Finset.mem_range] at hi
    have h1 : a.choose (a - i) = a.choose i := Nat.choose_symm hi.le
    have h2 : a.choose (a - i - 1) = a.choose (i + 1) := by
      rw [show a - i - 1 = a - (i + 1) by omega]; exact Nat.choose_symm hi
    have h3 : (a + 1 + (a - i) - 1).choose (a - i) = (a + (a - i)).choose a := by
      rw [show a + 1 + (a - i) - 1 = a + (a - i) by omega]; exact Nat.choose_symm_add.symm
    rw [h1, h2, h3]
    push_cast; ring


/-- Collapsing a sum over `range (a+1)` whose summand vanishes at `i = a`. -/
lemma sum_range_succ_ite (a : ℕ) (g : ℕ → ℚ) :
    ∑ i ∈ Finset.range (a + 1), (if i < a then g i else 0) = ∑ i ∈ Finset.range a, g i := by
  rw [Finset.sum_range_succ, if_neg (lt_irrefl a), add_zero]
  exact Finset.sum_congr rfl fun i hi => if_pos (Finset.mem_range.mp hi)

/-- The coefficient extraction for `x^a y^a z^(a+1)`. -/
lemma coeff_V_diag_z (a : ℕ) : coeff (expo 0 a (a + 1)) (V a) =
    ∑ i ∈ Finset.range a,
      ((a.choose i : ℕ) : ℚ) * (a.choose (i + 1) : ℕ) * ((a + (a - i)).choose a : ℕ) := by
  rw [coeff_V, ← sum_range_succ_ite a]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  have hcongr : ∀ l ∈ Finset.range (a + 1),
      (if i ≤ a ∧ l ≤ a + 1 ∧ a - i = a + 1 - l then
        ((a.choose i : ℕ) : ℚ) * (a.choose l : ℕ) * ((a + (a - i)).choose a : ℕ) else 0) =
      (if i + 1 = l then
        ((a.choose i : ℕ) : ℚ) * (a.choose l : ℕ) * ((a + (a - i)).choose a : ℕ) else 0) := by
    intro l hl
    rw [Finset.mem_range] at hl
    exact if_congr (by omega) rfl rfl
  rw [Finset.sum_congr rfl hcongr, Finset.sum_ite_eq]
  exact if_congr (by rw [Finset.mem_range]; omega) rfl rfl

/-- The coefficient extraction for `x^a y^(a+1) z^a`. -/
lemma coeff_V_diag_y (a : ℕ) : coeff (expo 0 (a + 1) a) (V a) =
    ∑ i ∈ Finset.range a,
      ((a.choose i : ℕ) : ℚ) * (a.choose (i + 1) : ℕ) * ((a + (a - i)).choose a : ℕ) := by
  rw [coeff_V, Finset.sum_comm, ← sum_range_succ_ite a]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [Finset.mem_range] at hl
  have hcongr : ∀ i ∈ Finset.range (a + 1),
      (if i ≤ a + 1 ∧ l ≤ a ∧ a + 1 - i = a - l then
        ((a.choose i : ℕ) : ℚ) * (a.choose l : ℕ) * ((a + (a + 1 - i)).choose a : ℕ) else 0) =
      (if l + 1 = i then
        ((a.choose i : ℕ) : ℚ) * (a.choose l : ℕ) * ((a + (a + 1 - i)).choose a : ℕ) else 0) := by
    intro i hi
    rw [Finset.mem_range] at hi
    exact if_congr (by omega) rfl rfl
  rw [Finset.sum_congr rfl hcongr, Finset.sum_ite_eq]
  refine if_congr (by rw [Finset.mem_range]; omega) ?_ rfl
  rw [show a + 1 - (l + 1) = a - l by omega]
  ring

/-- **A352654 conjecture (Peter Bala), first form.** For `n ≥ 1`,
`a(n) = ∑_{k=1}^{n-1} C(n-1,k) C(n-1,k-1) C(n+k-1,k)` equals the coefficient of
`x^(n-1) y^(n-1) z^n` in `1/(1 - x - xy - yz - xz - xyz)`. -/
theorem a352654_eq_coeff_xy (n : ℕ) (hn : 1 ≤ n) :
    (a352654 n : ℚ) = coeff (expo (n - 1) (n - 1) n) denom⁻¹ := by
  obtain ⟨a, rfl⟩ : ∃ a, n = a + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel, coeff_denom_inv, coeff_V_diag_z, sum_reflect]

/-- **A352654 conjecture (Peter Bala), second form.** For `n ≥ 1`, `a(n)` equals the
coefficient of `x^(n-1) y^n z^(n-1)` in `1/(1 - x - xy - yz - xz - xyz)`. -/
theorem a352654_eq_coeff_xz (n : ℕ) (hn : 1 ≤ n) :
    (a352654 n : ℚ) = coeff (expo (n - 1) n (n - 1)) denom⁻¹ := by
  obtain ⟨a, rfl⟩ : ∃ a, n = a + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel, coeff_denom_inv, coeff_V_diag_y, sum_reflect]

/-- **A352654, Bala's conjecture (Apr 14 2022), first equality — proved.**
For `n ≥ 1`, the coefficient of `x^(n-1) y^(n-1) z^n` (`x = X 0`, `y = X 1`,
`z = X 2`) in `1/(1 - x - xy - yz - xz - xyz)` over `ℚ` equals
`a(n) = ∑_{k=1}^{n-1} C(n-1,k) C(n-1,k-1) C(n+k-1,k)`. -/
theorem coeff_xy_pow_mul_z_pow_eq (n : ℕ) (hn : 1 ≤ n) :
    coeff (Finsupp.single 0 (n - 1) + Finsupp.single 1 (n - 1) + Finsupp.single 2 n)
      (1 - X 0 - X 0 * X 1 - X 1 * X 2 - X 0 * X 2 - X 0 * X 1 * X 2 :
        MvPowerSeries (Fin 3) ℚ)⁻¹ = (a352654 n : ℚ) :=
  (a352654_eq_coeff_xy n hn).symm

/-- **A352654, Bala's conjecture (Apr 14 2022), second equality — proved.**
For `n ≥ 1`, the coefficient of `x^(n-1) y^n z^(n-1)` in
`1/(1 - x - xy - yz - xz - xyz)` over `ℚ` equals `a(n)`. -/
theorem coeff_xz_pow_mul_y_pow_eq (n : ℕ) (hn : 1 ≤ n) :
    coeff (Finsupp.single 0 (n - 1) + Finsupp.single 1 n + Finsupp.single 2 (n - 1))
      (1 - X 0 - X 0 * X 1 - X 1 * X 2 - X 0 * X 2 - X 0 * X 1 * X 2 :
        MvPowerSeries (Fin 3) ℚ)⁻¹ = (a352654 n : ℚ) :=
  (a352654_eq_coeff_xz n hn).symm

/-! ## Sanity layer -/

-- Ground truth: the definition reproduces the first listed terms
-- 0, 0, 2, 18, 162, 1500, 14240 (offset 0).
example : a352654 0 = 0 := by decide
example : a352654 1 = 0 := by decide
example : a352654 2 = 2 := by decide
example : a352654 3 = 18 := by decide
example : a352654 4 = 162 := by decide
example : a352654 5 = 1500 := by decide
example : a352654 6 = 14240 := by decide

-- Non-vacuity: the hypothesis `1 ≤ n` is satisfiable, and at `n = 3` the theorem
-- asserts the nonzero value `18` for the coefficient of `x^2 y^2 z^3`.
example : coeff (Finsupp.single 0 2 + Finsupp.single 1 2 + Finsupp.single 2 3)
    (1 - X 0 - X 0 * X 1 - X 1 * X 2 - X 0 * X 2 - X 0 * X 1 * X 2 :
      MvPowerSeries (Fin 3) ℚ)⁻¹ = 18 := by
  have h := coeff_xy_pow_mul_z_pow_eq 3 (by norm_num)
  have h3 : a352654 3 = 18 := by decide
  rw [h3] at h
  exact_mod_cast h

end Candidates.A352654SumCoefficientXyz
