/-
# A sharp Lucas-number congruence (A144837)

Source: Peter Bala's OEIS A144837 formulas (Nov 14 2022).
For `a(n)=Lucas(5^n)`, `n ≥ 1` and `r ≤ n`,
`5^(n+r+1)` divides `a(n+1)-a(n)` in `ℤ`.
In fact this difference has 5-adic valuation exactly `2n+1`, so the range
of `r` is sharp. The proof uses `L(5m)=L(m)^5+5L(m)^3+5L(m)` for odd `m`
and factors successive differences. The entry starts at index 1.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A144837LucasDividesEquivalently

open Real

/-! ## Definitions -/

/-- The Lucas numbers `A000032`: `L(0) = 2`, `L(1) = 1`,
`L(n + 2) = L(n + 1) + L(n)`. -/
def lucas : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | n + 2 => lucas (n + 1) + lucas n

/-- `A144837`: `a(n) = Lucas(5^n)` (the entry's offset is `1`). -/
def a (n : ℕ) : ℤ := lucas (5 ^ n)

/-! ## Examples -/

example : lucas 0 = 2 ∧ lucas 1 = 1 ∧ lucas 2 = 3 ∧ lucas 3 = 4 ∧ lucas 4 = 7 ∧
    lucas 5 = 11 ∧ lucas 6 = 18 := by decide

example : a 1 = 11 := by decide

example : a 2 = 167761 := by decide

set_option maxRecDepth 10000 in
example : a 3 = 132878596168524201724674011 := by decide

/-! ## The quintupling identity -/

/-- Binet's formula for the Lucas numbers: `L(n) = φ^n + ψ^n`. -/
theorem lucas_eq_goldenRatio_pow_add (n : ℕ) :
    (lucas n : ℝ) = goldenRatio ^ n + goldenConj ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => norm_num [lucas]
    | 1, _ => simp [lucas, goldenRatio_add_goldenConj]
    | n + 2, ih =>
      rw [lucas, Int.cast_add, ih (n + 1) (by omega), ih n (by omega)]
      have h1 : goldenRatio ^ (n + 2) = goldenRatio ^ (n + 1) + goldenRatio ^ n := by
        rw [pow_succ, pow_succ, mul_assoc, ← sq, goldenRatio_sq]; ring
      have h2 : goldenConj ^ (n + 2) = goldenConj ^ (n + 1) + goldenConj ^ n := by
        rw [pow_succ, pow_succ, mul_assoc, ← sq, goldenConj_sq]; ring
      rw [h1, h2]; ring

/-- For odd `m`, `L(5m) = L(m)^5 + 5 L(m)^3 + 5 L(m)`. -/
theorem lucas_five_mul (m : ℕ) (hm : Odd m) :
    lucas (5 * m) = lucas m ^ 5 + 5 * lucas m ^ 3 + 5 * lucas m := by
  have hab : goldenRatio ^ m * goldenConj ^ m = -1 := by
    rw [← mul_pow, goldenRatio_mul_goldenConj, hm.neg_one_pow]
  have key : ((lucas (5 * m) : ℤ) : ℝ) =
      ((lucas m ^ 5 + 5 * lucas m ^ 3 + 5 * lucas m : ℤ) : ℝ) := by
    push_cast
    rw [lucas_eq_goldenRatio_pow_add, lucas_eq_goldenRatio_pow_add, pow_mul',
      pow_mul' goldenConj]
    set x := goldenRatio ^ m
    set y := goldenConj ^ m
    linear_combination (-5 * (x + y) ^ 3 + 5 * (x + y) * (x * y - 1)) * hab
  exact_mod_cast key

/-- The recurrence `a(n + 1) = a(n)^5 + 5 a(n)^3 + 5 a(n)` from the entry. -/
theorem a_succ (n : ℕ) : a (n + 1) = a n ^ 5 + 5 * a n ^ 3 + 5 * a n := by
  unfold a
  rw [pow_succ']
  exact lucas_five_mul (5 ^ n) (Odd.pow (by decide))

/-! ## Residues modulo `125` -/

/-- `a(n) ≡ 11 (mod 125)` for `n ≥ 1`. -/
theorem a_cast_zmod_125 (n : ℕ) (hn : 1 ≤ n) : (a n : ZMod 125) = 11 := by
  induction n, hn using Nat.le_induction with
  | base => rw [show a 1 = 11 by decide]; rfl
  | succ n hn ih =>
    rw [a_succ]
    push_cast
    rw [ih]
    decide

/-- The difference quotient `g(x, y) = (f(x) - f(y)) / (x - y)` for
`f(x) = x^5 + 5x^3 + 5x`. -/
def g (x y : ℤ) : ℤ :=
  x ^ 4 + x ^ 3 * y + x ^ 2 * y ^ 2 + x * y ^ 3 + y ^ 4 + 5 * (x ^ 2 + x * y + y ^ 2) + 5

/-- `f(x) - f(y) = (x - y) g(x, y)`. -/
theorem f_sub_f (x y : ℤ) :
    (x ^ 5 + 5 * x ^ 3 + 5 * x) - (y ^ 5 + 5 * y ^ 3 + 5 * y) = (x - y) * g x y := by
  unfold g; ring

/-- For `n ≥ 1`, `g(a(n + 1), a(n)) = 25 (1 + 5t)` for some integer `t`. -/
theorem g_eq (n : ℕ) (hn : 1 ≤ n) : ∃ t : ℤ, g (a (n + 1)) (a n) = 25 * (1 + 5 * t) := by
  have hcast : ((g (a (n + 1)) (a n) : ℤ) : ZMod 125) = ((25 : ℤ) : ZMod 125) := by
    unfold g
    push_cast
    rw [a_cast_zmod_125 n hn, a_cast_zmod_125 (n + 1) (by omega)]
    decide
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hcast
  obtain ⟨t, ht⟩ := hcast
  exact ⟨-t, by push_cast at ht; linarith⟩

/-! ## The exact `5`-adic order of the differences -/

/-- For `n ≥ 1`, `a(n + 1) - a(n) = 5^(2n+1) u` with `5 ∤ u`. -/
theorem a_succ_sub_eq (n : ℕ) (hn : 1 ≤ n) :
    ∃ u : ℤ, a (n + 1) - a n = 5 ^ (2 * n + 1) * u ∧ ¬ (5 : ℤ) ∣ u := by
  induction n, hn using Nat.le_induction with
  | base =>
    refine ⟨1342, ?_, by decide⟩
    rw [show a 2 = 167761 by decide, show a 1 = 11 by decide]
    norm_num
  | succ n hn ih =>
    obtain ⟨u, hu, hu5⟩ := ih
    obtain ⟨t, ht⟩ := g_eq n hn
    refine ⟨u * (1 + 5 * t), ?_, ?_⟩
    · rw [a_succ (n + 1), a_succ n, f_sub_f, ← a_succ n, hu, ht]
      ring
    · have hp : Prime (5 : ℤ) := Int.prime_iff_natAbs_prime.mpr (by norm_num)
      intro hdvd
      rcases hp.dvd_or_dvd hdvd with h | h
      · exact hu5 h
      · omega

/-- **Sharper statement.** For `n ≥ 1`, the `5`-adic valuation of
`Lucas(5^(n+1)) - Lucas(5^n)` is exactly `2n + 1`. -/
theorem padicValInt_a_succ_sub (n : ℕ) (hn : 1 ≤ n) :
    padicValInt 5 (a (n + 1) - a n) = 2 * n + 1 := by
  obtain ⟨u, hu, hu5⟩ := a_succ_sub_eq n hn
  have hu0 : u ≠ 0 := by rintro rfl; exact hu5 (dvd_zero 5)
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [hu, padicValInt.mul (pow_ne_zero _ (by norm_num)) hu0,
    padicValInt.eq_zero_of_not_dvd (p := 5) (z := u) (by exact_mod_cast hu5)]
  simp [padicValInt]

/-- Bala's congruence: for `a(n)=Lucas(5^n)`, `n ≥ 1`, and `r ≤ n`,
`5^(n+r+1)` divides `a(n+1)-a(n)`. -/
theorem conjecture (r n : ℕ) (hn : 1 ≤ n) (hrn : r ≤ n) :
    (5 : ℤ) ^ (n + r + 1) ∣ a (n + 1) - a n := by
  obtain ⟨u, hu, -⟩ := a_succ_sub_eq n hn
  rw [hu]
  exact (pow_dvd_pow 5 (by omega)).mul_right u

-- Non-vacuity: the hypotheses of `conjecture` are met at `n = r = 1`.
example : (5 : ℤ) ^ 3 ∣ a 2 - a 1 := conjecture 1 1 le_rfl le_rfl

/-- The range `r ≤ n` in `conjecture` is sharp: for `n ≥ 1`,
`5^(2n+2)` does not divide `a(n+1) - a(n)`. -/
theorem not_pow_dvd_a_succ_sub (n : ℕ) (hn : 1 ≤ n) :
    ¬ (5 : ℤ) ^ (2 * n + 2) ∣ a (n + 1) - a n := by
  obtain ⟨u, hu, hu5⟩ := a_succ_sub_eq n hn
  rw [hu, pow_succ, mul_dvd_mul_iff_left (pow_ne_zero _ (by norm_num))]
  exact hu5

end Candidates.A144837LucasDividesEquivalently
