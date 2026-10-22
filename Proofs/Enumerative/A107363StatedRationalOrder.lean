/-
Values of the rational generating function in OEIS A107363
(Creighton Dement, May 24 2005).

The sequence is defined by its initial twelve values and
 a(n+12)=4a(n+6)+a(n) (Colin Barker, May 11 2019).
The denominator/numerator identity and uniqueness identify this with the
entry's rational generating function. The six residue-class formulas give
both descriptions of its nonnegative value set as the Fibonacci numbers,
and a(6n+2)=-Lucas(3n+1)=-A048876(n). Natural indices include zero.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A107363StatedRationalOrder

open PowerSeries

/-! ## Definition layer -/

/-- A107363, given by Barker's recurrence `a(n) = 4*a(n-6) + a(n-12)` (`n > 11`)
with the twelve initial terms listed in the entry.  `gf_mul_eq` and
`eq_mk_of_gf` show this is exactly the coefficient sequence of the entry's
rational generating function. -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | 2 => -1
  | 3 => 1
  | 4 => 2
  | 5 => 0
  | 6 => 5
  | 7 => 3
  | 8 => -7
  | 9 => 3
  | 10 => 8
  | 11 => 0
  | n + 12 => 4 * a (n + 6) + a n

/-- A048876: `b(n) = 4*b(n-1) + b(n-2)`, `b(0) = 1`, `b(1) = 7`. -/
def b : ℕ → ℕ
  | 0 => 1
  | 1 => 7
  | n + 2 => 4 * b (n + 1) + b n

/-- The Lucas numbers A000032: `L(0) = 2`, `L(1) = 1`, `L(n+2) = L(n+1) + L(n)`. -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => lucas (n + 1) + lucas n

-- The first 30 listed terms of A107363.
example : (List.range 30).map a =
    [1, 1, -1, 1, 2, 0, 5, 3, -7, 3, 8, 0, 21, 13, -29, 13, 34, 0, 89, 55, -123,
      55, 144, 0, 377, 233, -521, 233, 610, 0] := by decide

-- The first terms of A048876 and of the Lucas numbers.
example : (List.range 8).map b = [1, 7, 29, 123, 521, 2207, 9349, 39603] := by decide
example : (List.range 10).map lucas = [2, 1, 3, 4, 7, 11, 18, 29, 47, 76] := by decide

/-- Barker's recurrence, as an equation. -/
theorem a_add_twelve (n : ℕ) : a (n + 12) = 4 * a (n + 6) + a n := by
  rw [a]

/-! ## Fibonacci and Lucas step-three identities -/

/-- `F(m+6) = 4*F(m+3) + F(m)`. -/
theorem fib_add_six (m : ℕ) : Nat.fib (m + 6) = 4 * Nat.fib (m + 3) + Nat.fib m := by
  simp only [Nat.fib_add_two, show m + 6 = m + 4 + 2 by omega, show m + 5 = m + 3 + 2 by omega,
    show m + 4 = m + 2 + 2 by omega, show m + 3 = m + 1 + 2 by omega]
  ring

/-- `L(m+2) = L(m+1) + L(m)`, as an equation. -/
theorem lucas_add_two (m : ℕ) : lucas (m + 2) = lucas (m + 1) + lucas m := by
  rw [lucas]

/-- `L(m+6) = 4*L(m+3) + L(m)`. -/
theorem lucas_add_six (m : ℕ) : lucas (m + 6) = 4 * lucas (m + 3) + lucas m := by
  simp only [lucas_add_two, show m + 6 = m + 4 + 2 by omega, show m + 5 = m + 3 + 2 by omega,
    show m + 4 = m + 2 + 2 by omega, show m + 3 = m + 1 + 2 by omega]
  ring

/-- Lucas numbers are positive. -/
theorem lucas_pos (m : ℕ) : 0 < lucas m := by
  induction m using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n _ ih => rw [lucas_add_two]; omega

/-- A048876 is the Lucas trisection `b(n) = L(3n+1)` (the entry's cross-reference
`A048876(n) = A000032(3*n+1)`). -/
theorem b_eq_lucas (n : ℕ) : b n = lucas (3 * n + 1) := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n ih0 ih1 =>
    rw [b, ih0, ih1, show 3 * (n + 2) + 1 = (3 * n + 1) + 6 by ring, lucas_add_six,
      show 3 * n + 1 + 3 = 3 * (n + 1) + 1 by ring]

/-! ## The six residue-class closed forms -/

/-- The closed forms of `a` on the six residue classes mod `6`:
`a(6k) = F(3k+2)`, `a(6k+1) = a(6k+3) = F(3k+1)`, `a(6k+2) = -L(3k+1)`,
`a(6k+4) = F(3k+3)`, `a(6k+5) = 0`. -/
def ClosedForm (k : ℕ) : Prop :=
  a (6 * k) = Nat.fib (3 * k + 2) ∧ a (6 * k + 1) = Nat.fib (3 * k + 1) ∧
    a (6 * k + 2) = -(lucas (3 * k + 1) : ℤ) ∧ a (6 * k + 3) = Nat.fib (3 * k + 1) ∧
    a (6 * k + 4) = Nat.fib (3 * k + 3) ∧ a (6 * k + 5) = 0

/-- The closed forms hold for every `k`, by two-step induction from Barker's
recurrence and the step-three Fibonacci/Lucas identities. -/
theorem closedForm (k : ℕ) : ClosedForm k := by
  induction k using Nat.twoStepInduction with
  | zero => unfold ClosedForm; decide
  | one => unfold ClosedForm; decide
  | more n ih0 ih1 =>
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ := ih0
    obtain ⟨h0', h1', h2', h3', h4', h5'⟩ := ih1
    have e : ∀ r : ℕ, 6 * (n + 2) + r = (6 * n + r) + 12 := fun r => by ring
    have e' : ∀ r : ℕ, 6 * n + r + 6 = 6 * (n + 1) + r := fun r => by ring
    have f : ∀ r : ℕ, 3 * (n + 2) + r = (3 * n + r) + 6 := fun r => by ring
    have f' : ∀ r : ℕ, 3 * n + r + 3 = 3 * (n + 1) + r := fun r => by ring
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [show 6 * (n + 2) = 6 * n + 12 by ring, a_add_twelve, show 6 * n + 6 = 6 * (n + 1) by ring,
        h0, h0', f, fib_add_six, f']
      push_cast; ring
    · rw [e, a_add_twelve, e', h1, h1', f, fib_add_six, f']
      push_cast; ring
    · rw [e, a_add_twelve, e', h2, h2', f, lucas_add_six, f']
      push_cast; ring
    · rw [e, a_add_twelve, e', h3, h3', f, fib_add_six, f']
      push_cast; ring
    · rw [e, a_add_twelve, e', h4, h4', f, fib_add_six, f']
      push_cast; ring
    · rw [e, a_add_twelve, e', h5, h5']
      ring

/-! ## The A048876 / Lucas formula -/

/-- **Entry formula (stated as a conjecture in the entry).**
`a(6n+2) = -A048876(n) = -L(3n+1)`. -/
theorem a_six_mul_add_two (n : ℕ) :
    a (6 * n + 2) = -(b n : ℤ) ∧ a (6 * n + 2) = -(lucas (3 * n + 1) : ℤ) := by
  have h := (closedForm n).2.2.1
  exact ⟨by rw [h, b_eq_lucas], h⟩

/-! ## The set equalities -/

/-- Every Fibonacci number is a value `a n` with `n % 6 ≠ 2`. -/
theorem exists_a_eq_fib (m : ℕ) : ∃ n : ℕ, n % 6 ≠ 2 ∧ a n = Nat.fib m := by
  obtain ⟨j, hj | hj | hj⟩ : ∃ j, m = 3 * j ∨ m = 3 * j + 1 ∨ m = 3 * j + 2 :=
    ⟨m / 3, by omega⟩
  · rcases j with _ | j
    · exact ⟨5, by decide, by subst hj; decide⟩
    · refine ⟨6 * j + 4, by omega, ?_⟩
      rw [(closedForm j).2.2.2.2.1, hj, show 3 * (j + 1) = 3 * j + 3 by ring]
  · exact ⟨6 * j + 1, by omega, by rw [(closedForm j).2.1, hj]⟩
  · exact ⟨6 * j, by omega, by rw [(closedForm j).1, hj]⟩

/-- Every value `a n` with `n % 6 ≠ 2` is a Fibonacci number. -/
theorem exists_fib_eq_a (n : ℕ) (hn : n % 6 ≠ 2) : ∃ m : ℕ, (Nat.fib m : ℤ) = a n := by
  obtain ⟨k, r, hr, rfl⟩ : ∃ k r, r < 6 ∧ n = 6 * k + r := ⟨n / 6, n % 6, by omega, by omega⟩
  obtain ⟨h0, h1, _, h3, h4, h5⟩ := closedForm k
  interval_cases r
  · exact ⟨3 * k + 2, h0.symm⟩
  · exact ⟨3 * k + 1, h1.symm⟩
  · omega
  · exact ⟨3 * k + 1, h3.symm⟩
  · exact ⟨3 * k + 3, h4.symm⟩
  · exact ⟨0, by rw [h5]; rfl⟩

/-- The values `a(6k+2)` are negative, so a nonnegative value has `n % 6 ≠ 2`. -/
theorem a_neg_of_mod_eq_two (n : ℕ) (hn : n % 6 = 2) : a n < 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 6 * k + 2 := ⟨n / 6, by omega⟩
  rw [(closedForm k).2.2.1]
  have hpos := lucas_pos (3 * k + 1)
  omega

/-- The Fibonacci numbers are exactly the nonnegative values of A107363,
and exactly its values at indices not congruent to `2` modulo `6`.
These are subsets of `ℤ`; natural indices include zero. -/
theorem conjecture :
    {x : ℤ | ∃ m : ℕ, (Nat.fib m : ℤ) = x} = {x : ℤ | ∃ n : ℕ, a n = x ∧ 0 ≤ x} ∧
      {x : ℤ | ∃ n : ℕ, a n = x ∧ 0 ≤ x} = {x : ℤ | ∃ n : ℕ, n % 6 ≠ 2 ∧ a n = x} := by
  have hFA : {x : ℤ | ∃ m : ℕ, (Nat.fib m : ℤ) = x} =
      {x : ℤ | ∃ n : ℕ, n % 6 ≠ 2 ∧ a n = x} := by
    ext x
    constructor
    · rintro ⟨m, rfl⟩
      exact exists_a_eq_fib m
    · rintro ⟨n, hn, rfl⟩
      exact exists_fib_eq_a n hn
  have hAA : {x : ℤ | ∃ n : ℕ, a n = x ∧ 0 ≤ x} =
      {x : ℤ | ∃ n : ℕ, n % 6 ≠ 2 ∧ a n = x} := by
    ext x
    constructor
    · rintro ⟨n, rfl, hx⟩
      refine ⟨n, fun hn => ?_, rfl⟩
      have hneg := a_neg_of_mod_eq_two n hn
      omega
    · rintro ⟨n, hn, rfl⟩
      obtain ⟨m, hm⟩ := exists_fib_eq_a n hn
      exact ⟨n, rfl, hm ▸ Int.natCast_nonneg _⟩
  exact ⟨hFA.trans hAA.symm, hAA⟩

/-! ## The generating function -/

/-- The entry's numerator `(1 - x)(1 + x)^2(1 + x^2)(1 - x^2 + 2x^3 + x^4)`. -/
noncomputable def numer : PowerSeries ℤ :=
  (1 - X) * (1 + X) ^ 2 * (1 + X ^ 2) * (1 - X ^ 2 + 2 * X ^ 3 + X ^ 4)

/-- The entry's denominator `(1 - x^2 - x^4)(1 + x^2 + 2x^4 - x^6 + x^8)`. -/
noncomputable def denom : PowerSeries ℤ :=
  (1 - X ^ 2 - X ^ 4) * (1 + X ^ 2 + 2 * X ^ 4 - X ^ 6 + X ^ 8)

/-- The denominator multiplies out to `1 - 4x^6 - x^12`. -/
theorem denom_eq : denom = 1 - 4 * X ^ 6 - X ^ 12 := by
  unfold denom; ring

/-- The numerator multiplies out to `1 + x - x^2 + x^3 + 2x^4 + x^6 - x^7 - 3x^8 - x^9`. -/
theorem numer_eq :
    numer = 1 + X - X ^ 2 + X ^ 3 + 2 * X ^ 4 + X ^ 6 - X ^ 7 - 3 * X ^ 8 - X ^ 9 := by
  unfold numer; ring

/-- **The g.f. of `a` is the entry's rational function:**
`denom * Σ a(n) xⁿ = numer`. -/
theorem gf_mul_eq : denom * PowerSeries.mk a = numer := by
  rw [denom_eq, numer_eq]
  have hsplit : (1 - 4 * X ^ 6 - X ^ 12) * PowerSeries.mk a =
      PowerSeries.mk a - C (4 : ℤ) * (X ^ 6 * PowerSeries.mk a) - X ^ 12 * PowerSeries.mk a := by
    rw [show (C (4 : ℤ) : PowerSeries ℤ) = 4 from map_ofNat C 4]; ring
  have hnum : (1 + X - X ^ 2 + X ^ 3 + 2 * X ^ 4 + X ^ 6 - X ^ 7 - 3 * X ^ 8 - X ^ 9 :
      PowerSeries ℤ) = 1 + X - X ^ 2 + X ^ 3 + C (2 : ℤ) * X ^ 4 + X ^ 6 - X ^ 7
        - C (3 : ℤ) * X ^ 8 - X ^ 9 := by
    rw [show (C (2 : ℤ) : PowerSeries ℤ) = 2 from map_ofNat C 2,
      show (C (3 : ℤ) : PowerSeries ℤ) = 3 from map_ofNat C 3]
  rw [hsplit, hnum]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_X_pow_mul', coeff_mk, coeff_X_pow, coeff_one,
    coeff_X]
  rcases lt_or_ge n 12 with hn | hn
  · interval_cases n <;> decide
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 12 := ⟨n - 12, by omega⟩
    rw [a_add_twelve]
    simp only [show 6 ≤ m + 12 by omega, show 12 ≤ m + 12 by omega, if_true,
      show m + 12 - 6 = m + 6 by omega, show m + 12 - 12 = m by omega]
    simp

/-- **The g.f. determines the sequence:** any power series `f` with
`denom * f = numer` (i.e. `f = numer / denom`, the entry's NAME) is `Σ a(n) xⁿ`.
The hypothesis is satisfiable, by `gf_mul_eq`. -/
theorem eq_mk_of_gf (f : PowerSeries ℤ) (hf : denom * f = numer) : f = PowerSeries.mk a := by
  have hden : denom ≠ 0 := by
    intro h
    have h0 := congrArg (PowerSeries.constantCoeff) h
    rw [denom_eq] at h0
    simp at h0
  exact mul_left_cancel₀ hden (hf.trans gf_mul_eq.symm)

end Candidates.A107363StatedRationalOrder
