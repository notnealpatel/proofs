/-
# A038867 — Purath: no term of `(n+5)^3 - n^3` is a perfect square

Klaus Purath's conjecture in OEIS A038867 (2026): no term of
`a(n) = (n+5)^3 - n^3` (offset 0) is a square. Elmo R. Oliveira's formula
(2025) is `a(n) = 5(3n^2 + 15n + 25)`.

The result holds for every integer `n` (hence in particular
for every `n ≥ 0`), by a 5-adic valuation argument: if
`m^2 = 5 (3n^2 + 15n + 25)` then `5 ∣ m`, then `5 ∣ n`; writing `n = 5t` gives
`a(n) = 125 (3t^2 + 3t + 1)` and `3t^2 + 3t + 1` is never divisible by `5`,
so the `5`-adic valuation of `a(n)` is `3`, which is odd.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A038867ParticularPerfectSquare

/-! ## Definitions -/

/-- The OEIS sequence A038867, `a(n) = (n+5)^3 - n^3`, extended to all integers
`n` (the entry itself mentions `a(-1) = 65` and `a(-2) = 35`). -/
def a (n : ℤ) : ℤ := (n + 5) ^ 3 - n ^ 3

/-! ## Examples against the DATA line `125, 215, 335, 485, 665, 875` -/

example : a 0 = 125 := by decide
example : a 1 = 215 := by decide
example : a 2 = 335 := by decide
example : a 3 = 485 := by decide
example : a 4 = 665 := by decide
example : a 5 = 875 := by decide
-- The values `a(-1) = 65` and `a(-2) = 35` quoted in Purath's comment.
example : a (-1) = 65 := by decide
example : a (-2) = 35 := by decide

/-- The closed form `a(n) = 5 (3n^2 + 15n + 25)` (Oliveira's formula). -/
theorem a_eq (n : ℤ) : a n = 5 * (3 * n ^ 2 + 15 * n + 25) := by
  unfold a
  ring

/-! ## Helper lemmas -/

/-- In `ZMod 5`, the quadratic `3t^2 + 3t + 1` has no root (its discriminant
`9 - 12 ≡ 2` is a non-residue modulo `5`). -/
theorem zmod5_quadratic_ne_zero : ∀ t : ZMod 5, 3 * t ^ 2 + 3 * t + 1 ≠ 0 := by
  decide

/-- If `5` divides `c * x^2` for an integer `x` and `c` is a unit modulo `5`
(here `c ≢ 0 mod 5`), then `5` divides `x`. -/
theorem five_dvd_of_five_dvd_mul_sq (c x : ℤ) (hc : ¬ (5 : ℤ) ∣ c)
    (h : (5 : ℤ) ∣ c * x ^ 2) : (5 : ℤ) ∣ x := by
  have hprime : Prime (5 : ℤ) := Int.prime_iff_natAbs_prime.mpr (by norm_num)
  rcases hprime.dvd_or_dvd h with hdc | hdx
  · exact absurd hdc hc
  · exact hprime.dvd_of_dvd_pow hdx

/-- The integer `3t^2 + 3t + 1` is never divisible by `5`. -/
theorem not_five_dvd_quadratic (t : ℤ) : ¬ (5 : ℤ) ∣ 3 * t ^ 2 + 3 * t + 1 := by
  intro h
  have hz : ((3 * t ^ 2 + 3 * t + 1 : ℤ) : ZMod 5) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mpr h
  push_cast at hz
  exact zmod5_quadratic_ne_zero (t : ZMod 5) hz

/-! ## The conjecture -/

/-- Purath's conjecture (OEIS A038867, 2026), extended from `n ≥ 0` to all
integers: `(n+5)^3-n^3` is not an integer square. The proof forces `5 ∣ m`
and `5 ∣ n`; writing `n=5t` gives `a(5t)=125(3t²+3t+1)` with
`5 ∤ 3t²+3t+1`. -/
theorem a_ne_sq (n m : ℤ) : a n ≠ m ^ 2 := by
  intro h
  rw [a_eq] at h
  -- Step 1: `5 ∣ m`.
  have h5m : (5 : ℤ) ∣ m :=
    five_dvd_of_five_dvd_mul_sq 1 m (by decide) ⟨3 * n ^ 2 + 15 * n + 25, by linarith⟩
  obtain ⟨k, rfl⟩ := h5m
  have hk : 3 * n ^ 2 + 15 * n + 25 = 5 * k ^ 2 := by linarith
  -- Step 2: `5 ∣ n`.
  have h5n : (5 : ℤ) ∣ n :=
    five_dvd_of_five_dvd_mul_sq 3 n (by decide) ⟨k ^ 2 - 3 * n - 5, by linarith⟩
  obtain ⟨t, rfl⟩ := h5n
  have ht : 15 * t ^ 2 + 15 * t + 5 = k ^ 2 := by linarith
  -- Step 3: `5 ∣ k`.
  have h5k : (5 : ℤ) ∣ k :=
    five_dvd_of_five_dvd_mul_sq 1 k (by decide) ⟨3 * t ^ 2 + 3 * t + 1, by linarith⟩
  obtain ⟨l, rfl⟩ := h5k
  -- Step 4: `3t^2 + 3t + 1 = 5 l^2`, contradicting `not_five_dvd_quadratic`.
  exact not_five_dvd_quadratic t ⟨l ^ 2, by linarith⟩

/-- **Purath's conjecture, `IsSquare` form.** For every integer `n` (in
particular every `n ≥ 0` indexing the entry), `a(n) = (n+5)^3 - n^3` is not a
perfect square. -/
theorem not_isSquare_a (n : ℤ) : ¬ IsSquare (a n) := by
  rintro ⟨m, hm⟩
  exact a_ne_sq n m (by rw [hm]; ring)

/-- **Purath's conjecture over the natural numbers**, matching the entry's
offset `0`: for every `n : ℕ`, `(n+5)^3 - n^3` (a natural number, since
`n^3 ≤ (n+5)^3`; the subtraction is not truncated) is not a perfect square. -/
theorem nat_not_isSquare (n : ℕ) : ¬ IsSquare ((n + 5) ^ 3 - n ^ 3) := by
  rintro ⟨m, hm⟩
  have hle : n ^ 3 ≤ (n + 5) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have hz : (((n + 5) ^ 3 - n ^ 3 : ℕ) : ℤ) = ((m * m : ℕ) : ℤ) := by rw [hm]
  push_cast [Nat.cast_sub hle] at hz
  exact a_ne_sq (n : ℤ) (m : ℤ) (by unfold a; rw [hz]; ring)

/-! ## Examples -/

-- The quantified domain is nonempty and the hypothesis-free statement is
-- non-vacuous: the closed form really is near squares, e.g. `a(0) = 125`
-- lies between `11^2 = 121` and `12^2 = 144`.
example : (11 : ℤ) ^ 2 < a 0 ∧ a 0 < 12 ^ 2 := by decide

-- The obstruction genuinely needs the 5-adic valuation: `a(n)` is divisible by
-- `5` for every `n`, and by `125` at `n = 0`, yet `125` is not a square.
example : ¬ IsSquare (125 : ℤ) := not_isSquare_a 0

end Candidates.A038867ParticularPerfectSquare
