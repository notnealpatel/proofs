/-
# A232174 — Sun: the list of `n` with `a(n) = 1` omits `n = 66`

Zhi-Wei Sun's conjecture (i) in OEIS A232174 combines positivity of `a(n)`
for `n > 1` with a list of indices at which `a(n) = 1`. The list omits `66`:
the unique representation `66 = 53+13` gives the primes `911` and `13963`.
This refutes the list, not the positivity claim. Parts (ii) and (iii), the
positivity claim, and a list enlarged by `66` are not treated.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A232174Refutation

open Finset

/-! ## Definitions -/

/-- OEIS A232174: `a(n)` is the number of `x` with `0 < x < n` such that, with
`y = n - x`, both `x + n*y` and `x^2 + n*y^2` are prime.  The `ℕ` subtraction
`n - x` is exact on the range `x < n`; see `mem_filter_a232174_iff` for the
two-variable form `x + y = n`, `x, y > 0`.  (OEIS offset 1; `a 0 = 0`.) -/
def a232174 (n : ℕ) : ℕ :=
  #{x ∈ Ioo 0 n | (x + n * (n - x)).Prime ∧ (x ^ 2 + n * (n - x) ^ 2).Prime}

/-- The counted set is exactly the set of first parts `x` of representations
`n = x + y` with `x, y > 0` and `x + n*y`, `x^2 + n*y^2` both prime, so
`a232174` counts the representations of the OEIS name. -/
theorem mem_filter_a232174_iff (n x : ℕ) :
    x ∈ ({x ∈ Ioo 0 n | (x + n * (n - x)).Prime ∧ (x ^ 2 + n * (n - x) ^ 2).Prime} :
      Finset ℕ) ↔
      ∃ y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧ (x + n * y).Prime ∧ (x ^ 2 + n * y ^ 2).Prime := by
  simp only [mem_filter, mem_Ioo]
  constructor
  · rintro ⟨⟨hx0, hxn⟩, hp1, hp2⟩
    exact ⟨n - x, hx0, by omega, by omega, hp1, hp2⟩
  · rintro ⟨y, hx0, hy0, hxy, hp1, hp2⟩
    have hy : n - x = y := by omega
    rw [hy]
    exact ⟨⟨hx0, by omega⟩, hp1, hp2⟩

/-- `a(1), …, a(12)` match the OEIS data. -/
example : (List.range 12).map (fun i => a232174 (i + 1)) =
    [0, 1, 2, 2, 1, 2, 3, 1, 2, 2, 3, 2] := by
  decide +kernel

/-- Sun's conjecture (i) on A232174 (Zhi-Wei Sun):
`a(n) > 0` for all `n > 1`, and `a(n) = 1` only for
`n = 2, 5, 8, 14, 19, 20, 24, 32, 54, 68, 101, 168`.

"Only for" is rendered as the implication `a(n) = 1 → n ∈ list` over the OEIS
domain `n ≥ 1`; this is the weaker reading, so refuting it refutes every
stronger one (e.g. the biconditional). -/
def Conjecture : Prop :=
  (∀ n : ℕ, 1 < n → 0 < a232174 n) ∧
  ∀ n : ℕ, 1 ≤ n → a232174 n = 1 →
    n ∈ ({2, 5, 8, 14, 19, 20, 24, 32, 54, 68, 101, 168} : Finset ℕ)

/-! ## The refutation -/

/-- For `n = 66` the only admissible `x` is `53`: `53 + 66*13 = 911` and
`53^2 + 66*13^2 = 13963` are prime, while every other `0 < x < 66` makes one of
the two values composite. -/
theorem filter_a232174_sixtysix :
    ({x ∈ Ioo 0 66 | (x + 66 * (66 - x)).Prime ∧ (x ^ 2 + 66 * (66 - x) ^ 2).Prime} :
      Finset ℕ) = {53} := by
  ext x
  simp only [mem_filter, mem_Ioo, mem_singleton]
  constructor
  · rintro ⟨⟨hx0, hx66⟩, hprime⟩
    interval_cases x <;> first | rfl | norm_num at hprime
  · rintro rfl
    norm_num

/-- `a(66) = 1`, the unique representation being `66 = 53 + 13`
(this is the 66th term of the OEIS data). -/
theorem a232174_sixtysix : a232174 66 = 1 := by
  rw [a232174, filter_a232174_sixtysix, card_singleton]

/-- Sun's conjecture (i) on A232174 is false: `a(66) = 1` (unique
representation `66 = 53 + 13`, with `911` and `13963` prime), but `66` is
missing from the list `2, 5, 8, 14, 19, 20, 24, 32, 54, 68, 101, 168`.  The positivity part `a(n) > 0` for `n > 1` is untouched. -/
theorem a232174_conjecture_false : ¬ Conjecture := by
  rintro ⟨-, honly⟩
  have hmem := honly 66 (by norm_num) a232174_sixtysix
  simp at hmem

end Candidates.A232174Refutation
