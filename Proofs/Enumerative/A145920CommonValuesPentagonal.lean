/-
# A145920 — Mathar: recurrence and g.f. for common values of pentagonal numbers and C(n,4)

## OEIS source (retrieved with `oeis show A145920`, 2026-10-21)

```
NAME:     List of numbers that are both pentagonal (A000326) and binomial
          coefficients C(n,4) (A000332).
TERMS:    0,1,5,35,70,210,330,715,1001,1820,2380,3876,4845,7315,8855,12650,
          14950,20475,23751,31465,35960,46376,52360,66045,73815,91390,101270,...
OFFSET:   1 (a(1) = 0, as fixed by Tedeschi's formula below)
COMMENT:  All binomial coefficients C(n,4) belong to the generalized pentagonal
          sequence (A001318).
FORMULA:  a(n+1) = A000326 (A001318(n)).
FORMULA:  Positive values of A000332(n) belong to the sequence if and only if 3
          does not divide n. A000332(n) is positive when n>3.
FORMULA (the conjecture):
  Conjecture: a(n) = a(n-1) + 4a(n-2) - 4a(n-3) - 6a(n-4) + 6a(n-5) + 4a(n-6)
  - 4a(n-7) - a(n-8) + a(n-9). - _R. J. Mathar_, Oct 29 2008
  Conjecture: G.f.: x^2(1 + 4x + 26x^2 + 19x^3 + 4x^5 + x^6 + 26x^4)/((1+x)^4(1-x)^5).
  - _R. J. Mathar_, Oct 29 2008
FORMULA:  a(n) = (27x^4 - 18x^3 - 3x^2 + 2x)/8 where x = floor(n/2)*(-1)^n,
          for n >= 1. - _William A. Tedeschi_, Aug 16 2010
```

## Status

Triage: open (no proof in the entry or the literature found).  The entry's
own formulas make it a quasi-polynomial identity; this file proves both
conjectures from the definition (intersection of the two sets, enumerated in
increasing order), not from the unproved formula lines.

## Argument

* `24·C(n,4) + 1 = (n² - 3n + 1)²` for every `n`, and `m` is pentagonal iff
  `24m + 1 = (6j - 1)²` for some `j : ℕ`.
* Hence `C(n,4)` (with `n ≥ 4`) is pentagonal iff `3 ∤ n`: if `3 ∣ n` then
  `n² - 3n + 1 ≡ 1 (mod 3)` while `6j - 1 ≡ 2 (mod 3)`, and the negative root
  is excluded by size.
* So the set is `{C((3k+5)/2, 4) : k ∈ ℕ}`, listed in increasing order by `k`,
  i.e. `a(k+1) = C(⌊(3k+5)/2⌋, 4)`; the recurrence and the g.f. are then
  polynomial identities on each parity class of `k`.

Computation (python, 2026-10-21): the set enumerated directly up to `10^13`
(2624 terms) agrees with `C(⌊(3k+5)/2⌋, 4)`, satisfies the recurrence for all
`10 ≤ n ≤ 2624`, and `(1+x)^4(1-x)^5 · Σ a(n)xⁿ` has the stated numerator.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A145920CommonValuesPentagonal

open PowerSeries

/-! ## Definition layer -/

/-- `m` is a pentagonal number (A000326): `m = j(3j-1)/2` for some `j ≥ 0`.
The truncated subtraction `3 * j - 1` is harmless: it only truncates at
`j = 0`, where the product is `0` anyway, and `j(3j-1)` is always even. -/
def IsPentagonal (m : ℕ) : Prop := ∃ j : ℕ, m = j * (3 * j - 1) / 2

/-- `m` is a binomial coefficient `C(n,4)` (a term of A000332) for some `n ≥ 0`. -/
def IsChooseFour (m : ℕ) : Prop := ∃ n : ℕ, m = n.choose 4

/-- Membership in A145920: `m` is both pentagonal and of the form `C(n,4)`. -/
def InA145920 (m : ℕ) : Prop := IsPentagonal m ∧ IsChooseFour m

/-- The sequence A145920 with OEIS offset 1: `a n` is the `n`-th smallest
element (1-indexed) of the set of numbers that are both pentagonal and a
`C(n,4)`.  The value `a 0` is a junk value and is never used in statements. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth InA145920 (n - 1)

/-- The explicit enumeration: `closedForm k = C(⌊(3k+5)/2⌋, 4)`; the indices
`⌊(3k+5)/2⌋ = 2, 4, 5, 7, 8, 10, …` run over the non-multiples of `3`. -/
def closedForm (k : ℕ) : ℕ := ((3 * k + 5) / 2).choose 4

/-! ## Sanity layer for the definitions -/

-- Ground truth: the explicit enumeration reproduces the first DATA terms.
example : (List.range 12).map closedForm =
    [0, 1, 5, 35, 70, 210, 330, 715, 1001, 1820, 2380, 3876] := by decide

-- Ground truth: listed terms are members, by explicit witnesses
-- (`35 = P(5) = C(7,4)`, `70 = P(7) = C(8,4)`, `0 = P(0) = C(0,4)`).
example : InA145920 35 ∧ InA145920 70 ∧ InA145920 0 :=
  ⟨⟨⟨5, by decide⟩, ⟨7, by decide⟩⟩, ⟨⟨7, by decide⟩, ⟨8, by decide⟩⟩,
    ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩⟩

-- Ground truth: `15 = C(6,4)` is not pentagonal (`P(3) = 12 < 15 < 22 = P(4)`),
-- matching the FORMULA line "iff 3 does not divide n".
example : ¬ IsPentagonal 15 := by
  rintro ⟨j, hj⟩
  rcases Nat.lt_or_ge j 4 with h | h
  · interval_cases j <;> simp at hj
  · have h22 : 22 ≤ j * (3 * j - 1) / 2 := by
      have hmul : 4 * 11 ≤ j * (3 * j - 1) := Nat.mul_le_mul h (by omega)
      omega
    omega

/-! ## Algebraic helpers -/

/-- `24·C(n,4) = n(n-1)(n-2)(n-3)` in `ℤ`, for every `n`. -/
theorem choose_four_cast (n : ℕ) :
    24 * (n.choose 4 : ℤ) = n * (n - 1) * (n - 2) * (n - 3) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose n 4
  rcases Nat.lt_or_ge n 4 with hn | hn
  · interval_cases n <;> simp [Nat.choose]
  · obtain ⟨t, rfl⟩ : ∃ t, n = t + 4 := ⟨n - 4, by omega⟩
    have hdesc : (t + 4).descFactorial 4 = (t + 4) * (t + 3) * (t + 2) * (t + 1) := by
      simp only [Nat.descFactorial_succ, Nat.reduceSubDiff, Nat.add_one_sub_one, tsub_zero,
        Nat.descFactorial_zero, mul_one]
      ring
    rw [hdesc, show (4 : ℕ).factorial = 24 by decide] at h
    have hcast : ((t + 4 : ℕ) : ℤ) * (t + 3 : ℕ) * (t + 2 : ℕ) * (t + 1 : ℕ) =
        24 * ((t + 4).choose 4 : ℤ) := by
      exact_mod_cast h
    rw [← hcast]
    push_cast
    ring

/-- `24·C(n,4) + 1 = (n² - 3n + 1)²`: every `C(n,4)` is a generalized pentagonal
number (the entry's first comment). -/
theorem choose_four_sq (n : ℕ) :
    24 * (n.choose 4 : ℤ) + 1 = ((n : ℤ) ^ 2 - 3 * n + 1) ^ 2 := by
  rw [choose_four_cast]
  ring

/-- `m` is pentagonal iff `24m + 1 = (6j - 1)²` for some `j : ℕ`. -/
theorem isPentagonal_iff (m : ℕ) :
    IsPentagonal m ↔ ∃ j : ℕ, 24 * (m : ℤ) + 1 = (6 * (j : ℤ) - 1) ^ 2 := by
  constructor
  · rintro ⟨j, rfl⟩
    refine ⟨j, ?_⟩
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · have heven : Even (j * (3 * j - 1)) := by
        rcases Nat.even_or_odd j with h | h
        · exact h.mul_right _
        · apply Even.mul_left
          rcases h with ⟨r, rfl⟩
          exact ⟨3 * r + 1, by omega⟩
      have h2 : 2 * (j * (3 * j - 1) / 2) = j * (3 * j - 1) := Nat.two_mul_div_two_of_even heven
      have h2' : 2 * ((j * (3 * j - 1) / 2 : ℕ) : ℤ) = (j : ℤ) * (3 * j - 1) := by
        have hsub : ((3 * j - 1 : ℕ) : ℤ) = 3 * (j : ℤ) - 1 := by omega
        rw [← hsub]
        exact_mod_cast h2
      linear_combination 12 * h2'
  · rintro ⟨j, hj⟩
    refine ⟨j, ?_⟩
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · have hm : m = 0 := by
        simp only [Nat.cast_zero, mul_zero, zero_sub] at hj
        omega
      simp [hm]
    · have h2 : (2 * m : ℤ) = (j : ℤ) * (3 * j - 1) := by
        have h12 : (12 : ℤ) * (2 * m) = 12 * ((j : ℤ) * (3 * j - 1)) := by
          linear_combination hj
        exact mul_left_cancel₀ (by norm_num) h12
      have hsub : ((3 * j - 1 : ℕ) : ℤ) = 3 * (j : ℤ) - 1 := by omega
      have h2n : 2 * m = j * (3 * j - 1) := by
        have : ((2 * m : ℕ) : ℤ) = ((j * (3 * j - 1) : ℕ) : ℤ) := by
          push_cast [hsub]
          exact h2
        exact_mod_cast this
      omega

/-- `24·closedForm k` as an explicit polynomial in any `n` with `⌊(3k+5)/2⌋ = n`. -/
theorem closedForm_cast {k n : ℕ} (h : (3 * k + 5) / 2 = n) :
    24 * (closedForm k : ℤ) = n * (n - 1) * (n - 2) * (n - 3) := by
  rw [closedForm, h, choose_four_cast]

/-! ## The set is exactly the range of `closedForm` -/

/-- Every `closedForm k` lies in A145920. -/
theorem closedForm_mem (k : ℕ) : InA145920 (closedForm k) := by
  refine ⟨?_, ⟨_, rfl⟩⟩
  rw [isPentagonal_iff]
  rcases Nat.even_or_odd' k with ⟨g, rfl | rfl⟩
  · -- `k = 2g`, `n = 3g + 2`, root `6j - 1 = 9g² + 3g - 1`, `2j = g(3g+1)`.
    obtain ⟨j, hj⟩ : Even (g * (3 * g + 1)) := by
      rcases Nat.even_or_odd g with h | h
      · exact h.mul_right _
      · apply Even.mul_left
        rcases h with ⟨r, rfl⟩
        exact ⟨3 * r + 2, by ring⟩
    refine ⟨j, ?_⟩
    have hj' : (g : ℤ) * (3 * g + 1) = j + j := by exact_mod_cast hj
    rw [closedForm, show (3 * (2 * g) + 5) / 2 = 3 * g + 2 by omega, choose_four_sq]
    push_cast
    linear_combination (3 * (9 * (g : ℤ) ^ 2 + 3 * g + 6 * j - 2)) * hj'
  · -- `k = 2g + 1`, `n = 3(g+1) + 1`, root `6j - 1 = 9h² - 3h - 1`, `2j = h(3h-1)`.
    obtain ⟨j, hj⟩ : Even ((g + 1) * (3 * g + 2)) := by
      rcases Nat.even_or_odd g with h | h
      · apply Even.mul_left
        rcases h with ⟨r, rfl⟩
        exact ⟨3 * r + 1, by ring⟩
      · apply Even.mul_right
        rcases h with ⟨r, rfl⟩
        exact ⟨r + 1, by ring⟩
    refine ⟨j, ?_⟩
    have hj' : ((g : ℤ) + 1) * (3 * g + 2) = j + j := by exact_mod_cast hj
    rw [closedForm, show (3 * (2 * g + 1) + 5) / 2 = 3 * g + 4 by omega, choose_four_sq]
    push_cast
    linear_combination (3 * (9 * ((g : ℤ) + 1) ^ 2 - 3 * (g + 1) + 6 * j - 2)) * hj'

/-- If `C(n,4)` is pentagonal then it is some `closedForm k`. -/
theorem exists_closedForm_of_mem {m : ℕ} (hm : InA145920 m) : ∃ k, closedForm k = m := by
  obtain ⟨hpent, n, rfl⟩ := hm
  obtain ⟨j, hj⟩ := (isPentagonal_iff _).mp hpent
  rcases Nat.lt_or_ge n 4 with hn | hn
  · refine ⟨0, ?_⟩
    rw [Nat.choose_eq_zero_of_lt hn]
    decide
  obtain ⟨t, rfl | rfl | rfl⟩ : ∃ t, n = 3 * t ∨ n = 3 * t + 1 ∨ n = 3 * t + 2 :=
    ⟨n / 3, by omega⟩
  · -- `3 ∣ n` is impossible: compare the two square roots of `24m+1` modulo `3`.
    exfalso
    have hsq := choose_four_sq (3 * t)
    rw [hj] at hsq
    push_cast at hsq
    have hu : (2 : ℤ) ≤ (t : ℤ) * t - t := by
      have ht : (2 : ℤ) ≤ t := by omega
      nlinarith
    set u : ℤ := (t : ℤ) * t - t with hu_def
    have hroot : (6 * (j : ℤ) - 1) = 9 * u + 1 ∨ (6 * (j : ℤ) - 1) = -(9 * u + 1) := by
      apply sq_eq_sq_iff_eq_or_eq_neg.mp
      rw [hsq, hu_def]
      ring
    rcases hroot with h | h <;> omega
  · -- `n = 3t + 1` with `t ≥ 1`: `k = 2t - 1`.
    refine ⟨2 * (t - 1) + 1, ?_⟩
    rw [closedForm, show (3 * (2 * (t - 1) + 1) + 5) / 2 = 3 * t + 1 by omega]
  · -- `n = 3t + 2`: `k = 2t`.
    refine ⟨2 * t, ?_⟩
    rw [closedForm, show (3 * (2 * t) + 5) / 2 = 3 * t + 2 by omega]

/-- The range of `closedForm` is exactly the set A145920. -/
theorem range_closedForm : Set.range closedForm = Set.ofPred InA145920 := by
  ext m
  constructor
  · rintro ⟨k, rfl⟩
    exact closedForm_mem k
  · intro hm
    exact exists_closedForm_of_mem hm

/-- `closedForm` is strictly increasing. -/
theorem closedForm_strictMono : StrictMono closedForm := by
  refine strictMono_nat_of_lt_succ fun k => ?_
  have hle : (3 * k + 5) / 2 ≤ (3 * (k + 1) + 5) / 2 - 1 := by omega
  have hsucc : (3 * (k + 1) + 5) / 2 = ((3 * (k + 1) + 5) / 2 - 1) + 1 := by omega
  have hthree : 3 ≤ (3 * (k + 1) + 5) / 2 - 1 := by omega
  unfold closedForm
  calc ((3 * k + 5) / 2).choose 4 ≤ ((3 * (k + 1) + 5) / 2 - 1).choose 4 :=
        Nat.choose_le_choose 4 hle
    _ < ((3 * (k + 1) + 5) / 2 - 1).choose 4 + ((3 * (k + 1) + 5) / 2 - 1).choose 3 :=
        Nat.lt_add_of_pos_right (Nat.choose_pos hthree)
    _ = ((3 * (k + 1) + 5) / 2).choose 4 := by
        rw [hsucc, Nat.choose_succ_succ', Nat.add_comm (Nat.choose _ 3)]
        simp only [Nat.add_sub_cancel]

/-- **Load-bearing bridge.** The increasing enumeration of A145920 is
`closedForm`: `Nat.nth InA145920 k = C(⌊(3k+5)/2⌋, 4)`. -/
theorem nth_eq_closedForm : Nat.nth InA145920 = closedForm := by
  have hinf : (Set.ofPred InA145920).Infinite := by
    rw [← range_closedForm]
    exact Set.infinite_range_of_injective closedForm_strictMono.injective
  refine (StrictMono.range_inj (Nat.nth_strictMono hinf) closedForm_strictMono).mp ?_
  rw [Nat.range_nth_of_infinite hinf, range_closedForm]

/-- `a (k+1) = C(⌊(3k+5)/2⌋, 4)` (the entry's `a(n)` with offset 1). -/
theorem a_succ (k : ℕ) : a (k + 1) = closedForm k := by
  rw [a, Nat.add_sub_cancel, nth_eq_closedForm]

-- Ground truth: the definition `a` (offset 1) reproduces the first DATA terms.
example : [a 1, a 2, a 3, a 4, a 5, a 6, a 7, a 8, a 9, a 10, a 11, a 12] =
    [0, 1, 5, 35, 70, 210, 330, 715, 1001, 1820, 2380, 3876] := by
  simp only [a_succ]
  decide

/-! ## The recurrence -/

/-- The order-9 recurrence for the explicit enumeration, in `ℤ`. -/
theorem closedForm_rec (k : ℕ) :
    (closedForm (k + 9) : ℤ) = closedForm (k + 8) + 4 * closedForm (k + 7)
      - 4 * closedForm (k + 6) - 6 * closedForm (k + 5) + 6 * closedForm (k + 4)
      + 4 * closedForm (k + 3) - 4 * closedForm (k + 2) - closedForm (k + 1)
      + closedForm k := by
  suffices h24 : 24 * (closedForm (k + 9) : ℤ) = 24 * (closedForm (k + 8) + 4 * closedForm (k + 7)
      - 4 * closedForm (k + 6) - 6 * closedForm (k + 5) + 6 * closedForm (k + 4)
      + 4 * closedForm (k + 3) - 4 * closedForm (k + 2) - closedForm (k + 1)
      + closedForm k) from mul_left_cancel₀ (by norm_num) h24
  rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
  · have h0 := closedForm_cast (k := 2 * m) (n := 3 * m + 2) (by omega)
    have h1 := closedForm_cast (k := 2 * m + 1) (n := 3 * m + 4) (by omega)
    have h2 := closedForm_cast (k := 2 * m + 2) (n := 3 * m + 5) (by omega)
    have h3 := closedForm_cast (k := 2 * m + 3) (n := 3 * m + 7) (by omega)
    have h4 := closedForm_cast (k := 2 * m + 4) (n := 3 * m + 8) (by omega)
    have h5 := closedForm_cast (k := 2 * m + 5) (n := 3 * m + 10) (by omega)
    have h6 := closedForm_cast (k := 2 * m + 6) (n := 3 * m + 11) (by omega)
    have h7 := closedForm_cast (k := 2 * m + 7) (n := 3 * m + 13) (by omega)
    have h8 := closedForm_cast (k := 2 * m + 8) (n := 3 * m + 14) (by omega)
    have h9 := closedForm_cast (k := 2 * m + 9) (n := 3 * m + 16) (by omega)
    push_cast at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
    linear_combination h9 - h8 - 4 * h7 + 4 * h6 + 6 * h5 - 6 * h4 - 4 * h3 + 4 * h2 + h1 - h0
  · have h0 := closedForm_cast (k := 2 * m + 1) (n := 3 * m + 4) (by omega)
    have h1 := closedForm_cast (k := 2 * m + 1 + 1) (n := 3 * m + 5) (by omega)
    have h2 := closedForm_cast (k := 2 * m + 1 + 2) (n := 3 * m + 7) (by omega)
    have h3 := closedForm_cast (k := 2 * m + 1 + 3) (n := 3 * m + 8) (by omega)
    have h4 := closedForm_cast (k := 2 * m + 1 + 4) (n := 3 * m + 10) (by omega)
    have h5 := closedForm_cast (k := 2 * m + 1 + 5) (n := 3 * m + 11) (by omega)
    have h6 := closedForm_cast (k := 2 * m + 1 + 6) (n := 3 * m + 13) (by omega)
    have h7 := closedForm_cast (k := 2 * m + 1 + 7) (n := 3 * m + 14) (by omega)
    have h8 := closedForm_cast (k := 2 * m + 1 + 8) (n := 3 * m + 16) (by omega)
    have h9 := closedForm_cast (k := 2 * m + 1 + 9) (n := 3 * m + 17) (by omega)
    push_cast at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
    linear_combination h9 - h8 - 4 * h7 + 4 * h6 + 6 * h5 - 6 * h4 - 4 * h3 + 4 * h2 + h1 - h0

/-- **Mathar's recurrence conjecture (A145920, R. J. Mathar, Oct 29 2008).**

Verbatim: "Conjecture: a(n) = a(n-1) + 4a(n-2) - 4a(n-3) - 6a(n-4) + 6a(n-5)
+ 4a(n-6) - 4a(n-7) - a(n-8) + a(n-9)."

Stated for every `n ≥ 10` (written `n + 10` to avoid truncated subtraction), so
that all nine earlier indices are `≥ 1` and lie in the entry's offset; `a` is the
increasing enumeration of the numbers that are both pentagonal and a `C(n,4)`. -/
theorem mathar_recurrence (n : ℕ) :
    (a (n + 10) : ℤ) = a (n + 9) + 4 * a (n + 8) - 4 * a (n + 7) - 6 * a (n + 6)
      + 6 * a (n + 5) + 4 * a (n + 4) - 4 * a (n + 3) - a (n + 2) + a (n + 1) := by
  simp only [a_succ]
  exact closedForm_rec n

/-! ## The generating function -/

/-- Coefficient-level form of the g.f.: the series `Σ_{k ≥ 0} closedForm k · xᵏ`
times `(1+x)^4 (1-x)^5` is the polynomial `x(1 + 4x + 26x² + 19x³ + 26x⁴ + 4x⁵ + x⁶)`. -/
theorem closedForm_series_mul :
    ((1 + X) ^ 4 * (1 - X) ^ 5 : ℤ⟦X⟧) * mk (fun k => (closedForm k : ℤ)) =
      X * (1 + 4 * X + 26 * X ^ 2 + 19 * X ^ 3 + 4 * X ^ 5 + X ^ 6 + 26 * X ^ 4) := by
  set B : ℤ⟦X⟧ := mk (fun k => (closedForm k : ℤ)) with hB
  have hL : ((1 + X) ^ 4 * (1 - X) ^ 5 : ℤ⟦X⟧) * B =
      X ^ 0 * B - X ^ 1 * B - C 4 * (X ^ 2 * B) + C 4 * (X ^ 3 * B) + C 6 * (X ^ 4 * B)
        - C 6 * (X ^ 5 * B) - C 4 * (X ^ 6 * B) + C 4 * (X ^ 7 * B) + X ^ 8 * B
        - X ^ 9 * B := by
    simp only [map_ofNat]
    ring
  have hR : (X * (1 + 4 * X + 26 * X ^ 2 + 19 * X ^ 3 + 4 * X ^ 5 + X ^ 6 + 26 * X ^ 4) :
      ℤ⟦X⟧) = X ^ 1 + C 4 * X ^ 2 + C 26 * X ^ 3 + C 19 * X ^ 4 + C 26 * X ^ 5
        + C 4 * X ^ 6 + X ^ 7 := by
    simp only [map_ofNat]
    ring
  rw [hL, hR]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', coeff_X_pow, hB, coeff_mk]
  rcases Nat.lt_or_ge n 9 with hn | hn
  · interval_cases n <;> decide
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 9 := ⟨n - 9, by omega⟩
    have hrec := closedForm_rec k
    simp only [show 0 ≤ k + 9 by omega, show 1 ≤ k + 9 by omega, show 2 ≤ k + 9 by omega,
      show 3 ≤ k + 9 by omega, show 4 ≤ k + 9 by omega, show 5 ≤ k + 9 by omega,
      show 6 ≤ k + 9 by omega, show 7 ≤ k + 9 by omega, show 8 ≤ k + 9 by omega,
      show 9 ≤ k + 9 by omega, if_true, show k + 9 ≠ 1 by omega, show k + 9 ≠ 2 by omega,
      show k + 9 ≠ 3 by omega, show k + 9 ≠ 4 by omega, show k + 9 ≠ 5 by omega,
      show k + 9 ≠ 6 by omega, show k + 9 ≠ 7 by omega, if_false]
    rw [show k + 9 - 0 = k + 9 by omega, show k + 9 - 1 = k + 8 by omega,
      show k + 9 - 2 = k + 7 by omega, show k + 9 - 3 = k + 6 by omega,
      show k + 9 - 4 = k + 5 by omega, show k + 9 - 5 = k + 4 by omega,
      show k + 9 - 6 = k + 3 by omega, show k + 9 - 7 = k + 2 by omega,
      show k + 9 - 8 = k + 1 by omega, show k + 9 - 9 = k by omega]
    linear_combination hrec

/-- **Mathar's g.f. conjecture (A145920, R. J. Mathar, Oct 29 2008).**

Verbatim: "Conjecture: G.f.: x^2(1 + 4x + 26x^2 + 19x^3 + 4x^5 + x^6 + 26x^4)/((1+x)^4(1-x)^5)."

With the entry's offset 1 the g.f. is `Σ_{n ≥ 1} a(n) xⁿ = x · Σ_{k ≥ 0} a(k+1) xᵏ`.
The quotient is stated in multiplied-out form over `ℤ⟦X⟧`; since the denominator
`(1+x)^4 (1-x)^5` has constant term `1` it is a unit, so this is equivalent to
the stated quotient. -/
theorem mathar_gf :
    ((1 + X) ^ 4 * (1 - X) ^ 5 : ℤ⟦X⟧) * (X * mk (fun k => (a (k + 1) : ℤ))) =
      X ^ 2 * (1 + 4 * X + 26 * X ^ 2 + 19 * X ^ 3 + 4 * X ^ 5 + X ^ 6 + 26 * X ^ 4) := by
  simp only [a_succ]
  rw [mul_left_comm, closedForm_series_mul]
  ring

end Candidates.A145920CommonValuesPentagonal
