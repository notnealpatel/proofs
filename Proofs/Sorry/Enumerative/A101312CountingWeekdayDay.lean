/-
# A101312 — counting "weekday W on day d" repeats the Friday-the-13th pattern

## OEIS source (`oeis show A101312`, retrieved 2026-10-21)

```
NAME:     Number of "Friday the 13ths" in year n (starting at 1901).
TERMS:    2,1,3,1,2,2,2,2,1,1,2,2,1,3,1,1,2,2,1,2,1,2,2,1,3,1,1,3,2,1,3,1,2,
          2,2,2,1,1,2,2,1,3,1,1,2,2,1,2,1,2,2,1,3,1,1,3,2,1,3,1,2,2,2,2,1,1,
          2,2,1,3,1,1,2,2,1,2,1,2,2,1,3,1,1,3,2,1,3,1,2,2,2,2,1,1,2,2,1,3,1,
          1,2,2,1,2,1
COMMENT:  This sequence is basically periodic with period 28 [example:
          a(1901) = a(1929) = a(1957)], with "jumps" when it passes a
          non-leap-year century such as 2100 [all centuries which are not
          multiples of 400].
COMMENT:  At these points [for example, a(2101)], the sequence simply "jumps"
          to a different point in the same pattern, "dropping back" 12
          entries [or equivalently, "skipping ahead" 16 entries], but still
          continuing with the same repeating [period 28] pattern.
COMMENT (the conjecture, unattributed in the entry; the entry is by
         Adam M. Kalman, Dec 22 2004, per the live entry AUTHOR line):
          Conjecture: The same basic repeating pattern results if we seek the
          number of "Sunday the 22nds" or "Wednesday the 8ths" or anything
          else similar, with the only difference being that the sequence
          starts at a different point in the repeating pattern.
COMMENT:  Periodic with period 400. (Because the number of days in 400 years
          is 400*365 + 97 = 146097, which happens to be divisible by 7.)
          - Pontus von Brömssen, Sep 09 2021
PROGRAM (Haskell, Reinhard Zumkeller, May 16 2011): Zeller's congruence.
```

## Literature status (triage)

Unclear: the triage found no proof in the entry or the literature; it notes
the claim is vague as stated, that for `d ≤ 28` the count depends only on
`(W - d) mod 7`, and that an exact year shift across the whole 400-year
Gregorian cycle is impossible.

## What this module proves

* `count_eq_count_thirteen`: for `d ≤ 28` the "weekday `W` on day `d`" count
  equals a "weekday `W'` on the 13th" count, `W' = (W + 41 - d) % 7`.
* `a101312_conjecture` (the conjecture, in its "basic repeating pattern"
  reading): for every weekday `W` and every day `d ≤ 28`, over the whole
  Julian-regular stretch 1901–2099 the count sequence is the 28-year pattern
  `P i = a (1901 + i)` started at some point `s < 28`.
* `exists_global_shift_iff` (the literal "exact shift" reading is false):
  a single year shift `s` with `count W d n = a (n + s)` for all `n ≥ 1901`
  exists iff `W = d % 7`, i.e. iff the count is literally the Friday-the-13th
  count.  The obstruction is the 400-year total: 688 Friday-the-13ths but
  684, 687, 685, 685, 687, 684 for Saturday, …, Thursday.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace Candidates.A101312CountingWeekdayDay

/-! ## Definition layer: Zeller's congruence (Gregorian calendar)

Mirrors the entry's Haskell program (Zeller's congruence).  Weekdays are
numbered `0 = Saturday, 1 = Sunday, …, 6 = Friday`; months `1, …, 12`. -/

/-- Zeller's adjusted year: January and February count as months of the
previous year.  (Only meaningful for `1 ≤ y`; the sequence starts at 1901.) -/
def adjYear (y m : ℕ) : ℕ := if m ≤ 2 then y - 1 else y

/-- Zeller's adjusted month: January and February are months 13 and 14. -/
def adjMonth (m : ℕ) : ℕ := if m ≤ 2 then m + 12 else m

/-- The day-independent part of Zeller's congruence for month `m` of year `y`:
`⌊13 (M + 1) / 5⌋ + K + ⌊K / 4⌋ + ⌊J / 4⌋ + 5 J` with `Y = 100 J + K` the
adjusted year and `M` the adjusted month. -/
def offset (y m : ℕ) : ℕ :=
  13 * (adjMonth m + 1) / 5 + adjYear y m % 100 + adjYear y m % 100 / 4
    + adjYear y m / 100 / 4 + 5 * (adjYear y m / 100)

/-- Gregorian weekday of day `d` of month `m` of year `y`
(`0 = Saturday, …, 6 = Friday`), by Zeller's congruence. -/
def weekday (y m d : ℕ) : ℕ := (d + offset y m) % 7

/-- Number of months of year `y` whose `d`-th day falls on weekday `W`. -/
def count (W d y : ℕ) : ℕ :=
  ((Finset.range 12).filter (fun i => weekday y (i + 1) d = W)).card

/-- A101312: number of Friday-the-13ths in year `n`. -/
def a (n : ℕ) : ℕ := count 6 13 n

/-! ## Ground truth -/

-- 2026-10-21 is a Wednesday; 2000-01-01 was a Saturday; 1901-01-01 a Tuesday.
example : weekday 2026 10 21 = 4 := by decide
example : weekday 2000 1 1 = 0 := by decide
example : weekday 1901 1 1 = 3 := by decide

-- The 105 listed terms a(1901), …, a(2005).
example : (List.range 105).map (fun i => a (1901 + i)) =
    [2,1,3,1,2,2,2,2,1,1,2,2,1,3,1,1,2,2,1,2,1,2,2,1,3,1,1,3,2,1,3,1,2,2,2,2,1,
     1,2,2,1,3,1,1,2,2,1,2,1,2,2,1,3,1,1,3,2,1,3,1,2,2,2,2,1,1,2,2,1,3,1,1,2,2,
     1,2,1,2,2,1,3,1,1,3,2,1,3,1,2,2,2,2,1,1,2,2,1,3,1,1,2,2,1,2,1] := by
  decide

/-! ## Reduction to the 13th -/

/-- For `W < 7` and `d ≤ 28`, the "weekday `W` on day `d`" count equals the
"weekday `(W + 41 - d) % 7` on the 13th" count, in every year. -/
theorem count_eq_count_thirteen (W d y : ℕ) (hW : W < 7) (hd : d ≤ 28) :
    count W d y = count ((W + 41 - d) % 7) 13 y := by
  unfold count weekday
  congr 1
  apply Finset.filter_congr
  intro i _
  omega

/-! ## Gregorian 400-year periodicity -/

/-- Moving 400 years ahead adds 21 to Zeller's offset (for `1 ≤ y`). -/
theorem offset_add_400 (y m : ℕ) (hy : 1 ≤ y) :
    offset (y + 400) m = offset y m + 21 := by
  unfold offset adjYear
  split_ifs <;> omega

/-- Counts are 400-periodic in the year (for `1 ≤ y`). -/
theorem count_add_400 (W d y : ℕ) (hy : 1 ≤ y) :
    count W d (y + 400) = count W d y := by
  unfold count weekday
  congr 1
  apply Finset.filter_congr
  intro i _
  rw [offset_add_400 y (i + 1) hy]
  omega

/-- Shifting a 400-periodic function does not change its sum over 400
consecutive arguments. -/
theorem sum_range_400_add (g : ℕ → ℕ) (hg : ∀ k, g (k + 400) = g k) (s : ℕ) :
    ∑ k ∈ Finset.range 400, g (k + s) = ∑ k ∈ Finset.range 400, g k := by
  induction s with
  | zero => simp
  | succ s ih =>
    have h1 := Finset.sum_range_succ (fun k => g (k + s)) 400
    have h2 := Finset.sum_range_succ' (fun k => g (k + s)) 400
    have h3 : g (400 + s) = g (0 + s) := by
      rw [Nat.add_comm 400 s, hg, Nat.zero_add]
    have h4 : ∑ k ∈ Finset.range 400, g (k + 1 + s) =
        ∑ k ∈ Finset.range 400, g (k + (s + 1)) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Nat.add_assoc, Nat.add_comm 1 s]
    omega

/-- 400-year totals of "weekday `W` on the 13th", starting in 1901:
688 Fridays, 687 Sundays/Wednesdays, 685 Mondays/Tuesdays,
684 Saturdays/Thursdays. -/
theorem sum_count_thirteen :
    ∀ W ∈ Finset.range 7, ∑ n ∈ Finset.range 400, count W 13 (1901 + n) =
      if W = 6 then 688 else if W = 1 ∨ W = 4 then 687
      else if W = 2 ∨ W = 3 then 685 else 684 := by
  decide +kernel

/-! ## The conjecture: the same 28-year pattern, started elsewhere -/

/-- The start point in the 28-year pattern for "weekday `W` on the 13th"
over 1901–2099 (each 4-year block moves weekdays by `1461 ≡ 5 (mod 7)`). -/
def shiftOf (W : ℕ) : ℕ := 4 * (3 * (6 - W) % 7)

/-- Over 1901–2099, "weekday `W` on the 13th" is the 28-year Friday-the-13th
pattern started at `shiftOf W`. -/
theorem count_thirteen_window :
    ∀ W ∈ Finset.range 7, ∀ k ∈ Finset.range 199,
      count W 13 (1901 + k) = a (1901 + (k + shiftOf W) % 28) := by
  decide +kernel

/-- **A101312 conjecture, "basic repeating pattern" reading.**

Verbatim: "Conjecture: The same basic repeating pattern results if we seek the
number of "Sunday the 22nds" or "Wednesday the 8ths" or anything else similar,
with the only difference being that the sequence starts at a different point
in the repeating pattern."

Formal reading: the basic repeating pattern is the 28-year block
`P i = a (1901 + i)`, `i < 28`, which `a` follows over the Julian-regular
stretch 1901–2099.  For every weekday `W < 7` (`0 = Saturday, …, 6 = Friday`)
and every day `d ≤ 28` (so that every month has a `d`-th day; the junk day
`d = 0` is harmlessly included), there is a
start point `s < 28` such that the number of months of year `n` whose `d`-th
day is a `W` equals `P ((n - 1901 + s) % 28)` for all `1901 ≤ n ≤ 2099`.
(Across the non-leap century 2100 the pattern jumps, for every `(W, d)` as for
`a` itself; an exact global shift is refuted in `exists_global_shift_iff`.) -/
theorem a101312_conjecture (W d : ℕ) (hW : W < 7) (hd : d ≤ 28) :
    ∃ s < 28, ∀ n, 1901 ≤ n → n ≤ 2099 →
      count W d n = a (1901 + (n - 1901 + s) % 28) := by
  have hW' : (W + 41 - d) % 7 ∈ Finset.range 7 := by
    rw [Finset.mem_range]
    omega
  refine ⟨shiftOf ((W + 41 - d) % 7), ?_, ?_⟩
  · unfold shiftOf
    omega
  · intro n hn1 hn2
    have hk : n - 1901 ∈ Finset.range 199 := by
      rw [Finset.mem_range]
      omega
    have hwin := count_thirteen_window _ hW' (n - 1901) hk
    rw [Nat.add_sub_cancel' hn1] at hwin
    rw [count_eq_count_thirteen W d n hW hd]
    exact hwin

/-! ## The literal "exact shift" reading is false -/

/-- **Refutation of the exact-shift reading.**  For a weekday `W < 7` and a day
`d ≤ 28` (the junk day `d = 0` is harmlessly included), the "weekday `W` on
day `d`" count sequence is an exact year
shift of A101312 on all years `n ≥ 1901` iff `W = d % 7`, in which case it is
A101312 itself (shift `0`).  So e.g. "Sunday the 22nds" (`W = 1`, `d = 22`,
`22 % 7 = 1`) coincide year by year with Friday-the-13ths, while
"Wednesday the 8ths" (`W = 4`, `d = 8`) are not any exact shift: over 400
years there are 687 of them against 688 Friday-the-13ths. -/
theorem exists_global_shift_iff (W d : ℕ) (hW : W < 7) (hd : d ≤ 28) :
    (∃ s, ∀ n, 1901 ≤ n → count W d n = a (n + s)) ↔ W = d % 7 := by
  have hred : ∀ n, count W d n = count ((W + 41 - d) % 7) 13 n :=
    fun n => count_eq_count_thirteen W d n hW hd
  constructor
  · rintro ⟨s, hs⟩
    have hper : ∀ k, a (1901 + (k + 400)) = a (1901 + k) := by
      intro k
      rw [← Nat.add_assoc]
      exact count_add_400 6 13 (1901 + k) (by omega)
    have hsum : ∑ n ∈ Finset.range 400, count W d (1901 + n) = 688 := by
      calc ∑ n ∈ Finset.range 400, count W d (1901 + n)
          = ∑ n ∈ Finset.range 400, a (1901 + (n + s)) := by
            apply Finset.sum_congr rfl
            intro n _
            rw [hs (1901 + n) (by omega), Nat.add_assoc]
        _ = ∑ n ∈ Finset.range 400, a (1901 + n) :=
            sum_range_400_add (fun k => a (1901 + k)) hper s
        _ = 688 := by
            have h6 := sum_count_thirteen 6 (by simp)
            simpa [a] using h6
    have hW' : (W + 41 - d) % 7 ∈ Finset.range 7 := by
      rw [Finset.mem_range]
      omega
    have htot := sum_count_thirteen _ hW'
    simp_rw [hred] at hsum
    rw [hsum] at htot
    have h6 : (W + 41 - d) % 7 = 6 := by
      split_ifs at htot <;> omega
    omega
  · intro hWd
    refine ⟨0, fun n _ => ?_⟩
    have h6 : (W + 41 - d) % 7 = 6 := by omega
    rw [hred n, h6, Nat.add_zero]
    rfl

/-! ## Sanity layer -/

-- Satisfiability of the hypotheses: "Wednesday the 8ths" (`W = 4`, `d = 8`).
example : ∃ s < 28, ∀ n, 1901 ≤ n → n ≤ 2099 →
    count 4 8 n = a (1901 + (n - 1901 + s) % 28) :=
  a101312_conjecture 4 8 (by norm_num) (by norm_num)

-- "Sunday the 22nds" coincide with Friday-the-13ths; "Wednesday the 8ths" are
-- not an exact shift.
example : ∃ s, ∀ n, 1901 ≤ n → count 1 22 n = a (n + s) :=
  (exists_global_shift_iff 1 22 (by norm_num) (by norm_num)).mpr rfl
example : ¬ ∃ s, ∀ n, 1901 ≤ n → count 4 8 n = a (n + s) := by
  rw [exists_global_shift_iff 4 8 (by norm_num) (by norm_num)]
  decide

-- The window is not vacuous: a non-Friday case genuinely needs `s ≠ 0`
-- ("Wednesday the 8ths" differ from Friday-the-13ths in 1901).
example : count 4 8 1901 ≠ a 1901 := by decide

end Candidates.A101312CountingWeekdayDay
