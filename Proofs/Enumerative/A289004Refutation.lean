/-
# A289004 — Kimberling: iterate lengths of `00->0010, 01->001, 10->010` (refuted)

## OEIS source (retrieved 2026-10-21 with `oeis show A289004`, `oeis show
## A289001`, and the live entry https://oeis.org/A289004)

```
NAME:     a(n) = 2*a(n-1) - a(n-2) + 2*a(n-4) - a(n-5) + a(n-7) - a(n-8)
          - a(n-10) for n >= 10, where a(0) = 2, a(1) = 4, a(2) = 7,
          a(3) = 11, a(4) = 18, a(5) = 31, a(6) = 52, a(7) = 89,
          a(9) = 151, a(9) = 257.
OFFSET:   0
TERMS:    2,4,7,11,18,31,52,89,151,257,438,748,1277,2179,3719,6348,10837,
          18499,31579,53908,92027,157099,268182,457812,781531,...
COMMENT:  Conjecture: a(n) is the number of letters (0's and 1's) in the
          n-th iterate of the mapping 00->0010, 01->001, 10->010, starting
          with 00; see A289001.
MATH:     LinearRecurrence[{2, -1, 0, 2, -1, 0, 1, -1, 0, -1},
          {2, 4, 7, 11, 18, 31, 52, 89, 151, 257}, 20]
AUTHOR:   _Clark Kimberling_, Jun 26 2017
```

The NAME line misprints `a(8) = 151` as a second `a(9) = 151`; the
Mathematica and PARI programs and the DATA line fix `a(8) = 151`, which is
what `a` below uses.  The conjecture comment carries no separate signature;
it belongs to the entry's author, Clark Kimberling (Jun 26 2017).  The
companion entry A289001 repeats it ("Conjecture: the number of letters
(0's and 1's) in the n-th iterate of the mapping is given by A289004.")
and fixes the meaning of "iterate" through its Mathematica program:

```
w[n_] := StringReplace[w[n - 1], {"00" -> "0010", "01" -> "001", "10" -> "010"}]
Table[StringLength[w[n]], {n, 0, 20}] (* A289004 *)
```

`StringReplace` scans left to right, replaces non-overlapping matches, tries
the rules in order at each position, and keeps unmatched characters.  No
later comment on either entry retracts or corrects the conjecture.

## Status

This module **refutes** the conjecture.  The iterate lengths agree with the
recurrence for `n = 0, ..., 21` (proved below as
`length_eq_a_of_lt_twentytwo`) and first differ at `n = 22`: the 22nd
iterate has `268184` letters, while `a(22) = 268182`.  (Python check:
`n = 23` gives `457819` against `457812`, `n = 24` gives `781545` against
`781531`; the gap grows.)  The program `Table[..., {n, 0, 20}]` that
generated the conjecture stopped two iterates short of the first failure.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A289004Refutation

/-! ## Definition layer

Letters are `Bool`, with `false` for `0` and `true` for `1`. -/

/-- One application of Mathematica's
`StringReplace[s, {"00" -> "0010", "01" -> "001", "10" -> "010"}]`:
scan left to right; at each position replace the first matching two-letter
pattern and skip past it; otherwise (pattern `11`, or a final single letter)
keep the letter and advance by one. -/
def step : List Bool → List Bool
  | false :: false :: t => false :: false :: true :: false :: step t
  | false :: true :: t => false :: false :: true :: step t
  | true :: false :: t => false :: true :: false :: step t
  | b :: t => b :: step t
  | [] => []

/-- The `n`-th iterate of `step`, starting from the word `00`. -/
def w (n : ℕ) : List Bool := step^[n] [false, false]

/-- A289004 as defined by its NAME line (with `a(8) = 151`):
`a(n) = 2a(n-1) - a(n-2) + 2a(n-4) - a(n-5) + a(n-7) - a(n-8) - a(n-10)`
for `n ≥ 10`. -/
def a : ℕ → ℤ
  | 0 => 2
  | 1 => 4
  | 2 => 7
  | 3 => 11
  | 4 => 18
  | 5 => 31
  | 6 => 52
  | 7 => 89
  | 8 => 151
  | 9 => 257
  | n + 10 => 2 * a (n + 9) - a (n + 8) + 2 * a (n + 6) - a (n + 5)
      + a (n + 3) - a (n + 2) - a n

/-! ## Ground truth -/

-- The first iterates, as printed by the A289001 program
-- (`00`, `0010`, `0010010`, `00100100010`).
example : w 0 = [false, false] := rfl
example : w 1 = [false, false, true, false] := rfl
example : w 2 = [false, false, true, false, false, true, false] := rfl
example : w 3 =
    [false, false, true, false, false, true, false, false, false, true, false] := rfl

-- `step` keeps an unmatched `1` of a pattern `11` and a final single letter.
example : step [true, true, false] = [true, false, true, false] := rfl
example : step [false, false, true] = [false, false, true, false, true] := rfl

-- The recurrence reproduces the DATA line `2, 4, 7, ..., 268182, 457812`.
example : (List.range 24).map a =
    [2, 4, 7, 11, 18, 31, 52, 89, 151, 257, 438, 748, 1277, 2179, 3719, 6348,
      10837, 18499, 31579, 53908, 92027, 157099, 268182, 457812] := by
  decide +kernel

-- The iterate lengths reproduce the first ten listed terms.
example : (List.range 10).map (fun n => (w n).length) =
    [2, 4, 7, 11, 18, 31, 52, 89, 151, 257] := by
  decide +kernel

/-! ## The conjecture and its refutation -/

/-- **Kimberling's conjecture (A289004, Jun 26 2017).**
Verbatim: "Conjecture: a(n) is the number of letters (0's and 1's) in the
n-th iterate of the mapping 00->0010, 01->001, 10->010, starting with 00;
see A289001."  The length is cast to `ℤ`, where `a` takes its values. -/
def Conjecture : Prop :=
  ∀ n : ℕ, ((w n).length : ℤ) = a n

/-- The conjecture holds for `n = 0, ..., 21`, so `n = 22` is the least
counterexample. -/
theorem length_eq_a_of_lt_twentytwo : ∀ n < 22, ((w n).length : ℤ) = a n := by
  decide +kernel

/-- The 22nd iterate has `268184` letters (kernel computation). -/
theorem length_w_twentytwo : (w 22).length = 268184 := by
  decide +kernel

/-- The recurrence gives `a(22) = 268182`, the listed term. -/
theorem a_twentytwo : a 22 = 268182 := by
  decide +kernel

/-- **The conjecture is false**, with counterexample `n = 22`: the 22nd
iterate of `00->0010, 01->001, 10->010` from `00` has `268184` letters, while
`a(22) = 268182`.  It is the least counterexample
(`length_eq_a_of_lt_twentytwo`); the A289001 program tabulates only
`n ≤ 20`. -/
theorem conjecture_false : ¬ Conjecture := by
  intro h
  have h22 := h 22
  rw [length_w_twentytwo, a_twentytwo] at h22
  norm_num at h22

end Candidates.A289004Refutation
