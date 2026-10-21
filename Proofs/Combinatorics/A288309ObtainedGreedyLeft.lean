/-
# A288309 — Kimberling: lengths of the iterates of 00 -> 0010, 1 -> 110

## OEIS source (retrieved 2026-10-21, local `oeis show A288309` and the live
## internal-format entry)

```
NAME:     a(n) = 2*a(n-1) + 2*a(n-2) - 3*a(n-3), where a(0) = 2, a(1) = 4,
          a(2) = 8.
TERMS:    2,4,8,18,40,92,210,484,1112,2562,5896,13580,31266,72004,165800,...
KEYWORDS: nonn,easy
AUTHOR:   _Clark Kimberling_, Jun 09 2017
COMMENT (the conjecture, by the entry author, Jun 09 2017):
  Conjecture: a(n) is the number of letters (0's and 1's) in the n-th
  iteration of the mapping 00->0010, 1->110, starting with 00; see A288306.
PROGRAM (A288306, the defining word):
  w[n_] := StringReplace[w[n - 1], {"00" -> "0010", "1" -> "110"}]
```

The mapping is Mathematica's `StringReplace`: a greedy left-to-right scan that
rewrites a block `00` to `0010`, a letter `1` to `110`, and leaves a lone `0`
(a `0` not followed by `0`) unchanged.

## Status

Triage: open (no proof in the entry or the literature as far as the triage
could tell).  Evidence: direct rewriting for `n = 0..21` (re-checked here with
Python's `re.sub`, which has the same greedy semantics).

## Proof (this file)

Parse a word greedily into tokens `00` (count `P`), lone `0` (count `C`) and
`1` (count `O`); its length is `2P + C + O`.  For words beginning with `00`,
one rewriting pass sends `(P, C, O)` to `(P + C, P + O - C, P + 2O)`: the only
nontrivial coordinate is the lone-zero count, obtained from the auxiliary
identity `lone (0 :: step r) + lone r = pairs r + #1(r) + 1` valid for every
word `r`.  The matrix has characteristic polynomial
`(x - 1)(x^2 - x - 3) = x^3 - 2x^2 - 2x + 3`, whence the recurrence.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A288309ObtainedGreedyLeft

/-! ## Definitions

Letters are `Bool`: `false` is the letter `0` and `true` is the letter `1`. -/

/-- One greedy left-to-right rewriting pass (Mathematica
`StringReplace[w, {"00" -> "0010", "1" -> "110"}]`): a block `00` becomes
`0010`, a letter `1` becomes `110`, a lone `0` (one not followed by `0`)
is left unchanged. -/
def step : List Bool → List Bool
  | [] => []
  | true :: r => true :: true :: false :: step r
  | [false] => [false]
  | false :: true :: r => false :: step (true :: r)
  | false :: false :: r => false :: false :: true :: false :: step r

/-- The iterates `w_0 = 00`, `w_{n+1} = step w_n` (OEIS A288306 is their
limit). -/
def w : ℕ → List Bool
  | 0 => [false, false]
  | n + 1 => step (w n)

/-- The OEIS A288309 sequence, by its defining recurrence:
`a(0) = 2`, `a(1) = 4`, `a(2) = 8`, `a(n) = 2a(n-1) + 2a(n-2) - 3a(n-3)`. -/
def a : ℕ → ℤ
  | 0 => 2
  | 1 => 4
  | 2 => 8
  | n + 3 => 2 * a (n + 2) + 2 * a (n + 1) - 3 * a n

/-- Number of `00` tokens in the greedy left-to-right parse of a word. -/
def pairs : List Bool → ℕ
  | [] => 0
  | true :: r => pairs r
  | [false] => 0
  | false :: true :: r => pairs (true :: r)
  | false :: false :: r => pairs r + 1

/-- Number of lone-`0` tokens (a `0` not followed by `0`) in the greedy
left-to-right parse of a word. -/
def lone : List Bool → ℕ
  | [] => 0
  | true :: r => lone r
  | [false] => 1
  | false :: true :: r => lone (true :: r) + 1
  | false :: false :: r => lone r

/-! ### Ground truth -/

example : w 1 = [false, false, true, false] := rfl
example : w 2 = [false, false, true, false, true, true, false, false] := rfl

/-- The first 86 letters of `w 5` are the 86 listed terms of A288306. -/
example : ((w 5).map fun b => if b then 1 else 0).take 86 =
    [0,0,1,0,1,1,0,0,1,1,0,1,1,0,0,0,1,0,1,1,0,1,1,0,0,1,1,0,1,1,0,0,0,1,0,0,
     1,1,0,0,1,1,0,1,1,0,0,1,1,0,1,1,0,0,0,1,0,1,1,0,1,1,0,0,1,1,0,1,1,0,0,0,
     1,0,0,1,1,0,0,0,1,0,1,1,0,1] := by decide

example : (List.range 8).map a = [2, 4, 8, 18, 40, 92, 210, 484] := by decide

example : (List.range 7).map (fun n => (w n).length) = [2, 4, 8, 18, 40, 92, 210] := rfl

example : pairs [false, false, true, false] = 1 ∧ lone [false, false, true, false] = 1 := by
  decide

/-! ## Token-count bookkeeping -/

/-- The length of a word is `2 · #00 + #lone 0 + #1` for its greedy parse. -/
theorem length_eq_pairs_lone_count : ∀ r : List Bool,
    r.length = 2 * pairs r + lone r + r.count true
  | [] => rfl
  | true :: r => by
    have ih := length_eq_pairs_lone_count r
    simp only [List.length_cons, pairs, lone, List.count_cons_self]
    omega
  | [false] => rfl
  | false :: true :: r => by
    have ih := length_eq_pairs_lone_count (true :: r)
    simp only [List.length_cons, pairs, lone, List.count_cons_self,
      List.count_cons_of_ne Bool.false_ne_true] at ih ⊢
    omega
  | false :: false :: r => by
    have ih := length_eq_pairs_lone_count r
    simp only [List.length_cons, pairs, lone,
      List.count_cons_of_ne Bool.false_ne_true]
    omega

/-- One pass sends a word with parse counts `(P, C, O)` to a word of length
`4P + C + 3O`. -/
theorem length_step : ∀ r : List Bool,
    (step r).length = 4 * pairs r + lone r + 3 * r.count true
  | [] => rfl
  | true :: r => by
    have ih := length_step r
    simp only [step, List.length_cons, pairs, lone, List.count_cons_self]
    omega
  | [false] => rfl
  | false :: true :: r => by
    have ih := length_step (true :: r)
    simp only [step, List.length_cons, pairs, lone, List.count_cons_self,
      List.count_cons_of_ne Bool.false_ne_true] at ih ⊢
    omega
  | false :: false :: r => by
    have ih := length_step r
    simp only [step, List.length_cons, pairs, lone,
      List.count_cons_of_ne Bool.false_ne_true]
    omega

/-- One pass sends a word with parse counts `(P, C, O)` to a word with
`P + 2O` letters `1`. -/
theorem count_true_step : ∀ r : List Bool,
    (step r).count true = pairs r + 2 * r.count true
  | [] => rfl
  | true :: r => by
    have ih := count_true_step r
    simp only [step, pairs, List.count_cons_self,
      List.count_cons_of_ne Bool.false_ne_true]
    omega
  | [false] => rfl
  | false :: true :: r => by
    have ih := count_true_step (true :: r)
    simp only [step, pairs, List.count_cons_self,
      List.count_cons_of_ne Bool.false_ne_true] at ih ⊢
    omega
  | false :: false :: r => by
    have ih := count_true_step r
    simp only [step, pairs, List.count_cons_self,
      List.count_cons_of_ne Bool.false_ne_true]
    omega

/-- The key identity: the number of lone zeros in `0 :: step r` (the image of
`r` preceded by the trailing `0` of an earlier image) satisfies
`lone (0 :: step r) + lone r = pairs r + #1(r) + 1`, for every word `r`. -/
theorem lone_false_cons_step_add_lone : ∀ r : List Bool,
    lone (false :: step r) + lone r = pairs r + r.count true + 1
  | [] => rfl
  | true :: r => by
    have ih := lone_false_cons_step_add_lone r
    simp only [step, lone, pairs, List.count_cons_self]
    omega
  | [false] => rfl
  | false :: true :: r => by
    have ih := lone_false_cons_step_add_lone r
    simp only [step, lone, pairs, List.count_cons_self,
      List.count_cons_of_ne Bool.false_ne_true]
    omega
  | false :: false :: r => by
    have ih := lone_false_cons_step_add_lone r
    simp only [step, lone, pairs, List.count_cons_of_ne Bool.false_ne_true]
    omega

/-- For a word beginning with `00`, one pass has
`lone (step w) + lone w = pairs w + #1(w)`. -/
theorem lone_step_add_lone (s : List Bool) :
    lone (step (false :: false :: s)) + lone (false :: false :: s) =
      pairs (false :: false :: s) + (false :: false :: s).count true := by
  have key := lone_false_cons_step_add_lone s
  simp only [step, lone, pairs, List.count_cons_of_ne Bool.false_ne_true]
  omega

/-- For a word beginning with `00`, one pass has
`pairs (step w) = pairs w + lone w`. -/
theorem pairs_step (s : List Bool) :
    pairs (step (false :: false :: s)) =
      pairs (false :: false :: s) + lone (false :: false :: s) := by
  have hlen := length_eq_pairs_lone_count (step (false :: false :: s))
  have hstep := length_step (false :: false :: s)
  have hone := count_true_step (false :: false :: s)
  have hlone := lone_step_add_lone s
  omega

/-- Every iterate begins with `00`. -/
theorem exists_w_eq (n : ℕ) : ∃ s, w n = false :: false :: s := by
  induction n with
  | zero => exact ⟨[], rfl⟩
  | succ n ih =>
    obtain ⟨s, hs⟩ := ih
    exact ⟨true :: false :: step s, by simp only [w, hs, step]⟩

/-- The parse-count recurrences along the iterates. -/
theorem counts_succ (n : ℕ) :
    pairs (w (n + 1)) = pairs (w n) + lone (w n) ∧
    lone (w (n + 1)) + lone (w n) = pairs (w n) + (w n).count true ∧
    (w (n + 1)).count true = pairs (w n) + 2 * (w n).count true := by
  obtain ⟨s, hs⟩ := exists_w_eq n
  simp only [w, hs]
  exact ⟨pairs_step s, lone_step_add_lone s, count_true_step _⟩

/-! ## The conjecture -/

/-- **Kimberling's conjecture (A288309, Clark Kimberling, Jun 09 2017).**

Verbatim: "Conjecture: a(n) is the number of letters (0's and 1's) in the
n-th iteration of the mapping 00->0010, 1->110, starting with 00; see
A288306."  Here `w n` is the `n`-th iterate (`w 0 = 00`) of the greedy
left-to-right rewriting `step`, and `a` is the entry's defining recurrence. -/
theorem length_w_eq_a (n : ℕ) : ((w n).length : ℤ) = a n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | n + 3, ih =>
      have h0 := ih n (by omega)
      have h1 := ih (n + 1) (by omega)
      have h2 := ih (n + 2) (by omega)
      obtain ⟨p0, c0, o0⟩ := counts_succ n
      obtain ⟨p1, c1, o1⟩ := counts_succ (n + 1)
      obtain ⟨p2, c2, o2⟩ := counts_succ (n + 2)
      simp only [show n + 1 + 1 = n + 2 from rfl, show n + 2 + 1 = n + 3 from rfl]
        at p1 c1 o1 p2 c2 o2
      have l0 := length_eq_pairs_lone_count (w n)
      have l1 := length_eq_pairs_lone_count (w (n + 1))
      have l2 := length_eq_pairs_lone_count (w (n + 2))
      have l3 := length_eq_pairs_lone_count (w (n + 3))
      rw [a, ← h0, ← h1, ← h2]
      push_cast [l0, l1, l2, l3]
      -- Cayley–Hamilton for the count matrix `(P, C, O) ↦ (P + C, P + O - C, P + 2O)`,
      -- whose characteristic polynomial is `x^3 - 2x^2 - 2x + 3`.
      omega

end Candidates.A288309ObtainedGreedyLeft
