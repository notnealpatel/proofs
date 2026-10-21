/-
# A286062 — Kimberling: lengths of iterates of 00->001, 1->011

## OEIS source (retrieved with `oeis show A286062` and https://oeis.org/A286062, 2026-10-21)

```
NAME:     a(n) = 2*a(n-1) + a(n-2) - a(n-3), where a(0) = 2, a(1) = 3, a(2) = 6.
TERMS:    2,3,6,13,29,65,146,328,737,1656,3721,8361,18787,42214,94854,...
FORMULA:  G.f.: (2 - x - 2*x^2)/(1 - 2*x - x^2 + x^3).
MATHEMATICA: LinearRecurrence[{2, 1, -1}, {2, 3, 6}, 40]
COMMENT (the conjecture; no separate signature, entry by Clark Kimberling,
         Jun 05 2017):
  Conjecture:  a(n) is the number of letters (0's and 1's) in the n-th
  iteration of the mapping 00->001, 1->011, starting with 00; see A286939.
```

## Status

Triage: open (no proof in the entry or the literature found).  The mapping is
read with Mathematica `StringReplace` semantics: scan left to right, at each
position try `00 -> 001` first, then `1 -> 011`; a `0` not followed by `0` is
left unchanged.  (A strict parse into the blocks `00` and `1` fails at the
third iterate, so the lone-`0` convention is load-bearing.)

## Result

Proved here (`length_iterate_step`).  From the first iterate on, every word
is a concatenation of the blocks `001`, `01`, `1`, and the rewrite maps
`001 ↦ 001·01·1`, `01 ↦ 001·1`, `1 ↦ 01·1`.  The block-count matrix has
characteristic polynomial `x^3 - 2x^2 - x + 1`, which gives the recurrence.

Encoding: `false` is the letter `0`, `true` is the letter `1`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A286062RewriteBinaryWord

/-! ## Definitions -/

/-- One leftmost-first rewriting pass with the rules `00 -> 001` and `1 -> 011`
(tried in that order), leaving a `0` that is not followed by `0` unchanged.
Letters: `false = 0`, `true = 1`. -/
def step : List Bool → List Bool
  | [] => []
  | false :: false :: t => [false, false, true] ++ step t
  | true :: t => [false, true, true] ++ step t
  | false :: t => false :: step t

/-- The sequence A286062: `a 0 = 2`, `a 1 = 3`, `a 2 = 6`,
`a (n + 3) = 2 a (n + 2) + a (n + 1) - a n` (valued in `ℤ`, so the subtraction
is honest). -/
def a : ℕ → ℤ
  | 0 => 2
  | 1 => 3
  | 2 => 6
  | n + 3 => 2 * a (n + 2) + a (n + 1) - a n

/-! ## Ground truth -/

example : step [false, false] = [false, false, true] := rfl
example : step^[2] [false, false] = [false, false, true, false, true, true] := rfl
-- third iterate `0010110011011`: the lone `0` before `011` is kept
example : step^[3] [false, false] =
    [false, false, true, false, true, true, false, false, true, true, false, true, true] := rfl
example : [a 0, a 1, a 2, a 3, a 4, a 5, a 6, a 7, a 8, a 9] =
    [2, 3, 6, 13, 29, 65, 146, 328, 737, 1656] := by decide
example : (List.range 8).map (fun n => (step^[n] [false, false]).length) =
    [2, 3, 6, 13, 29, 65, 146, 328] := by decide +kernel

/-! ## Block decomposition -/

/-- The three blocks of the iterates: `P = 001`, `Q = 01`, `R = 1`. -/
inductive Tok
  | P
  | Q
  | R
  deriving DecidableEq

/-- The binary word spelled by a block. -/
def Tok.word : Tok → List Bool
  | .P => [false, false, true]
  | .Q => [false, true]
  | .R => [true]

/-- The block sequence of the image of a block under `step`. -/
def Tok.next : Tok → List Tok
  | .P => [.P, .Q, .R]
  | .Q => [.P, .R]
  | .R => [.Q, .R]

/-- The binary word spelled by a block sequence. -/
def render (ts : List Tok) : List Bool := ts.flatMap Tok.word

/-- One block is rewritten independently of what follows it. -/
theorem step_word_append (τ : Tok) (rest : List Bool) :
    step (τ.word ++ rest) = render τ.next ++ step rest := by
  cases τ <;> rfl

/-- `step` acts on rendered block sequences by substituting `Tok.next`. -/
theorem step_render (ts : List Tok) :
    step (render ts) = render (ts.flatMap Tok.next) := by
  induction ts with
  | nil => rfl
  | cons τ ts ih =>
    simp only [render, List.flatMap_cons, List.flatMap_append] at ih ⊢
    rw [step_word_append, ih]
    rfl

/-- The block-substitution map. -/
def subst (ts : List Tok) : List Tok := ts.flatMap Tok.next

/-- The `(n+1)`-st iterate is the rendering of `subst^[n] [P]`. -/
theorem iterate_succ_eq_render (n : ℕ) :
    step^[n + 1] [false, false] = render (subst^[n] [Tok.P]) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, step_render, Function.iterate_succ_apply']
    rfl

/-! ## Block counts -/

/-- The length of a rendered block sequence is `3 #P + 2 #Q + #R`. -/
theorem length_render (ts : List Tok) :
    (render ts).length = 3 * ts.count .P + 2 * ts.count .Q + ts.count .R := by
  induction ts with
  | nil => rfl
  | cons τ ts ih =>
    simp only [render, List.flatMap_cons, List.length_append] at ih ⊢
    cases τ <;>
      simp only [Tok.word, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, ih,
        List.count_cons_self, ne_eq, reduceCtorEq, not_false_eq_true, List.count_cons_of_ne] <;>
      omega

/-- Block counts after substitution: `#P' = #P + #Q`. -/
theorem count_P_subst (ts : List Tok) :
    (subst ts).count .P = ts.count .P + ts.count .Q := by
  induction ts with
  | nil => rfl
  | cons τ ts ih =>
    simp only [subst, List.flatMap_cons, List.count_append] at ih ⊢
    cases τ <;>
      simp only [Tok.next, List.count_cons_self, ne_eq, reduceCtorEq, not_false_eq_true,
        List.count_cons_of_ne, List.count_nil, ih] <;>
      omega

/-- Block counts after substitution: `#Q' = #P + #R`. -/
theorem count_Q_subst (ts : List Tok) :
    (subst ts).count .Q = ts.count .P + ts.count .R := by
  induction ts with
  | nil => rfl
  | cons τ ts ih =>
    simp only [subst, List.flatMap_cons, List.count_append] at ih ⊢
    cases τ <;>
      simp only [Tok.next, List.count_cons_self, ne_eq, reduceCtorEq, not_false_eq_true,
        List.count_cons_of_ne, List.count_nil, ih] <;>
      omega

/-- Block counts after substitution: `#R' = #P + #Q + #R`. -/
theorem count_R_subst (ts : List Tok) :
    (subst ts).count .R = ts.count .P + ts.count .Q + ts.count .R := by
  induction ts with
  | nil => rfl
  | cons τ ts ih =>
    simp only [subst, List.flatMap_cons, List.count_append] at ih ⊢
    cases τ <;>
      simp only [Tok.next, List.count_cons_self, ne_eq, reduceCtorEq, not_false_eq_true,
        List.count_cons_of_ne, List.count_nil, ih] <;>
      omega

/-- The length of the `(n+1)`-st iterate, as an integer. -/
def len (n : ℕ) : ℤ := ((step^[n + 1] [false, false]).length : ℤ)

/-- The lengths of the iterates from the first one on satisfy the
characteristic recurrence `x^3 = 2x^2 + x - 1` of the block-count matrix. -/
theorem len_add_three (n : ℕ) :
    len (n + 3) = 2 * len (n + 2) + len (n + 1) - len n := by
  have hlen : ∀ k, len k = 3 * ((subst^[k] [Tok.P]).count .P : ℤ)
      + 2 * ((subst^[k] [Tok.P]).count .Q : ℤ) + ((subst^[k] [Tok.P]).count .R : ℤ) := by
    intro k
    rw [len, iterate_succ_eq_render, length_render]
    push_cast
    ring
  have hsucc : ∀ k, subst^[k + 1] [Tok.P] = subst (subst^[k] [Tok.P]) := fun k =>
    Function.iterate_succ_apply' _ _ _
  rw [hlen, hlen, hlen, hlen]
  simp only [hsucc, count_P_subst, count_Q_subst, count_R_subst]
  push_cast
  ring

/-- **A286062, Kimberling's conjecture (Clark Kimberling, Jun 05 2017).**

Verbatim: "Conjecture:  a(n) is the number of letters (0's and 1's) in the
n-th iteration of the mapping 00->001, 1->011, starting with 00; see A286939."

Formal reading: with `step` the leftmost-first rewrite (`00 -> 001` tried
before `1 -> 011`, a lone `0` kept, as in Mathematica `StringReplace`), the
`n`-th iterate of `step` on `00` has length `a n`, where
`a n = 2 a (n-1) + a (n-2) - a (n-3)`, `a 0 = 2`, `a 1 = 3`, `a 2 = 6`. -/
theorem length_iterate_step (n : ℕ) :
    ((step^[n] [false, false]).length : ℤ) = a n := by
  have key : ∀ k, len k = a (k + 1) ∧ len (k + 1) = a (k + 2) ∧ len (k + 2) = a (k + 3) := by
    intro k
    induction k with
    | zero => exact ⟨rfl, rfl, rfl⟩
    | succ k ih =>
      obtain ⟨h0, h1, h2⟩ := ih
      refine ⟨h1, h2, ?_⟩
      rw [len_add_three, h0, h1, h2]
      rfl
  cases n with
  | zero => rfl
  | succ k => exact (key k).1

end Candidates.A286062RewriteBinaryWord
