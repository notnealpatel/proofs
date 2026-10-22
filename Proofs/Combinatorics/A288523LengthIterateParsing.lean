/-
# A288523 — length of the iterates of the parsing map 00 → 0101, 10 → 010

OEIS A288523 and A288520, Clark Kimberling (2017): the recurrence
`a(n) = a(n-1)+a(n-2)+a(n-3)-2a(n-4)` for `5 ≤ n`, with initial values
`2,4,5,8,11`, gives the lengths of iterates of `00 ↦ 0101`, `10 ↦ 010`
starting from `00`.

## Semantics of the parsing map

`StringReplace` scans left to right; at each position it replaces `00` by
`0101` or `10` by `010` (consuming both letters) and otherwise copies one
letter.  Since the two patterns begin with different letters there is no
priority ambiguity.  Letters are encoded as `Bool` (`false = 0`, `true = 1`).

## Proof idea

For `n ≥ 1` the `n`-th iterate has the form `0^h · seg(b₁) ⋯ seg(bₘ) · seg(1) · 1`
with `h ∈ {1, 2}`, `seg(k) = 1 0^k` and `bᵢ ∈ {1, 2, 3}`.  The parse never
crosses a block boundary, and one step acts on the block list as the
substitution `σ : 1 ↦ 2, 2 ↦ 3, 3 ↦ 2 1 1` (prefixed by `1 1` when `h = 2`),
up to a one-letter conjugation `img(b) ++ 0 = 0 ++ seg(σ b)`.  The weight
identity `|seg(σ³ M)| = |seg(σ M)| + 2 |seg M|` gives
`L(m+3) + 2 = L(m+1) + 2 L(m)` for `m ≥ 1`, which yields the order-4
recurrence.
-/
import Mathlib.Tactic.Linarith
import Mathlib.Logic.Function.Iterate

set_option autoImplicit false

namespace Candidates.A288523LengthIterateParsing

/-! ## Definition layer -/

/-- One left-to-right parsing step: `00 ↦ 0101`, `10 ↦ 010`, any other letter
is copied (encoding `false = 0`, `true = 1`). -/
def step : List Bool → List Bool
  | false :: false :: r => [false, true, false, true] ++ step r
  | true :: false :: r => [false, true, false] ++ step r
  | x :: r => x :: step r
  | [] => []

/-- The OEIS A288523 sequence, defined by its NAME line:
`a(n) = a(n-1) + a(n-2) + a(n-3) - 2 a(n-4)` for `n ≥ 5`, with initial values
`2, 4, 5, 8, 11`.  Valued in `ℤ` so the subtraction is genuine. -/
def a : ℕ → ℤ
  | 0 => 2
  | 1 => 4
  | 2 => 5
  | 3 => 8
  | 4 => 11
  | n + 5 => a (n + 4) + a (n + 3) + a (n + 2) - 2 * a (n + 1)

/-! ## Examples -/

-- The iterates listed in A288520.
example : step^[0] [false, false] = [false, false] := rfl
example : step^[1] [false, false] = [false, true, false, true] := rfl
example : step^[2] [false, false] = [false, false, true, false, true] := rfl
example : step^[3] [false, false] =
    [false, true, false, true, false, true, false, true] := rfl
example : step^[4] [false, false] =
    [false, false, true, false, false, true, false, false, true, false, true] := rfl
-- A letter not followed by a matching pattern is copied (`01`, `11`, trailing).
example : step [false, true, true, false] = [false, true, false, true, false] := rfl

-- The first terms of A288523.
example : (List.range 12).map a = [2, 4, 5, 8, 11, 16, 25, 36, 55, 84, 125, 192] := by
  decide

/-! ## Block structure -/

/-- Block letters `1, 2, 3` standing for the words `seg k = 1 0^k`. -/
inductive Blk
  | one
  | two
  | three
  deriving DecidableEq

/-- The word `1 0^k` of a block. -/
def seg : Blk → List Bool
  | .one => [true, false]
  | .two => [true, false, false]
  | .three => [true, false, false, false]

/-- The image of a block under `step` when the block is followed by a `1`. -/
def img : Blk → List Bool
  | .one => [false, true, false]
  | .two => [false, true, false, false]
  | .three => [false, true, false, false, true, false, true]

/-- The block substitution `1 ↦ 2, 2 ↦ 3, 3 ↦ 2 1 1`. -/
def sigma : Blk → List Blk
  | .one => [.two]
  | .two => [.three]
  | .three => [.two, .one, .one]

/-- The head `0^h` of a word, `h = 2` for `true` and `h = 1` for `false`. -/
def head : Bool → List Bool
  | true => [false, false]
  | false => [false]

/-- The word `0^h · seg(M ++ [1]) · 1` encoded by a state `(b, M)`. -/
def word (s : Bool × List Blk) : List Bool :=
  head s.1 ++ (s.2 ++ [Blk.one]).flatMap seg ++ [true]

/-- The state transition matching one parsing step. -/
def next : Bool × List Blk → Bool × List Blk
  | (false, M) => (true, M.flatMap sigma)
  | (true, M) => (false, [Blk.one, Blk.one] ++ M.flatMap sigma)

/-- Weight of a block list: the length of the word it encodes. -/
def wt (M : List Blk) : ℕ := (M.flatMap seg).length

/-! ## Step lemmas -/

/-- A block word followed by a `1` is parsed without crossing its boundary. -/
theorem step_seg (b : Blk) (v : List Bool) :
    step (seg b ++ true :: v) = img b ++ step (true :: v) := by
  cases b <;> rfl

/-- A block list followed by a `1` starts with `1`. -/
theorem flatMap_seg_append_cons (M : List Blk) (v : List Bool) :
    ∃ w, M.flatMap seg ++ true :: v = true :: w := by
  cases M with
  | nil => exact ⟨v, rfl⟩
  | cons b M => cases b <;> exact ⟨_, rfl⟩

/-- A block list followed by a `1` is parsed block by block. -/
theorem step_flatMap_seg (M : List Blk) (v : List Bool) :
    step (M.flatMap seg ++ true :: v) = M.flatMap img ++ step (true :: v) := by
  induction M with
  | nil => rfl
  | cons b M ih =>
    obtain ⟨w, hw⟩ := flatMap_seg_append_cons M v
    rw [List.flatMap_cons, List.append_assoc, hw, step_seg, ← hw, ih,
      List.flatMap_cons, List.append_assoc]

/-- The one-letter conjugation `img(M) ++ 0 = 0 ++ seg(σ M)`. -/
theorem flatMap_img_append (M : List Blk) :
    M.flatMap img ++ [false] = false :: (M.flatMap sigma).flatMap seg := by
  induction M with
  | nil => rfl
  | cons b M ih =>
    rw [List.flatMap_cons, List.append_assoc, ih, List.flatMap_cons,
      List.flatMap_append]
    cases b <;> rfl

/-- One parsing step acts on encoded words as the state transition `next`. -/
theorem step_word (s : Bool × List Blk) : step (word s) = word (next s) := by
  obtain ⟨b, M⟩ := s
  have hconj := flatMap_img_append M
  cases b with
  | false =>
    have hstep : step (word (false, M)) =
        false :: (M.flatMap img ++ [false, true, false] ++ [true]) := by
      simp only [word, head, List.flatMap_append, List.append_assoc]
      show step (false :: (M.flatMap seg ++ true :: false :: [true])) = _
      rw [show step (false :: (M.flatMap seg ++ true :: false :: [true])) =
          false :: step (M.flatMap seg ++ true :: false :: [true]) by
        obtain ⟨w, hw⟩ := flatMap_seg_append_cons M [false, true]
        rw [hw]; rfl]
      rw [step_flatMap_seg]
      rfl
    rw [hstep]
    simp only [word, next, head, List.flatMap_append]
    rw [show M.flatMap img ++ [false, true, false] ++ [true] =
        (M.flatMap img ++ [false]) ++ [true, false, true] by simp, hconj]
    simp [seg]
  | true =>
    have hstep : step (word (true, M)) =
        [false, true, false, true] ++ (M.flatMap img ++ [false, true, false] ++ [true]) := by
      simp only [word, head, List.flatMap_append, List.append_assoc]
      show step (false :: false :: (M.flatMap seg ++ true :: false :: [true])) = _
      rw [show step (false :: false :: (M.flatMap seg ++ true :: false :: [true])) =
          [false, true, false, true] ++ step (M.flatMap seg ++ true :: false :: [true]) by
        rfl]
      rw [step_flatMap_seg]
      rfl
    rw [hstep]
    simp only [word, next, head, List.flatMap_append]
    rw [show M.flatMap img ++ [false, true, false] ++ [true] =
        (M.flatMap img ++ [false]) ++ [true, false, true] by simp, hconj]
    simp [seg]

/-- For `k ≥ 0`, the `(k+1)`-st iterate of `00` is the word of the `k`-th state. -/
theorem iterate_succ_eq_word (k : ℕ) :
    step^[k + 1] [false, false] = word (next^[k] (false, [])) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, step_word, ← Function.iterate_succ_apply' next]

/-! ## Length bookkeeping -/

/-- The weight is additive. -/
theorem wt_append (M N : List Blk) : wt (M ++ N) = wt M + wt N := by
  simp [wt, List.flatMap_append]

/-- The weight identity `|σ³ M| = |σ M| + 2 |M|` (characteristic polynomial
`x³ - x - 2` of the substitution). -/
theorem wt_sigma_three (M : List Blk) :
    wt (((M.flatMap sigma).flatMap sigma).flatMap sigma) = wt (M.flatMap sigma) + 2 * wt M := by
  induction M with
  | nil => rfl
  | cons b M ih =>
    simp only [List.flatMap_cons, List.flatMap_append, wt_append] at ih ⊢
    have hb : wt (((sigma b).flatMap sigma).flatMap sigma) = wt (sigma b) + 2 * wt [b] := by
      cases b <;> rfl
    have hc : wt (b :: M) = wt [b] + wt M := wt_append [b] M
    omega

/-- Length of an encoded word. -/
theorem length_word (b : Bool) (M : List Blk) :
    (word (b, M)).length = (if b then 2 else 1) + wt M + 3 := by
  cases b <;>
    simp only [word, head, List.flatMap_append, List.flatMap_cons, seg, List.flatMap_nil,
      List.append_nil, List.cons_append, List.nil_append, List.append_assoc, List.length_cons,
      List.length_append, List.length_flatMap, List.length_nil, zero_add, Nat.reduceAdd,
      Bool.false_eq_true, ↓reduceIte, wt, Nat.add_right_cancel_iff, Nat.reduceEqDiff] <;>
    omega

/-- Three-step length relation `L(next³ s) + 2 = L(next s) + 2 L(s)`. -/
theorem length_word_next_three (s : Bool × List Blk) :
    (word (next^[3] s)).length + 2 = (word (next s)).length + 2 * (word s).length := by
  obtain ⟨b, M⟩ := s
  have h3 := wt_sigma_three M
  cases b
  · simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, next,
      List.flatMap_append, length_word, wt_append] at h3 ⊢
    have h11 : wt (([Blk.one, Blk.one].flatMap sigma)) = 6 := rfl
    simp only [if_true, if_false, Bool.false_eq_true] at h3 ⊢
    omega
  · simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, next,
      List.flatMap_append, length_word, wt_append] at h3 ⊢
    have h11 : wt [Blk.one, Blk.one] = 4 := rfl
    have h22 : wt (([Blk.one, Blk.one].flatMap sigma).flatMap sigma) = 8 := rfl
    simp only [if_true, if_false, Bool.false_eq_true] at h3 ⊢
    omega

/-- Length of the `n`-th iterate of `00`. -/
def L (n : ℕ) : ℕ := (step^[n] [false, false]).length

/-- `L(m+3) + 2 = L(m+1) + 2 L(m)` for `1 ≤ m`. -/
theorem L_add_three (m : ℕ) (hm : 1 ≤ m) : L (m + 3) + 2 = L (m + 1) + 2 * L m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have h := length_word_next_three (next^[k] (false, []))
  rw [← Function.iterate_add_apply, ← Function.iterate_succ_apply' next] at h
  simp only [L]
  rw [show k + 1 + 3 = (3 + k) + 1 by omega, iterate_succ_eq_word,
    show k + 1 + 1 = (k + 1) + 1 by rfl, iterate_succ_eq_word, iterate_succ_eq_word]
  exact h

/-! ## The conjecture -/

/-- **Kimberling's conjecture (A288523 / A288520, Jun 2017), proved.**

The length of the nth iterate of `00` equals `a n`.
Here `step` is the left-to-right parse of the Mathematica program
`StringReplace[w, {"00" -> "0101", "10" -> "010"}]` and `a` is the recurrence
of the NAME line, `a(n) = a(n-1)+a(n-2)+a(n-3)-2a(n-4)` (`n ≥ 5`) with initial
values `2, 4, 5, 8, 11`.  Holds for every `n ≥ 0`. -/
theorem length_iterate_eq_a (n : ℕ) :
    ((step^[n] [false, false]).length : ℤ) = a n := by
  change (L n : ℤ) = a n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | 3, _ => rfl
    | 4, _ => rfl
    | n + 5, ih =>
      have h1 := L_add_three (n + 2) (by omega)
      have h2 := L_add_three (n + 1) (by omega)
      rw [a, ← ih (n + 4) (by omega), ← ih (n + 3) (by omega), ← ih (n + 2) (by omega),
        ← ih (n + 1) (by omega)]
      have h1' : (L (n + 5) : ℤ) + 2 = L (n + 3) + 2 * L (n + 2) := by exact_mod_cast h1
      have h2' : (L (n + 4) : ℤ) + 2 = L (n + 2) + 2 * L (n + 1) := by exact_mod_cast h2
      linarith

end Candidates.A288523LengthIterateParsing
