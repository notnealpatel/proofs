/-
# Subtraction Nim with a pass: the reverse-mex / pass-independence conjecture fails

## Source

U. Larsson, H. Manabe, R. Miyadera, *A Subtraction Nim with a Pass*,
arXiv:2605.14321.  Section "Conjectures" (label `conject`), subsection
"Prediction on Reverse-Mex Property for Subtraction Nim with a Pass".

Rules (paper, Definitions `defofmove`, `subtractionsmallpass`, and the
introduction of Section `subtractionnimpass`): a position is `(x, p)`, `x`
stones and `p = 1` if a pass is still available.  A move removes `s ∈ S`
stones with `s ≤ x`; the one-time pass `(x,1) → (x,0)` "may be used at most
once in the game and not from a terminal position".  Hence

  `𝒢(x,1) = mex({𝒢(x-s,1) : s ∈ S, s ≤ x} ∪ {𝒢(x,0)})`  (`x` not terminal).

The paper's equations, verbatim:

  (conjecture1) `𝒢(x,0) = mex({𝒢(x+s_1,0), 𝒢(x+s_2,0), 𝒢(x+s_3,0)})`
  (conjecture2) `𝒢(x,1) = mex({𝒢(x-s_1,1), 𝒢(x-s_2,1), 𝒢(x-s_3,1)})`
  (conjecture3) `𝒢(x) = mex({𝒢(x+s_1,1), 𝒢(x+s_2,1), 𝒢(x+s_3,1)})`
                (the left side is evidently a typo for `𝒢(x,1)`)

Conjecture (verbatim, part (a)): "For a subtraction Nim with a subtraction
set `{s_1,s_2,s_3} = {a,2an,2an+a}`, where `a, n ∈ ℕ`, we obtain
(conjecture1), and for `x ≥ 6an+(4a+1)`, we have (conjecture2) and
(conjecture3).  The sequence of Grundy numbers enters into a loop when
`x ≥ 6an+(4a+1)`."  Parts (b) and (iii) treat `{a,(2n+1)a,(2n+3)a}` and
`{a,(2n+1)a,(2n+5)a}`.

Status in the paper: a conjecture based on computer calculation (not proved).

## This module (2026-10-21)

Refutation of part (a) at `a = 1`, `n = 2`, i.e. `S = {1,4,5}`, threshold
`6an + 4a + 1 = 17`, witness `x = 18`:
`𝒢(18,0) = 0`, `𝒢(18,1) = 4`, but
`mex{𝒢(17,1), 𝒢(14,1), 𝒢(13,1)} = mex{2,3,1} = 0` (so (conjecture2) fails) and
`mex{𝒢(19,1), 𝒢(22,1), 𝒢(23,1)} = mex{2,1,0} = 3` (so (conjecture3) fails).
With `a = 1` the only terminal position is `x = 0`, so the reading
"pass usable from every non-terminal position" and the reading
"pass usable from every nonzero pile" coincide here.
-/
import Mathlib

set_option autoImplicit false

namespace SubtractionNimPass

/-- The minimum excluded value of a finite set of natural numbers: the least
`m : ℕ` with `m ∉ s`. -/
noncomputable def mex (s : Finset ℕ) : ℕ :=
  Nat.find (Infinite.exists_notMem_finset s)

/-- Characterisation of `mex`: `mex s = m` iff `m ∉ s` and every smaller
natural number lies in `s`. -/
theorem mex_eq_iff (s : Finset ℕ) (m : ℕ) : mex s = m ↔ m ∉ s ∧ ∀ n < m, n ∈ s := by
  unfold mex
  rw [Nat.find_eq_iff]
  simp

/-- The legal subtraction amounts at a pile of `x` stones: the `s ∈ S` with
`0 < s ≤ x` (the paper's subtraction sets consist of positive integers). -/
def legal (S : Finset ℕ) (x : ℕ) : Finset ℕ :=
  S.filter (fun s => 0 < s ∧ s ≤ x)

/-- Grundy number `𝒢(x,0)` of the subtraction game with set `S` and no pass:
`𝒢(x,0) = mex{𝒢(x-s,0) : s ∈ S, s ≤ x}`. -/
noncomputable def grundy0 (S : Finset ℕ) (x : ℕ) : ℕ :=
  mex ((legal S x).attach.image (fun s => grundy0 S (x - s.1)))
termination_by x
decreasing_by
  have h := (Finset.mem_filter.mp s.2).2
  omega

/-- Grundy number `𝒢(x,1)` of the subtraction game with set `S` when the
one-time pass is still available: the options are `(x-s,1)` for legal `s` and,
when `x` is not terminal, the pass to `(x,0)`. -/
noncomputable def grundy1 (S : Finset ℕ) (x : ℕ) : ℕ :=
  mex ((legal S x).attach.image (fun s => grundy1 S (x - s.1)) ∪
    (if (legal S x).Nonempty then {grundy0 S x} else ∅))
termination_by x
decreasing_by
  have h := (Finset.mem_filter.mp s.2).2
  omega

/-- The paper's subtraction set `{a, 2an, 2an+a}` of Conjecture (a). -/
def setA (a n : ℕ) : Finset ℕ := {a, 2 * a * n, 2 * a * n + a}

/-- Unfolding equation for `grundy0` once the legal moves are known. -/
theorem grundy0_of_moves (S : Finset ℕ) (x : ℕ) (T : Finset ℕ) (hT : legal S x = T) :
    grundy0 S x = mex (T.image (fun s => grundy0 S (x - s))) := by
  rw [grundy0, ← hT]
  congr 1
  ext v
  simp

/-- Unfolding equation for `grundy1` at a non-terminal position. -/
theorem grundy1_of_moves (S : Finset ℕ) (x : ℕ) (T : Finset ℕ) (hT : legal S x = T)
    (hne : T.Nonempty) :
    grundy1 S x = mex (insert (grundy0 S x) (T.image (fun s => grundy1 S (x - s)))) := by
  rw [grundy1, hT, if_pos hne]
  congr 1
  ext v
  simp

/-- Unfolding equation for `grundy1` at a terminal position: no option at all. -/
theorem grundy1_of_terminal (S : Finset ℕ) (x : ℕ) (hT : legal S x = ∅) :
    grundy1 S x = mex ∅ := by
  rw [grundy1, hT]
  simp

/-- The counterexample set `S = {1,4,5} = setA 1 2`. -/
abbrev S145 : Finset ℕ := {1, 4, 5}

/-- `S145` is the paper's set `{a, 2an, 2an+a}` at `a = 1`, `n = 2`. -/
theorem setA_one_two : setA 1 2 = S145 := by decide

/-- `𝒢(0,0) = 0` for `S = {1,4,5}`. -/
theorem g0_0 : grundy0 S145 0 = 0 := by
  rw [grundy0_of_moves S145 0 ∅ (by decide)]
  exact (mex_eq_iff _ _).mpr (by decide)

/-- `𝒢(0,1) = 0` for `S = {1,4,5}` (terminal: no pass). -/
theorem g1_0 : grundy1 S145 0 = 0 := by
  rw [grundy1_of_terminal S145 0 (by decide)]
  exact (mex_eq_iff _ _).mpr (by decide)

/-- `𝒢(1,0) = 1` for `S = {1,4,5}`. -/
theorem g0_1 : grundy0 S145 1 = 1 := by
  rw [grundy0_of_moves S145 1 {1} (by decide)]
  simp only [Finset.image_singleton, Nat.reduceSub, g0_0]
  exact (mex_eq_iff _ _).mpr (by decide)

/-- `𝒢(1,1) = 2` for `S = {1,4,5}`. -/
theorem g1_1 : grundy1 S145 1 = 2 := by
  rw [grundy1_of_moves S145 1 {1} (by decide) (by decide)]
  simp only [Finset.image_singleton, Nat.reduceSub, g0_1, g1_0]
  exact (mex_eq_iff _ _).mpr (by decide)

/-- `𝒢(2,0) = 0` for `S = {1,4,5}`. -/
theorem g0_2 : grundy0 S145 2 = 0 := by
  rw [grundy0_of_moves S145 2 {1} (by decide)]
  simp only [Finset.image_singleton, Nat.reduceSub, g0_1]
  exact (mex_eq_iff _ _).mpr (by decide)

/-- `𝒢(2,1) = 1` for `S = {1,4,5}`. -/
theorem g1_2 : grundy1 S145 2 = 1 := by
  rw [grundy1_of_moves S145 2 {1} (by decide) (by decide)]
  simp only [Finset.image_singleton, Nat.reduceSub, g0_2, g1_1]
  exact (mex_eq_iff _ _).mpr (by decide)

/-- `𝒢(3,0) = 1` for `S = {1,4,5}`. -/
theorem g0_3 : grundy0 S145 3 = 1 := by
  rw [grundy0_of_moves S145 3 {1} (by decide)]
  simp only [Finset.image_singleton, Nat.reduceSub, g0_2]
  exact (mex_eq_iff _ _).mpr (by decide)

/-- `𝒢(3,1) = 0` for `S = {1,4,5}`. -/
theorem g1_3 : grundy1 S145 3 = 0 := by
  rw [grundy1_of_moves S145 3 {1} (by decide) (by decide)]
  simp only [Finset.image_singleton, Nat.reduceSub, g0_3, g1_2]
  exact (mex_eq_iff _ _).mpr (by decide)

/-- `𝒢(4,0) = 2` for `S = {1,4,5}`. -/
theorem g0_4 : grundy0 S145 4 = 2 := by
  rw [grundy0_of_moves S145 4 {1, 4} (by decide)]
  simp only [Finset.image_insert, Finset.image_singleton, Nat.reduceSub, g0_3, g0_0]
  exact (mex_eq_iff _ _).mpr (by decide)

/-- `𝒢(4,1) = 1` for `S = {1,4,5}`. -/
theorem g1_4 : grundy1 S145 4 = 1 := by
  rw [grundy1_of_moves S145 4 {1, 4} (by decide) (by decide)]
  simp only [Finset.image_insert, Finset.image_singleton, Nat.reduceSub, g0_4, g1_3, g1_0]
  exact (mex_eq_iff _ _).mpr (by decide)

/-- `𝒢(5,0) = 3` for `S = {1,4,5}`. -/
theorem g0_5 : grundy0 S145 5 = 3 := by
  rw [grundy0_of_moves S145 5 {1, 4, 5} (by decide)]
  simp only [Finset.image_insert, Finset.image_singleton, Nat.reduceSub, g0_4, g0_1, g0_0]
  exact (mex_eq_iff _ _).mpr (by decide)

/-- `𝒢(5,1) = 4` for `S = {1,4,5}`. -/
theorem g1_5 : grundy1 S145 5 = 4 := by
  rw [grundy1_of_moves S145 5 {1, 4, 5} (by decide) (by decide)]
  simp only [Finset.image_insert, Finset.image_singleton, Nat.reduceSub, g0_5, g1_4, g1_1, g1_0]
  exact (mex_eq_iff _ _).mpr (by decide)

/-- `𝒢(6,0) = 2` for `S = {1,4,5}`. -/
theorem g0_6 : grundy0 S145 6 = 2 := by
  rw [grundy0_of_moves S145 6 {1, 4, 5} (by decide)]
  simp only [Finset.image_insert, Finset.image_singleton, Nat.reduceSub, g0_5, g0_2, g0_1]
  exact (mex_eq_iff _ _).mpr (by decide)

/-- `𝒢(6,1) = 0` for `S = {1,4,5}`. -/
theorem g1_6 : grundy1 S145 6 = 0 := by
  rw [grundy1_of_moves S145 6 {1, 4, 5} (by decide) (by decide)]
  simp only [Finset.image_insert, Finset.image_singleton, Nat.reduceSub, g0_6, g1_5, g1_2, g1_1]
  exact (mex_eq_iff _ _).mpr (by decide)

/-- `𝒢(7,0) = 3` for `S = {1,4,5}`. -/
theorem g0_7 : grundy0 S145 7 = 3 := by
  rw [grundy0_of_moves S145 7 {1, 4, 5} (by decide)]
  simp only [Finset.image_insert, Finset.image_singleton, Nat.reduceSub, g0_6, g0_3, g0_2]
  exact (mex_eq_iff _ _).mpr (by decide)

/-- `𝒢(7,1) = 2` for `S = {1,4,5}`. -/
theorem g1_7 : grundy1 S145 7 = 2 := by
  rw [grundy1_of_moves S145 7 {1, 4, 5} (by decide) (by decide)]
  simp only [Finset.image_insert, Finset.image_singleton, Nat.reduceSub, g0_7, g1_6, g1_3, g1_2]
  exact (mex_eq_iff _ _).mpr (by decide)

/-- `𝒢(8,0) = 0` for `S = {1,4,5}`. -/
theorem g0_8 : grundy0 S145 8 = 0 := by
  rw [grundy0_of_moves S145 8 {1, 4, 5} (by decide)]
  simp only [Finset.image_insert, Finset.image_singleton, Nat.reduceSub, g0_7, g0_4, g0_3]
  exact (mex_eq_iff _ _).mpr (by decide)

/-- `𝒢(8,1) = 3` for `S = {1,4,5}`. -/
theorem g1_8 : grundy1 S145 8 = 3 := by
  rw [grundy1_of_moves S145 8 {1, 4, 5} (by decide) (by decide)]
  simp only [Finset.image_insert, Finset.image_singleton, Nat.reduceSub, g0_8, g1_7, g1_4, g1_3]
  exact (mex_eq_iff _ _).mpr (by decide)

/-- `𝒢(9,0) = 1` for `S = {1,4,5}`. -/
theorem g0_9 : grundy0 S145 9 = 1 := by
  rw [grundy0_of_moves S145 9 {1, 4, 5} (by decide)]
  simp only [Finset.image_insert, Finset.image_singleton, Nat.reduceSub, g0_8, g0_5, g0_4]
  exact (mex_eq_iff _ _).mpr (by decide)

/-- `𝒢(9,1) = 0` for `S = {1,4,5}`. -/
theorem g1_9 : grundy1 S145 9 = 0 := by
  rw [grundy1_of_moves S145 9 {1, 4, 5} (by decide) (by decide)]
  simp only [Finset.image_insert, Finset.image_singleton, Nat.reduceSub, g0_9, g1_8, g1_5, g1_4]
  exact (mex_eq_iff _ _).mpr (by decide)

/-- `𝒢(10,0) = 0` for `S = {1,4,5}`. -/
theorem g0_10 : grundy0 S145 10 = 0 := by
  rw [grundy0_of_moves S145 10 {1, 4, 5} (by decide)]
  simp only [Finset.image_insert, Finset.image_singleton, Nat.reduceSub, g0_9, g0_6, g0_5]
  exact (mex_eq_iff _ _).mpr (by decide)

/-- `𝒢(10,1) = 1` for `S = {1,4,5}`. -/
theorem g1_10 : grundy1 S145 10 = 1 := by
  rw [grundy1_of_moves S145 10 {1, 4, 5} (by decide) (by decide)]
  simp only [Finset.image_insert, Finset.image_singleton, Nat.reduceSub, g0_10, g1_9, g1_6, g1_5]
  exact (mex_eq_iff _ _).mpr (by decide)

/-- `𝒢(11,0) = 1` for `S = {1,4,5}`. -/
theorem g0_11 : grundy0 S145 11 = 1 := by
  rw [grundy0_of_moves S145 11 {1, 4, 5} (by decide)]
  simp only [Finset.image_insert, Finset.image_singleton, Nat.reduceSub, g0_10, g0_7, g0_6]
  exact (mex_eq_iff _ _).mpr (by decide)

/-- `𝒢(11,1) = 3` for `S = {1,4,5}`. -/
theorem g1_11 : grundy1 S145 11 = 3 := by
  rw [grundy1_of_moves S145 11 {1, 4, 5} (by decide) (by decide)]
  simp only [Finset.image_insert, Finset.image_singleton, Nat.reduceSub, g0_11, g1_10, g1_7, g1_6]
  exact (mex_eq_iff _ _).mpr (by decide)

/-- `𝒢(12,0) = 2` for `S = {1,4,5}`. -/
theorem g0_12 : grundy0 S145 12 = 2 := by
  rw [grundy0_of_moves S145 12 {1, 4, 5} (by decide)]
  simp only [Finset.image_insert, Finset.image_singleton, Nat.reduceSub, g0_11, g0_8, g0_7]
  exact (mex_eq_iff _ _).mpr (by decide)

/-- `𝒢(12,1) = 0` for `S = {1,4,5}`. -/
theorem g1_12 : grundy1 S145 12 = 0 := by
  rw [grundy1_of_moves S145 12 {1, 4, 5} (by decide) (by decide)]
  simp only [Finset.image_insert, Finset.image_singleton, Nat.reduceSub, g0_12, g1_11, g1_8, g1_7]
  exact (mex_eq_iff _ _).mpr (by decide)

/-- `𝒢(13,0) = 3` for `S = {1,4,5}`. -/
theorem g0_13 : grundy0 S145 13 = 3 := by
  rw [grundy0_of_moves S145 13 {1, 4, 5} (by decide)]
  simp only [Finset.image_insert, Finset.image_singleton, Nat.reduceSub, g0_12, g0_9, g0_8]
  exact (mex_eq_iff _ _).mpr (by decide)

/-- `𝒢(13,1) = 1` for `S = {1,4,5}`. -/
theorem g1_13 : grundy1 S145 13 = 1 := by
  rw [grundy1_of_moves S145 13 {1, 4, 5} (by decide) (by decide)]
  simp only [Finset.image_insert, Finset.image_singleton, Nat.reduceSub, g0_13, g1_12, g1_9, g1_8]
  exact (mex_eq_iff _ _).mpr (by decide)

/-- `𝒢(14,0) = 2` for `S = {1,4,5}`. -/
theorem g0_14 : grundy0 S145 14 = 2 := by
  rw [grundy0_of_moves S145 14 {1, 4, 5} (by decide)]
  simp only [Finset.image_insert, Finset.image_singleton, Nat.reduceSub, g0_13, g0_10, g0_9]
  exact (mex_eq_iff _ _).mpr (by decide)

/-- `𝒢(14,1) = 3` for `S = {1,4,5}`. -/
theorem g1_14 : grundy1 S145 14 = 3 := by
  rw [grundy1_of_moves S145 14 {1, 4, 5} (by decide) (by decide)]
  simp only [Finset.image_insert, Finset.image_singleton, Nat.reduceSub, g0_14, g1_13, g1_10, g1_9]
  exact (mex_eq_iff _ _).mpr (by decide)

/-- `𝒢(15,0) = 3` for `S = {1,4,5}`. -/
theorem g0_15 : grundy0 S145 15 = 3 := by
  rw [grundy0_of_moves S145 15 {1, 4, 5} (by decide)]
  simp only [Finset.image_insert, Finset.image_singleton, Nat.reduceSub, g0_14, g0_11, g0_10]
  exact (mex_eq_iff _ _).mpr (by decide)

/-- `𝒢(15,1) = 0` for `S = {1,4,5}`. -/
theorem g1_15 : grundy1 S145 15 = 0 := by
  rw [grundy1_of_moves S145 15 {1, 4, 5} (by decide) (by decide)]
  simp only [Finset.image_insert, Finset.image_singleton, Nat.reduceSub, g0_15, g1_14, g1_11, g1_10]
  exact (mex_eq_iff _ _).mpr (by decide)

/-- `𝒢(16,0) = 0` for `S = {1,4,5}`. -/
theorem g0_16 : grundy0 S145 16 = 0 := by
  rw [grundy0_of_moves S145 16 {1, 4, 5} (by decide)]
  simp only [Finset.image_insert, Finset.image_singleton, Nat.reduceSub, g0_15, g0_12, g0_11]
  exact (mex_eq_iff _ _).mpr (by decide)

/-- `𝒢(16,1) = 1` for `S = {1,4,5}`. -/
theorem g1_16 : grundy1 S145 16 = 1 := by
  rw [grundy1_of_moves S145 16 {1, 4, 5} (by decide) (by decide)]
  simp only [Finset.image_insert, Finset.image_singleton, Nat.reduceSub, g0_16, g1_15, g1_12, g1_11]
  exact (mex_eq_iff _ _).mpr (by decide)

/-- `𝒢(17,0) = 1` for `S = {1,4,5}`. -/
theorem g0_17 : grundy0 S145 17 = 1 := by
  rw [grundy0_of_moves S145 17 {1, 4, 5} (by decide)]
  simp only [Finset.image_insert, Finset.image_singleton, Nat.reduceSub, g0_16, g0_13, g0_12]
  exact (mex_eq_iff _ _).mpr (by decide)

/-- `𝒢(17,1) = 2` for `S = {1,4,5}`. -/
theorem g1_17 : grundy1 S145 17 = 2 := by
  rw [grundy1_of_moves S145 17 {1, 4, 5} (by decide) (by decide)]
  simp only [Finset.image_insert, Finset.image_singleton, Nat.reduceSub, g0_17, g1_16, g1_13, g1_12]
  exact (mex_eq_iff _ _).mpr (by decide)

/-- `𝒢(18,0) = 0` for `S = {1,4,5}`. -/
theorem g0_18 : grundy0 S145 18 = 0 := by
  rw [grundy0_of_moves S145 18 {1, 4, 5} (by decide)]
  simp only [Finset.image_insert, Finset.image_singleton, Nat.reduceSub, g0_17, g0_14, g0_13]
  exact (mex_eq_iff _ _).mpr (by decide)

/-- `𝒢(18,1) = 4` for `S = {1,4,5}`. -/
theorem g1_18 : grundy1 S145 18 = 4 := by
  rw [grundy1_of_moves S145 18 {1, 4, 5} (by decide) (by decide)]
  simp only [Finset.image_insert, Finset.image_singleton, Nat.reduceSub, g0_18, g1_17, g1_14, g1_13]
  exact (mex_eq_iff _ _).mpr (by decide)

/-- `𝒢(19,0) = 1` for `S = {1,4,5}`. -/
theorem g0_19 : grundy0 S145 19 = 1 := by
  rw [grundy0_of_moves S145 19 {1, 4, 5} (by decide)]
  simp only [Finset.image_insert, Finset.image_singleton, Nat.reduceSub, g0_18, g0_15, g0_14]
  exact (mex_eq_iff _ _).mpr (by decide)

/-- `𝒢(19,1) = 2` for `S = {1,4,5}`. -/
theorem g1_19 : grundy1 S145 19 = 2 := by
  rw [grundy1_of_moves S145 19 {1, 4, 5} (by decide) (by decide)]
  simp only [Finset.image_insert, Finset.image_singleton, Nat.reduceSub, g0_19, g1_18, g1_15, g1_14]
  exact (mex_eq_iff _ _).mpr (by decide)

/-- `𝒢(20,0) = 2` for `S = {1,4,5}`. -/
theorem g0_20 : grundy0 S145 20 = 2 := by
  rw [grundy0_of_moves S145 20 {1, 4, 5} (by decide)]
  simp only [Finset.image_insert, Finset.image_singleton, Nat.reduceSub, g0_19, g0_16, g0_15]
  exact (mex_eq_iff _ _).mpr (by decide)

/-- `𝒢(20,1) = 3` for `S = {1,4,5}`. -/
theorem g1_20 : grundy1 S145 20 = 3 := by
  rw [grundy1_of_moves S145 20 {1, 4, 5} (by decide) (by decide)]
  simp only [Finset.image_insert, Finset.image_singleton, Nat.reduceSub, g0_20, g1_19, g1_16, g1_15]
  exact (mex_eq_iff _ _).mpr (by decide)

/-- `𝒢(21,0) = 3` for `S = {1,4,5}`. -/
theorem g0_21 : grundy0 S145 21 = 3 := by
  rw [grundy0_of_moves S145 21 {1, 4, 5} (by decide)]
  simp only [Finset.image_insert, Finset.image_singleton, Nat.reduceSub, g0_20, g0_17, g0_16]
  exact (mex_eq_iff _ _).mpr (by decide)

/-- `𝒢(21,1) = 0` for `S = {1,4,5}`. -/
theorem g1_21 : grundy1 S145 21 = 0 := by
  rw [grundy1_of_moves S145 21 {1, 4, 5} (by decide) (by decide)]
  simp only [Finset.image_insert, Finset.image_singleton, Nat.reduceSub, g0_21, g1_20, g1_17, g1_16]
  exact (mex_eq_iff _ _).mpr (by decide)

/-- `𝒢(22,0) = 2` for `S = {1,4,5}`. -/
theorem g0_22 : grundy0 S145 22 = 2 := by
  rw [grundy0_of_moves S145 22 {1, 4, 5} (by decide)]
  simp only [Finset.image_insert, Finset.image_singleton, Nat.reduceSub, g0_21, g0_18, g0_17]
  exact (mex_eq_iff _ _).mpr (by decide)

/-- `𝒢(22,1) = 1` for `S = {1,4,5}`. -/
theorem g1_22 : grundy1 S145 22 = 1 := by
  rw [grundy1_of_moves S145 22 {1, 4, 5} (by decide) (by decide)]
  simp only [Finset.image_insert, Finset.image_singleton, Nat.reduceSub, g0_22, g1_21, g1_18, g1_17]
  exact (mex_eq_iff _ _).mpr (by decide)

/-- `𝒢(23,0) = 3` for `S = {1,4,5}`. -/
theorem g0_23 : grundy0 S145 23 = 3 := by
  rw [grundy0_of_moves S145 23 {1, 4, 5} (by decide)]
  simp only [Finset.image_insert, Finset.image_singleton, Nat.reduceSub, g0_22, g0_19, g0_18]
  exact (mex_eq_iff _ _).mpr (by decide)

/-- `𝒢(23,1) = 0` for `S = {1,4,5}`. -/
theorem g1_23 : grundy1 S145 23 = 0 := by
  rw [grundy1_of_moves S145 23 {1, 4, 5} (by decide) (by decide)]
  simp only [Finset.image_insert, Finset.image_singleton, Nat.reduceSub, g0_23, g1_22, g1_19, g1_18]
  exact (mex_eq_iff _ _).mpr (by decide)

/-! ### Ground-truth checks -/

example : mex {0, 1, 3} = 2 := (mex_eq_iff _ _).mpr (by decide)

example : mex ∅ = 0 := (mex_eq_iff _ _).mpr (by decide)

example : legal S145 3 = {1} := by decide

example : setA 2 3 = {2, 12, 14} := by decide

/-! ### The paper's equations and Conjecture (a) -/

/-- Equation (conjecture1) at `x`: reverse-mex for `𝒢(·,0)`,
`𝒢(x,0) = mex{𝒢(x+s,0) : s ∈ S}`. -/
def ReverseMexAt (S : Finset ℕ) (x : ℕ) : Prop :=
  grundy0 S x = mex (S.image (fun s => grundy0 S (x + s)))

/-- Equation (conjecture2) at `x`: the pass option is irrelevant,
`𝒢(x,1) = mex{𝒢(x-s,1) : s ∈ S}`.  It is only asserted for `x` beyond the
threshold, where every `s ∈ S` satisfies `s ≤ x`, so the subtraction is genuine. -/
def PassIndependentAt (S : Finset ℕ) (x : ℕ) : Prop :=
  grundy1 S x = mex (S.image (fun s => grundy1 S (x - s)))

/-- Equation (conjecture3) at `x` (with the paper's typo `𝒢(x)` read as
`𝒢(x,1)`): reverse-mex for `𝒢(·,1)`, `𝒢(x,1) = mex{𝒢(x+s,1) : s ∈ S}`. -/
def ReverseMexPassAt (S : Finset ℕ) (x : ℕ) : Prop :=
  grundy1 S x = mex (S.image (fun s => grundy1 S (x + s)))

/-- Conjecture (a) of arXiv:2605.14321, Section "Conjectures": for every
`a, n ∈ ℕ` (positive) and `S = {a, 2an, 2an+a}`, (conjecture1) holds for all
`x`, and (conjecture2), (conjecture3) hold for all `x ≥ 6an + 4a + 1`.
(The accompanying periodicity remark is omitted; dropping a conjunct only
strengthens the refutation `¬ ConjectureA`.) -/
def ConjectureA : Prop :=
  ∀ a n : ℕ, 0 < a → 0 < n →
    (∀ x, ReverseMexAt (setA a n) x) ∧
      ∀ x, 6 * a * n + 4 * a + 1 ≤ x →
        PassIndependentAt (setA a n) x ∧ ReverseMexPassAt (setA a n) x

/-! ### The counterexample -/

/-- For `S = {1,4,5}`: `mex{𝒢(17,1), 𝒢(14,1), 𝒢(13,1)} = 0` while `𝒢(18,1) = 4`,
so (conjecture2) fails at `x = 18`, although `18 ≥ 6·1·2 + 4·1 + 1 = 17`. -/
theorem not_passIndependentAt_S145_18 : ¬ PassIndependentAt S145 18 := by
  unfold PassIndependentAt
  simp only [Finset.image_insert, Finset.image_singleton, Nat.reduceSub, g1_18, g1_17, g1_14,
    g1_13]
  have hmex : mex {2, 3, 1} = 0 := (mex_eq_iff _ _).mpr (by decide)
  rw [hmex]
  decide

/-- For `S = {1,4,5}`: `mex{𝒢(19,1), 𝒢(22,1), 𝒢(23,1)} = 3` while `𝒢(18,1) = 4`,
so (conjecture3) fails at `x = 18`. -/
theorem not_reverseMexPassAt_S145_18 : ¬ ReverseMexPassAt S145 18 := by
  unfold ReverseMexPassAt
  simp only [Finset.image_insert, Finset.image_singleton, Nat.reduceAdd, g1_18, g1_19, g1_22,
    g1_23]
  have hmex : mex {2, 1, 0} = 3 := (mex_eq_iff _ _).mpr (by decide)
  rw [hmex]
  decide

/-- **Conjecture (a) of arXiv:2605.14321 is false.**  At `a = 1`, `n = 2`
(`S = {1,4,5}`, threshold `17`) and `x = 18`, both (conjecture2)
(pass-independence) and (conjecture3) (reverse-mex with a pass) fail. -/
theorem conjectureA_false : ¬ ConjectureA := by
  intro h
  have h18 := ((h 1 2 (by norm_num) (by norm_num)).2 18 (by norm_num)).1
  rw [setA_one_two] at h18
  exact not_passIndependentAt_S145_18 h18

/-- The explicit failing data at `S = {1,4,5}`, `x = 18`: `𝒢(18,0) = 0`,
`𝒢(18,1) = 4`, the backward mex is `0`, and the forward mex is `3`. -/
theorem counterexample_values :
    grundy0 S145 18 = 0 ∧ grundy1 S145 18 = 4 ∧
      mex (S145.image (fun s => grundy1 S145 (18 - s))) = 0 ∧
      mex (S145.image (fun s => grundy1 S145 (18 + s))) = 3 := by
  refine ⟨g0_18, g1_18, ?_, ?_⟩
  · simp only [Finset.image_insert, Finset.image_singleton, Nat.reduceSub, g1_17, g1_14, g1_13]
    exact (mex_eq_iff _ _).mpr (by decide)
  · simp only [Finset.image_insert, Finset.image_singleton, Nat.reduceAdd, g1_19, g1_22, g1_23]
    exact (mex_eq_iff _ _).mpr (by decide)

/-- Non-vacuity: at `x = 17` (the threshold) both equations do hold for
`S = {1,4,5}`, so the predicates are not trivially false. -/
example : PassIndependentAt S145 17 ∧ ReverseMexPassAt S145 17 := by
  unfold PassIndependentAt ReverseMexPassAt
  simp only [Finset.image_insert, Finset.image_singleton, Nat.reduceSub, Nat.reduceAdd, g1_17,
    g1_16, g1_13, g1_12, g1_18, g1_21, g1_22]
  exact ⟨((mex_eq_iff _ _).mpr (by decide)).symm, ((mex_eq_iff _ _).mpr (by decide)).symm⟩

end SubtractionNimPass
