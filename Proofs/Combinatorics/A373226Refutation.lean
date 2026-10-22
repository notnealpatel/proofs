/-
# A373226 — the odd terms are not A151907

OEIS A373226 (Sidharth Ghoshal, May 28, 2024) counts points of a diagonal
Vicsek fractal in a central `n × n` window. For even `n`, the top-left
of the four most central placements is used. Its third conjecture identifies
`a(2n+1)` with A151907, with both sequences at offset 0.

A151907 is the sequence of partial sums of A151906 (Applegate and Sloane,
July 31, 2009); its auxiliary sequences are defined below.

The literal conjecture fails at `n = 0`: `a(1) = 1` but `A151907(0) = 0`.
The shifted identity `a(2n+1) = A151907(n+1)` fails at `n = 8`:
`a(17) = 49` but `A151907(9) = 57`. No nonnegative index shift works
(`oddTerms_ne_A151907_shift`). The growth and scaling conjectures
in the entry are not addressed.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A373226Refutation

open Finset

/-! ## The diagonal Vicsek fractal and the window count -/

/-- The allowed ternary digit pairs of the diagonal Vicsek seed
`[[1,0,1],[0,1,0],[1,0,1]]`: the corners and the centre of a `3 × 3` block,
i.e. `(u, v) ∈ {(0,0), (0,2), (1,1), (2,0), (2,2)}`. -/
def okPair (u v : ℕ) : Bool :=
  (u == 0 && v == 0) || (u == 0 && v == 2) || (u == 1 && v == 1) ||
    (u == 2 && v == 0) || (u == 2 && v == 2)

/-- `inVicsek K x y`: the cell in row `x`, column `y` (0-indexed) of the level-`K`
diagonal Vicsek fractal on a `3^K × 3^K` grid is filled, i.e. each of the `K`
lowest ternary digit pairs of `(x, y)` is an allowed seed position.  This is
the matrix produced by the entry's `descend(seed, zero, [[1]], K)`. -/
def inVicsek : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => true
  | K + 1, x, y => okPair (x % 3) (y % 3) && inVicsek K (x / 3) (y / 3)

/-- The number of filled cells of the level-`K` fractal in the `n × n` window
whose rows and columns are `3^K / 2 - n / 2, …, 3^K / 2 - n / 2 + n - 1`.
For odd `n` this is the window centred at the grid centre `3^K / 2`; for even
`n` it is the top-left of the four most central placements, exactly as in the
entry's `count`.  The `ℕ` subtraction is honest when `n ≤ 3^K`. -/
def windowCount (K n : ℕ) : ℕ :=
  ∑ i ∈ range n, ∑ j ∈ range n,
    if inVicsek K (3 ^ K / 2 - n / 2 + i) (3 ^ K / 2 - n / 2 + j) then 1 else 0

/-- The fractal level used for the `n × n` window: `Nat.log 3 n + 1`, the least
`k` with `n < 3^k`. -/
def level (n : ℕ) : ℕ := Nat.log 3 n + 1

/-- **A373226**: the number of points of the diagonal Vicsek fractal in a
central `n × n` window.  The entry builds the fractal on any `3^k × 3^k` grid
with `3^k ≥ n`; we take `k = level n`, which satisfies `n < 3^k`
(`lt_three_pow_level`). -/
def a (n : ℕ) : ℕ := windowCount (level n) n

/-- The level is large enough for the window: `n < 3^(level n)`, so the grid
contains the window and the subtraction in `windowCount (level n) n` is not
truncated. -/
theorem lt_three_pow_level (n : ℕ) : n < 3 ^ level n :=
  Nat.lt_pow_succ_log_self (by norm_num) n

/-! ### Examples: the 50 listed terms of A373226 and the entry's examples -/

example : (List.range 25).map a =
    [0, 1, 2, 5, 6, 9, 10, 13, 18, 25, 26, 29, 30, 33, 38, 45, 46, 49, 50, 53,
      58, 65, 74, 85, 90] := by decide

example : (List.range' 25 25).map a =
    [97, 110, 125, 126, 129, 130, 133, 138, 145, 146, 149, 150, 153, 158, 165,
      174, 185, 190, 197, 210, 225, 226, 229, 230, 233] := by decide +kernel

/-- The entry's `n = 4` picture `x... / .x.x / ..x. / .x.x` (top-left choice),
built at level 2 where the window starts at row and column `9 / 2 - 2 = 2`. -/
example : (List.range 4).map (fun i => (List.range 4).map (fun j => inVicsek 2 (2 + i) (2 + j))) =
    [[true, false, false, false], [false, true, false, true],
      [false, false, true, false], [false, true, false, true]] := by decide

/-- Level independence on a sample: the entry's own call `count(descend(…, 2), 5)`
(level 2) gives the same value as levels 3 and 5. -/
example : windowCount 2 5 = a 5 ∧ windowCount 3 5 = a 5 ∧ windowCount 5 5 = a 5 := by
  decide

/-! ## A151907 -/

/-- `A000120`: the binary weight of `n`. -/
def wt (n : ℕ) : ℕ := (Nat.digits 2 n).sum

example : (List.range 16).map wt = [0, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 2, 3, 3, 4] := by
  decide

/-- `A151899`: period 6, repeat `[0, 0, 1, 1, 1, 2]`. -/
def f (n : ℕ) : ℕ :=
  if n % 6 ≤ 1 then 0 else if n % 6 ≤ 4 then 1 else 2

example : (List.range 12).map f = [0, 0, 1, 1, 1, 2, 0, 0, 1, 1, 1, 2] := by decide

/-- `A151904`: `a(6k + j) = (3^(wt(k) + f(j)) - 1) / 2` for `0 ≤ j < 6`
(the division is exact: `3^e - 1` is even, and `3^e ≥ 1`). -/
def A151904 (n : ℕ) : ℕ := (3 ^ (wt (n / 6) + f (n % 6)) - 1) / 2

example : (List.range 24).map A151904 =
    [0, 0, 1, 1, 1, 4, 1, 1, 4, 4, 4, 13, 1, 1, 4, 4, 4, 13, 4, 4, 13, 13, 13, 40] := by
  decide

/-- `A151905`: `a(0) = a(2) = 0`, `a(1) = 1`; for `n ≥ 3`, writing
`n = 3·2^k + j` with `0 ≤ j < 3·2^k` (so `k = ⌊log₂(n/3)⌋ = Nat.log 2 (n / 3)`),
`a(n) = A151904(j)`. -/
def A151905 (n : ℕ) : ℕ :=
  if n < 3 then (if n = 1 then 1 else 0)
  else A151904 (n - 3 * 2 ^ Nat.log 2 (n / 3))

example : (List.range 36).map A151905 =
    [0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 4, 0, 0, 1, 1, 1, 4, 1, 1, 4, 4, 4, 13,
      0, 0, 1, 1, 1, 4, 1, 1, 4, 4, 4, 13] := by decide

/-- `A151906`: `a(0) = 0`, `a(1) = 1`, and `a(n) = 8·A151905(n) + 4` for `n > 1`. -/
def A151906 (n : ℕ) : ℕ :=
  if n ≤ 1 then n else 8 * A151905 n + 4

example : (List.range 26).map A151906 =
    [0, 1, 4, 4, 4, 12, 4, 4, 12, 12, 12, 36, 4, 4, 12, 12, 12, 36, 12, 12, 36, 36,
      36, 108, 4, 4] := by decide

/-- `A151907`: partial sums of `A151906`, `a(n) = ∑_{i ≤ n} A151906(i)`. -/
def A151907 (n : ℕ) : ℕ := ∑ i ∈ range (n + 1), A151906 i

example : (List.range 21).map A151907 =
    [0, 1, 5, 9, 13, 25, 29, 33, 45, 57, 69, 105, 109, 113, 125, 137, 149, 185, 197,
      209, 245] := by decide

/-- `A151907` is monotone (partial sums of a sequence in `ℕ`). -/
theorem A151907_mono {m n : ℕ} (hmn : m ≤ n) : A151907 m ≤ A151907 n :=
  sum_le_sum_of_subset (range_subset_range.mpr (Nat.succ_le_succ hmn))

/-! ## The conjecture and its refutation -/

/-- Ghoshal's third conjecture (OEIS A373226, May 28, 2024):
`a(2n+1) = A151907(n)`, with both sequences at offset 0. -/
def Conjecture : Prop := ∀ n : ℕ, a (2 * n + 1) = A151907 n

/-- The shifted alignment `a(2n+1) = A151907(n+1)`, matching the initial
odd terms `1,5,9,13,25,29,33,45`. -/
def ShiftedConjecture : Prop := ∀ n : ℕ, a (2 * n + 1) = A151907 (n + 1)

/-- The identity `a(2n+1) = A151907(n)` fails at `n = 0`:
`a(1) = 1`, whereas `A151907(0) = 0`. The shift by 1 is refuted
separately in `shiftedConjecture_false`. -/
theorem conjecture_false : ¬ Conjecture := fun h => by
  have ha : a 1 = 1 := by decide
  have hA : A151907 0 = 0 := by decide
  have h0 : a (2 * 0 + 1) = A151907 0 := h 0
  rw [ha, hA] at h0
  exact absurd h0 (by decide)

/-- The shifted alignment also fails: `a(17) = 49`,
whereas `A151907(9) = 57` (the case `n = 8`). -/
theorem shiftedConjecture_false : ¬ ShiftedConjecture := fun h => by
  have ha : a 17 = 49 := by decide
  have hA : A151907 9 = 57 := by decide
  have h8 : a (2 * 8 + 1) = A151907 (8 + 1) := h 8
  rw [ha, hA] at h8
  exact absurd h8 (by decide)

/-- **No index shift repairs the conjecture**: for every `d`, the identity
`a(2n+1) = A151907(n+d)` fails for some `n`.  (`d = 0`: `n = 0`; `d = 1`:
`n = 8`, `a(17) = 49 ≠ 57`; `d ≥ 2`: `n = 0`, since `A151907(d) ≥ 5 > 1 = a(1)`.) -/
theorem oddTerms_ne_A151907_shift (d : ℕ) :
    ¬ ∀ n : ℕ, a (2 * n + 1) = A151907 (n + d) := by
  intro h
  rcases Nat.lt_or_ge d 2 with hd | hd
  · interval_cases d
    · exact conjecture_false fun n => h n
    · exact shiftedConjecture_false fun n => h n
  · have h0 : a (2 * 0 + 1) = A151907 (0 + d) := h 0
    have ha1 : a (2 * 0 + 1) = 1 := by decide
    have h2 : A151907 2 = 5 := by decide
    have hmono : A151907 2 ≤ A151907 (0 + d) := A151907_mono (by omega)
    omega

end Candidates.A373226Refutation
