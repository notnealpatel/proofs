/-
# Cain: the prime-field Parker conjecture (Conjecture 7.1)

## Source

Onno M. Cain, *Gaussian Integers, Rings, Finite Fields, and the Magic Square
of Squares*, arXiv:1908.03236.

* Section 1 defines a magic square of squares: nine distinct squares in a
  `3 × 3` grid whose rows, columns and both main diagonals all have the same
  sum `T`.
* Section 5: "We call a finite field -- or ring in general -- *Parker* if no
  magic square of square can be formed; that is, if no nine distinct squared
  elements can be found satisfying the constraints given in the Section 1."
* Section 7, Observation 7.1 (computation, `p < 1000`) and Conjecture 7.1
  (verbatim): "The only Parker fields of prime order are: F_2, F_3, F_5, F_7,
  F_11, F_13, F_17, F_19, F_23, F_31, F_43, F_47, and F_67."

Status in the paper: Conjecture 7.1 is **open**. Cain gives only a
probabilistic heuristic. The direction "`p ∈ L` implies Parker" is the finite
computation behind Observation 7.1. As of the 2026-10-21 triage, OEIS A308838
still lists the sequence as conjectural.

## What this file proves (2026-10-21)

* `exists_isMagicOfSquares_of_not_mem_parkerPrimes`: for every prime
  `p ∉ L`, `ZMod p` carries a magic square of nine distinct squares. This is
  the open, infinite direction of Conjecture 7.1.
* `isParker_zmod_iff`: the full conjecture,
  `IsParker (ZMod p) ↔ p ∈ L` for every prime `p`.

## Proof outline

1. `grid e x y` is the array `[[e+x, e-x-y, e+y], [e-x+y, e, e+x-y],
   [e-y, e+x+y, e-x]]`. Every line sums to `3e`. Its entries are distinct
   when no form `a x + b y` with `(a, b) ∈ gridDiffs` vanishes.
2. Large primes `p > 67`: twenty integer grids have entries `c m²`, where `c`
   is a product of the generators `-1, 2, 3, 5, 7, 11, 13`. Every offset form
   of these grids divides `67!`. Splitting on the Legendre symbols of the seven
   generators gives a 33-leaf decision tree, and each leaf uses a grid all of
   whose classes `c` are residues. This cover was found by a MILP search for
   this file. It differs from the 17-grid cover in the triage notes and does
   not need any extra prime threshold.
3. The six non-Parker primes `29, 37, 41, 53, 59, 61 ≤ 67` get explicit grids,
   checked by `decide`.
4. Converse: every magic square over a commutative ring is a grid
   (`eq_grid_of_lines`). Over `ZMod p`, rescaling by the inverse square of a
   root of the centre reduces the centre to `0` or `1`. A two-stage `decide`
   then rules out all grids for the thirteen primes of `L`.
-/
import Mathlib

set_option autoImplicit false

namespace CainMagicSquareSquaresModP

/-- A `3 × 3` array `M` over a commutative ring is a *magic square of squares*
(Cain, Section 1 and Section 5) if its nine entries are pairwise distinct
squares and the three rows, the three columns and the two main diagonals all
have one common sum `T`. -/
def IsMagicOfSquares {R : Type*} [CommRing R] (M : Fin 3 → Fin 3 → R) : Prop :=
  Function.Injective (fun ij : Fin 3 × Fin 3 => M ij.1 ij.2) ∧ (∀ i j, IsSquare (M i j)) ∧
  ∃ T, (∀ i, ∑ j, M i j = T) ∧ (∀ j, ∑ i, M i j = T) ∧
    M 0 0 + M 1 1 + M 2 2 = T ∧ M 0 2 + M 1 1 + M 2 0 = T

/-- Cain's terminology (Section 5): a ring `R` is *Parker* if it admits no magic
square of nine distinct squares. -/
def IsParker (R : Type*) [CommRing R] : Prop :=
  ¬ ∃ M : Fin 3 → Fin 3 → R, IsMagicOfSquares M

/-- The list `L` of Conjecture 7.1: the primes `p` for which Cain conjectures
that `𝔽_p` is Parker. -/
def parkerPrimes : Finset ℕ := {2, 3, 5, 7, 11, 13, 17, 19, 23, 31, 43, 47, 67}

/-- The Lucas-type grid with centre `e` and offsets `x`, `y`:
`[[e+x, e-x-y, e+y], [e-x+y, e, e+x-y], [e-y, e+x+y, e-x]]`.
Every row, column and diagonal sums to `3e`. -/
def grid {R : Type*} [CommRing R] (e x y : R) : Fin 3 → Fin 3 → R :=
  ![![e + x, e - x - y, e + y], ![e - x + y, e, e + x - y], ![e - y, e + x + y, e - x]]

/-- The integer coefficients `(a, b)` with `grid e x y i j = e + a x + b y`. -/
def gridOffset : Fin 3 → Fin 3 → ℤ × ℤ :=
  ![![(1, 0), (-1, -1), (0, 1)], ![(-1, 1), (0, 0), (1, -1)], ![(0, -1), (1, 1), (-1, 0)]]

/-- Representatives, up to sign, of the nonzero differences of two grid
offsets. -/
def gridDiffs : List (ℤ × ℤ) :=
  [(1, 0), (0, 1), (1, 1), (1, -1), (2, 0), (0, 2), (2, 1), (1, 2), (2, -1), (1, -2),
    (2, 2), (2, -2)]


/-! ## Ground truth -/

/-- `L` contains `67` but not `29`. -/
example : 67 ∈ parkerPrimes ∧ 29 ∉ parkerPrimes := by decide

/-- Cain's Section 5 example: `[[9², 11², 1²], [6², 0², 14²], [12², 16², 8²]]`
is a magic square of squares in `𝔽₂₉`, with line sum `0`. -/
example : IsMagicOfSquares (fun i j => (![![9, 11, 1], ![6, 0, 14], ![12, 16, 8]] i j) ^ 2 :
    Fin 3 → Fin 3 → ZMod 29) :=
  ⟨by decide, fun _ _ => ⟨_, sq _⟩, 0, by decide, by decide, by decide, by decide⟩

/-- Cain's Corollary 7.1 example in `𝔽₅₉`:
`[[20², 12², 7²], [2², 1², 23²], [22², 25², 29²]]`, with line sum `3`. -/
example : IsMagicOfSquares (fun i j => (![![20, 12, 7], ![2, 1, 23], ![22, 25, 29]] i j) ^ 2 :
    Fin 3 → Fin 3 → ZMod 59) :=
  ⟨by decide, fun _ _ => ⟨_, sq _⟩, 3, by decide, by decide, by decide, by decide⟩

/-- A repeated entry is not allowed: the constant grid of `1`s in `𝔽₂₉` is
magic with square entries but is not a magic square of squares. -/
example : ¬ IsMagicOfSquares (fun _ _ => 1 : Fin 3 → Fin 3 → ZMod 29) := by
  rintro ⟨hinj, -⟩
  exact absurd (hinj (a₁ := (0, 0)) (a₂ := (0, 1)) rfl) (by decide)

/-- The grid entries for `(e, x, y) = (0, 1, 5)` modulo `29`. -/
example : grid (0 : ZMod 29) 1 5 = ![![1, 23, 5], ![4, 0, 25], ![24, 6, 28]] := by
  decide

/-! ## Grids -/

/-- Two distinct grid cells have offsets differing by an element of
`gridDiffs` up to sign. -/
theorem gridOffset_sub_mem :
    ∀ a b : Fin 3 × Fin 3, a ≠ b →
      gridOffset a.1 a.2 - gridOffset b.1 b.2 ∈ gridDiffs ∨
      gridOffset b.1 b.2 - gridOffset a.1 a.2 ∈ gridDiffs := by
  decide

/-- Each grid entry is `e + a x + b y` with `(a, b)` its offset. -/
theorem grid_eq_offset {R : Type*} [CommRing R] (e x y : R) (i j : Fin 3) :
    grid e x y i j = e + ((gridOffset i j).1 : R) * x + ((gridOffset i j).2 : R) * y := by
  fin_cases i <;> fin_cases j <;> simp [grid, gridOffset] <;> ring

/-- The grid has nine distinct entries as soon as no linear form `a x + b y`
with `(a, b) ∈ gridDiffs` vanishes. -/
theorem grid_injective {R : Type*} [CommRing R] (e x y : R)
    (hd : ∀ d ∈ gridDiffs, (d.1 : R) * x + (d.2 : R) * y ≠ 0) :
    Function.Injective (fun ij : Fin 3 × Fin 3 => grid e x y ij.1 ij.2) := by
  intro a b hab
  by_contra hne
  simp only [grid_eq_offset] at hab
  rcases gridOffset_sub_mem a b hne with h | h
  · refine hd _ h ?_
    simp only [Prod.fst_sub, Prod.snd_sub, Int.cast_sub]
    linear_combination hab
  · refine hd _ h ?_
    simp only [Prod.fst_sub, Prod.snd_sub, Int.cast_sub]
    linear_combination -hab

/-- Every line of the grid sums to `3e`. -/
theorem grid_lines {R : Type*} [CommRing R] (e x y : R) :
    ∃ T, (∀ i, ∑ j, grid e x y i j = T) ∧ (∀ j, ∑ i, grid e x y i j = T) ∧
      grid e x y 0 0 + grid e x y 1 1 + grid e x y 2 2 = T ∧
      grid e x y 0 2 + grid e x y 1 1 + grid e x y 2 0 = T := by
  refine ⟨3 * e, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [grid, Fin.sum_univ_three] <;> ring
  · intro j
    fin_cases j <;> simp [grid, Fin.sum_univ_three] <;> ring
  · simp only [grid, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    ring
  · simp only [grid, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    ring

/-- A grid with distinct square entries is a magic square of squares. -/
theorem isMagicOfSquares_grid {R : Type*} [CommRing R] (e x y : R)
    (hd : ∀ d ∈ gridDiffs, (d.1 : R) * x + (d.2 : R) * y ≠ 0)
    (hsq : ∀ i j, IsSquare (grid e x y i j)) : IsMagicOfSquares (grid e x y) :=
  ⟨grid_injective e x y hd, hsq, grid_lines e x y⟩

/-- Concrete version: a grid whose entries are given squares `r i j * r i j`. -/
theorem isMagicOfSquares_grid_of_roots {R : Type*} [CommRing R] (e x y : R)
    (r : Fin 3 → Fin 3 → R)
    (hd : ∀ d ∈ gridDiffs, (d.1 : R) * x + (d.2 : R) * y ≠ 0)
    (hr : ∀ i j, grid e x y i j = r i j * r i j) : IsMagicOfSquares (grid e x y) :=
  isMagicOfSquares_grid e x y hd fun i j => ⟨r i j, hr i j⟩

section Prime

variable (p : ℕ) [Fact p.Prime]

/-- An integer all of whose prime factors are at most `67` (witnessed by
`|n| ∣ 67!`) is nonzero modulo every prime `p > 67`. -/
theorem intCast_ne_zero_of_dvd_factorial (hp : 67 < p) {n : ℤ}
    (hdvd : n.natAbs ∣ Nat.factorial 67) : (n : ZMod p) ≠ 0 := by
  intro h
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_dvd] at h
  have hpf : p ∣ Nat.factorial 67 := h.trans hdvd
  have hle : p ≤ 67 := (Nat.Prime.dvd_factorial (Fact.out : p.Prime)).mp hpf
  omega

/-- If `c` is a quadratic residue mod `p` then so is `c m²`. -/
theorem isSquare_intCast_of_legendreSym {N : ℤ} (c m : ℤ) (hN : N = c * m ^ 2)
    (hc : legendreSym p c = 1) : IsSquare (N : ZMod p) := by
  have hc0 : (c : ZMod p) ≠ 0 := by
    intro h0
    rw [(legendreSym.eq_zero_iff p c).mpr h0] at hc
    exact zero_ne_one hc
  obtain ⟨r, hr⟩ := (legendreSym.eq_one_iff p hc0).mp hc
  refine ⟨r * (m : ZMod p), ?_⟩
  rw [hN]
  push_cast
  rw [hr]
  ring

/-- A perfect square integer is a square mod `p`. -/
theorem isSquare_intCast_of_eq_sq {N : ℤ} (m : ℤ) (hN : N = m ^ 2) :
    IsSquare (N : ZMod p) :=
  ⟨(m : ZMod p), by rw [hN]; push_cast; ring⟩

/-- Integer grids: if all twelve linear forms `a x + b y` divide `67!` (so are
nonzero with all prime factors at most `67`), and all nine entries are squares mod `p`, then the
grid is a magic square of squares mod `p` for every prime `p > 67`. -/
theorem exists_magic_of_int_grid (hp : 67 < p) (e x y : ℤ)
    (hd : ∀ d ∈ gridDiffs, (d.1 * x + d.2 * y).natAbs ∣ Nat.factorial 67)
    (h00 : IsSquare ((e + x : ℤ) : ZMod p)) (h01 : IsSquare ((e - x - y : ℤ) : ZMod p))
    (h02 : IsSquare ((e + y : ℤ) : ZMod p)) (h10 : IsSquare ((e - x + y : ℤ) : ZMod p))
    (h11 : IsSquare ((e : ℤ) : ZMod p)) (h12 : IsSquare ((e + x - y : ℤ) : ZMod p))
    (h20 : IsSquare ((e - y : ℤ) : ZMod p)) (h21 : IsSquare ((e + x + y : ℤ) : ZMod p))
    (h22 : IsSquare ((e - x : ℤ) : ZMod p)) :
    ∃ M : Fin 3 → Fin 3 → ZMod p, IsMagicOfSquares M := by
  refine ⟨grid (e : ZMod p) x y, isMagicOfSquares_grid _ _ _ ?_ ?_⟩
  · intro d hdm
    have h := intCast_ne_zero_of_dvd_factorial p hp (hd d hdm)
    push_cast at h
    exact h
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [grid, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      push_cast at h00 h01 h02 h10 h11 h12 h20 h21 h22 <;> assumption


/-! ## Twenty integer grids for primes `p > 67` -/

/-- The integer grid `(e, x, y) = (0, 3, 1)` (entries [3, -4, 1, -2, 0, 2, -1, 4, -3]) is a magic
square of squares mod every prime `p > 67` at which the listed square classes
are quadratic residues. -/
theorem exists_magic_grid_0 (hp : 67 < p)
    (hc4 : legendreSym p 3 = 1)
    (hc1 : legendreSym p (-1) = 1)
    (hc3 : legendreSym p (-1) * legendreSym p 2 = 1)
    (hc2 : legendreSym p 2 = 1)
    (hc5 : legendreSym p (-1) * legendreSym p 3 = 1) :
    ∃ M : Fin 3 → Fin 3 → ZMod p, IsMagicOfSquares M :=
  exists_magic_of_int_grid p hp 0 3 1 (by decide)
    (isSquare_intCast_of_legendreSym p (3) 1 (by norm_num) hc4)
    (isSquare_intCast_of_legendreSym p ((-1)) 2 (by norm_num) hc1)
    (isSquare_intCast_of_eq_sq p 1 (by norm_num))
    (isSquare_intCast_of_legendreSym p ((-1) * 2) 1 (by norm_num)
      (by rw [legendreSym.mul]; exact hc3))
    (isSquare_intCast_of_eq_sq p 0 (by norm_num))
    (isSquare_intCast_of_legendreSym p (2) 1 (by norm_num) hc2)
    (isSquare_intCast_of_legendreSym p ((-1)) 1 (by norm_num) hc1)
    (isSquare_intCast_of_eq_sq p 2 (by norm_num))
    (isSquare_intCast_of_legendreSym p ((-1) * 3) 1 (by norm_num)
      (by rw [legendreSym.mul]; exact hc5))

/-- The integer grid `(e, x, y) = (0, 4, 3)` (entries [4, -7, 3, -1, 0, 1, -3, 7, -4]) is a magic
square of squares mod every prime `p > 67` at which the listed square classes
are quadratic residues. -/
theorem exists_magic_grid_1 (hp : 67 < p)
    (hc17 : legendreSym p (-1) * legendreSym p 7 = 1)
    (hc4 : legendreSym p 3 = 1)
    (hc1 : legendreSym p (-1) = 1)
    (hc5 : legendreSym p (-1) * legendreSym p 3 = 1)
    (hc16 : legendreSym p 7 = 1) :
    ∃ M : Fin 3 → Fin 3 → ZMod p, IsMagicOfSquares M :=
  exists_magic_of_int_grid p hp 0 4 3 (by decide)
    (isSquare_intCast_of_eq_sq p 2 (by norm_num))
    (isSquare_intCast_of_legendreSym p ((-1) * 7) 1 (by norm_num)
      (by rw [legendreSym.mul]; exact hc17))
    (isSquare_intCast_of_legendreSym p (3) 1 (by norm_num) hc4)
    (isSquare_intCast_of_legendreSym p ((-1)) 1 (by norm_num) hc1)
    (isSquare_intCast_of_eq_sq p 0 (by norm_num))
    (isSquare_intCast_of_eq_sq p 1 (by norm_num))
    (isSquare_intCast_of_legendreSym p ((-1) * 3) 1 (by norm_num)
      (by rw [legendreSym.mul]; exact hc5))
    (isSquare_intCast_of_legendreSym p (7) 1 (by norm_num) hc16)
    (isSquare_intCast_of_legendreSym p ((-1)) 2 (by norm_num) hc1)

/-- The integer grid `(e, x, y) = (0, 5, 4)` (entries [5, -9, 4, -1, 0, 1, -4, 9, -5]) is a magic
square of squares mod every prime `p > 67` at which the listed square classes
are quadratic residues. -/
theorem exists_magic_grid_2 (hp : 67 < p)
    (hc8 : legendreSym p 5 = 1)
    (hc1 : legendreSym p (-1) = 1)
    (hc9 : legendreSym p (-1) * legendreSym p 5 = 1) :
    ∃ M : Fin 3 → Fin 3 → ZMod p, IsMagicOfSquares M :=
  exists_magic_of_int_grid p hp 0 5 4 (by decide)
    (isSquare_intCast_of_legendreSym p (5) 1 (by norm_num) hc8)
    (isSquare_intCast_of_legendreSym p ((-1)) 3 (by norm_num) hc1)
    (isSquare_intCast_of_eq_sq p 2 (by norm_num))
    (isSquare_intCast_of_legendreSym p ((-1)) 1 (by norm_num) hc1)
    (isSquare_intCast_of_eq_sq p 0 (by norm_num))
    (isSquare_intCast_of_eq_sq p 1 (by norm_num))
    (isSquare_intCast_of_legendreSym p ((-1)) 2 (by norm_num) hc1)
    (isSquare_intCast_of_eq_sq p 3 (by norm_num))
    (isSquare_intCast_of_legendreSym p ((-1) * 5) 1 (by norm_num)
      (by rw [legendreSym.mul]; exact hc9))

/-- The integer grid `(e, x, y) = (1, 9, 6)` (entries [10, -14, 7, -2, 1, 4, -5, 16, -8]) is a magic
square of squares mod every prime `p > 67` at which the listed square classes
are quadratic residues. -/
theorem exists_magic_grid_3 (hp : 67 < p)
    (hc10 : legendreSym p 2 * legendreSym p 5 = 1)
    (hc19 : legendreSym p (-1) * legendreSym p 2 * legendreSym p 7 = 1)
    (hc16 : legendreSym p 7 = 1)
    (hc3 : legendreSym p (-1) * legendreSym p 2 = 1)
    (hc9 : legendreSym p (-1) * legendreSym p 5 = 1) :
    ∃ M : Fin 3 → Fin 3 → ZMod p, IsMagicOfSquares M :=
  exists_magic_of_int_grid p hp 1 9 6 (by decide)
    (isSquare_intCast_of_legendreSym p (2 * 5) 1 (by norm_num)
      (by rw [legendreSym.mul]; exact hc10))
    (isSquare_intCast_of_legendreSym p ((-1) * 2 * 7) 1 (by norm_num)
      (by rw [legendreSym.mul, legendreSym.mul]; exact hc19))
    (isSquare_intCast_of_legendreSym p (7) 1 (by norm_num) hc16)
    (isSquare_intCast_of_legendreSym p ((-1) * 2) 1 (by norm_num)
      (by rw [legendreSym.mul]; exact hc3))
    (isSquare_intCast_of_eq_sq p 1 (by norm_num))
    (isSquare_intCast_of_eq_sq p 2 (by norm_num))
    (isSquare_intCast_of_legendreSym p ((-1) * 5) 1 (by norm_num)
      (by rw [legendreSym.mul]; exact hc9))
    (isSquare_intCast_of_eq_sq p 4 (by norm_num))
    (isSquare_intCast_of_legendreSym p ((-1) * 2) 2 (by norm_num)
      (by rw [legendreSym.mul]; exact hc3))

/-- The integer grid `(e, x, y) = (0, 10, 6)` (entries [10, -16, 6, -4, 0, 4, -6, 16, -10]) is a magic
square of squares mod every prime `p > 67` at which the listed square classes
are quadratic residues. -/
theorem exists_magic_grid_4 (hp : 67 < p)
    (hc10 : legendreSym p 2 * legendreSym p 5 = 1)
    (hc1 : legendreSym p (-1) = 1)
    (hc6 : legendreSym p 2 * legendreSym p 3 = 1)
    (hc7 : legendreSym p (-1) * legendreSym p 2 * legendreSym p 3 = 1)
    (hc11 : legendreSym p (-1) * legendreSym p 2 * legendreSym p 5 = 1) :
    ∃ M : Fin 3 → Fin 3 → ZMod p, IsMagicOfSquares M :=
  exists_magic_of_int_grid p hp 0 10 6 (by decide)
    (isSquare_intCast_of_legendreSym p (2 * 5) 1 (by norm_num)
      (by rw [legendreSym.mul]; exact hc10))
    (isSquare_intCast_of_legendreSym p ((-1)) 4 (by norm_num) hc1)
    (isSquare_intCast_of_legendreSym p (2 * 3) 1 (by norm_num)
      (by rw [legendreSym.mul]; exact hc6))
    (isSquare_intCast_of_legendreSym p ((-1)) 2 (by norm_num) hc1)
    (isSquare_intCast_of_eq_sq p 0 (by norm_num))
    (isSquare_intCast_of_eq_sq p 2 (by norm_num))
    (isSquare_intCast_of_legendreSym p ((-1) * 2 * 3) 1 (by norm_num)
      (by rw [legendreSym.mul, legendreSym.mul]; exact hc7))
    (isSquare_intCast_of_eq_sq p 4 (by norm_num))
    (isSquare_intCast_of_legendreSym p ((-1) * 2 * 5) 1 (by norm_num)
      (by rw [legendreSym.mul, legendreSym.mul]; exact hc11))

/-- The integer grid `(e, x, y) = (1, 13, 2)` (entries [14, -14, 3, -10, 1, 12, -1, 16, -12]) is a magic
square of squares mod every prime `p > 67` at which the listed square classes
are quadratic residues. -/
theorem exists_magic_grid_5 (hp : 67 < p)
    (hc18 : legendreSym p 2 * legendreSym p 7 = 1)
    (hc19 : legendreSym p (-1) * legendreSym p 2 * legendreSym p 7 = 1)
    (hc4 : legendreSym p 3 = 1)
    (hc11 : legendreSym p (-1) * legendreSym p 2 * legendreSym p 5 = 1)
    (hc1 : legendreSym p (-1) = 1)
    (hc5 : legendreSym p (-1) * legendreSym p 3 = 1) :
    ∃ M : Fin 3 → Fin 3 → ZMod p, IsMagicOfSquares M :=
  exists_magic_of_int_grid p hp 1 13 2 (by decide)
    (isSquare_intCast_of_legendreSym p (2 * 7) 1 (by norm_num)
      (by rw [legendreSym.mul]; exact hc18))
    (isSquare_intCast_of_legendreSym p ((-1) * 2 * 7) 1 (by norm_num)
      (by rw [legendreSym.mul, legendreSym.mul]; exact hc19))
    (isSquare_intCast_of_legendreSym p (3) 1 (by norm_num) hc4)
    (isSquare_intCast_of_legendreSym p ((-1) * 2 * 5) 1 (by norm_num)
      (by rw [legendreSym.mul, legendreSym.mul]; exact hc11))
    (isSquare_intCast_of_eq_sq p 1 (by norm_num))
    (isSquare_intCast_of_legendreSym p (3) 2 (by norm_num) hc4)
    (isSquare_intCast_of_legendreSym p ((-1)) 1 (by norm_num) hc1)
    (isSquare_intCast_of_eq_sq p 4 (by norm_num))
    (isSquare_intCast_of_legendreSym p ((-1) * 3) 2 (by norm_num)
      (by rw [legendreSym.mul]; exact hc5))

/-- The integer grid `(e, x, y) = (8, 7, 1)` (entries [15, 0, 9, 2, 8, 14, 7, 16, 1]) is a magic
square of squares mod every prime `p > 67` at which the listed square classes
are quadratic residues. -/
theorem exists_magic_grid_6 (hp : 67 < p)
    (hc12 : legendreSym p 3 * legendreSym p 5 = 1)
    (hc2 : legendreSym p 2 = 1)
    (hc18 : legendreSym p 2 * legendreSym p 7 = 1)
    (hc16 : legendreSym p 7 = 1) :
    ∃ M : Fin 3 → Fin 3 → ZMod p, IsMagicOfSquares M :=
  exists_magic_of_int_grid p hp 8 7 1 (by decide)
    (isSquare_intCast_of_legendreSym p (3 * 5) 1 (by norm_num)
      (by rw [legendreSym.mul]; exact hc12))
    (isSquare_intCast_of_eq_sq p 0 (by norm_num))
    (isSquare_intCast_of_eq_sq p 3 (by norm_num))
    (isSquare_intCast_of_legendreSym p (2) 1 (by norm_num) hc2)
    (isSquare_intCast_of_legendreSym p (2) 2 (by norm_num) hc2)
    (isSquare_intCast_of_legendreSym p (2 * 7) 1 (by norm_num)
      (by rw [legendreSym.mul]; exact hc18))
    (isSquare_intCast_of_legendreSym p (7) 1 (by norm_num) hc16)
    (isSquare_intCast_of_eq_sq p 4 (by norm_num))
    (isSquare_intCast_of_eq_sq p 1 (by norm_num))

/-- The integer grid `(e, x, y) = (9, 7, 2)` (entries [16, 0, 11, 4, 9, 14, 7, 18, 2]) is a magic
square of squares mod every prime `p > 67` at which the listed square classes
are quadratic residues. -/
theorem exists_magic_grid_7 (hp : 67 < p)
    (hc32 : legendreSym p 11 = 1)
    (hc18 : legendreSym p 2 * legendreSym p 7 = 1)
    (hc16 : legendreSym p 7 = 1)
    (hc2 : legendreSym p 2 = 1) :
    ∃ M : Fin 3 → Fin 3 → ZMod p, IsMagicOfSquares M :=
  exists_magic_of_int_grid p hp 9 7 2 (by decide)
    (isSquare_intCast_of_eq_sq p 4 (by norm_num))
    (isSquare_intCast_of_eq_sq p 0 (by norm_num))
    (isSquare_intCast_of_legendreSym p (11) 1 (by norm_num) hc32)
    (isSquare_intCast_of_eq_sq p 2 (by norm_num))
    (isSquare_intCast_of_eq_sq p 3 (by norm_num))
    (isSquare_intCast_of_legendreSym p (2 * 7) 1 (by norm_num)
      (by rw [legendreSym.mul]; exact hc18))
    (isSquare_intCast_of_legendreSym p (7) 1 (by norm_num) hc16)
    (isSquare_intCast_of_legendreSym p (2) 3 (by norm_num) hc2)
    (isSquare_intCast_of_legendreSym p (2) 1 (by norm_num) hc2)

/-- The integer grid `(e, x, y) = (5, 11, 4)` (entries [16, -10, 9, -2, 5, 12, 1, 20, -6]) is a magic
square of squares mod every prime `p > 67` at which the listed square classes
are quadratic residues. -/
theorem exists_magic_grid_8 (hp : 67 < p)
    (hc11 : legendreSym p (-1) * legendreSym p 2 * legendreSym p 5 = 1)
    (hc3 : legendreSym p (-1) * legendreSym p 2 = 1)
    (hc8 : legendreSym p 5 = 1)
    (hc4 : legendreSym p 3 = 1)
    (hc7 : legendreSym p (-1) * legendreSym p 2 * legendreSym p 3 = 1) :
    ∃ M : Fin 3 → Fin 3 → ZMod p, IsMagicOfSquares M :=
  exists_magic_of_int_grid p hp 5 11 4 (by decide)
    (isSquare_intCast_of_eq_sq p 4 (by norm_num))
    (isSquare_intCast_of_legendreSym p ((-1) * 2 * 5) 1 (by norm_num)
      (by rw [legendreSym.mul, legendreSym.mul]; exact hc11))
    (isSquare_intCast_of_eq_sq p 3 (by norm_num))
    (isSquare_intCast_of_legendreSym p ((-1) * 2) 1 (by norm_num)
      (by rw [legendreSym.mul]; exact hc3))
    (isSquare_intCast_of_legendreSym p (5) 1 (by norm_num) hc8)
    (isSquare_intCast_of_legendreSym p (3) 2 (by norm_num) hc4)
    (isSquare_intCast_of_eq_sq p 1 (by norm_num))
    (isSquare_intCast_of_legendreSym p (5) 2 (by norm_num) hc8)
    (isSquare_intCast_of_legendreSym p ((-1) * 2 * 3) 1 (by norm_num)
      (by rw [legendreSym.mul, legendreSym.mul]; exact hc7))

/-- The integer grid `(e, x, y) = (1, 12, 9)` (entries [13, -20, 10, -2, 1, 4, -8, 22, -11]) is a magic
square of squares mod every prime `p > 67` at which the listed square classes
are quadratic residues. -/
theorem exists_magic_grid_9 (hp : 67 < p)
    (hc64 : legendreSym p 13 = 1)
    (hc9 : legendreSym p (-1) * legendreSym p 5 = 1)
    (hc10 : legendreSym p 2 * legendreSym p 5 = 1)
    (hc3 : legendreSym p (-1) * legendreSym p 2 = 1)
    (hc34 : legendreSym p 2 * legendreSym p 11 = 1)
    (hc33 : legendreSym p (-1) * legendreSym p 11 = 1) :
    ∃ M : Fin 3 → Fin 3 → ZMod p, IsMagicOfSquares M :=
  exists_magic_of_int_grid p hp 1 12 9 (by decide)
    (isSquare_intCast_of_legendreSym p (13) 1 (by norm_num) hc64)
    (isSquare_intCast_of_legendreSym p ((-1) * 5) 2 (by norm_num)
      (by rw [legendreSym.mul]; exact hc9))
    (isSquare_intCast_of_legendreSym p (2 * 5) 1 (by norm_num)
      (by rw [legendreSym.mul]; exact hc10))
    (isSquare_intCast_of_legendreSym p ((-1) * 2) 1 (by norm_num)
      (by rw [legendreSym.mul]; exact hc3))
    (isSquare_intCast_of_eq_sq p 1 (by norm_num))
    (isSquare_intCast_of_eq_sq p 2 (by norm_num))
    (isSquare_intCast_of_legendreSym p ((-1) * 2) 2 (by norm_num)
      (by rw [legendreSym.mul]; exact hc3))
    (isSquare_intCast_of_legendreSym p (2 * 11) 1 (by norm_num)
      (by rw [legendreSym.mul]; exact hc34))
    (isSquare_intCast_of_legendreSym p ((-1) * 11) 1 (by norm_num)
      (by rw [legendreSym.mul]; exact hc33))

/-- The integer grid `(e, x, y) = (5, 16, 1)` (entries [21, -12, 6, -10, 5, 20, 4, 22, -11]) is a magic
square of squares mod every prime `p > 67` at which the listed square classes
are quadratic residues. -/
theorem exists_magic_grid_10 (hp : 67 < p)
    (hc20 : legendreSym p 3 * legendreSym p 7 = 1)
    (hc5 : legendreSym p (-1) * legendreSym p 3 = 1)
    (hc6 : legendreSym p 2 * legendreSym p 3 = 1)
    (hc11 : legendreSym p (-1) * legendreSym p 2 * legendreSym p 5 = 1)
    (hc8 : legendreSym p 5 = 1)
    (hc34 : legendreSym p 2 * legendreSym p 11 = 1)
    (hc33 : legendreSym p (-1) * legendreSym p 11 = 1) :
    ∃ M : Fin 3 → Fin 3 → ZMod p, IsMagicOfSquares M :=
  exists_magic_of_int_grid p hp 5 16 1 (by decide)
    (isSquare_intCast_of_legendreSym p (3 * 7) 1 (by norm_num)
      (by rw [legendreSym.mul]; exact hc20))
    (isSquare_intCast_of_legendreSym p ((-1) * 3) 2 (by norm_num)
      (by rw [legendreSym.mul]; exact hc5))
    (isSquare_intCast_of_legendreSym p (2 * 3) 1 (by norm_num)
      (by rw [legendreSym.mul]; exact hc6))
    (isSquare_intCast_of_legendreSym p ((-1) * 2 * 5) 1 (by norm_num)
      (by rw [legendreSym.mul, legendreSym.mul]; exact hc11))
    (isSquare_intCast_of_legendreSym p (5) 1 (by norm_num) hc8)
    (isSquare_intCast_of_legendreSym p (5) 2 (by norm_num) hc8)
    (isSquare_intCast_of_eq_sq p 2 (by norm_num))
    (isSquare_intCast_of_legendreSym p (2 * 11) 1 (by norm_num)
      (by rw [legendreSym.mul]; exact hc34))
    (isSquare_intCast_of_legendreSym p ((-1) * 11) 1 (by norm_num)
      (by rw [legendreSym.mul]; exact hc33))

/-- The integer grid `(e, x, y) = (5, 19, 4)` (entries [24, -18, 9, -10, 5, 20, 1, 28, -14]) is a magic
square of squares mod every prime `p > 67` at which the listed square classes
are quadratic residues. -/
theorem exists_magic_grid_11 (hp : 67 < p)
    (hc6 : legendreSym p 2 * legendreSym p 3 = 1)
    (hc3 : legendreSym p (-1) * legendreSym p 2 = 1)
    (hc11 : legendreSym p (-1) * legendreSym p 2 * legendreSym p 5 = 1)
    (hc8 : legendreSym p 5 = 1)
    (hc16 : legendreSym p 7 = 1)
    (hc19 : legendreSym p (-1) * legendreSym p 2 * legendreSym p 7 = 1) :
    ∃ M : Fin 3 → Fin 3 → ZMod p, IsMagicOfSquares M :=
  exists_magic_of_int_grid p hp 5 19 4 (by decide)
    (isSquare_intCast_of_legendreSym p (2 * 3) 2 (by norm_num)
      (by rw [legendreSym.mul]; exact hc6))
    (isSquare_intCast_of_legendreSym p ((-1) * 2) 3 (by norm_num)
      (by rw [legendreSym.mul]; exact hc3))
    (isSquare_intCast_of_eq_sq p 3 (by norm_num))
    (isSquare_intCast_of_legendreSym p ((-1) * 2 * 5) 1 (by norm_num)
      (by rw [legendreSym.mul, legendreSym.mul]; exact hc11))
    (isSquare_intCast_of_legendreSym p (5) 1 (by norm_num) hc8)
    (isSquare_intCast_of_legendreSym p (5) 2 (by norm_num) hc8)
    (isSquare_intCast_of_eq_sq p 1 (by norm_num))
    (isSquare_intCast_of_legendreSym p (7) 2 (by norm_num) hc16)
    (isSquare_intCast_of_legendreSym p ((-1) * 2 * 7) 1 (by norm_num)
      (by rw [legendreSym.mul, legendreSym.mul]; exact hc19))

/-- The integer grid `(e, x, y) = (9, 16, 7)` (entries [25, -14, 16, 0, 9, 18, 2, 32, -7]) is a magic
square of squares mod every prime `p > 67` at which the listed square classes
are quadratic residues. -/
theorem exists_magic_grid_12 (hp : 67 < p)
    (hc19 : legendreSym p (-1) * legendreSym p 2 * legendreSym p 7 = 1)
    (hc2 : legendreSym p 2 = 1)
    (hc17 : legendreSym p (-1) * legendreSym p 7 = 1) :
    ∃ M : Fin 3 → Fin 3 → ZMod p, IsMagicOfSquares M :=
  exists_magic_of_int_grid p hp 9 16 7 (by decide)
    (isSquare_intCast_of_eq_sq p 5 (by norm_num))
    (isSquare_intCast_of_legendreSym p ((-1) * 2 * 7) 1 (by norm_num)
      (by rw [legendreSym.mul, legendreSym.mul]; exact hc19))
    (isSquare_intCast_of_eq_sq p 4 (by norm_num))
    (isSquare_intCast_of_eq_sq p 0 (by norm_num))
    (isSquare_intCast_of_eq_sq p 3 (by norm_num))
    (isSquare_intCast_of_legendreSym p (2) 3 (by norm_num) hc2)
    (isSquare_intCast_of_legendreSym p (2) 1 (by norm_num) hc2)
    (isSquare_intCast_of_legendreSym p (2) 4 (by norm_num) hc2)
    (isSquare_intCast_of_legendreSym p ((-1) * 7) 1 (by norm_num)
      (by rw [legendreSym.mul]; exact hc17))

/-- The integer grid `(e, x, y) = (-8, 17, 7)` (entries [9, -32, -1, -18, -8, 2, -15, 16, -25]) is a magic
square of squares mod every prime `p > 67` at which the listed square classes
are quadratic residues. -/
theorem exists_magic_grid_13 (hp : 67 < p)
    (hc3 : legendreSym p (-1) * legendreSym p 2 = 1)
    (hc1 : legendreSym p (-1) = 1)
    (hc2 : legendreSym p 2 = 1)
    (hc13 : legendreSym p (-1) * legendreSym p 3 * legendreSym p 5 = 1) :
    ∃ M : Fin 3 → Fin 3 → ZMod p, IsMagicOfSquares M :=
  exists_magic_of_int_grid p hp (-8) 17 7 (by decide)
    (isSquare_intCast_of_eq_sq p 3 (by norm_num))
    (isSquare_intCast_of_legendreSym p ((-1) * 2) 4 (by norm_num)
      (by rw [legendreSym.mul]; exact hc3))
    (isSquare_intCast_of_legendreSym p ((-1)) 1 (by norm_num) hc1)
    (isSquare_intCast_of_legendreSym p ((-1) * 2) 3 (by norm_num)
      (by rw [legendreSym.mul]; exact hc3))
    (isSquare_intCast_of_legendreSym p ((-1) * 2) 2 (by norm_num)
      (by rw [legendreSym.mul]; exact hc3))
    (isSquare_intCast_of_legendreSym p (2) 1 (by norm_num) hc2)
    (isSquare_intCast_of_legendreSym p ((-1) * 3 * 5) 1 (by norm_num)
      (by rw [legendreSym.mul, legendreSym.mul]; exact hc13))
    (isSquare_intCast_of_eq_sq p 4 (by norm_num))
    (isSquare_intCast_of_legendreSym p ((-1)) 5 (by norm_num) hc1)

/-- The integer grid `(e, x, y) = (-8, 19, 5)` (entries [11, -32, -3, -22, -8, 6, -13, 16, -27]) is a magic
square of squares mod every prime `p > 67` at which the listed square classes
are quadratic residues. -/
theorem exists_magic_grid_14 (hp : 67 < p)
    (hc32 : legendreSym p 11 = 1)
    (hc3 : legendreSym p (-1) * legendreSym p 2 = 1)
    (hc5 : legendreSym p (-1) * legendreSym p 3 = 1)
    (hc35 : legendreSym p (-1) * legendreSym p 2 * legendreSym p 11 = 1)
    (hc6 : legendreSym p 2 * legendreSym p 3 = 1)
    (hc65 : legendreSym p (-1) * legendreSym p 13 = 1) :
    ∃ M : Fin 3 → Fin 3 → ZMod p, IsMagicOfSquares M :=
  exists_magic_of_int_grid p hp (-8) 19 5 (by decide)
    (isSquare_intCast_of_legendreSym p (11) 1 (by norm_num) hc32)
    (isSquare_intCast_of_legendreSym p ((-1) * 2) 4 (by norm_num)
      (by rw [legendreSym.mul]; exact hc3))
    (isSquare_intCast_of_legendreSym p ((-1) * 3) 1 (by norm_num)
      (by rw [legendreSym.mul]; exact hc5))
    (isSquare_intCast_of_legendreSym p ((-1) * 2 * 11) 1 (by norm_num)
      (by rw [legendreSym.mul, legendreSym.mul]; exact hc35))
    (isSquare_intCast_of_legendreSym p ((-1) * 2) 2 (by norm_num)
      (by rw [legendreSym.mul]; exact hc3))
    (isSquare_intCast_of_legendreSym p (2 * 3) 1 (by norm_num)
      (by rw [legendreSym.mul]; exact hc6))
    (isSquare_intCast_of_legendreSym p ((-1) * 13) 1 (by norm_num)
      (by rw [legendreSym.mul]; exact hc65))
    (isSquare_intCast_of_eq_sq p 4 (by norm_num))
    (isSquare_intCast_of_legendreSym p ((-1) * 3) 3 (by norm_num)
      (by rw [legendreSym.mul]; exact hc5))

/-- The integer grid `(e, x, y) = (11, 31, 2)` (entries [42, -22, 13, -18, 11, 40, 9, 44, -20]) is a magic
square of squares mod every prime `p > 67` at which the listed square classes
are quadratic residues. -/
theorem exists_magic_grid_15 (hp : 67 < p)
    (hc22 : legendreSym p 2 * legendreSym p 3 * legendreSym p 7 = 1)
    (hc35 : legendreSym p (-1) * legendreSym p 2 * legendreSym p 11 = 1)
    (hc64 : legendreSym p 13 = 1)
    (hc3 : legendreSym p (-1) * legendreSym p 2 = 1)
    (hc32 : legendreSym p 11 = 1)
    (hc10 : legendreSym p 2 * legendreSym p 5 = 1)
    (hc9 : legendreSym p (-1) * legendreSym p 5 = 1) :
    ∃ M : Fin 3 → Fin 3 → ZMod p, IsMagicOfSquares M :=
  exists_magic_of_int_grid p hp 11 31 2 (by decide)
    (isSquare_intCast_of_legendreSym p (2 * 3 * 7) 1 (by norm_num)
      (by rw [legendreSym.mul, legendreSym.mul]; exact hc22))
    (isSquare_intCast_of_legendreSym p ((-1) * 2 * 11) 1 (by norm_num)
      (by rw [legendreSym.mul, legendreSym.mul]; exact hc35))
    (isSquare_intCast_of_legendreSym p (13) 1 (by norm_num) hc64)
    (isSquare_intCast_of_legendreSym p ((-1) * 2) 3 (by norm_num)
      (by rw [legendreSym.mul]; exact hc3))
    (isSquare_intCast_of_legendreSym p (11) 1 (by norm_num) hc32)
    (isSquare_intCast_of_legendreSym p (2 * 5) 2 (by norm_num)
      (by rw [legendreSym.mul]; exact hc10))
    (isSquare_intCast_of_eq_sq p 3 (by norm_num))
    (isSquare_intCast_of_legendreSym p (11) 2 (by norm_num) hc32)
    (isSquare_intCast_of_legendreSym p ((-1) * 5) 2 (by norm_num)
      (by rw [legendreSym.mul]; exact hc9))

/-- The integer grid `(e, x, y) = (-7, 32, 11)` (entries [25, -50, 4, -28, -7, 14, -18, 36, -39]) is a magic
square of squares mod every prime `p > 67` at which the listed square classes
are quadratic residues. -/
theorem exists_magic_grid_16 (hp : 67 < p)
    (hc3 : legendreSym p (-1) * legendreSym p 2 = 1)
    (hc17 : legendreSym p (-1) * legendreSym p 7 = 1)
    (hc18 : legendreSym p 2 * legendreSym p 7 = 1)
    (hc69 : legendreSym p (-1) * legendreSym p 3 * legendreSym p 13 = 1) :
    ∃ M : Fin 3 → Fin 3 → ZMod p, IsMagicOfSquares M :=
  exists_magic_of_int_grid p hp (-7) 32 11 (by decide)
    (isSquare_intCast_of_eq_sq p 5 (by norm_num))
    (isSquare_intCast_of_legendreSym p ((-1) * 2) 5 (by norm_num)
      (by rw [legendreSym.mul]; exact hc3))
    (isSquare_intCast_of_eq_sq p 2 (by norm_num))
    (isSquare_intCast_of_legendreSym p ((-1) * 7) 2 (by norm_num)
      (by rw [legendreSym.mul]; exact hc17))
    (isSquare_intCast_of_legendreSym p ((-1) * 7) 1 (by norm_num)
      (by rw [legendreSym.mul]; exact hc17))
    (isSquare_intCast_of_legendreSym p (2 * 7) 1 (by norm_num)
      (by rw [legendreSym.mul]; exact hc18))
    (isSquare_intCast_of_legendreSym p ((-1) * 2) 3 (by norm_num)
      (by rw [legendreSym.mul]; exact hc3))
    (isSquare_intCast_of_eq_sq p 6 (by norm_num))
    (isSquare_intCast_of_legendreSym p ((-1) * 3 * 13) 1 (by norm_num)
      (by rw [legendreSym.mul, legendreSym.mul]; exact hc69))

/-- The integer grid `(e, x, y) = (4, 31, 28)` (entries [35, -55, 32, 1, 4, 7, -24, 63, -27]) is a magic
square of squares mod every prime `p > 67` at which the listed square classes
are quadratic residues. -/
theorem exists_magic_grid_17 (hp : 67 < p)
    (hc24 : legendreSym p 5 * legendreSym p 7 = 1)
    (hc41 : legendreSym p (-1) * legendreSym p 5 * legendreSym p 11 = 1)
    (hc2 : legendreSym p 2 = 1)
    (hc16 : legendreSym p 7 = 1)
    (hc7 : legendreSym p (-1) * legendreSym p 2 * legendreSym p 3 = 1)
    (hc5 : legendreSym p (-1) * legendreSym p 3 = 1) :
    ∃ M : Fin 3 → Fin 3 → ZMod p, IsMagicOfSquares M :=
  exists_magic_of_int_grid p hp 4 31 28 (by decide)
    (isSquare_intCast_of_legendreSym p (5 * 7) 1 (by norm_num)
      (by rw [legendreSym.mul]; exact hc24))
    (isSquare_intCast_of_legendreSym p ((-1) * 5 * 11) 1 (by norm_num)
      (by rw [legendreSym.mul, legendreSym.mul]; exact hc41))
    (isSquare_intCast_of_legendreSym p (2) 4 (by norm_num) hc2)
    (isSquare_intCast_of_eq_sq p 1 (by norm_num))
    (isSquare_intCast_of_eq_sq p 2 (by norm_num))
    (isSquare_intCast_of_legendreSym p (7) 1 (by norm_num) hc16)
    (isSquare_intCast_of_legendreSym p ((-1) * 2 * 3) 2 (by norm_num)
      (by rw [legendreSym.mul, legendreSym.mul]; exact hc7))
    (isSquare_intCast_of_legendreSym p (7) 3 (by norm_num) hc16)
    (isSquare_intCast_of_legendreSym p ((-1) * 3) 3 (by norm_num)
      (by rw [legendreSym.mul]; exact hc5))

/-- The integer grid `(e, x, y) = (-13, 53, 14)` (entries [40, -80, 1, -52, -13, 26, -27, 54, -66]) is a magic
square of squares mod every prime `p > 67` at which the listed square classes
are quadratic residues. -/
theorem exists_magic_grid_18 (hp : 67 < p)
    (hc10 : legendreSym p 2 * legendreSym p 5 = 1)
    (hc9 : legendreSym p (-1) * legendreSym p 5 = 1)
    (hc65 : legendreSym p (-1) * legendreSym p 13 = 1)
    (hc66 : legendreSym p 2 * legendreSym p 13 = 1)
    (hc5 : legendreSym p (-1) * legendreSym p 3 = 1)
    (hc6 : legendreSym p 2 * legendreSym p 3 = 1)
    (hc39 : legendreSym p (-1) * legendreSym p 2 * legendreSym p 3 * legendreSym p 11 = 1) :
    ∃ M : Fin 3 → Fin 3 → ZMod p, IsMagicOfSquares M :=
  exists_magic_of_int_grid p hp (-13) 53 14 (by decide)
    (isSquare_intCast_of_legendreSym p (2 * 5) 2 (by norm_num)
      (by rw [legendreSym.mul]; exact hc10))
    (isSquare_intCast_of_legendreSym p ((-1) * 5) 4 (by norm_num)
      (by rw [legendreSym.mul]; exact hc9))
    (isSquare_intCast_of_eq_sq p 1 (by norm_num))
    (isSquare_intCast_of_legendreSym p ((-1) * 13) 2 (by norm_num)
      (by rw [legendreSym.mul]; exact hc65))
    (isSquare_intCast_of_legendreSym p ((-1) * 13) 1 (by norm_num)
      (by rw [legendreSym.mul]; exact hc65))
    (isSquare_intCast_of_legendreSym p (2 * 13) 1 (by norm_num)
      (by rw [legendreSym.mul]; exact hc66))
    (isSquare_intCast_of_legendreSym p ((-1) * 3) 3 (by norm_num)
      (by rw [legendreSym.mul]; exact hc5))
    (isSquare_intCast_of_legendreSym p (2 * 3) 3 (by norm_num)
      (by rw [legendreSym.mul]; exact hc6))
    (isSquare_intCast_of_legendreSym p ((-1) * 2 * 3 * 11) 1 (by norm_num)
      (by rw [legendreSym.mul, legendreSym.mul, legendreSym.mul]; exact hc39))

/-- The integer grid `(e, x, y) = (128, 161, 47)` (entries [289, -80, 175, 14, 128, 242, 81, 336, -33]) is a magic
square of squares mod every prime `p > 67` at which the listed square classes
are quadratic residues. -/
theorem exists_magic_grid_19 (hp : 67 < p)
    (hc9 : legendreSym p (-1) * legendreSym p 5 = 1)
    (hc16 : legendreSym p 7 = 1)
    (hc18 : legendreSym p 2 * legendreSym p 7 = 1)
    (hc2 : legendreSym p 2 = 1)
    (hc20 : legendreSym p 3 * legendreSym p 7 = 1)
    (hc37 : legendreSym p (-1) * legendreSym p 3 * legendreSym p 11 = 1) :
    ∃ M : Fin 3 → Fin 3 → ZMod p, IsMagicOfSquares M :=
  exists_magic_of_int_grid p hp 128 161 47 (by decide)
    (isSquare_intCast_of_eq_sq p 17 (by norm_num))
    (isSquare_intCast_of_legendreSym p ((-1) * 5) 4 (by norm_num)
      (by rw [legendreSym.mul]; exact hc9))
    (isSquare_intCast_of_legendreSym p (7) 5 (by norm_num) hc16)
    (isSquare_intCast_of_legendreSym p (2 * 7) 1 (by norm_num)
      (by rw [legendreSym.mul]; exact hc18))
    (isSquare_intCast_of_legendreSym p (2) 8 (by norm_num) hc2)
    (isSquare_intCast_of_legendreSym p (2) 11 (by norm_num) hc2)
    (isSquare_intCast_of_eq_sq p 9 (by norm_num))
    (isSquare_intCast_of_legendreSym p (3 * 7) 4 (by norm_num)
      (by rw [legendreSym.mul]; exact hc20))
    (isSquare_intCast_of_legendreSym p ((-1) * 3 * 11) 1 (by norm_num)
      (by rw [legendreSym.mul, legendreSym.mul]; exact hc37))
/-- **Large primes.** For every prime `p > 67` the field `ZMod p` carries a
magic square of nine distinct squares. The proof splits on the quadratic
characters of `-1, 2, 3, 5, 7, 11, 13` modulo `p` (33 leaves) and in each leaf
applies one of twenty explicit integer grids. -/
theorem exists_magic_of_67_lt (hp : 67 < p) :
    ∃ M : Fin 3 → Fin 3 → ZMod p, IsMagicOfSquares M := by
  have dm1 := legendreSym.eq_one_or_neg_one p (a := -1)
    (intCast_ne_zero_of_dvd_factorial p hp (by decide))
  have d2 := legendreSym.eq_one_or_neg_one p (a := 2)
    (intCast_ne_zero_of_dvd_factorial p hp (by decide))
  have d3 := legendreSym.eq_one_or_neg_one p (a := 3)
    (intCast_ne_zero_of_dvd_factorial p hp (by decide))
  have d5 := legendreSym.eq_one_or_neg_one p (a := 5)
    (intCast_ne_zero_of_dvd_factorial p hp (by decide))
  have d7 := legendreSym.eq_one_or_neg_one p (a := 7)
    (intCast_ne_zero_of_dvd_factorial p hp (by decide))
  have d11 := legendreSym.eq_one_or_neg_one p (a := 11)
    (intCast_ne_zero_of_dvd_factorial p hp (by decide))
  have d13 := legendreSym.eq_one_or_neg_one p (a := 13)
    (intCast_ne_zero_of_dvd_factorial p hp (by decide))
  rcases dm1 with hm1 | hm1
  · rcases d2 with h2 | h2
    · rcases d3 with h3 | h3
      · exact exists_magic_grid_0 p hp (by norm_num [h3]) (by norm_num [hm1]) (by norm_num [hm1, h2]) (by norm_num [h2]) (by norm_num [hm1, h3])
      · rcases d5 with h5 | h5
        · exact exists_magic_grid_2 p hp (by norm_num [h5]) (by norm_num [hm1]) (by norm_num [hm1, h5])
        · exact exists_magic_grid_13 p hp (by norm_num [hm1, h2]) (by norm_num [hm1]) (by norm_num [h2]) (by norm_num [hm1, h3, h5])
    · rcases d3 with h3 | h3
      · rcases d5 with h5 | h5
        · exact exists_magic_grid_2 p hp (by norm_num [h5]) (by norm_num [hm1]) (by norm_num [hm1, h5])
        · rcases d7 with h7 | h7
          · exact exists_magic_grid_1 p hp (by norm_num [hm1, h7]) (by norm_num [h3]) (by norm_num [hm1]) (by norm_num [hm1, h3]) (by norm_num [h7])
          · exact exists_magic_grid_5 p hp (by norm_num [h2, h7]) (by norm_num [hm1, h2, h7]) (by norm_num [h3]) (by norm_num [hm1, h2, h5]) (by norm_num [hm1]) (by norm_num [hm1, h3])
      · rcases d5 with h5 | h5
        · exact exists_magic_grid_2 p hp (by norm_num [h5]) (by norm_num [hm1]) (by norm_num [hm1, h5])
        · exact exists_magic_grid_4 p hp (by norm_num [h2, h5]) (by norm_num [hm1]) (by norm_num [h2, h3]) (by norm_num [hm1, h2, h3]) (by norm_num [hm1, h2, h5])
  · rcases d2 with h2 | h2
    · rcases d3 with h3 | h3
      · rcases d5 with h5 | h5
        · rcases d7 with h7 | h7
          · exact exists_magic_grid_6 p hp (by norm_num [h3, h5]) (by norm_num [h2]) (by norm_num [h2, h7]) (by norm_num [h7])
          · exact exists_magic_grid_12 p hp (by norm_num [hm1, h2, h7]) (by norm_num [h2]) (by norm_num [hm1, h7])
        · rcases d7 with h7 | h7
          · rcases d11 with h11 | h11
            · exact exists_magic_grid_7 p hp (by norm_num [h11]) (by norm_num [h2, h7]) (by norm_num [h7]) (by norm_num [h2])
            · exact exists_magic_grid_19 p hp (by norm_num [hm1, h5]) (by norm_num [h7]) (by norm_num [h2, h7]) (by norm_num [h2]) (by norm_num [h3, h7]) (by norm_num [hm1, h3, h11])
          · exact exists_magic_grid_12 p hp (by norm_num [hm1, h2, h7]) (by norm_num [h2]) (by norm_num [hm1, h7])
      · rcases d5 with h5 | h5
        · rcases d7 with h7 | h7
          · rcases d11 with h11 | h11
            · exact exists_magic_grid_7 p hp (by norm_num [h11]) (by norm_num [h2, h7]) (by norm_num [h7]) (by norm_num [h2])
            · exact exists_magic_grid_17 p hp (by norm_num [h5, h7]) (by norm_num [hm1, h5, h11]) (by norm_num [h2]) (by norm_num [h7]) (by norm_num [hm1, h2, h3]) (by norm_num [hm1, h3])
          · exact exists_magic_grid_12 p hp (by norm_num [hm1, h2, h7]) (by norm_num [h2]) (by norm_num [hm1, h7])
        · rcases d7 with h7 | h7
          · exact exists_magic_grid_6 p hp (by norm_num [h3, h5]) (by norm_num [h2]) (by norm_num [h2, h7]) (by norm_num [h7])
          · exact exists_magic_grid_12 p hp (by norm_num [hm1, h2, h7]) (by norm_num [h2]) (by norm_num [hm1, h7])
    · rcases d3 with h3 | h3
      · rcases d5 with h5 | h5
        · exact exists_magic_grid_8 p hp (by norm_num [hm1, h2, h5]) (by norm_num [hm1, h2]) (by norm_num [h5]) (by norm_num [h3]) (by norm_num [hm1, h2, h3])
        · rcases d7 with h7 | h7
          · exact exists_magic_grid_3 p hp (by norm_num [h2, h5]) (by norm_num [hm1, h2, h7]) (by norm_num [h7]) (by norm_num [hm1, h2]) (by norm_num [hm1, h5])
          · rcases d11 with h11 | h11
            · rcases d13 with h13 | h13
              · exact exists_magic_grid_15 p hp (by norm_num [h2, h3, h7]) (by norm_num [hm1, h2, h11]) (by norm_num [h13]) (by norm_num [hm1, h2]) (by norm_num [h11]) (by norm_num [h2, h5]) (by norm_num [hm1, h5])
              · exact exists_magic_grid_16 p hp (by norm_num [hm1, h2]) (by norm_num [hm1, h7]) (by norm_num [h2, h7]) (by norm_num [hm1, h3, h13])
            · rcases d13 with h13 | h13
              · exact exists_magic_grid_9 p hp (by norm_num [h13]) (by norm_num [hm1, h5]) (by norm_num [h2, h5]) (by norm_num [hm1, h2]) (by norm_num [h2, h11]) (by norm_num [hm1, h11])
              · exact exists_magic_grid_16 p hp (by norm_num [hm1, h2]) (by norm_num [hm1, h7]) (by norm_num [h2, h7]) (by norm_num [hm1, h3, h13])
      · rcases d5 with h5 | h5
        · rcases d7 with h7 | h7
          · exact exists_magic_grid_11 p hp (by norm_num [h2, h3]) (by norm_num [hm1, h2]) (by norm_num [hm1, h2, h5]) (by norm_num [h5]) (by norm_num [h7]) (by norm_num [hm1, h2, h7])
          · rcases d11 with h11 | h11
            · rcases d13 with h13 | h13
              · exact exists_magic_grid_16 p hp (by norm_num [hm1, h2]) (by norm_num [hm1, h7]) (by norm_num [h2, h7]) (by norm_num [hm1, h3, h13])
              · exact exists_magic_grid_14 p hp (by norm_num [h11]) (by norm_num [hm1, h2]) (by norm_num [hm1, h3]) (by norm_num [hm1, h2, h11]) (by norm_num [h2, h3]) (by norm_num [hm1, h13])
            · exact exists_magic_grid_10 p hp (by norm_num [h3, h7]) (by norm_num [hm1, h3]) (by norm_num [h2, h3]) (by norm_num [hm1, h2, h5]) (by norm_num [h5]) (by norm_num [h2, h11]) (by norm_num [hm1, h11])
        · rcases d7 with h7 | h7
          · exact exists_magic_grid_3 p hp (by norm_num [h2, h5]) (by norm_num [hm1, h2, h7]) (by norm_num [h7]) (by norm_num [hm1, h2]) (by norm_num [hm1, h5])
          · rcases d11 with h11 | h11
            · rcases d13 with h13 | h13
              · exact exists_magic_grid_16 p hp (by norm_num [hm1, h2]) (by norm_num [hm1, h7]) (by norm_num [h2, h7]) (by norm_num [hm1, h3, h13])
              · exact exists_magic_grid_14 p hp (by norm_num [h11]) (by norm_num [hm1, h2]) (by norm_num [hm1, h3]) (by norm_num [hm1, h2, h11]) (by norm_num [h2, h3]) (by norm_num [hm1, h13])
            · rcases d13 with h13 | h13
              · exact exists_magic_grid_16 p hp (by norm_num [hm1, h2]) (by norm_num [hm1, h7]) (by norm_num [h2, h7]) (by norm_num [hm1, h3, h13])
              · exact exists_magic_grid_18 p hp (by norm_num [h2, h5]) (by norm_num [hm1, h5]) (by norm_num [hm1, h13]) (by norm_num [h2, h13]) (by norm_num [hm1, h3]) (by norm_num [h2, h3]) (by norm_num [hm1, h2, h3, h11])

end Prime

/-! ## The six small non-Parker primes below `67`

For `p ∈ {29, 37, 41, 53, 59, 61}` we give explicit grids `(e, x, y)` in
`ZMod p` together with square roots of the nine entries; everything is
checked by `decide`. -/

/-- `𝔽₂₉` is non-Parker: the grid `(e, x, y) = (0, 1, 5)`. -/
theorem isMagicOfSquares_grid_29 : IsMagicOfSquares (grid (0 : ZMod 29) 1 5) :=
  isMagicOfSquares_grid_of_roots _ _ _ ![![1, 9, 11], ![2, 0, 5], ![13, 8, 12]]
    (by decide) (by decide)

/-- `𝔽₃₇` is non-Parker: the grid `(e, x, y) = (0, 1, 10)`. -/
theorem isMagicOfSquares_grid_37 : IsMagicOfSquares (grid (0 : ZMod 37) 1 10) :=
  isMagicOfSquares_grid_of_roots _ _ _ ![![1, 10, 11], ![3, 0, 18], ![8, 14, 6]]
    (by decide) (by decide)

/-- `𝔽₄₁` is non-Parker: the grid `(e, x, y) = (0, 1, 9)`. -/
theorem isMagicOfSquares_grid_41 : IsMagicOfSquares (grid (0 : ZMod 41) 1 9) :=
  isMagicOfSquares_grid_of_roots _ _ _ ![![1, 20, 3], ![7, 0, 19], ![14, 16, 9]]
    (by decide) (by decide)

/-- `𝔽₅₃` is non-Parker: the grid `(e, x, y) = (0, 1, 10)`. -/
theorem isMagicOfSquares_grid_53 : IsMagicOfSquares (grid (0 : ZMod 53) 1 10) :=
  isMagicOfSquares_grid_of_roots _ _ _ ![![1, 25, 13], ![3, 0, 16], ![19, 8, 23]]
    (by decide) (by decide)

/-- `𝔽₅₉` is non-Parker: the grid `(e, x, y) = (1, 11, 14)`. -/
theorem isMagicOfSquares_grid_59 : IsMagicOfSquares (grid (1 : ZMod 59) 11 14) :=
  isMagicOfSquares_grid_of_roots _ _ _ ![![22, 25, 29], ![2, 1, 23], ![20, 12, 7]]
    (by decide) (by decide)

/-- `𝔽₆₁` is non-Parker: the grid `(e, x, y) = (0, 1, 4)`. -/
theorem isMagicOfSquares_grid_61 : IsMagicOfSquares (grid (0 : ZMod 61) 1 4) :=
  isMagicOfSquares_grid_of_roots _ _ _ ![![1, 19, 2], ![8, 0, 27], ![22, 26, 11]]
    (by decide) (by decide)

/-- **Cain, Conjecture 7.1 (non-Parker direction).** For every prime `p` not in
`L = {2, 3, 5, 7, 11, 13, 17, 19, 23, 31, 43, 47, 67}` there is a `3 × 3` magic
square of nine distinct squares in `ZMod p`. -/
theorem exists_isMagicOfSquares_of_not_mem_parkerPrimes (p : ℕ) [Fact p.Prime]
    (hL : p ∉ parkerPrimes) : ∃ M : Fin 3 → Fin 3 → ZMod p, IsMagicOfSquares M := by
  by_cases hp : 67 < p
  · exact exists_magic_of_67_lt p hp
  · have hprime : p.Prime := Fact.out
    have hle : p ≤ 67 := Nat.le_of_not_lt hp
    interval_cases p
    all_goals try exact absurd hL (by decide)
    all_goals try exact absurd hprime (by decide)
    · exact ⟨_, isMagicOfSquares_grid_29⟩
    · exact ⟨_, isMagicOfSquares_grid_37⟩
    · exact ⟨_, isMagicOfSquares_grid_41⟩
    · exact ⟨_, isMagicOfSquares_grid_53⟩
    · exact ⟨_, isMagicOfSquares_grid_59⟩
    · exact ⟨_, isMagicOfSquares_grid_61⟩

/-- **Cain, Conjecture 7.1 (non-Parker direction), Parker phrasing.** If `p` is
a prime outside `L`, then `𝔽_p = ZMod p` is not Parker. -/
theorem not_isParker_of_not_mem_parkerPrimes (p : ℕ) [Fact p.Prime]
    (hL : p ∉ parkerPrimes) : ¬ IsParker (ZMod p) :=
  fun h => h (exists_isMagicOfSquares_of_not_mem_parkerPrimes p hL)

/-! ## The Parker direction for `p ∈ L` (Cain's finite computation)

Every magic square over a commutative ring is a grid `grid e x y`
(`eq_grid_of_lines`).  Over `ZMod p` the centre `e` is a square `s²`; if
`s ≠ 0` we rescale by `s⁻²` to centre `1`.  So it suffices to rule out grids
with centre `0` or `1`, which is a finite check. -/

/-- A `3 × 3` array whose rows, columns and diagonals all sum to `T` is the
grid with centre `e = M 1 1` and offsets `x = M 0 0 - e`, `y = M 0 2 - e`. -/
theorem eq_grid_of_lines {R : Type*} [CommRing R] (M : Fin 3 → Fin 3 → R) (T : R)
    (hrow : ∀ i, ∑ j, M i j = T) (hcol : ∀ j, ∑ i, M i j = T)
    (hd1 : M 0 0 + M 1 1 + M 2 2 = T) (hd2 : M 0 2 + M 1 1 + M 2 0 = T) :
    M = grid (M 1 1) (M 0 0 - M 1 1) (M 0 2 - M 1 1) := by
  have r0 := hrow 0
  have r1 := hrow 1
  have r2 := hrow 2
  have c0 := hcol 0
  have c1 := hcol 1
  have c2 := hcol 2
  simp only [Fin.sum_univ_three] at r0 r1 r2 c0 c1 c2
  have hT : T = 3 * M 1 1 := by
    linear_combination r0 + r2 - c1 - hd1 - hd2
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp only [grid, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  all_goals first
    | ring1
    | linear_combination r0 + hT
    | linear_combination c0 - hd2
    | linear_combination r1 - c0 + hd2 + hT
    | linear_combination hd2 + hT
    | linear_combination c1 - r0
    | linear_combination hd1 + hT

/-- Every magic square of squares is a grid. -/
theorem exists_grid_of_isMagicOfSquares {R : Type*} [CommRing R]
    {M : Fin 3 → Fin 3 → R} (hM : IsMagicOfSquares M) :
    ∃ e x y : R, IsMagicOfSquares (grid e x y) := by
  obtain ⟨T, hrow, hcol, hd1, hd2⟩ := hM.2.2
  refine ⟨M 1 1, M 0 0 - M 1 1, M 0 2 - M 1 1, ?_⟩
  rw [← eq_grid_of_lines M T hrow hcol hd1 hd2]
  exact hM

/-- `NoSquareGrid QR e`: no grid with centre `e` has its nine entries in `QR`
and its twelve offset differences nonzero. -/
def NoSquareGrid {R : Type*} [CommRing R] (QR : Finset R) (e : R) : Prop :=
  ∀ x y : R, e + x ∈ QR → e - x ∈ QR → e + y ∈ QR → e - y ∈ QR → e - x - y ∈ QR →
    e - x + y ∈ QR → e + x - y ∈ QR → e + x + y ∈ QR → x ≠ 0 → y ≠ 0 → x + y ≠ 0 →
    x - y ≠ 0 → 2 * x + y ≠ 0 → x + 2 * y ≠ 0 → 2 * x - y ≠ 0 → x - 2 * y ≠ 0 → False

/-- Two-stage finite check for `NoSquareGrid`: first restrict `x` (and `y`) to
an explicit list of offsets, then check all pairs from that list. -/
theorem noSquareGrid_of_offsets {R : Type*} [CommRing R] (QR : Finset R) (e : R)
    (X : List R) (hA : ∀ x : R, e + x ∈ QR → e - x ∈ QR → x ∈ X)
    (hB : ∀ x ∈ X, ∀ y ∈ X, e - x - y ∈ QR → e - x + y ∈ QR → e + x - y ∈ QR →
      e + x + y ∈ QR → x ≠ 0 → y ≠ 0 → x + y ≠ 0 → x - y ≠ 0 → 2 * x + y ≠ 0 →
      x + 2 * y ≠ 0 → 2 * x - y ≠ 0 → x - 2 * y ≠ 0 → False) :
    NoSquareGrid QR e :=
  fun x y h1 h2 h3 h4 => hB x (hA x h1 h2) y (hA y h3 h4)

/-- The twelve offset differences of an injective grid are nonzero. -/
theorem forms_ne_zero_of_injective {R : Type*} [CommRing R] {e x y : R}
    (hinj : Function.Injective (fun ij : Fin 3 × Fin 3 => grid e x y ij.1 ij.2)) :
    x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 ∧ x - y ≠ 0 ∧ 2 * x + y ≠ 0 ∧ x + 2 * y ≠ 0 ∧
      2 * x - y ≠ 0 ∧ x - 2 * y ≠ 0 := by
  have n00_11 := hinj.ne (show ((0 : Fin 3), (0 : Fin 3)) ≠ (1, 1) by decide)
  have n02_11 := hinj.ne (show ((0 : Fin 3), (2 : Fin 3)) ≠ (1, 1) by decide)
  have n21_11 := hinj.ne (show ((2 : Fin 3), (1 : Fin 3)) ≠ (1, 1) by decide)
  have n12_11 := hinj.ne (show ((1 : Fin 3), (2 : Fin 3)) ≠ (1, 1) by decide)
  have n00_01 := hinj.ne (show ((0 : Fin 3), (0 : Fin 3)) ≠ (0, 1) by decide)
  have n02_01 := hinj.ne (show ((0 : Fin 3), (2 : Fin 3)) ≠ (0, 1) by decide)
  have n00_10 := hinj.ne (show ((0 : Fin 3), (0 : Fin 3)) ≠ (1, 0) by decide)
  have n12_02 := hinj.ne (show ((1 : Fin 3), (2 : Fin 3)) ≠ (0, 2) by decide)
  simp only [grid, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    at n00_11 n02_11 n21_11 n12_11 n00_01 n02_01 n00_10 n12_02
  refine ⟨fun h => n00_11 ?_, fun h => n02_11 ?_, fun h => n21_11 ?_, fun h => n12_11 ?_,
    fun h => n00_01 ?_, fun h => n02_01 ?_, fun h => n00_10 ?_, fun h => n12_02 ?_⟩ <;>
    linear_combination h

section Converse

variable {p : ℕ}

/-- If `QR ⊇` all squares of `ZMod p` and no grid with centre `0` or `1` has
all entries in `QR`, then `𝔽_p` is Parker. -/
theorem isParker_of_noSquareGrid (hp : p.Prime) (QR : Finset (ZMod p)) (hQR : ∀ r : ZMod p, r * r ∈ QR)
    (h0 : NoSquareGrid QR 0) (h1 : NoSquareGrid QR 1) : IsParker (ZMod p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rintro ⟨M, hM⟩
  obtain ⟨e, x, y, hinj, hsq, -⟩ := exists_grid_of_isMagicOfSquares hM
  obtain ⟨fx, fy, fxy, fxy', f1, f2, f3, f4⟩ := forms_ne_zero_of_injective hinj
  have mem : ∀ a : ZMod p, IsSquare a → a ∈ QR := by
    rintro a ⟨r, rfl⟩
    exact hQR r
  have s00 := hsq 0 0
  have s01 := hsq 0 1
  have s02 := hsq 0 2
  have s10 := hsq 1 0
  have s11 := hsq 1 1
  have s12 := hsq 1 2
  have s20 := hsq 2 0
  have s21 := hsq 2 1
  have s22 := hsq 2 2
  simp only [grid, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    at s00 s01 s02 s10 s11 s12 s20 s21 s22
  obtain ⟨s, hs⟩ := s11
  by_cases hs0 : s = 0
  · have he : e = 0 := by rw [hs, hs0, zero_mul]
    subst he
    exact h0 x y (mem _ s00) (mem _ s22) (mem _ s02) (mem _ s20) (mem _ s01) (mem _ s10)
      (mem _ s12) (mem _ s21) fx fy fxy fxy' f1 f2 f3 f4
  · set u : ZMod p := s⁻¹ * s⁻¹ with hu
    have hu0 : u ≠ 0 := mul_ne_zero (inv_ne_zero hs0) (inv_ne_zero hs0)
    have hue : u * e = 1 := by
      rw [hu, hs]
      field_simp
    have scale : ∀ a b : ZMod p, IsSquare a → b = u * a → b ∈ QR := by
      rintro a b ⟨r, rfl⟩ rfl
      have : u * (r * r) = (s⁻¹ * r) * (s⁻¹ * r) := by rw [hu]; ring
      rw [this]
      exact hQR _
    refine h1 (u * x) (u * y) (scale _ _ s00 ?_) (scale _ _ s22 ?_) (scale _ _ s02 ?_)
      (scale _ _ s20 ?_) (scale _ _ s01 ?_) (scale _ _ s10 ?_) (scale _ _ s12 ?_)
      (scale _ _ s21 ?_) (mul_ne_zero hu0 fx) (mul_ne_zero hu0 fy) ?_ ?_ ?_ ?_ ?_ ?_
    any_goals linear_combination -hue
    · rw [← mul_add]; exact mul_ne_zero hu0 fxy
    · rw [← mul_sub]; exact mul_ne_zero hu0 fxy'
    · have h : 2 * (u * x) + u * y = u * (2 * x + y) := by ring
      rw [h]; exact mul_ne_zero hu0 f1
    · have h : u * x + 2 * (u * y) = u * (x + 2 * y) := by ring
      rw [h]; exact mul_ne_zero hu0 f2
    · have h : 2 * (u * x) - u * y = u * (2 * x - y) := by ring
      rw [h]; exact mul_ne_zero hu0 f3
    · have h : u * x - 2 * (u * y) = u * (x - 2 * y) := by ring
      rw [h]; exact mul_ne_zero hu0 f4

end Converse


/-! ### Finite checks for the thirteen primes of `L` -/

/-- The quadratic residues (with `0`) modulo `2`. -/
def qr2 : Finset (ZMod 2) := {0, 1}

/-- Every square in `ZMod 2` lies in `qr2`. -/
theorem mul_self_mem_qr2 : ∀ r : ZMod 2, r * r ∈ qr2 := by
  decide

/-- The `x` with `0 + x` and `0 - x` both squares modulo `2`. -/
def offsets2_0 : List (ZMod 2) := [0, 1]

set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 4000 in
/-- No grid with centre `0` consists of nine distinct squares modulo `2`. -/
theorem noSquareGrid_2_0 : NoSquareGrid qr2 (0 : ZMod 2) :=
  noSquareGrid_of_offsets _ _ offsets2_0 (by decide) (by decide)

/-- The `x` with `1 + x` and `1 - x` both squares modulo `2`. -/
def offsets2_1 : List (ZMod 2) := [0, 1]

set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 4000 in
/-- No grid with centre `1` consists of nine distinct squares modulo `2`. -/
theorem noSquareGrid_2_1 : NoSquareGrid qr2 (1 : ZMod 2) :=
  noSquareGrid_of_offsets _ _ offsets2_1 (by decide) (by decide)

/-- `𝔽_{2}` is Parker (part of Cain's Observation 7.1). -/
theorem isParker_zmod_2 : IsParker (ZMod 2) :=
  isParker_of_noSquareGrid (by norm_num) qr2 mul_self_mem_qr2 noSquareGrid_2_0 noSquareGrid_2_1

/-- The quadratic residues (with `0`) modulo `3`. -/
def qr3 : Finset (ZMod 3) := {0, 1}

/-- Every square in `ZMod 3` lies in `qr3`. -/
theorem mul_self_mem_qr3 : ∀ r : ZMod 3, r * r ∈ qr3 := by
  decide

/-- The `x` with `0 + x` and `0 - x` both squares modulo `3`. -/
def offsets3_0 : List (ZMod 3) := [0]

set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 4000 in
/-- No grid with centre `0` consists of nine distinct squares modulo `3`. -/
theorem noSquareGrid_3_0 : NoSquareGrid qr3 (0 : ZMod 3) :=
  noSquareGrid_of_offsets _ _ offsets3_0 (by decide) (by decide)

/-- The `x` with `1 + x` and `1 - x` both squares modulo `3`. -/
def offsets3_1 : List (ZMod 3) := [0]

set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 4000 in
/-- No grid with centre `1` consists of nine distinct squares modulo `3`. -/
theorem noSquareGrid_3_1 : NoSquareGrid qr3 (1 : ZMod 3) :=
  noSquareGrid_of_offsets _ _ offsets3_1 (by decide) (by decide)

/-- `𝔽_{3}` is Parker (part of Cain's Observation 7.1). -/
theorem isParker_zmod_3 : IsParker (ZMod 3) :=
  isParker_of_noSquareGrid (by norm_num) qr3 mul_self_mem_qr3 noSquareGrid_3_0 noSquareGrid_3_1

/-- The quadratic residues (with `0`) modulo `5`. -/
def qr5 : Finset (ZMod 5) := {0, 1, 4}

/-- Every square in `ZMod 5` lies in `qr5`. -/
theorem mul_self_mem_qr5 : ∀ r : ZMod 5, r * r ∈ qr5 := by
  decide

/-- The `x` with `0 + x` and `0 - x` both squares modulo `5`. -/
def offsets5_0 : List (ZMod 5) := [0, 1, 4]

set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 4000 in
/-- No grid with centre `0` consists of nine distinct squares modulo `5`. -/
theorem noSquareGrid_5_0 : NoSquareGrid qr5 (0 : ZMod 5) :=
  noSquareGrid_of_offsets _ _ offsets5_0 (by decide) (by decide)

/-- The `x` with `1 + x` and `1 - x` both squares modulo `5`. -/
def offsets5_1 : List (ZMod 5) := [0]

set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 4000 in
/-- No grid with centre `1` consists of nine distinct squares modulo `5`. -/
theorem noSquareGrid_5_1 : NoSquareGrid qr5 (1 : ZMod 5) :=
  noSquareGrid_of_offsets _ _ offsets5_1 (by decide) (by decide)

/-- `𝔽_{5}` is Parker (part of Cain's Observation 7.1). -/
theorem isParker_zmod_5 : IsParker (ZMod 5) :=
  isParker_of_noSquareGrid (by norm_num) qr5 mul_self_mem_qr5 noSquareGrid_5_0 noSquareGrid_5_1

/-- The quadratic residues (with `0`) modulo `7`. -/
def qr7 : Finset (ZMod 7) := {0, 1, 2, 4}

/-- Every square in `ZMod 7` lies in `qr7`. -/
theorem mul_self_mem_qr7 : ∀ r : ZMod 7, r * r ∈ qr7 := by
  decide

/-- The `x` with `0 + x` and `0 - x` both squares modulo `7`. -/
def offsets7_0 : List (ZMod 7) := [0]

set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 4000 in
/-- No grid with centre `0` consists of nine distinct squares modulo `7`. -/
theorem noSquareGrid_7_0 : NoSquareGrid qr7 (0 : ZMod 7) :=
  noSquareGrid_of_offsets _ _ offsets7_0 (by decide) (by decide)

/-- The `x` with `1 + x` and `1 - x` both squares modulo `7`. -/
def offsets7_1 : List (ZMod 7) := [0, 1, 6]

set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 4000 in
/-- No grid with centre `1` consists of nine distinct squares modulo `7`. -/
theorem noSquareGrid_7_1 : NoSquareGrid qr7 (1 : ZMod 7) :=
  noSquareGrid_of_offsets _ _ offsets7_1 (by decide) (by decide)

/-- `𝔽_{7}` is Parker (part of Cain's Observation 7.1). -/
theorem isParker_zmod_7 : IsParker (ZMod 7) :=
  isParker_of_noSquareGrid (by norm_num) qr7 mul_self_mem_qr7 noSquareGrid_7_0 noSquareGrid_7_1

/-- The quadratic residues (with `0`) modulo `11`. -/
def qr11 : Finset (ZMod 11) := {0, 1, 3, 4, 5, 9}

/-- Every square in `ZMod 11` lies in `qr11`. -/
theorem mul_self_mem_qr11 : ∀ r : ZMod 11, r * r ∈ qr11 := by
  decide

/-- The `x` with `0 + x` and `0 - x` both squares modulo `11`. -/
def offsets11_0 : List (ZMod 11) := [0]

set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 4000 in
/-- No grid with centre `0` consists of nine distinct squares modulo `11`. -/
theorem noSquareGrid_11_0 : NoSquareGrid qr11 (0 : ZMod 11) :=
  noSquareGrid_of_offsets _ _ offsets11_0 (by decide) (by decide)

/-- The `x` with `1 + x` and `1 - x` both squares modulo `11`. -/
def offsets11_1 : List (ZMod 11) := [0, 3, 8]

set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 4000 in
/-- No grid with centre `1` consists of nine distinct squares modulo `11`. -/
theorem noSquareGrid_11_1 : NoSquareGrid qr11 (1 : ZMod 11) :=
  noSquareGrid_of_offsets _ _ offsets11_1 (by decide) (by decide)

/-- `𝔽_{11}` is Parker (part of Cain's Observation 7.1). -/
theorem isParker_zmod_11 : IsParker (ZMod 11) :=
  isParker_of_noSquareGrid (by norm_num) qr11 mul_self_mem_qr11 noSquareGrid_11_0 noSquareGrid_11_1

/-- The quadratic residues (with `0`) modulo `13`. -/
def qr13 : Finset (ZMod 13) := {0, 1, 3, 4, 9, 10, 12}

/-- Every square in `ZMod 13` lies in `qr13`. -/
theorem mul_self_mem_qr13 : ∀ r : ZMod 13, r * r ∈ qr13 := by
  decide

/-- The `x` with `0 + x` and `0 - x` both squares modulo `13`. -/
def offsets13_0 : List (ZMod 13) := [0, 1, 3, 4, 9, 10, 12]

set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 4000 in
/-- No grid with centre `0` consists of nine distinct squares modulo `13`. -/
theorem noSquareGrid_13_0 : NoSquareGrid qr13 (0 : ZMod 13) :=
  noSquareGrid_of_offsets _ _ offsets13_0 (by decide) (by decide)

/-- The `x` with `1 + x` and `1 - x` both squares modulo `13`. -/
def offsets13_1 : List (ZMod 13) := [0, 2, 11]

set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 4000 in
/-- No grid with centre `1` consists of nine distinct squares modulo `13`. -/
theorem noSquareGrid_13_1 : NoSquareGrid qr13 (1 : ZMod 13) :=
  noSquareGrid_of_offsets _ _ offsets13_1 (by decide) (by decide)

/-- `𝔽_{13}` is Parker (part of Cain's Observation 7.1). -/
theorem isParker_zmod_13 : IsParker (ZMod 13) :=
  isParker_of_noSquareGrid (by norm_num) qr13 mul_self_mem_qr13 noSquareGrid_13_0 noSquareGrid_13_1

/-- The quadratic residues (with `0`) modulo `17`. -/
def qr17 : Finset (ZMod 17) := {0, 1, 2, 4, 8, 9, 13, 15, 16}

/-- Every square in `ZMod 17` lies in `qr17`. -/
theorem mul_self_mem_qr17 : ∀ r : ZMod 17, r * r ∈ qr17 := by
  decide

/-- The `x` with `0 + x` and `0 - x` both squares modulo `17`. -/
def offsets17_0 : List (ZMod 17) := [0, 1, 2, 4, 8, 9, 13, 15, 16]

set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 4000 in
/-- No grid with centre `0` consists of nine distinct squares modulo `17`. -/
theorem noSquareGrid_17_0 : NoSquareGrid qr17 (0 : ZMod 17) :=
  noSquareGrid_of_offsets _ _ offsets17_0 (by decide) (by decide)

/-- The `x` with `1 + x` and `1 - x` both squares modulo `17`. -/
def offsets17_1 : List (ZMod 17) := [0, 1, 3, 14, 16]

set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 4000 in
/-- No grid with centre `1` consists of nine distinct squares modulo `17`. -/
theorem noSquareGrid_17_1 : NoSquareGrid qr17 (1 : ZMod 17) :=
  noSquareGrid_of_offsets _ _ offsets17_1 (by decide) (by decide)

/-- `𝔽_{17}` is Parker (part of Cain's Observation 7.1). -/
theorem isParker_zmod_17 : IsParker (ZMod 17) :=
  isParker_of_noSquareGrid (by norm_num) qr17 mul_self_mem_qr17 noSquareGrid_17_0 noSquareGrid_17_1

/-- The quadratic residues (with `0`) modulo `19`. -/
def qr19 : Finset (ZMod 19) := {0, 1, 4, 5, 6, 7, 9, 11, 16, 17}

/-- Every square in `ZMod 19` lies in `qr19`. -/
theorem mul_self_mem_qr19 : ∀ r : ZMod 19, r * r ∈ qr19 := by
  decide

/-- The `x` with `0 + x` and `0 - x` both squares modulo `19`. -/
def offsets19_0 : List (ZMod 19) := [0]

set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 4000 in
/-- No grid with centre `0` consists of nine distinct squares modulo `19`. -/
theorem noSquareGrid_19_0 : NoSquareGrid qr19 (0 : ZMod 19) :=
  noSquareGrid_of_offsets _ _ offsets19_0 (by decide) (by decide)

/-- The `x` with `1 + x` and `1 - x` both squares modulo `19`. -/
def offsets19_1 : List (ZMod 19) := [0, 3, 4, 15, 16]

set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 4000 in
/-- No grid with centre `1` consists of nine distinct squares modulo `19`. -/
theorem noSquareGrid_19_1 : NoSquareGrid qr19 (1 : ZMod 19) :=
  noSquareGrid_of_offsets _ _ offsets19_1 (by decide) (by decide)

/-- `𝔽_{19}` is Parker (part of Cain's Observation 7.1). -/
theorem isParker_zmod_19 : IsParker (ZMod 19) :=
  isParker_of_noSquareGrid (by norm_num) qr19 mul_self_mem_qr19 noSquareGrid_19_0 noSquareGrid_19_1

/-- The quadratic residues (with `0`) modulo `23`. -/
def qr23 : Finset (ZMod 23) := {0, 1, 2, 3, 4, 6, 8, 9, 12, 13, 16, 18}

/-- Every square in `ZMod 23` lies in `qr23`. -/
theorem mul_self_mem_qr23 : ∀ r : ZMod 23, r * r ∈ qr23 := by
  decide

/-- The `x` with `0 + x` and `0 - x` both squares modulo `23`. -/
def offsets23_0 : List (ZMod 23) := [0]

set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 4000 in
/-- No grid with centre `0` consists of nine distinct squares modulo `23`. -/
theorem noSquareGrid_23_0 : NoSquareGrid qr23 (0 : ZMod 23) :=
  noSquareGrid_of_offsets _ _ offsets23_0 (by decide) (by decide)

/-- The `x` with `1 + x` and `1 - x` both squares modulo `23`. -/
def offsets23_1 : List (ZMod 23) := [0, 1, 8, 11, 12, 15, 22]

set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 4000 in
/-- No grid with centre `1` consists of nine distinct squares modulo `23`. -/
theorem noSquareGrid_23_1 : NoSquareGrid qr23 (1 : ZMod 23) :=
  noSquareGrid_of_offsets _ _ offsets23_1 (by decide) (by decide)

/-- `𝔽_{23}` is Parker (part of Cain's Observation 7.1). -/
theorem isParker_zmod_23 : IsParker (ZMod 23) :=
  isParker_of_noSquareGrid (by norm_num) qr23 mul_self_mem_qr23 noSquareGrid_23_0 noSquareGrid_23_1

/-- The quadratic residues (with `0`) modulo `31`. -/
def qr31 : Finset (ZMod 31) := {0, 1, 2, 4, 5, 7, 8, 9, 10, 14, 16, 18, 19, 20, 25, 28}

/-- Every square in `ZMod 31` lies in `qr31`. -/
theorem mul_self_mem_qr31 : ∀ r : ZMod 31, r * r ∈ qr31 := by
  decide

/-- The `x` with `0 + x` and `0 - x` both squares modulo `31`. -/
def offsets31_0 : List (ZMod 31) := [0]

set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 4000 in
/-- No grid with centre `0` consists of nine distinct squares modulo `31`. -/
theorem noSquareGrid_31_0 : NoSquareGrid qr31 (0 : ZMod 31) :=
  noSquareGrid_of_offsets _ _ offsets31_0 (by decide) (by decide)

/-- The `x` with `1 + x` and `1 - x` both squares modulo `31`. -/
def offsets31_1 : List (ZMod 31) := [0, 1, 4, 7, 13, 18, 24, 27, 30]

set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 4000 in
/-- No grid with centre `1` consists of nine distinct squares modulo `31`. -/
theorem noSquareGrid_31_1 : NoSquareGrid qr31 (1 : ZMod 31) :=
  noSquareGrid_of_offsets _ _ offsets31_1 (by decide) (by decide)

/-- `𝔽_{31}` is Parker (part of Cain's Observation 7.1). -/
theorem isParker_zmod_31 : IsParker (ZMod 31) :=
  isParker_of_noSquareGrid (by norm_num) qr31 mul_self_mem_qr31 noSquareGrid_31_0 noSquareGrid_31_1

/-- The quadratic residues (with `0`) modulo `43`. -/
def qr43 : Finset (ZMod 43) := {0, 1, 4, 6, 9, 10, 11, 13, 14, 15, 16, 17, 21, 23, 24, 25, 31, 35, 36, 38, 40, 41}

/-- Every square in `ZMod 43` lies in `qr43`. -/
theorem mul_self_mem_qr43 : ∀ r : ZMod 43, r * r ∈ qr43 := by
  decide

/-- The `x` with `0 + x` and `0 - x` both squares modulo `43`. -/
def offsets43_0 : List (ZMod 43) := [0]

set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 4000 in
/-- No grid with centre `0` consists of nine distinct squares modulo `43`. -/
theorem noSquareGrid_43_0 : NoSquareGrid qr43 (0 : ZMod 43) :=
  noSquareGrid_of_offsets _ _ offsets43_0 (by decide) (by decide)

/-- The `x` with `1 + x` and `1 - x` both squares modulo `43`. -/
def offsets43_1 : List (ZMod 43) := [0, 3, 8, 9, 13, 20, 23, 30, 34, 35, 40]

set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 4000 in
/-- No grid with centre `1` consists of nine distinct squares modulo `43`. -/
theorem noSquareGrid_43_1 : NoSquareGrid qr43 (1 : ZMod 43) :=
  noSquareGrid_of_offsets _ _ offsets43_1 (by decide) (by decide)

/-- `𝔽_{43}` is Parker (part of Cain's Observation 7.1). -/
theorem isParker_zmod_43 : IsParker (ZMod 43) :=
  isParker_of_noSquareGrid (by norm_num) qr43 mul_self_mem_qr43 noSquareGrid_43_0 noSquareGrid_43_1

/-- The quadratic residues (with `0`) modulo `47`. -/
def qr47 : Finset (ZMod 47) := {0, 1, 2, 3, 4, 6, 7, 8, 9, 12, 14, 16, 17, 18, 21, 24, 25, 27, 28, 32, 34, 36, 37, 42}

/-- Every square in `ZMod 47` lies in `qr47`. -/
theorem mul_self_mem_qr47 : ∀ r : ZMod 47, r * r ∈ qr47 := by
  decide

/-- The `x` with `0 + x` and `0 - x` both squares modulo `47`. -/
def offsets47_0 : List (ZMod 47) := [0]

set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 4000 in
/-- No grid with centre `0` consists of nine distinct squares modulo `47`. -/
theorem noSquareGrid_47_0 : NoSquareGrid qr47 (0 : ZMod 47) :=
  noSquareGrid_of_offsets _ _ offsets47_0 (by decide) (by decide)

/-- The `x` with `1 + x` and `1 - x` both squares modulo `47`. -/
def offsets47_1 : List (ZMod 47) := [0, 1, 6, 11, 16, 20, 23, 24, 27, 31, 36, 41, 46]

set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 4000 in
/-- No grid with centre `1` consists of nine distinct squares modulo `47`. -/
theorem noSquareGrid_47_1 : NoSquareGrid qr47 (1 : ZMod 47) :=
  noSquareGrid_of_offsets _ _ offsets47_1 (by decide) (by decide)

/-- `𝔽_{47}` is Parker (part of Cain's Observation 7.1). -/
theorem isParker_zmod_47 : IsParker (ZMod 47) :=
  isParker_of_noSquareGrid (by norm_num) qr47 mul_self_mem_qr47 noSquareGrid_47_0 noSquareGrid_47_1

/-- The quadratic residues (with `0`) modulo `67`. -/
def qr67 : Finset (ZMod 67) := {0, 1, 4, 6, 9, 10, 14, 15, 16, 17, 19, 21, 22, 23, 24, 25, 26, 29, 33, 35, 36, 37, 39, 40, 47, 49, 54, 55, 56, 59, 60, 62, 64, 65}

/-- Every square in `ZMod 67` lies in `qr67`. -/
theorem mul_self_mem_qr67 : ∀ r : ZMod 67, r * r ∈ qr67 := by
  decide

/-- The `x` with `0 + x` and `0 - x` both squares modulo `67`. -/
def offsets67_0 : List (ZMod 67) := [0]

set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 4000 in
/-- No grid with centre `0` consists of nine distinct squares modulo `67`. -/
theorem noSquareGrid_67_0 : NoSquareGrid qr67 (0 : ZMod 67) :=
  noSquareGrid_of_offsets _ _ offsets67_0 (by decide) (by decide)

/-- The `x` with `1 + x` and `1 - x` both squares modulo `67`. -/
def offsets67_1 : List (ZMod 67) := [0, 3, 8, 9, 13, 14, 21, 28, 32, 35, 39, 46, 53, 54, 58, 59, 64]

set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 4000 in
/-- No grid with centre `1` consists of nine distinct squares modulo `67`. -/
theorem noSquareGrid_67_1 : NoSquareGrid qr67 (1 : ZMod 67) :=
  noSquareGrid_of_offsets _ _ offsets67_1 (by decide) (by decide)

/-- `𝔽_{67}` is Parker (part of Cain's Observation 7.1). -/
theorem isParker_zmod_67 : IsParker (ZMod 67) :=
  isParker_of_noSquareGrid (by norm_num) qr67 mul_self_mem_qr67 noSquareGrid_67_0 noSquareGrid_67_1

/-- **Cain, Conjecture 7.1 (full statement).** For a prime `p`, the prime
field `𝔽_p = ZMod p` is Parker (it has no `3 × 3` magic square of nine
distinct squares) iff `p` lies in
`L = {2, 3, 5, 7, 11, 13, 17, 19, 23, 31, 43, 47, 67}`. -/
theorem isParker_zmod_iff (p : ℕ) [Fact p.Prime] : IsParker (ZMod p) ↔ p ∈ parkerPrimes := by
  constructor
  · intro h
    by_contra hL
    exact not_isParker_of_not_mem_parkerPrimes p hL h
  · intro h
    simp only [parkerPrimes, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact isParker_zmod_2
    · exact isParker_zmod_3
    · exact isParker_zmod_5
    · exact isParker_zmod_7
    · exact isParker_zmod_11
    · exact isParker_zmod_13
    · exact isParker_zmod_17
    · exact isParker_zmod_19
    · exact isParker_zmod_23
    · exact isParker_zmod_31
    · exact isParker_zmod_43
    · exact isParker_zmod_47
    · exact isParker_zmod_67

end CainMagicSquareSquaresModP
