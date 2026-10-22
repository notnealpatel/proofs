/-
# Bergot's bordered Delannoy array (A026002)

Source: J. M. Bergot's OEIS A026002 comment (Apr 24 2013).
The array has border `m(n,1) = m(1,n) = n(n-1)+1` and the Delannoy recurrence.
For positive indices, `2m(i,j) = D(i-1,j+1)+D(i+1,j-1)`.
Consequently `m(n,n) = D(n-1,n+1)` for `n ≥ 1`, the offset-1 A026002 term
(`a(1)=1`, `a(2)=7`). Here `D` is the square Delannoy array with border 1.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A026002DelannoyBergot

/-- The square Delannoy array: `D(a,0) = D(0,b) = 1` and
`D(a+1,b+1) = D(a,b+1) + D(a+1,b) + D(a,b)` (OEIS A008288 as a square array). -/
def delannoy : ℕ → ℕ → ℕ
  | 0, _ => 1
  | _ + 1, 0 => 1
  | a + 1, b + 1 => delannoy a (b + 1) + delannoy (a + 1) b + delannoy a b

/-- Bergot's array, 1-indexed as in the entry: `m(1,n) = m(n,1) = n(n-1)+1` and
`m(i,j) = m(i,j-1) + m(i-1,j-1) + m(i-1,j)` for `i, j ≥ 2`.  Values with an index
`0` lie outside the array and are set to `0` (junk, never used by the
statements below). -/
def bergot : ℕ → ℕ → ℕ
  | 0, _ => 0
  | _ + 1, 0 => 0
  | 1, n + 1 => (n + 1) * n + 1
  | n + 2, 1 => (n + 2) * (n + 1) + 1
  | i + 2, j + 2 => bergot (i + 2) (j + 1) + bergot (i + 1) (j + 1) + bergot (i + 1) (j + 2)

/-! ## Examples -/

/-- Central Delannoy numbers `D(n,n)` (A001850): `1, 3, 13, 63, 321`. -/
example : (List.range 5).map (fun n => delannoy n n) = [1, 3, 13, 63, 321] := by
  simp [List.range_succ, delannoy]

/-- First row/column of Bergot's array: `n(n-1)+1 = 1, 3, 7, 13, 21`. -/
example : (List.range 5).map (fun n => bergot 1 (n + 1)) = [1, 3, 7, 13, 21] ∧
    (List.range 5).map (fun n => bergot (n + 1) 1) = [1, 3, 7, 13, 21] := by
  simp [List.range_succ, bergot]

/-- The first terms of A026002 (offset 1) are `D(n-1, n+1)`. -/
example : (List.range 6).map (fun n => delannoy n (n + 2)) =
    [1, 7, 41, 231, 1289, 7183] := by
  simp [List.range_succ, delannoy]

/-- The diagonal of Bergot's array matches the first terms of A026002. -/
example : (List.range 5).map (fun n => bergot (n + 1) (n + 1)) =
    [1, 7, 41, 231, 1289] := by
  simp [List.range_succ, bergot]

/-! ## Delannoy lemmas -/

/-- The Delannoy recurrence `D(a+1,b+1) = D(a,b+1) + D(a+1,b) + D(a,b)`. -/
theorem delannoy_succ_succ (a b : ℕ) :
    delannoy (a + 1) (b + 1) = delannoy a (b + 1) + delannoy (a + 1) b + delannoy a b := by
  rw [delannoy]

/-- The Delannoy array is symmetric: `D(a,b) = D(b,a)`. -/
theorem delannoy_comm (a b : ℕ) : delannoy a b = delannoy b a := by
  induction a generalizing b with
  | zero => cases b <;> simp [delannoy]
  | succ a iha =>
    induction b with
    | zero => simp [delannoy]
    | succ b ihb =>
      rw [delannoy_succ_succ, delannoy_succ_succ, iha (b + 1), iha b, ihb]
      ring

/-- Second row of the Delannoy array: `D(1,b) = 2b + 1`. -/
theorem delannoy_one_left (b : ℕ) : delannoy 1 b = 2 * b + 1 := by
  induction b with
  | zero => simp [delannoy]
  | succ b ih =>
    rw [delannoy_succ_succ, ih]
    simp only [delannoy]
    ring

/-- Third row of the Delannoy array: `D(2,b) = 2b² + 2b + 1`. -/
theorem delannoy_two_left (b : ℕ) : delannoy 2 b = 2 * b ^ 2 + 2 * b + 1 := by
  induction b with
  | zero => simp [delannoy]
  | succ b ih =>
    rw [delannoy_succ_succ, ih, delannoy_one_left, delannoy_one_left]
    ring

/-! ## Bergot's array in closed form -/

/-- First row of Bergot's array: `m(1,n+1) = (n+1)n + 1`. -/
theorem bergot_one_left (n : ℕ) : bergot 1 (n + 1) = (n + 1) * n + 1 := by
  rw [bergot]

/-- First column of Bergot's array: `m(n+2,1) = (n+2)(n+1) + 1`. -/
theorem bergot_succ_succ_one (n : ℕ) : bergot (n + 2) 1 = (n + 2) * (n + 1) + 1 := by
  rw [bergot]

/-- Interior recurrence: `m(i+2,j+2) = m(i+2,j+1) + m(i+1,j+1) + m(i+1,j+2)`. -/
theorem bergot_succ_succ (i j : ℕ) :
    bergot (i + 2) (j + 2) =
      bergot (i + 2) (j + 1) + bergot (i + 1) (j + 1) + bergot (i + 1) (j + 2) := by
  rw [bergot]

/-- **Closed form.** For all `i, j ≥ 1`,
`2 m(i,j) = D(i-1, j+1) + D(i+1, j-1)` (stated with `i, j` shifted by one). -/
theorem two_mul_bergot (i j : ℕ) :
    2 * bergot (i + 1) (j + 1) = delannoy i (j + 2) + delannoy (i + 2) j := by
  induction i generalizing j with
  | zero =>
    rw [delannoy_two_left, bergot_one_left]
    simp only [delannoy]
    ring
  | succ i ihi =>
    induction j with
    | zero =>
      rw [delannoy_comm (i + 1) 2, delannoy_two_left, bergot_succ_succ_one]
      simp only [delannoy]
      ring
    | succ j ihj =>
      have hrec := bergot_succ_succ i j
      have h3 : 2 * bergot (i + 2) (j + 1) = delannoy (i + 1) (j + 2) + delannoy (i + 3) j := ihj
      show 2 * bergot (i + 2) (j + 2) = delannoy (i + 1) (j + 3) + delannoy (i + 3) (j + 1)
      have h1 : 2 * bergot (i + 1) (j + 1) = delannoy i (j + 2) + delannoy (i + 2) j := ihi j
      have h2 : 2 * bergot (i + 1) (j + 2) = delannoy i (j + 3) + delannoy (i + 2) (j + 1) :=
        ihi (j + 1)
      have hD1 : delannoy (i + 1) (j + 3) =
          delannoy i (j + 3) + delannoy (i + 1) (j + 2) + delannoy i (j + 2) :=
        delannoy_succ_succ i (j + 2)
      have hD2 : delannoy (i + 3) (j + 1) =
          delannoy (i + 2) (j + 1) + delannoy (i + 3) j + delannoy (i + 2) j :=
        delannoy_succ_succ (i + 2) j
      omega

/-! ## The conjecture -/

/-- **Bergot's conjecture (A026002, J. M. Bergot, Apr 24 2013), shifted form.**
For every `n : ℕ`, the diagonal entry `m(n+1,n+1)` of Bergot's array equals the
Delannoy number `D(n, n+2)`, i.e. the term `a(n+1)` of A026002. -/
theorem bergot_diag_succ (n : ℕ) : bergot (n + 1) (n + 1) = delannoy n (n + 2) := by
  have hkey := two_mul_bergot n n
  have hsymm : delannoy (n + 2) n = delannoy n (n + 2) := delannoy_comm (n + 2) n
  omega

/-- Bergot's diagonal identity for the offset-1 sequence A026002.
The guard `1 ≤ n` keeps both array indices and `n-1` in their intended domains. -/
theorem bergot_conjecture (n : ℕ) (hn : 1 ≤ n) : bergot n n = delannoy (n - 1) (n + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simpa using bergot_diag_succ k

end Candidates.A026002DelannoyBergot
