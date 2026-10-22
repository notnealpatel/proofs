/-
# Positive Pfaffians in Ferrario's class `M_6`

Davide L. Ferrario, *On Certain Pfaffians Connected with the Inverse Problem
for Collinear Central Configurations*, arXiv:2604.14827, Section 2:
Definitions `defi:T` and `defi:one-bordered`, Propositions `propo:factors` and
`propo:n6`, and Corollary `coro:mainineq`.

This module treats only `n = 6`.  A real skew matrix is recorded by its
strictly upper entries `a : ℕ → ℕ → ℝ`, read at `1 ≤ i < j ≤ 6` (the source's
1-based indexing).  `skewMat6 a` is the corresponding matrix and `pf6 a` its
first-row Pfaffian expansion; `det_skewMat6` identifies its square with the
determinant.  The class `InM` imposes positive upper entries, the source's
quadratic inequalities, and monotonicity along the first row and last column.

The proof rescales to a one-bordered matrix (`scale6_mem`, `pf6_eq_factor`),
uses the parametrization `μ(v)` (`mu6`), and bounds the pieces in the proof of
`propo:n6` (`one_le_pf6_mu`).  Two misprints in the source's displayed pieces
are corrected: in the second piece the last inner summand is `1`, not
`v₂₃ v₂₄ v₂₅`; the third piece equals
`v₁₄ v₂₅ (v₁₂ v₁₃ v₃₅ v₄₅ + v₂₄ - 1)`.  The corrected bounds follow the same
argument.

`coro_mainineq_six` gives
`(a₁₅ / (a₁₆ a₅₆))² · ∏_{j≤5} a_{j6} ≤ Pf A` on `M_6`.
Thus `pf6_pos` gives a positive Pfaffian, and `det_pos_of_skew_of_InM` gives a
positive determinant for the corresponding real skew matrix.
-/
import Mathlib

set_option autoImplicit false

namespace PolynomialClosure.CertainPfaffiansConnectedInverse

/-! ## Definitions -/

/-- The Pfaffian of the real skew `6 × 6` matrix whose strictly upper
triangular entries are `a i j` (`1 ≤ i < j ≤ 6`, paper's 1-indexing),
expanded along the first row. -/
def pf6 (a : ℕ → ℕ → ℝ) : ℝ :=
  a 1 2 * (a 3 4 * a 5 6 - a 3 5 * a 4 6 + a 3 6 * a 4 5)
  - a 1 3 * (a 2 4 * a 5 6 - a 2 5 * a 4 6 + a 2 6 * a 4 5)
  + a 1 4 * (a 2 3 * a 5 6 - a 2 5 * a 3 6 + a 2 6 * a 3 5)
  - a 1 5 * (a 2 3 * a 4 6 - a 2 4 * a 3 6 + a 2 6 * a 3 4)
  + a 1 6 * (a 2 3 * a 4 5 - a 2 4 * a 3 5 + a 2 5 * a 3 4)

/-- The real skew `6 × 6` matrix (0-indexed by `Fin 6`) whose entry in
paper position `(i, j)`, `i < j`, is `a i j`. -/
def skewMat6 (a : ℕ → ℕ → ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  fun i j => if i < j then a (i.val + 1) (j.val + 1)
    else if j < i then -a (j.val + 1) (i.val + 1) else 0

/-- Ferrario's class `M_n` (Definition `defi:T`), for the skew matrix with
upper entries `a i j`, `1 ≤ i < j ≤ n`:
(A1) positivity of the upper entries; (A2) the quadratic inequalities
`a_{i-1,j} a_{i,j+1} ≤ a_{i,j} a_{i-1,j+1}` for `2 ≤ i ≤ n-2`,
`i < j ≤ n-1`; (A3) monotonicity `a_{1,j+1} ≤ a_{1,j}` and
`a_{j,n} ≤ a_{j+1,n}` for `2 ≤ j ≤ n-2`.  (The natural-number
subtractions only shrink index ranges that are already empty for small `n`.) -/
structure InM (n : ℕ) (a : ℕ → ℕ → ℝ) : Prop where
  /-- (A1) positive. -/
  positive : ∀ i j, 1 ≤ i → i < j → j ≤ n → 0 < a i j
  /-- (A2) quadratic inequality. -/
  quadratic : ∀ i j, 2 ≤ i → i ≤ n - 2 → i < j → j ≤ n - 1 →
    a (i - 1) j * a i (j + 1) ≤ a i j * a (i - 1) (j + 1)
  /-- (A3) monotone first row and last column. -/
  monotone : ∀ j, 2 ≤ j → j ≤ n - 2 → a 1 (j + 1) ≤ a 1 j ∧ a j n ≤ a (j + 1) n

/-- Ferrario's one-bordered matrices (Definition `defi:one-bordered`):
`b_{j,n} = 1` for `1 ≤ j ≤ n-1` and `b_{1,n-1} = 1`. -/
def OneBordered (n : ℕ) (b : ℕ → ℕ → ℝ) : Prop :=
  (∀ j, 1 ≤ j → j ≤ n - 1 → b j n = 1) ∧ b 1 (n - 1) = 1

/-- The parametrization `μ(v)` of one-bordered `6 × 6` matrices by nine
variables `v_{xy}` (paper display `defi6vij`): upper entry `(i, j)` is the
product of `v_{xy}` over `x ≤ i`, `y ≥ j`, with `v_{15} = v_{j6} = 1`.
Unlisted positions (the border and junk positions) are `1`. -/
def mu6 (v12 v13 v14 v23 v24 v25 v34 v35 v45 : ℝ) : ℕ → ℕ → ℝ
  | 1, 2 => v12 * v13 * v14
  | 1, 3 => v13 * v14
  | 1, 4 => v14
  | 2, 3 => v13 * v14 * v23 * v24 * v25
  | 2, 4 => v14 * v24 * v25
  | 2, 5 => v25
  | 3, 4 => v14 * v24 * v25 * v34 * v35
  | 3, 5 => v25 * v35
  | 4, 5 => v25 * v35 * v45
  | _, _ => 1

/-- The one-bordered matrix `B` of Proposition `propo:factors` at `n = 6`:
divide row and column `j ≤ 5` by `a_{j6}`, then divide the upper-left
`5 × 5` block by `a'_{15} = a_{15} / (a_{16} a_{56})`. -/
noncomputable def scale6 (a : ℕ → ℕ → ℝ) (i j : ℕ) : ℝ :=
  if j = 6 then 1 else a i j / (a i 6 * a j 6) / (a 1 5 / (a 1 6 * a 5 6))

/-- The upper entries, in the paper's 1-indexing, of a matrix indexed by
`Fin 6`: `upper6 A i j = A (i-1) (j-1)` (read only at `1 ≤ i < j ≤ 6`). -/
def upper6 (A : Matrix (Fin 6) (Fin 6) ℝ) (i j : ℕ) : ℝ :=
  A (Fin.ofNat 6 (i - 1)) (Fin.ofNat 6 (j - 1))

/-! ## Examples -/

/-- `skewMat6 a` written out entrywise (row `i`, column `j`, 0-indexed). -/
theorem skewMat6_eq (a : ℕ → ℕ → ℝ) : skewMat6 a = !![0, a 1 2, a 1 3, a 1 4, a 1 5, a 1 6;
    -a 1 2, 0, a 2 3, a 2 4, a 2 5, a 2 6;
    -a 1 3, -a 2 3, 0, a 3 4, a 3 5, a 3 6;
    -a 1 4, -a 2 4, -a 3 4, 0, a 4 5, a 4 6;
    -a 1 5, -a 2 5, -a 3 5, -a 4 5, 0, a 5 6;
    -a 1 6, -a 2 6, -a 3 6, -a 4 6, -a 5 6, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [skewMat6]

/-- `pf6` is the Pfaffian: `det (skewMat6 a) = (pf6 a)²`. -/
theorem det_skewMat6 (a : ℕ → ℕ → ℝ) : (skewMat6 a).det = pf6 a ^ 2 := by
  rw [skewMat6_eq]
  simp only [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.submatrix_apply, Matrix.submatrix_submatrix, Function.comp_apply,
    Fin.succ_succAbove_succ, Fin.succ_succAbove_zero, Fin.zero_succAbove,
    Matrix.det_fin_zero, Fin.val_zero, Fin.val_succ, Matrix.of_apply, Matrix.cons_val_succ,
    Matrix.cons_val_zero]
  simp only [pf6]
  ring

/-- Every real skew `6 × 6` matrix is `skewMat6` of its upper entries. -/
theorem skewMat6_upper6 (A : Matrix (Fin 6) (Fin 6) ℝ) (hA : A.transpose = -A) :
    skewMat6 (upper6 A) = A := by
  have hA' : ∀ i j, A j i = -A i j := fun i j => by
    simpa using congrFun (congrFun hA i) j
  have hd : ∀ i, A i i = 0 := fun i => by linarith [hA' i i]
  have hk : ∀ k : Fin 6, Fin.ofNat 6 (k.val + 1 - 1) = k := fun k => by
    ext
    simp [Fin.ofNat, Nat.mod_eq_of_lt k.isLt]
  ext i j
  simp only [skewMat6, upper6, hk]
  split_ifs with hij hji
  · rfl
  · exact (hA' j i).symm
  · rw [le_antisymm (not_lt.mp hji) (not_lt.mp hij), hd]

/-- The paper's second example in Remark `remark:counterexamplen6`
(A1 and A3 hold, A2 fails): upper entries of the matrix with Pfaffian `-1`. -/
noncomputable def remarkEx2 : ℕ → ℕ → ℝ
  | 1, 2 => 4 | 1, 3 => 3 | 1, 4 => 2 | 2, 3 => 1 / 2 | 2, 4 => 1 | 3, 4 => 1 / 4
  | _, _ => 1

/-- The paper states the Pfaffian of its second example is `-1`. -/
example : pf6 remarkEx2 = -1 := by norm_num [pf6, remarkEx2]

/-- The second example violates (A2), as the paper says. -/
example : ¬ InM 6 remarkEx2 := by
  intro h
  have hq := h.quadratic 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [remarkEx2] at hq

/-- The paper's first example in Remark `remark:counterexamplen6`
(A1 and A2 hold, A3 fails). -/
noncomputable def remarkEx1 : ℕ → ℕ → ℝ
  | 1, 2 => 1 / 10000 | 1, 3 => 1 / 100 | 1, 4 => 1 / 10 | 1, 5 => 1 | 1, 6 => 1
  | 2, 3 => 13 / 1000 | 2, 4 => 3 / 25 | 2, 5 => 11 / 10 | 2, 6 => 1
  | 3, 4 => 11 / 50 | 3, 5 => 2 | 3, 6 => 1
  | 4, 5 => 3 | 4, 6 => 1 | 5, 6 => 1
  | _, _ => 0

/-- The paper states the Pfaffian of its first example is negative. -/
example : pf6 remarkEx1 < 0 := by norm_num [pf6, remarkEx1]

/-- `μ(1, …, 1)` is the all-ones one-bordered matrix, with Pfaffian `1`. -/
example : pf6 (mu6 1 1 1 1 1 1 1 1 1) = 1 := by norm_num [pf6, mu6]

/-- `μ` matches the paper's display `defi6vij` at a sample entry. -/
example : mu6 2 3 5 7 11 13 17 19 23 2 3 = 3 * 5 * 7 * 11 * 13 := by norm_num [mu6]

/-- The constant matrix `a_{ij} = 1` lies in `M_6`. -/
example : InM 6 (fun _ _ => 1) where
  positive := fun _ _ _ _ _ => one_pos
  quadratic := fun _ _ _ _ _ _ => le_refl _
  monotone := fun _ _ _ => ⟨le_refl _, le_refl _⟩

/-! ## The core inequality in the `v`-variables -/

/-- Proposition `propo:n6` in the `v`-parametrization: if all nine
`v_{xy} ≥ 1`, then `Pf μ(v) ≥ 1`.  The proof splits `Pf μ(v)` into the
paper's three pieces. -/
theorem one_le_pf6_mu (v12 v13 v14 v23 v24 v25 v34 v35 v45 : ℝ)
    (h12 : 1 ≤ v12) (h13 : 1 ≤ v13) (h14 : 1 ≤ v14) (h23 : 1 ≤ v23) (h24 : 1 ≤ v24)
    (h25 : 1 ≤ v25) (h34 : 1 ≤ v34) (h35 : 1 ≤ v35) (h45 : 1 ≤ v45) :
    1 ≤ pf6 (mu6 v12 v13 v14 v23 v24 v25 v34 v35 v45) := by
  simp only [pf6, mu6]
  have hX : 1 ≤ v13 * v45 := one_le_mul_of_one_le_of_one_le h13 h45
  have hY : 1 ≤ v24 * v25 := one_le_mul_of_one_le_of_one_le h24 h25
  have hZ : 1 ≤ v12 * v35 := one_le_mul_of_one_le_of_one_le h12 h35
  have hW : 1 ≤ v14 * v24 := one_le_mul_of_one_le_of_one_le h14 h24
  -- first piece: `X Y v₂₃ - Y - X + 1 ≥ (X - 1)(Y - 1) ≥ 0`
  have hin1 : 0 ≤ v13 * v23 * v24 * v25 * v45 - v24 * v25 - v13 * v45 + 1 := by
    have hXY : 0 ≤ (v13 * v45 - 1) * (v24 * v25 - 1) := by
      apply mul_nonneg <;> linarith
    have hv : v13 * v45 * (v24 * v25) ≤ v13 * v45 * (v24 * v25) * v23 :=
      le_mul_of_one_le_right (by positivity) h23
    nlinarith
  -- second piece: `Z W v₃₄ - W - Z + 1 ≥ (Z - 1)(W - 1) ≥ 0`
  have hin2 : 0 ≤ v12 * v14 * v24 * v34 * v35 - v14 * v24 - v12 * v35 + 1 := by
    have hZW : 0 ≤ (v12 * v35 - 1) * (v14 * v24 - 1) := by
      apply mul_nonneg <;> linarith
    have hv : v12 * v35 * (v14 * v24) ≤ v12 * v35 * (v14 * v24) * v34 :=
      le_mul_of_one_le_right (by positivity) h34
    nlinarith
  -- third piece
  have hin3 : 1 ≤ v12 * v13 * v35 * v45 + v24 - 1 := by
    have hp : 1 ≤ v12 * v13 * (v35 * v45) :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h12 h13)
        (one_le_mul_of_one_le_of_one_le h35 h45)
    nlinarith
  have hkey : v12 * v13 * v14 * (v14 * v24 * v25 * v34 * v35 * 1 - v25 * v35 * 1
        + 1 * (v25 * v35 * v45))
      - v13 * v14 * (v14 * v24 * v25 * 1 - v25 * 1 + 1 * (v25 * v35 * v45))
      + v14 * (v13 * v14 * v23 * v24 * v25 * 1 - v25 * 1 + 1 * (v25 * v35))
      - 1 * (v13 * v14 * v23 * v24 * v25 * 1 - v14 * v24 * v25 * 1
        + 1 * (v14 * v24 * v25 * v34 * v35))
      + 1 * (v13 * v14 * v23 * v24 * v25 * (v25 * v35 * v45) - v14 * v24 * v25 * (v25 * v35)
        + v25 * (v14 * v24 * v25 * v34 * v35))
      = v14 * v25 * v35 * (v13 * v23 * v24 * v25 * v45 - v24 * v25 - v13 * v45 + 1)
        + (v25 - 1) * (v14 * v24 * v25 * v34 * v35)
        + v13 * v14 * v25 * (v12 * v14 * v24 * v34 * v35 - v14 * v24 - v12 * v35 + 1)
        + (v14 - 1) * (v13 * v14 * v23 * v24 * v25)
        + v14 * v25 * (v12 * v13 * v35 * v45 + v24 - 1) := by ring
  rw [hkey]
  have hp1 : 0 ≤ v14 * v25 * v35 * (v13 * v23 * v24 * v25 * v45 - v24 * v25 - v13 * v45 + 1) :=
    mul_nonneg (by positivity) hin1
  have hp2 : 0 ≤ (v25 - 1) * (v14 * v24 * v25 * v34 * v35) :=
    mul_nonneg (by linarith) (by positivity)
  have hp3 : 0 ≤ v13 * v14 * v25 * (v12 * v14 * v24 * v34 * v35 - v14 * v24 - v12 * v35 + 1) :=
    mul_nonneg (by positivity) hin2
  have hp4 : 0 ≤ (v14 - 1) * (v13 * v14 * v23 * v24 * v25) :=
    mul_nonneg (by linarith) (by positivity)
  have hp5 : 1 ≤ v14 * v25 * (v12 * v13 * v35 * v45 + v24 - 1) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h14 h25) hin3
  linarith

/-! ## From one-bordered matrices to the `v`-variables -/

/-- Proposition `propo:n6` from the specific instances of (A1)–(A3) it uses:
for a one-bordered `b`, set `v_{xy}` as in the proof of `propo:vij`
(ratios along the first row and last inner column, cross-ratios inside);
these are `≥ 1` and `b = μ(v)` on the upper triangle. -/
theorem one_le_pf6_of_core (b : ℕ → ℕ → ℝ)
    (h16 : b 1 6 = 1) (h26 : b 2 6 = 1) (h36 : b 3 6 = 1) (h46 : b 4 6 = 1) (h56 : b 5 6 = 1)
    (h15 : b 1 5 = 1)
    (p13 : 0 < b 1 3) (p14 : 0 < b 1 4) (p24 : 0 < b 2 4) (p25 : 0 < b 2 5) (p35 : 0 < b 3 5)
    (m12 : b 1 3 ≤ b 1 2) (m13 : b 1 4 ≤ b 1 3) (m14 : 1 ≤ b 1 4)
    (q23 : b 1 3 * b 2 4 ≤ b 2 3 * b 1 4) (q24 : b 1 4 * b 2 5 ≤ b 2 4)
    (q25 : 1 ≤ b 2 5) (q34 : b 2 4 * b 3 5 ≤ b 3 4 * b 2 5) (q35 : b 2 5 ≤ b 3 5)
    (q45 : b 3 5 ≤ b 4 5) :
    1 ≤ pf6 b := by
  calc 1 ≤ pf6 (mu6 (b 1 2 / b 1 3) (b 1 3 / b 1 4) (b 1 4) (b 2 3 * b 1 4 / (b 1 3 * b 2 4))
        (b 2 4 / (b 1 4 * b 2 5)) (b 2 5) (b 3 4 * b 2 5 / (b 2 4 * b 3 5)) (b 3 5 / b 2 5)
        (b 4 5 / b 3 5)) := by
        apply one_le_pf6_mu
        · rw [one_le_div p13]; exact m12
        · rw [one_le_div p14]; exact m13
        · exact m14
        · rw [one_le_div (by positivity)]; exact q23
        · rw [one_le_div (by positivity)]; exact q24
        · exact q25
        · rw [one_le_div (by positivity)]; exact q34
        · rw [one_le_div p25]; exact q35
        · rw [one_le_div p35]; exact q45
    _ = pf6 b := by
        simp only [pf6, mu6]
        rw [h16, h26, h36, h46, h56, h15]
        field_simp

/-- Proposition `propo:n6` (Ferrario): every one-bordered matrix in `M_6`
has Pfaffian at least `1`. -/
theorem propo_n6 (b : ℕ → ℕ → ℝ) (hM : InM 6 b) (hB : OneBordered 6 b) : 1 ≤ pf6 b := by
  obtain ⟨hcol, h15⟩ := hB
  have hpos := hM.positive
  have hq := hM.quadratic
  have hm := hM.monotone
  have h16 := hcol 1 (by norm_num) (by norm_num)
  have h26 := hcol 2 (by norm_num) (by norm_num)
  have h36 := hcol 3 (by norm_num) (by norm_num)
  have h46 := hcol 4 (by norm_num) (by norm_num)
  have h56 := hcol 5 (by norm_num) (by norm_num)
  simp only [Nat.reduceSub] at h15
  have q23 := hq 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have q24 := hq 2 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have q25 := hq 2 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have q34 := hq 3 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have q35 := hq 3 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have q45 := hq 4 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have m2 := (hm 2 (by norm_num) (by norm_num)).1
  have m3 := (hm 3 (by norm_num) (by norm_num)).1
  have m4 := (hm 4 (by norm_num) (by norm_num)).1
  simp only [Nat.reduceSub, Nat.reduceAdd, h15, h16, h26, mul_one] at q23 q24 q25 q34 m2 m3 m4
  simp only [Nat.reduceSub, Nat.reduceAdd, h26, h36, h46, mul_one] at q35 q45
  exact one_le_pf6_of_core b h16 h26 h36 h46 h56 h15
    (hpos 1 3 (by norm_num) (by norm_num) (by norm_num))
    (hpos 1 4 (by norm_num) (by norm_num) (by norm_num))
    (hpos 2 4 (by norm_num) (by norm_num) (by norm_num))
    (hpos 2 5 (by norm_num) (by norm_num) (by norm_num))
    (hpos 3 5 (by norm_num) (by norm_num) (by norm_num))
    m2 m3 m4 q23 q24 q25 q34 q35 q45

/-! ## The factorization `propo:factors` at `n = 6` -/

/-- Pfaffian identity of Proposition `propo:factors` at `n = 6`:
`Pf A = (a₁₅ / (a₁₆ a₅₆))² · (∏_{j ≤ 5} a_{j6}) · Pf B` with `B = scale6 a`. -/
theorem pf6_eq_factor (a : ℕ → ℕ → ℝ)
    (p16 : 0 < a 1 6) (p26 : 0 < a 2 6) (p36 : 0 < a 3 6) (p46 : 0 < a 4 6) (p56 : 0 < a 5 6)
    (p15 : 0 < a 1 5) :
    pf6 a = (a 1 5 / (a 1 6 * a 5 6)) ^ 2 * (a 1 6 * a 2 6 * a 3 6 * a 4 6 * a 5 6)
      * pf6 (scale6 a) := by
  simp only [pf6, scale6, Nat.reduceEqDiff, ↓reduceIte]
  field_simp

/-- Proposition `propo:factors` at `n = 6`: if `A ∈ M_6` then the rescaled
matrix `B = scale6 a` lies in `M_6` and is one-bordered. -/
theorem scale6_mem (a : ℕ → ℕ → ℝ) (hM : InM 6 a) :
    InM 6 (scale6 a) ∧ OneBordered 6 (scale6 a) := by
  have hpos := hM.positive
  have hq := hM.quadratic
  have hm := hM.monotone
  have p16 := hpos 1 6 (by norm_num) (by norm_num) (by norm_num)
  have p26 := hpos 2 6 (by norm_num) (by norm_num) (by norm_num)
  have p36 := hpos 3 6 (by norm_num) (by norm_num) (by norm_num)
  have p46 := hpos 4 6 (by norm_num) (by norm_num) (by norm_num)
  have p56 := hpos 5 6 (by norm_num) (by norm_num) (by norm_num)
  have p15 := hpos 1 5 (by norm_num) (by norm_num) (by norm_num)
  have hc : 0 < a 1 5 / (a 1 6 * a 5 6) := by positivity
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro i j hi hij hj
    unfold scale6
    split_ifs with hj6
    · exact one_pos
    · have hij' : 0 < a i j := hpos i j hi hij hj
      have hi6 : 0 < a i 6 := hpos i 6 hi (by omega) le_rfl
      have hj6' : 0 < a j 6 := hpos j 6 (by omega) (by omega) le_rfl
      positivity
  · intro i j hi hi4 hij hj
    have hqij := hq i j hi hi4 hij hj
    simp only [Nat.reduceSub] at hi4 hj
    interval_cases i <;> interval_cases j <;> simp only [Nat.reduceSub, Nat.reduceAdd] at hqij ⊢ <;>
      simp only [scale6, Nat.reduceEqDiff, ↓reduceIte, mul_one] <;> field_simp <;> linarith
  · intro j hj hj4
    have hmj := hm j hj hj4
    simp only [Nat.reduceSub] at hj4
    have key : a 1 (j + 1) * a j 6 ≤ a 1 j * a (j + 1) 6 :=
      mul_le_mul hmj.1 hmj.2 (hpos j 6 (by omega) (by omega) le_rfl).le
        (hpos 1 j le_rfl (by omega) (by omega)).le
    refine ⟨?_, by simp only [scale6, ↓reduceIte, le_refl]⟩
    interval_cases j <;> simp only [Nat.reduceAdd] at key ⊢ <;>
      simp only [scale6, Nat.reduceEqDiff, ↓reduceIte] <;> field_simp <;> linarith
  · intro j _ _
    simp only [scale6, ↓reduceIte]
  · simp only [scale6, Nat.reduceSub, Nat.reduceEqDiff, ↓reduceIte]
    field_simp

/-! ## Main results -/

/-- Corollary `coro:mainineq` at `n = 6` (Ferrario, via Propositions
`propo:factors` and `propo:n6`): every real skew `6 × 6` matrix in `M_6`
satisfies `Pf A ≥ (a₁₅ / (a₁₆ a₅₆))² · a₁₆ a₂₆ a₃₆ a₄₆ a₅₆`. -/
theorem coro_mainineq_six (a : ℕ → ℕ → ℝ) (hM : InM 6 a) :
    (a 1 5 / (a 1 6 * a 5 6)) ^ 2 * (a 1 6 * a 2 6 * a 3 6 * a 4 6 * a 5 6) ≤ pf6 a := by
  have hpos := hM.positive
  have p16 := hpos 1 6 (by norm_num) (by norm_num) (by norm_num)
  have p26 := hpos 2 6 (by norm_num) (by norm_num) (by norm_num)
  have p36 := hpos 3 6 (by norm_num) (by norm_num) (by norm_num)
  have p46 := hpos 4 6 (by norm_num) (by norm_num) (by norm_num)
  have p56 := hpos 5 6 (by norm_num) (by norm_num) (by norm_num)
  have p15 := hpos 1 5 (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨hBM, hBB⟩ := scale6_mem a hM
  have hB : 1 ≤ pf6 (scale6 a) := propo_n6 (scale6 a) hBM hBB
  have hK : 0 < (a 1 5 / (a 1 6 * a 5 6)) ^ 2 * (a 1 6 * a 2 6 * a 3 6 * a 4 6 * a 5 6) := by
    positivity
  rw [pf6_eq_factor a p16 p26 p36 p46 p56 p15]
  exact le_mul_of_one_le_right hK.le hB

/-- Ferrario's theorem at `n = 6`: the Pfaffian of every real skew `6 × 6`
matrix in the class `M_6` (axioms A1–A3) is positive. -/
theorem pf6_pos (a : ℕ → ℕ → ℝ) (hM : InM 6 a) : 0 < pf6 a := by
  have hpos := hM.positive
  have p16 := hpos 1 6 (by norm_num) (by norm_num) (by norm_num)
  have p26 := hpos 2 6 (by norm_num) (by norm_num) (by norm_num)
  have p36 := hpos 3 6 (by norm_num) (by norm_num) (by norm_num)
  have p46 := hpos 4 6 (by norm_num) (by norm_num) (by norm_num)
  have p56 := hpos 5 6 (by norm_num) (by norm_num) (by norm_num)
  have p15 := hpos 1 5 (by norm_num) (by norm_num) (by norm_num)
  have hK : 0 < (a 1 5 / (a 1 6 * a 5 6)) ^ 2 * (a 1 6 * a 2 6 * a 3 6 * a 4 6 * a 5 6) := by
    positivity
  exact hK.trans_le (coro_mainineq_six a hM)

/-- Matrix form of Ferrario's `n = 6` theorem together with the
inverse-problem consequence: if a real skew `6 × 6` matrix `A` has upper
entries in `M_6`, then `Pf A > 0` and hence `det A = (Pf A)² > 0`. -/
theorem det_pos_of_skew_of_InM (A : Matrix (Fin 6) (Fin 6) ℝ) (hA : A.transpose = -A)
    (hM : InM 6 (upper6 A)) : 0 < A.det := by
  rw [← skewMat6_upper6 A hA, det_skewMat6]
  exact pow_pos (pf6_pos (upper6 A) hM) 2

end PolynomialClosure.CertainPfaffiansConnectedInverse
