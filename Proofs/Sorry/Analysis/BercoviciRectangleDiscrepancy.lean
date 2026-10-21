/-
# Bercovici's rectangle/square discrepancy problem: squares ≤ 1 imply rectangles ≤ 4

## Source

MathOverflow question 13820, "1 rectangle <= 4 squares",
<https://mathoverflow.net/questions/13820/1-rectangle-4-squares>, asked by
Yaakov Baruch (2010-02-02, last edited 2010-03-10).  The asker attributes the
problem to "a professor at Indiana U" (H. Bercovici).  No arXiv papers are
involved; the only further literature pointer is I. Z. Ruzsa, "The discrepancy
of rectangles and squares", Grazer Math. Ber. 318 (1992) (not read).

Verbatim informal claim (question body, re-pulled 2026-10-21 through the
StackExchange API):

> given a map $\mathbb{Z}^2\rightarrow\mathbb{R}$ such that the sum inside every
> square (parallel to the axes) is $\leq1$ in absolute value, prove that the sum
> inside every rectangle (parallel to axes) is $\leq4$ in absolute value.

Update 2 of the question sketches a proof of the bound 4 (cases (1), (2), (3)
on "big" and "small" envelopes, each multiplying the excess over 4 by -3,
iterated to a `3^n A × 3^n B` rectangle and tiled by `A·B` squares).  The
optimal constant is open in the thread: `181/48 ≤ b ≤ 254/67`.

Date of this card: 2026-10-21.  Status: **proved in the thread** (the bound 4);
this file gives a complete kernel-checked proof.

## Formalisation

* Corner form.  For `G : ℤ → ℤ → ℝ` the rectangle functional is
  `D G a b c d = G c d - G a d - G c b + G a b` (`x`-interval `[a, c]`,
  `y`-interval `[b, d]`).  A square is `D G a b (a + s) (b + s)` for an
  arbitrary integer `s` (negative `s` gives the same square up to the
  symmetry `D G a b c d = D G c d a b`).  Theorem
  `abs_rect_le_four_of_abs_square_le_one`.
* Cell form, the literal statement of the thread.  For `f : ℤ × ℤ → ℝ`, the
  sum over every box `Ico a (a + s) ×ˢ Ico b (b + s)` (`s : ℕ`) is at most 1 in
  absolute value; then the sum over every box `Ico a c ×ˢ Ico b d` is at
  most 4 in absolute value.  Theorem `abs_sum_rect_le_four_of_abs_sum_square_le_one`,
  obtained from the corner form via a signed two-dimensional prefix sum.

## Proof route

One linear identity (`rect_identity`), the composition of the thread's
cases (1) and (2), expresses the `3B × 3A` rectangle
`[x - B, x + 2B] × [y - A, y + 2A]` as `9` times the `B × A` rectangle
`[x, x + B] × [y, y + A]` plus 16 squares with coefficients `±1, ±3` of total
absolute value `32`.  It is a formal identity in the values of `G` and needs
no sign or size hypotheses on `A, B`.  Hence `|P| - 4 ≥ 9 (|R| - 4)`; iterating
gives a `3^n B × 3^n A` rectangle of excess `≥ 9^n (|R| - 4)`, while tiling it
by `B·A` squares of side `3^n` bounds it by `B·A`.  The thread's case split
(thin/fat) is not needed.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.BercoviciRectangleDiscrepancy

/-! ## Definitions and ground truth -/

/-- The rectangle functional of a corner function `G : ℤ → ℤ → ℝ`:
`D G a b c d = G c d - G a d - G c b + G a b`, the signed "sum" of `G` over the
rectangle with `x`-interval `[a, c]` and `y`-interval `[b, d]`.  When `G` is the
two-dimensional prefix sum of a cell function `f`, this is the sum of `f` over
the cells `[a, c) × [b, d)` (see `D_prefixSum2`). -/
def D (G : ℤ → ℤ → ℝ) (a b c d : ℤ) : ℝ := G c d - G a d - G c b + G a b

/-- Signed one-dimensional prefix sum of `g : ℤ → ℝ`:
`prefixSum g x = ∑_{0 ≤ i < x} g i - ∑_{x ≤ i < 0} g i`, so that
`prefixSum g c - prefixSum g a = ∑_{a ≤ i < c} g i` for `a ≤ c` (`prefixSum_sub`). -/
noncomputable def prefixSum (g : ℤ → ℝ) (x : ℤ) : ℝ :=
  ∑ i ∈ Finset.Ico 0 x, g i - ∑ i ∈ Finset.Ico x 0, g i

/-- Two-dimensional signed prefix sum of a cell function `f : ℤ × ℤ → ℝ`. -/
noncomputable def prefixSum2 (f : ℤ × ℤ → ℝ) (x y : ℤ) : ℝ :=
  prefixSum (fun i => prefixSum (fun j => f (i, j)) y) x

/-- Ground truth: for `G x y = x y` the functional `D` is the signed area. -/
example : D (fun x y => (x * y : ℝ)) 0 0 2 3 = 6 := by norm_num [D]

/-- Ground truth: reversing both intervals keeps the signed area positive. -/
example : D (fun x y => (x * y : ℝ)) 5 7 2 3 = 12 := by norm_num [D]

/-- Ground truth: the signed prefix sum of `1` at `3` is `3`. -/
example : prefixSum (fun _ => (1 : ℝ)) 3 = 3 := by simp [prefixSum]

/-- Ground truth: the signed prefix sum of `1` at `-2` is `-2`. -/
example : prefixSum (fun _ => (1 : ℝ)) (-2) = -2 := by simp [prefixSum]

/-- Ground truth: the 2D prefix sum of `1` at `(2, 3)` is `6`. -/
example : prefixSum2 (fun _ => (1 : ℝ)) 2 3 = 6 := by
  norm_num [prefixSum2, prefixSum, show Int.toNat 2 = 2 from rfl, show Int.toNat 3 = 3 from rfl]

/-- Ground truth: the 2D prefix sum of `1` at `(-1, -2)` is `2`. -/
example : prefixSum2 (fun _ => (1 : ℝ)) (-1) (-2) = 2 := by simp [prefixSum2, prefixSum]

/-- Ground truth: the indicator of the origin has prefix sum `1` at `(1, 1)`. -/
example : prefixSum2 (fun p => if p = (0, 0) then (1 : ℝ) else 0) 1 1 = 1 := by
  simp [prefixSum2, prefixSum, show Finset.Ico (0 : ℤ) 1 = {0} by decide,
    Finset.filter_singleton]

/-- Non-vacuity of the cell-form hypothesis: the indicator of the origin, a
nonzero function, has every square sum in `[-1, 1]`. -/
example : ∀ (a b : ℤ) (s : ℕ),
    |∑ p ∈ Finset.Ico a (a + s) ×ˢ Finset.Ico b (b + s),
        (if p = ((0 : ℤ), (0 : ℤ)) then (1 : ℝ) else 0)| ≤ 1 := by
  intro a b s
  rw [Finset.sum_ite_eq']
  split_ifs <;> simp

/-! ## Algebraic identities for `D` -/

/-- The composed identity (thread cases (1) and (2)): the `3B × 3A` rectangle
`[x - B, x + 2B] × [y - A, y + 2A]` equals `9` times the `B × A` rectangle
`[x, x + B] × [y, y + A]` plus 16 squares with coefficients `±1, ±3` (total
absolute coefficient `32`).  Formal in the values of `G`; no hypotheses on
`A, B`. -/
theorem rect_identity (G : ℤ → ℤ → ℝ) (x y A B : ℤ) :
    D G (x - B) (y - A) (x + 2 * B) (y + 2 * A) =
      9 * D G x y (x + B) (y + A)
      - D G (x - B) (y - B) (x - A) (y - A)
      - D G (x - B) (y + 2 * A) (x - A) (y + (B + A))
      + D G (x - B) (y - B) (x + (B + A)) (y + (B + A))
      + 3 * D G (x - A) y x (y + A)
      - 3 * D G (x - A) (y - B) (x + B) (y + A)
      - 3 * D G (x - A) y (x + B) (y + (B + A))
      + D G (x - A) (y - B) (x + (B + A)) (y + 2 * A)
      + D G (x - A) (y - A) (x + (B + A)) (y + (B + A))
      + D G (x - A) (y - B) (x + 2 * B) (y + (B + A))
      + 3 * D G x (y - B) (x + B) y
      + 3 * D G x (y + A) (x + B) (y + (B + A))
      - 3 * D G x (y - B) (x + (B + A)) (y + A)
      - 3 * D G x y (x + (B + A)) (y + (B + A))
      + 3 * D G (x + B) y (x + (B + A)) (y + A)
      - D G (x + (B + A)) (y - B) (x + 2 * B) (y - A)
      - D G (x + (B + A)) (y + 2 * A) (x + 2 * B) (y + (B + A)) := by
  simp only [D]
  ring_nf

/-- Horizontal additivity: `[a, c] = [a, e] ∪ [e, c]` in the `x`-direction. -/
theorem D_split_x (G : ℤ → ℤ → ℝ) (a b c d e : ℤ) :
    D G a b c d = D G a b e d + D G e b c d := by
  simp only [D]; ring

/-- Vertical additivity: `[b, d] = [b, e] ∪ [e, d]` in the `y`-direction. -/
theorem D_split_y (G : ℤ → ℤ → ℝ) (a b c d e : ℤ) :
    D G a b c d = D G a b c e + D G a e c d := by
  simp only [D]; ring

/-- Reversing the `x`-interval negates `D`. -/
theorem D_swap_x (G : ℤ → ℤ → ℝ) (a b c d : ℤ) : D G a b c d = -D G c b a d := by
  simp only [D]; ring

/-- Reversing the `y`-interval negates `D`. -/
theorem D_swap_y (G : ℤ → ℤ → ℝ) (a b c d : ℤ) : D G a b c d = -D G a d c b := by
  simp only [D]; ring

/-! ## The scaling step, tiling, and iteration -/

/-- Any `D G a b c d` with `c - a = d - b` is a square, hence bounded by `1`. -/
theorem abs_D_le_one_of_sub_eq (G : ℤ → ℤ → ℝ)
    (hsq : ∀ a b s : ℤ, |D G a b (a + s) (b + s)| ≤ 1)
    (a b c d : ℤ) (h : c - a = d - b) : |D G a b c d| ≤ 1 := by
  have hc : c = a + (c - a) := by ring
  have hd : d = b + (c - a) := by omega
  rw [hc, hd]
  exact hsq a b (c - a)

/-- Scaling step: `9 |R| - 32 ≤ |P|` for `R = [x, x + B] × [y, y + A]` and its
tripling `P = [x - B, x + 2B] × [y - A, y + 2A]`, from `rect_identity`. -/
theorem nine_mul_abs_sub_le (G : ℤ → ℤ → ℝ)
    (hsq : ∀ a b s : ℤ, |D G a b (a + s) (b + s)| ≤ 1) (x y A B : ℤ) :
    9 * |D G x y (x + B) (y + A)| - 32 ≤
      |D G (x - B) (y - A) (x + 2 * B) (y + 2 * A)| := by
  have e := rect_identity G x y A B
  have sq := abs_D_le_one_of_sub_eq G hsq
  have q1 := abs_le.1 (sq (x - B) (y - B) (x - A) (y - A) (by ring))
  have q2 := abs_le.1 (sq (x - B) (y + 2 * A) (x - A) (y + (B + A)) (by ring))
  have q3 := abs_le.1 (sq (x - B) (y - B) (x + (B + A)) (y + (B + A)) (by ring))
  have q4 := abs_le.1 (sq (x - A) y x (y + A) (by ring))
  have q5 := abs_le.1 (sq (x - A) (y - B) (x + B) (y + A) (by ring))
  have q6 := abs_le.1 (sq (x - A) y (x + B) (y + (B + A)) (by ring))
  have q7 := abs_le.1 (sq (x - A) (y - B) (x + (B + A)) (y + 2 * A) (by ring))
  have q8 := abs_le.1 (sq (x - A) (y - A) (x + (B + A)) (y + (B + A)) (by ring))
  have q9 := abs_le.1 (sq (x - A) (y - B) (x + 2 * B) (y + (B + A)) (by ring))
  have q10 := abs_le.1 (sq x (y - B) (x + B) y (by ring))
  have q11 := abs_le.1 (sq x (y + A) (x + B) (y + (B + A)) (by ring))
  have q12 := abs_le.1 (sq x (y - B) (x + (B + A)) (y + A) (by ring))
  have q13 := abs_le.1 (sq x y (x + (B + A)) (y + (B + A)) (by ring))
  have q14 := abs_le.1 (sq (x + B) y (x + (B + A)) (y + A) (by ring))
  have q15 := abs_le.1 (sq (x + (B + A)) (y - B) (x + 2 * B) (y - A) (by ring))
  have q16 := abs_le.1 (sq (x + (B + A)) (y + 2 * A) (x + 2 * B) (y + (B + A)) (by ring))
  rcases abs_cases (D G x y (x + B) (y + A)) with ⟨hR, _⟩ | ⟨hR, _⟩ <;>
  rcases abs_cases (D G (x - B) (y - A) (x + 2 * B) (y + 2 * A)) with ⟨hP, _⟩ | ⟨hP, _⟩ <;>
  · rw [hR, hP]
    linarith [q1.1, q1.2, q2.1, q2.2, q3.1, q3.2, q4.1, q4.2, q5.1, q5.2, q6.1, q6.2,
      q7.1, q7.2, q8.1, q8.2, q9.1, q9.2, q10.1, q10.2, q11.1, q11.2, q12.1, q12.2,
      q13.1, q13.2, q14.1, q14.2, q15.1, q15.2, q16.1, q16.2]

/-- A column of `k` squares of side `S` is bounded by `k`. -/
theorem abs_D_column_le (G : ℤ → ℤ → ℝ)
    (hsq : ∀ a b s : ℤ, |D G a b (a + s) (b + s)| ≤ 1)
    (x y S : ℤ) (k : ℕ) : |D G x y (x + S) (y + k * S)| ≤ k := by
  induction k with
  | zero => simp [D]
  | succ k ih =>
    rw [D_split_y G x y (x + S) (y + ↑(k + 1) * S) (y + k * S)]
    have h1 := abs_D_le_one_of_sub_eq G hsq x (y + k * S) (x + S) (y + ↑(k + 1) * S)
      (by push_cast; ring)
    calc _ ≤ |D G x y (x + S) (y + ↑k * S)| +
            |D G x (y + ↑k * S) (x + S) (y + ↑(k + 1) * S)| := abs_add_le _ _
      _ ≤ k + 1 := by linarith
      _ = ((k + 1 : ℕ) : ℝ) := by push_cast; ring

/-- Tiling: an `(m S) × (k S)` rectangle is a union of `m k` squares of side `S`,
so it is bounded by `m k`. -/
theorem abs_D_tiling_le (G : ℤ → ℤ → ℝ)
    (hsq : ∀ a b s : ℤ, |D G a b (a + s) (b + s)| ≤ 1)
    (x y S : ℤ) (m k : ℕ) : |D G x y (x + m * S) (y + k * S)| ≤ m * k := by
  induction m with
  | zero => simp [D]
  | succ m ih =>
    rw [D_split_x G x y (x + ↑(m + 1) * S) (y + k * S) (x + m * S)]
    have h1 := abs_D_column_le G hsq (x + m * S) y S k
    have e : x + ↑m * S + S = x + ↑(m + 1) * S := by push_cast; ring
    rw [e] at h1
    calc _ ≤ |D G x y (x + ↑m * S) (y + ↑k * S)| +
            |D G (x + ↑m * S) y (x + ↑(m + 1) * S) (y + k * S)| := abs_add_le _ _
      _ ≤ m * k + k := by linarith
      _ = ((m + 1 : ℕ) : ℝ) * k := by push_cast; ring

/-- Iteration: some `3^n B × 3^n A` rectangle has excess over `4` at least
`9^n` times the excess of `R = [a, a + B] × [b, b + A]`. -/
theorem exists_pow_mul_excess_le (G : ℤ → ℤ → ℝ)
    (hsq : ∀ a b s : ℤ, |D G a b (a + s) (b + s)| ≤ 1)
    (a b A B : ℤ) (n : ℕ) : ∃ x y : ℤ,
      9 ^ n * (|D G a b (a + B) (b + A)| - 4) ≤
        |D G x y (x + 3 ^ n * B) (y + 3 ^ n * A)| - 4 := by
  induction n with
  | zero => exact ⟨a, b, by simp⟩
  | succ n ih =>
    obtain ⟨x, y, hxy⟩ := ih
    refine ⟨x - 3 ^ n * B, y - 3 ^ n * A, ?_⟩
    have h := nine_mul_abs_sub_le G hsq x y (3 ^ n * A) (3 ^ n * B)
    have e1 : x - 3 ^ n * B + 3 ^ (n + 1) * B = x + 2 * (3 ^ n * B) := by ring
    have e2 : y - 3 ^ n * A + 3 ^ (n + 1) * A = y + 2 * (3 ^ n * A) := by ring
    rw [e1, e2, pow_succ]
    nlinarith

/-! ## Main theorems -/

/-- The bound `4` for rectangles with `a ≤ c` and `b ≤ d`. -/
theorem abs_rect_le_four_of_le (G : ℤ → ℤ → ℝ)
    (hsq : ∀ a b s : ℤ, |D G a b (a + s) (b + s)| ≤ 1)
    (a b c d : ℤ) (hac : a ≤ c) (hbd : b ≤ d) : |D G a b c d| ≤ 4 := by
  obtain ⟨B, hB⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 hac)
  obtain ⟨A, hA⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 hbd)
  have hc : c = a + (B : ℤ) := by omega
  have hd : d = b + (A : ℤ) := by omega
  subst hc hd
  by_contra hle
  have hlt := not_le.1 hle
  set ε : ℝ := |D G a b (a + B) (b + A)| - 4 with hε
  have hεpos : 0 < ε := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (((B : ℝ) * A + 4) / ε)
  obtain ⟨x, y, hxy⟩ := exists_pow_mul_excess_le G hsq a b A B n
  have ht := abs_D_tiling_le G hsq x y (3 ^ n) B A
  have e1 : x + 3 ^ n * (B : ℤ) = x + (B : ℤ) * 3 ^ n := by ring
  have e2 : y + 3 ^ n * (A : ℤ) = y + (A : ℤ) * 3 ^ n := by ring
  rw [e1, e2] at hxy
  have hpow : (n : ℝ) ≤ 9 ^ n := by
    have hlt9 : n < 9 ^ n := Nat.lt_pow_self (by norm_num)
    exact_mod_cast hlt9.le
  have h1 : (B : ℝ) * A + 4 < n * ε := by
    rwa [div_lt_iff₀ hεpos] at hn
  have h2 : (n : ℝ) * ε ≤ 9 ^ n * ε := mul_le_mul_of_nonneg_right hpow hεpos.le
  linarith

/-- **Bercovici's rectangle bound, corner form.**  If `G : ℤ → ℤ → ℝ` satisfies
`|D G a b (a + s) (b + s)| ≤ 1` for every axis-parallel square (all integers
`a, b, s`), then `|D G a b c d| ≤ 4` for every axis-parallel rectangle.
(MathOverflow 13820, Update 2.) -/
theorem abs_rect_le_four_of_abs_square_le_one (G : ℤ → ℤ → ℝ)
    (hsq : ∀ a b s : ℤ, |D G a b (a + s) (b + s)| ≤ 1)
    (a b c d : ℤ) : |D G a b c d| ≤ 4 := by
  rcases le_total a c with hac | hca <;> rcases le_total b d with hbd | hdb
  · exact abs_rect_le_four_of_le G hsq a b c d hac hbd
  · rw [D_swap_y, abs_neg]
    exact abs_rect_le_four_of_le G hsq a d c b hac hdb
  · rw [D_swap_x, abs_neg]
    exact abs_rect_le_four_of_le G hsq c b a d hca hbd
  · rw [D_swap_x, D_swap_y, neg_neg]
    exact abs_rect_le_four_of_le G hsq c d a b hca hdb

/-! ## Bridge to cell sums -/

/-- Concatenation of consecutive integer intervals for sums. -/
theorem sum_Ico_add_sum_Ico (g : ℤ → ℝ) {a b c : ℤ} (hab : a ≤ b) (hbc : b ≤ c) :
    ∑ i ∈ Finset.Ico a b, g i + ∑ i ∈ Finset.Ico b c, g i = ∑ i ∈ Finset.Ico a c, g i := by
  rw [← Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive a b c),
    Finset.Ico_union_Ico_eq_Ico hab hbc]

/-- Differences of the signed prefix sum are interval sums. -/
theorem prefixSum_sub (g : ℤ → ℝ) {a c : ℤ} (hac : a ≤ c) :
    prefixSum g c - prefixSum g a = ∑ i ∈ Finset.Ico a c, g i := by
  simp only [prefixSum]
  rcases le_total 0 a with h0a | ha0
  · rw [Finset.Ico_eq_empty_of_le h0a, Finset.Ico_eq_empty_of_le (h0a.trans hac),
      ← sum_Ico_add_sum_Ico g h0a hac]
    simp
  · rcases le_total c 0 with hc0 | h0c
    · rw [Finset.Ico_eq_empty_of_le ha0, Finset.Ico_eq_empty_of_le hc0,
        ← sum_Ico_add_sum_Ico g hac hc0]
      simp
    · rw [Finset.Ico_eq_empty_of_le ha0, Finset.Ico_eq_empty_of_le h0c,
        ← sum_Ico_add_sum_Ico g ha0 h0c]
      simp only [Finset.sum_empty]
      ring

/-- For `a ≤ c`, `b ≤ d`, the rectangle functional of the 2D prefix sum is the
cell sum over `[a, c) × [b, d)`. -/
theorem D_prefixSum2 (f : ℤ × ℤ → ℝ) {a b c d : ℤ} (hac : a ≤ c) (hbd : b ≤ d) :
    D (prefixSum2 f) a b c d = ∑ p ∈ Finset.Ico a c ×ˢ Finset.Ico b d, f p := by
  have h : D (prefixSum2 f) a b c d =
      (prefixSum2 f c d - prefixSum2 f a d) - (prefixSum2 f c b - prefixSum2 f a b) := by
    simp only [D]; ring
  rw [h]
  simp only [prefixSum2]
  rw [prefixSum_sub _ hac, prefixSum_sub _ hac, ← Finset.sum_sub_distrib, Finset.sum_product]
  exact Finset.sum_congr rfl fun i _ => prefixSum_sub _ hbd

/-- **Bercovici's rectangle bound, cell form (the statement of MathOverflow
13820).**  Let `f : ℤ × ℤ → ℝ` be such that the sum over every axis-parallel
square `[a, a + s) × [b, b + s)` is at most `1` in absolute value.  Then the sum
over every axis-parallel rectangle `[a, c) × [b, d)` is at most `4` in absolute
value. -/
theorem abs_sum_rect_le_four_of_abs_sum_square_le_one (f : ℤ × ℤ → ℝ)
    (hsq : ∀ (a b : ℤ) (s : ℕ),
      |∑ p ∈ Finset.Ico a (a + s) ×ˢ Finset.Ico b (b + s), f p| ≤ 1)
    (a b c d : ℤ) : |∑ p ∈ Finset.Ico a c ×ˢ Finset.Ico b d, f p| ≤ 4 := by
  have hG : ∀ a b s : ℤ, |D (prefixSum2 f) a b (a + s) (b + s)| ≤ 1 := by
    intro a b s
    rcases le_total 0 s with hs | hs
    · obtain ⟨t, ht⟩ := Int.eq_ofNat_of_zero_le hs
      subst ht
      rw [D_prefixSum2 f (by omega) (by omega)]
      exact hsq a b t
    · obtain ⟨t, ht⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.2 hs)
      have e : D (prefixSum2 f) a b (a + s) (b + s) =
          D (prefixSum2 f) (a + s) (b + s) (a + s + t) (b + s + t) := by
        have e1 : a + s + t = a := by omega
        have e2 : b + s + t = b := by omega
        rw [e1, e2]
        simp only [D]
        ring
      rw [e, D_prefixSum2 f (by omega) (by omega)]
      exact hsq (a + s) (b + s) t
  rcases le_total a c with hac | hca
  · rcases le_total b d with hbd | hdb
    · rw [← D_prefixSum2 f hac hbd]
      exact abs_rect_le_four_of_abs_square_le_one (prefixSum2 f) hG a b c d
    · rw [Finset.Ico_eq_empty_of_le hdb]
      simp
  · rw [Finset.Ico_eq_empty_of_le hca]
    simp

end Candidates.BercoviciRectangleDiscrepancy
