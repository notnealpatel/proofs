/-
A133212 and every fourth Pascal entry (R. J. Mathar, Oct 23 2007).

The integer recurrence sequence A133212 satisfies a(n)=2*A038503(n+3)
for n≥1, where A038503(m)=∑_k C(m,4k). A roots-of-unity filter and the
characteristic recurrence prove the identity. No other combinatorial
interpretations of A038503 are used.
The guard is necessary: a(0)=1 but 2*A038503(3)=2.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A133212SumBinomial

open Finset Complex

/-- OEIS A133212: `a(n) = 4*a(n-1) - 6*a(n-2) + 4*a(n-3)` for `n > 3`, with
`a(0) = 1, a(1) = 4, a(2) = 12, a(3) = 32`.  Defined over `ℤ` so that the
subtraction in the recurrence is honest. -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 4
  | 2 => 12
  | 3 => 32
  | n + 4 => 4 * a (n + 3) - 6 * a (n + 2) + 4 * a (n + 1)

/-- OEIS A038503: `A038503(m) = ∑_k binomial(m, 4k)`, the sum of every fourth
entry of row `m` of Pascal's triangle starting at `binomial(m, 0)`.  The index
range `k ≤ m` covers every nonzero term, since `binomial(m, 4k) = 0` for
`4k > m`. -/
def A038503 (m : ℕ) : ℕ := ∑ k ∈ range (m + 1), m.choose (4 * k)

example : [a 0, a 1, a 2, a 3, a 4, a 5, a 6, a 7, a 8, a 9] =
    [1, 4, 12, 32, 72, 144, 272, 512, 992, 1984] := by decide

example : (List.range 12).map A038503 = [1, 1, 1, 1, 2, 6, 16, 36, 72, 136, 256, 496] := by
  decide

/-! ## Roots-of-unity filter -/

/-- The fourth-roots-of-unity weight at an exponent `4k + r`. -/
lemma weight_eq (k r : ℕ) :
    (1 + I ^ (4 * k + r) + (-1) ^ (4 * k + r) + (-I) ^ (4 * k + r) : ℂ) =
      1 + I ^ r + (-1) ^ r + (-I) ^ r := by
  have h4 : I ^ 4 = 1 := I_pow_four
  have hm4 : (-I) ^ 4 = 1 := by rw [neg_pow, I_pow_four]; norm_num
  simp only [pow_add, pow_mul, h4, hm4, one_pow, one_mul]
  norm_num

/-- Grouping a range of length `4N` into blocks of four: only the
multiples of four survive the weight. -/
lemma sum_weight_choose (m N : ℕ) :
    ∑ j ∈ range (4 * N), (1 + I ^ j + (-1) ^ j + (-I) ^ j : ℂ) * (m.choose j : ℂ) =
      4 * ∑ k ∈ range N, (m.choose (4 * k) : ℂ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have w0 : (1 + I ^ (4 * N) + (-1) ^ (4 * N) + (-I) ^ (4 * N) : ℂ) = 4 := by
      rw [show 4 * N = 4 * N + 0 from rfl, weight_eq N 0]; norm_num
    have w1 := weight_eq N 1
    have w2 := weight_eq N 2
    have w3 := weight_eq N 3
    rw [show 4 * (N + 1) = 4 * N + 3 + 1 by ring, sum_range_succ,
      show 4 * N + 3 = 4 * N + 2 + 1 by ring, sum_range_succ,
      show 4 * N + 2 = 4 * N + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ, w0, show 4 * N + 1 + 1 = 4 * N + 2 by ring, w1, w2,
      show 4 * N + 2 + 1 = 4 * N + 3 by ring, w3]
    linear_combination 2 * (m.choose (4 * N + 2) : ℂ) * I_sq


/-- The binomial theorem `(x + 1)^m = ∑_j x^j * binomial(m, j)`, with the
index range padded to any length `N ≥ m + 1`. -/
lemma sum_pow_mul_choose (x : ℂ) (m N : ℕ) (hN : m + 1 ≤ N) :
    ∑ j ∈ range N, x ^ j * (m.choose j : ℂ) = (x + 1) ^ m := by
  rw [add_pow]
  simp only [one_pow, mul_one]
  symm
  apply sum_subset (range_subset_range.mpr hN)
  intro j _ hj
  rw [mem_range, not_lt] at hj
  simp [Nat.choose_eq_zero_of_lt (Nat.lt_of_succ_le hj)]

/-- Roots-of-unity filter: `4 * A038503(m) = 2^m + (1+i)^m + 0^m + (1-i)^m`. -/
lemma four_mul_A038503 (m : ℕ) :
    4 * (A038503 m : ℂ) = 2 ^ m + (1 + I) ^ m + 0 ^ m + (1 - I) ^ m := by
  have hN : m + 1 ≤ 4 * (m + 1) := by omega
  have hsplit : ∀ j : ℕ, (1 + I ^ j + (-1) ^ j + (-I) ^ j : ℂ) * (m.choose j : ℂ) =
      1 ^ j * (m.choose j : ℂ) + I ^ j * (m.choose j : ℂ) + (-1) ^ j * (m.choose j : ℂ) +
        (-I) ^ j * (m.choose j : ℂ) := by
    intro j
    ring
  rw [A038503, Nat.cast_sum, ← sum_weight_choose m (m + 1)]
  simp only [hsplit, sum_add_distrib, sum_pow_mul_choose _ m _ hN]
  ring


/-! ## Closed form of A133212 -/

/-- The closed form `C(n) = 2^(n+3) + (1+i)^(n+3) + (1-i)^(n+3)`. -/
noncomputable def closedForm (n : ℕ) : ℂ := 2 ^ (n + 3) + (1 + I) ^ (n + 3) + (1 - I) ^ (n + 3)

/-- A root of `x^3 - 4x^2 + 6x - 4` makes its powers satisfy the recurrence of A133212. -/
lemma pow_rec_of_root (x : ℂ) (hx : x ^ 3 = 4 * x ^ 2 - 6 * x + 4) (n : ℕ) :
    x ^ (n + 7) = 4 * x ^ (n + 6) - 6 * x ^ (n + 5) + 4 * x ^ (n + 4) := by
  linear_combination x ^ (n + 4) * hx

/-- The closed form satisfies the recurrence of A133212. -/
lemma closedForm_rec (n : ℕ) :
    closedForm (n + 4) = 4 * closedForm (n + 3) - 6 * closedForm (n + 2) +
      4 * closedForm (n + 1) := by
  have h2 : (2 : ℂ) ^ 3 = 4 * 2 ^ 2 - 6 * 2 + 4 := by norm_num
  have hp : (1 + I) ^ 3 = 4 * (1 + I) ^ 2 - 6 * (1 + I) + 4 := by
    linear_combination (I - 1) * I_sq
  have hm : (1 - I) ^ 3 = 4 * (1 - I) ^ 2 - 6 * (1 - I) + 4 := by
    linear_combination (-I - 1) * I_sq
  simp only [closedForm]
  rw [pow_rec_of_root 2 h2 n, pow_rec_of_root _ hp n, pow_rec_of_root _ hm n]
  ring

/-- For `n ≥ 1`, `2 * a(n) = 2^(n+3) + (1+i)^(n+3) + (1-i)^(n+3)`. -/
lemma two_mul_a (n : ℕ) (hn : 1 ≤ n) : 2 * (a n : ℂ) = closedForm n := by
  have key : ∀ k : ℕ, 2 * (a (k + 1) : ℂ) = closedForm (k + 1) ∧
      2 * (a (k + 2) : ℂ) = closedForm (k + 2) ∧ 2 * (a (k + 3) : ℂ) = closedForm (k + 3) := by
    intro k
    induction k with
    | zero =>
      have hI2 : I ^ 2 = -1 := I_sq
      refine ⟨?_, ?_, ?_⟩ <;> simp only [a, closedForm] <;> push_cast
      · linear_combination (-2 * I ^ 2 - 10) * hI2
      · linear_combination (-10 * (I ^ 2 + 1)) * hI2
      · linear_combination (-2 * (I ^ 4 + 14 * I ^ 2 + 1)) * hI2
    | succ k ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      refine ⟨h2, h3, ?_⟩
      have hrec : a (k + 4) = 4 * a (k + 3) - 6 * a (k + 2) + 4 * a (k + 1) := rfl
      rw [show k + 1 + 3 = k + 4 by ring, hrec, closedForm_rec]
      push_cast
      linear_combination 4 * h3 - 6 * h2 + 4 * h1
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact (key k).1


/-! ## The conjecture -/

/-- For `n≥1`, A133212(n)=2*A038503(n+3). The guard is necessary:
`a 0=1` whereas `2*A038503 3=2`. -/
theorem a_eq_two_mul_A038503 (n : ℕ) (hn : 1 ≤ n) : a n = 2 * (A038503 (n + 3) : ℤ) := by
  have hC : (2 : ℂ) * (a n : ℂ) = 4 * (A038503 (n + 3) : ℂ) := by
    rw [two_mul_a n hn, four_mul_A038503, closedForm, zero_pow (by omega), add_zero]
  have hC' : ((a n : ℤ) : ℂ) = ((2 * (A038503 (n + 3) : ℤ) : ℤ) : ℂ) := by
    push_cast
    linear_combination hC / 2
  exact_mod_cast hC'

/-- The guard `1 ≤ n` cannot be dropped: the identity fails at `n = 0`. -/
example : a 0 ≠ 2 * (A038503 (0 + 3) : ℤ) := by decide

/-- The hypotheses of `a_eq_two_mul_A038503` are satisfiable (at `n = 1`). -/
example : a 1 = 2 * (A038503 (1 + 3) : ℤ) := a_eq_two_mul_A038503 1 le_rfl

end Candidates.A133212SumBinomial
