/-
# A231897 — every binary weight is the weight of a square

N. J. A. Sloane's conjecture in OEIS A231897 says that every nonnegative
binary weight occurs as the weight of a square. The witness is `m = 2^n-1`:
for `n ≥ 1`, `(2^n-1)^2 = 2^(n+1)(2^(n-1)-1)+1` has weight `n`; `m = 0`
covers `n = 0`. This also gives `a(n) ≤ 2^n-1`.

Binary weight (A000120) is the digit sum `(Nat.digits 2 i).sum`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A231897ThereBinaryWeight

/-- The binary weight `wt(i) = A000120(i)`: the number of `1`s in the binary
expansion of `i`, i.e. the sum of its base-2 digits. -/
def wt (i : ℕ) : ℕ := (Nat.digits 2 i).sum

/-! ### `wt` on small values and on the listed terms of A231897 -/

example : wt 0 = 0 := by simp [wt]
example : wt 9 = 2 := by norm_num [wt]
example : wt 49 = 3 := by norm_num [wt]

/-- The first listed terms `a(0..8) = 0,1,3,5,13,11,21,39,45` satisfy
`wt(a(n)^2) = n`. -/
example : wt (0 ^ 2) = 0 ∧ wt (1 ^ 2) = 1 ∧ wt (3 ^ 2) = 2 ∧ wt (5 ^ 2) = 3 ∧
    wt (13 ^ 2) = 4 ∧ wt (11 ^ 2) = 5 ∧ wt (21 ^ 2) = 6 ∧ wt (39 ^ 2) = 7 ∧
    wt (45 ^ 2) = 8 := by
  norm_num [wt]

/-! ### Helper lemmas -/

/-- Appending a low-order binary `1`: `wt(2y + 1) = wt(y) + 1`. -/
theorem wt_two_mul_add_one (y : ℕ) : wt (2 * y + 1) = wt y + 1 := by
  have hdig : Nat.digits 2 (1 + 2 * y) = 1 :: Nat.digits 2 y :=
    Nat.digits_add 2 (by norm_num) 1 y (by norm_num) (Or.inl one_ne_zero)
  rw [wt, wt, add_comm (2 * y) 1, hdig, List.sum_cons, add_comm]

/-- Shifting left by `k` binary places does not change the weight:
`wt(2^k * m) = wt(m)`. -/
theorem wt_two_pow_mul (k m : ℕ) : wt (2 ^ k * m) = wt m := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · simp [hm]
  · rw [wt, wt, Nat.digits_base_pow_mul (by norm_num) hm, List.sum_append]
    simp

/-- A block of `k` ones: `wt(2^k - 1) = k`. -/
theorem wt_two_pow_sub_one (k : ℕ) : wt (2 ^ k - 1) = k := by
  induction k with
  | zero => simp [wt]
  | succ k ih =>
    have hpos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have hsplit : 2 ^ (k + 1) - 1 = 2 * (2 ^ k - 1) + 1 := by
      rw [pow_succ]; omega
    rw [hsplit, wt_two_mul_add_one, ih]

/-- The key identity: `(2^(k+1) - 1)^2 = 2 * (2^(k+1) * (2^k - 1)) + 1`,
i.e. `(2^n - 1)^2 = 2^(n+1) * (2^(n-1) - 1) + 1` for `n = k + 1 ≥ 1`. -/
theorem sq_two_pow_succ_sub_one (k : ℕ) :
    (2 ^ (k + 1) - 1) ^ 2 = 2 * (2 ^ (k + 1) * (2 ^ k - 1)) + 1 := by
  obtain ⟨s, hs⟩ : ∃ s, 2 ^ k = s + 1 := ⟨2 ^ k - 1, by have := @Nat.one_le_two_pow k; omega⟩
  have h2 : 2 ^ (k + 1) = 2 * s + 2 := by rw [pow_succ, hs]; ring
  rw [h2, hs]
  have h3 : 2 * s + 2 - 1 = 2 * s + 1 := by omega
  rw [h3, Nat.add_sub_cancel]
  ring

/-- **Explicit witness.** For every `n`, `wt((2^n - 1)^2) = n`. In particular
`a(n) ≤ 2^n - 1` for A231897. -/
theorem wt_sq_two_pow_sub_one (n : ℕ) : wt ((2 ^ n - 1) ^ 2) = n := by
  cases n with
  | zero => simp [wt]
  | succ k =>
    rw [sq_two_pow_succ_sub_one, wt_two_mul_add_one, wt_two_pow_mul, wt_two_pow_sub_one]

/-! ## The conjecture -/

/-- **A231897 conjecture (N. J. A. Sloane), proved.**

"Conjecture: a(n) is never -1." Here `a(n)` is the smallest `m`
with `wt(m^2) = n`, so the conjecture says that for every `n ≥ 0` some square
has binary weight exactly `n`.  Witness: `m = 2^n - 1`. -/
theorem exists_sq_binary_weight (n : ℕ) : ∃ m : ℕ, wt (m ^ 2) = n :=
  ⟨2 ^ n - 1, wt_sq_two_pow_sub_one n⟩

end Candidates.A231897ThereBinaryWeight
