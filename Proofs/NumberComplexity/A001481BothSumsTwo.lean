/-
# A001481 — Lowell: two distinct positive sums of two squares never add to a power of 2

OEIS A001481, J. Lowell: two distinct positive sums of two squares
cannot add to a power of two.

Informal proof.  An odd sum of two squares is `≡ 1 (mod 4)`.  An even sum of
two squares `2m = a² + b²` has `a ≡ b (mod 2)`, and `m = ((a+b)/2)² + ((a-b)/2)²`.
Induct on `k` in `x + y = 2^k`: if `x, y` are odd then `x + y ≡ 2 (mod 4)`, so
`x + y = 2` and `x = y = 1`; if they are even, halve both and recurse.

Note on the exceptions.  The entry's terms include `0`, and every power of two
is itself a term (`2^(2j) = (2^j)² + 0²`, `2^(2j+1) = (2^j)² + (2^j)²`), so
`0 + 2^k` is the only family of exceptions; it also contains `0 + 1 = 2^0`,
which Lowell's list "0+2, 0+4, ..." omits.  We record both the positive form
(`conjecture`) and the literal "barring 0 + 2^k" form (`conjecture_verbatim`).
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A001481BothSumsTwo

/-- `n` is a term of A001481: `n` is the sum of two nonnegative squares. -/
def IsSumTwoSq (n : ℕ) : Prop := ∃ a b : ℕ, n = a ^ 2 + b ^ 2

/-- Bounded form of `IsSumTwoSq`, used to decide membership for examples. -/
theorem isSumTwoSq_iff_bounded (n : ℕ) :
    IsSumTwoSq n ↔ ∃ a < n + 1, ∃ b < n + 1, n = a ^ 2 + b ^ 2 := by
  constructor
  · rintro ⟨a, b, hab⟩
    have ha : a ≤ a ^ 2 := by nlinarith
    have hb : b ≤ b ^ 2 := by nlinarith
    exact ⟨a, by omega, b, by omega, hab⟩
  · rintro ⟨a, -, b, -, hab⟩
    exact ⟨a, b, hab⟩

instance : DecidablePred IsSumTwoSq := fun n =>
  decidable_of_iff _ (isSumTwoSq_iff_bounded n).symm

/-- Examples: the terms of A001481 below `30` are exactly the listed ones. -/
example : (List.range 30).filter (fun n => decide (IsSumTwoSq n)) =
    [0, 1, 2, 4, 5, 8, 9, 10, 13, 16, 17, 18, 20, 25, 26, 29] := by
  decide

/-- An odd sum of two squares is `≡ 1 (mod 4)`. -/
theorem mod_four_eq_one_of_odd {n : ℕ} (hn : IsSumTwoSq n) (hodd : n % 2 = 1) :
    n % 4 = 1 := by
  obtain ⟨a, b, rfl⟩ := hn
  have hmod : (a ^ 2 + b ^ 2) % 4 = ((a % 4) ^ 2 + (b % 4) ^ 2) % 4 := by
    simp [Nat.add_mod, Nat.pow_mod]
  have hmod2 : (a ^ 2 + b ^ 2) % 2 = ((a % 4) ^ 2 + (b % 4) ^ 2) % 2 := by
    omega
  have ha : a % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hb : b % 4 < 4 := Nat.mod_lt _ (by norm_num)
  rw [hmod]
  rw [hmod2] at hodd
  interval_cases (a % 4) <;> interval_cases (b % 4) <;> simp_all

/-- Halving: if `2 * m` is a sum of two squares, so is `m`. -/
theorem isSumTwoSq_of_two_mul {m : ℕ} (h : IsSumTwoSq (2 * m)) : IsSumTwoSq m := by
  obtain ⟨a, b, hab⟩ := h
  -- Reduce to the case `b ≤ a`.
  have key : ∀ a b : ℕ, b ≤ a → 2 * m = a ^ 2 + b ^ 2 → IsSumTwoSq m := by
    intro a b hba hab
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hba
    have hd2 : Even (d ^ 2) := by
      have hexp : (b + d) ^ 2 + b ^ 2 = 2 * (b ^ 2 + b * d) + d ^ 2 := by ring
      rw [hexp] at hab
      rw [Nat.even_iff]
      omega
    obtain ⟨e, rfl⟩ := (Nat.even_pow.mp hd2).1
    refine ⟨b + e, e, ?_⟩
    apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 by norm_num)
    rw [hab]
    ring
  rcases le_total b a with hba | hab'
  · exact key a b hba hab
  · exact key b a hab' (by rw [hab]; ring)

/-- Core lemma: if `x, y` are positive sums of two squares with `x + y = 2 ^ k`,
then `x = y`. -/
theorem eq_of_add_eq_two_pow (k : ℕ) :
    ∀ x y : ℕ, IsSumTwoSq x → IsSumTwoSq y → 0 < x → 0 < y →
      x + y = 2 ^ k → x = y := by
  induction k with
  | zero =>
    intro x y _ _ hx0 hy0 h
    simp only [pow_zero] at h
    omega
  | succ k ih =>
    intro x y hx hy hx0 hy0 h
    rw [pow_succ] at h
    rcases Nat.mod_two_eq_zero_or_one x with hxe | hxo
    · -- both even: halve and recurse
      have hye : y % 2 = 0 := by omega
      obtain ⟨x', rfl⟩ : ∃ x', x = 2 * x' := ⟨x / 2, by omega⟩
      obtain ⟨y', rfl⟩ : ∃ y', y = 2 * y' := ⟨y / 2, by omega⟩
      have h' : x' + y' = 2 ^ k := by omega
      have := ih x' y' (isSumTwoSq_of_two_mul hx) (isSumTwoSq_of_two_mul hy)
        (by omega) (by omega) h'
      omega
    · -- both odd: both are `1 mod 4`, so `x + y ≡ 2 (mod 4)` forces `k = 0`
      have hyo : y % 2 = 1 := by omega
      have hx4 := mod_four_eq_one_of_odd hx hxo
      have hy4 := mod_four_eq_one_of_odd hy hyo
      rcases k with _ | k
      · simp only [pow_zero] at h
        omega
      · rw [pow_succ] at h
        omega

/-- **Lowell's conjecture (A001481, J. Lowell, 2022), positive form.**
If `x ≠ y` are both positive sums of two squares, then `x + y` is never a power
of `2`. -/
theorem conjecture (x y : ℕ) (hx : IsSumTwoSq x) (hy : IsSumTwoSq y)
    (hx0 : 0 < x) (hy0 : 0 < y) (hxy : x ≠ y) (k : ℕ) : x + y ≠ 2 ^ k :=
  fun h => hxy (eq_of_add_eq_two_pow k x y hx hy hx0 hy0 h)

/-- Lowell’s conjecture (A001481), including the zero exception: if two
distinct sums of two nonnegative squares add to a power of `2`, one is `0`. -/
theorem conjecture_verbatim (x y : ℕ) (hx : IsSumTwoSq x) (hy : IsSumTwoSq y)
    (hxy : x ≠ y) (k : ℕ) (h : x + y = 2 ^ k) : x = 0 ∨ y = 0 := by
  rcases Nat.eq_zero_or_pos x with hx0 | hx0
  · exact Or.inl hx0
  rcases Nat.eq_zero_or_pos y with hy0 | hy0
  · exact Or.inr hy0
  exact absurd h (conjecture x y hx hy hx0 hy0 hxy k)

/-- Non-vacuity: the hypotheses of `conjecture` are jointly satisfiable
(`x = 1`, `y = 2`), and the exceptional family is genuine (`0 + 2 = 2 ^ 1`). -/
example : IsSumTwoSq 1 ∧ IsSumTwoSq 2 ∧ (0 : ℕ) < 1 ∧ (0 : ℕ) < 2 ∧ (1 : ℕ) ≠ 2 ∧
    IsSumTwoSq 0 ∧ (0 : ℕ) + 2 = 2 ^ 1 :=
  ⟨⟨1, 0, rfl⟩, ⟨1, 1, rfl⟩, by norm_num, by norm_num, by norm_num, ⟨0, 0, rfl⟩, rfl⟩

end Candidates.A001481BothSumsTwo
