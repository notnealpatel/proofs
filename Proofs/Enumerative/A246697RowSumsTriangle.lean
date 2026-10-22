/-
# Row sums of A246696 (A246697)

Source: Luce Etienne's OEIS A246697 formula (Oct 16 2016) and the entry's
order-6 recurrence. For every `n ≥ 0`, the row sum of the recursively
defined triangle A246696 is `(2n³+6n²+9n+4+n(-1)^n)/4` in `ℚ`.
The recurrence with signature `(2,1,-4,1,2,-1)` follows over `ℤ`.
The proof sums the two interleaved arithmetic progressions in each row.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A246697RowSumsTriangle

/-! ## Definitions -/

/-- The triangle A246696, transcribed from the entry's recursive definition:
`t(0,0) = 1`, `t(1,0) = 2`, `t(1,1) = 3`; for `n > 1`, the row heads
`t(n,0)`, `t(n,1)` are taken from the previous row's last two entries according to
the parity of `n`, and `t(n,k) = t(n,k-2) + 2` for `2 ≤ k`.  Values with `k > n`
lie outside the triangle and are never used by `a`. -/
def t : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 1, 0 => 2
  | 1, 1 => 3
  | n + 2, 0 => if Odd (n + 2) then t (n + 1) n + 2 else t (n + 1) (n + 1) + 2
  | n + 2, 1 => if Odd (n + 2) then t (n + 1) (n + 1) + 2 else t (n + 1) n + 2
  | n + 2, k + 2 => t (n + 2) k + 2
  | _, _ => 0
termination_by n k => (n, k)

/-- A246697: the row sums `a(n) = ∑_{k=0}^{n} t(n,k)` of the triangle A246696. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), t n k

-- Rows 0..4 of A246696 against the DATA line
-- `1; 2,3; 5,4,7; 6,9,8,11; 13,10,15,12,17`.
example : [t 0 0, t 1 0, t 1 1, t 2 0, t 2 1, t 2 2, t 3 0, t 3 1, t 3 2, t 3 3,
    t 4 0, t 4 1, t 4 2, t 4 3, t 4 4] =
    [1, 2, 3, 5, 4, 7, 6, 9, 8, 11, 13, 10, 15, 12, 17] := by
  simp [t, Nat.odd_iff]

-- The first seven terms of A246697 against its DATA line.
example : [a 0, a 1, a 2, a 3, a 4, a 5, a 6] = [1, 5, 16, 34, 67, 111, 178] := by
  simp [a, Finset.sum_range_succ, t, Nat.odd_iff]

/-! ## Row structure -/

/-- Inside a row `n + 2`, entries two apart differ by `2`. -/
theorem t_add_two (n k : ℕ) : t (n + 2) (k + 2) = t (n + 2) k + 2 := by
  rw [t]

/-- Head `t(n,0)` of an odd row `n > 1` is `t(n-1,n-2) + 2`. -/
theorem t_zero_of_odd (n : ℕ) (h : Odd (n + 2)) : t (n + 2) 0 = t (n + 1) n + 2 := by
  rw [t, if_pos h]

/-- Second entry `t(n,1)` of an odd row `n > 1` is `t(n-1,n-1) + 2`. -/
theorem t_one_of_odd (n : ℕ) (h : Odd (n + 2)) :
    t (n + 2) 1 = t (n + 1) (n + 1) + 2 := by
  rw [t, if_pos h]

/-- Head `t(n,0)` of an even row `n > 1` is `t(n-1,n-1) + 2`. -/
theorem t_zero_of_even (n : ℕ) (h : ¬Odd (n + 2)) :
    t (n + 2) 0 = t (n + 1) (n + 1) + 2 := by
  rw [t, if_neg h]

/-- Second entry `t(n,1)` of an even row `n > 1` is `t(n-1,n-2) + 2`. -/
theorem t_one_of_even (n : ℕ) (h : ¬Odd (n + 2)) : t (n + 2) 1 = t (n + 1) n + 2 := by
  rw [t, if_neg h]

/-- A row `n + 2` consists of two interleaved arithmetic progressions with step `2`:
`t(n+2,k) = t(n+2, k mod 2) + 2 * (k / 2)`. -/
theorem t_row (n k : ℕ) : t (n + 2) k = t (n + 2) (k % 2) + 2 * (k / 2) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simp
    | 1 => simp
    | k + 2 =>
      rw [t_add_two, ih k (by omega)]
      have h1 : (k + 2) % 2 = k % 2 := by omega
      have h2 : (k + 2) / 2 = k / 2 + 1 := by omega
      rw [h1, h2]
      ring

/-- Even-position entries of row `n + 2`: `t(n+2, 2j) = t(n+2, 0) + 2j`. -/
theorem t_even_entry (n k j : ℕ) (hk : k = 2 * j) :
    t (n + 2) k = t (n + 2) 0 + 2 * j := by
  rw [t_row n k]
  have h1 : k % 2 = 0 := by omega
  have h2 : k / 2 = j := by omega
  rw [h1, h2]

/-- Odd-position entries of row `n + 2`: `t(n+2, 2j+1) = t(n+2, 1) + 2j`. -/
theorem t_odd_entry (n k j : ℕ) (hk : k = 2 * j + 1) :
    t (n + 2) k = t (n + 2) 1 + 2 * j := by
  rw [t_row n k]
  have h1 : k % 2 = 1 := by omega
  have h2 : k / 2 = j := by omega
  rw [h1, h2]

/-- Closed forms of the row heads: `t(2m+1,0) = 2m²+2m+2`, `t(2m+1,1) = 2m²+4m+3`,
`t(2m+2,0) = 2(m+1)²+2(m+1)+1` and `t(2m+2,1) = 2(m+1)²+2`. -/
theorem t_closed (m : ℕ) :
    t (2 * m + 1) 0 = 2 * m ^ 2 + 2 * m + 2 ∧
    t (2 * m + 1) 1 = 2 * m ^ 2 + 4 * m + 3 ∧
    t (2 * m + 2) 0 = 2 * (m + 1) ^ 2 + 2 * (m + 1) + 1 ∧
    t (2 * m + 2) 1 = 2 * (m + 1) ^ 2 + 2 := by
  induction m with
  | zero => simp [t, Nat.odd_iff]
  | succ m ih =>
    obtain ⟨_, _, ih0, ih1⟩ := ih
    have hodd : Odd (2 * m + 1 + 2) := ⟨m + 1, by ring⟩
    have heven : ¬Odd (2 * m + 2 + 2) := by
      rw [Nat.not_odd_iff_even]
      exact ⟨m + 2, by ring⟩
    have o0 : t (2 * m + 1 + 2) 0 = 2 * (m + 1) ^ 2 + 2 * (m + 1) + 2 := by
      rw [t_zero_of_odd _ hodd, t_odd_entry (2 * m) (2 * m + 1) m rfl, ih1]
      ring
    have o1 : t (2 * m + 1 + 2) 1 = 2 * (m + 1) ^ 2 + 4 * (m + 1) + 3 := by
      rw [t_one_of_odd _ hodd, t_even_entry (2 * m) (2 * m + 1 + 1) (m + 1) (by ring), ih0]
      ring
    have e0 : t (2 * m + 2 + 2) 0 = 2 * (m + 2) ^ 2 + 2 * (m + 2) + 1 := by
      rw [t_zero_of_even _ heven,
        t_odd_entry (2 * m + 1) (2 * m + 2 + 1) (m + 1) (by ring), o1]
      ring
    have e1 : t (2 * m + 2 + 2) 1 = 2 * (m + 2) ^ 2 + 2 := by
      rw [t_one_of_even _ heven, t_even_entry (2 * m + 1) (2 * m + 2) (m + 1) (by ring), o0]
      ring
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by ring, o0]
    · rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by ring, o1]
    · rw [show 2 * (m + 1) + 2 = 2 * m + 2 + 2 by ring, e0]
    · rw [show 2 * (m + 1) + 2 = 2 * m + 2 + 2 by ring, e1]

/-- The sum of the first `2j` entries of row `n + 2`:
`∑_{k<2j} t(n+2,k) + 2j = j (t(n+2,0) + t(n+2,1)) + 2j²`. -/
theorem sum_pairs (n j : ℕ) :
    ∑ k ∈ Finset.range (2 * j), t (n + 2) k + 2 * j =
      j * (t (n + 2) 0 + t (n + 2) 1) + 2 * j ^ 2 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, t_even_entry n (2 * j) j rfl, t_odd_entry n (2 * j + 1) j rfl]
    linear_combination ih

/-! ## The conjecture -/

/-- Integer form of Etienne's closed form: `4 a(n) = 2n³ + 6n² + 9n + 4 + n(-1)^n`
for every `n ≥ 0`. -/
theorem four_mul_a (n : ℕ) :
    4 * (a n : ℤ) = 2 * n ^ 3 + 6 * n ^ 2 + 9 * n + 4 + n * (-1) ^ n := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · cases m with
    | zero => simp [a, t]
    | succ m =>
      obtain ⟨_, _, hA, hB⟩ := t_closed m
      have hs := sum_pairs (2 * m) (m + 1)
      rw [show 2 * (m + 1) = 2 * m + 2 by ring] at hs ⊢
      have hrow : a (2 * m + 2) = ∑ k ∈ Finset.range (2 * m + 2), t (2 * m + 2) k
          + t (2 * m + 2) (2 * m + 2) := by
        rw [a, Finset.sum_range_succ]
      have hlast := t_even_entry (2 * m) (2 * m + 2) (m + 1) (by ring)
      have hsign : ((-1 : ℤ)) ^ (2 * m + 2) = 1 := by
        rw [show 2 * m + 2 = 2 * (m + 1) by ring, pow_mul]
        norm_num
      rw [hsign]
      rw [hA, hB] at hs
      rw [hA] at hlast
      zify at hs hlast hrow
      push_cast
      linear_combination 4 * hrow + 4 * hs + 4 * hlast
  · cases m with
    | zero => simp [a, t, Finset.sum_range_succ]
    | succ m =>
      obtain ⟨hA, hB, _, _⟩ := t_closed (m + 1)
      rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by ring] at hA hB ⊢
      have hs := sum_pairs (2 * m + 1) (m + 2)
      have hrow : a (2 * m + 1 + 2) =
          ∑ k ∈ Finset.range (2 * (m + 2)), t (2 * m + 1 + 2) k := by
        rw [a, show 2 * m + 1 + 2 + 1 = 2 * (m + 2) by ring]
      have hsign : ((-1 : ℤ)) ^ (2 * m + 1 + 2) = -1 := by
        rw [show 2 * m + 1 + 2 = 2 * (m + 1) + 1 by ring, pow_succ, pow_mul]
        norm_num
      rw [hsign]
      rw [hA, hB] at hs
      zify at hs hrow
      push_cast
      linear_combination 4 * hrow + 4 * hs

/-- Etienne's formula for the row sums of A246696, with division by 4 in
`ℚ`, not truncated natural division. -/
theorem a246697_closed_form (n : ℕ) :
    (a n : ℚ) = (2 * n ^ 3 + 6 * n ^ 2 + 9 * n + 4 + n * (-1) ^ n) / 4 := by
  have hz := four_mul_a n
  have hq : (4 : ℚ) * (a n : ℚ) = 2 * n ^ 3 + 6 * n ^ 2 + 9 * n + 4 + n * (-1) ^ n := by
    exact_mod_cast hz
  linear_combination hq / 4

/-- The A246697 recurrence with signature `(2,1,-4,1,2,-1)`, stated in `ℤ`
and shifted to avoid natural index subtraction. -/
theorem a246697_recurrence (n : ℕ) :
    (a (n + 6) : ℤ) = 2 * a (n + 5) + a (n + 4) - 4 * a (n + 3) + a (n + 2)
      + 2 * a (n + 1) - a n := by
  have h0 := four_mul_a n
  have h1 := four_mul_a (n + 1)
  have h2 := four_mul_a (n + 2)
  have h3 := four_mul_a (n + 3)
  have h4 := four_mul_a (n + 4)
  have h5 := four_mul_a (n + 5)
  have h6 := four_mul_a (n + 6)
  push_cast at h1 h2 h3 h4 h5 h6
  have key : (4 : ℤ) * a (n + 6) = 4 * (2 * a (n + 5) + a (n + 4) - 4 * a (n + 3)
      + a (n + 2) + 2 * a (n + 1) - a n) := by
    linear_combination h6 - 2 * h5 - h4 + 4 * h3 - h2 - 2 * h1 + h0
  exact mul_left_cancel₀ (by norm_num) key

end Candidates.A246697RowSumsTriangle
