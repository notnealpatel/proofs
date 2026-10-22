/-
# A389000 — Wu: a(9m+5) = 2*10^(2m+1) - 1

Chai Wah Wu's conjecture in OEIS A389000 gives the least positive `k`
whose decimal digit sums at `k` and `k²` are both divisible by `9m+5`:
`k = 2·10^(2m+1)-1` for `m ≥ 0`.

* `s(k) ≡ k (mod 9)`, hence `s(k^2) ≡ s(k)^2 (mod 9)`.
* If `k < K := 2*10^L - 1` (`L = 2m+1`) and `s(k) = n = 9m+5`, then
  `s(k^2) ≡ 7 (mod 9)` forces `s(k^2) ≥ 5n`, but `k^2 < 4*10^(2L)` gives
  `s(k^2) ≤ 3 + 18L < 5n`.
* If `s(k) ≥ 2n = 9L + 1` then `k < 2*10^L` gives `s(k) ≤ 1 + 9L` with equality
  only at `k = 2*10^L - 1`.
* `s(K) = s(K^2) = 2n`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A389000LeastDividesBoth

/-- Base-10 digit sum (OEIS A007953). -/
def ds (k : ℕ) : ℕ := (Nat.digits 10 k).sum

/-- `ds 199 = 19`. -/
example : ds 199 = 19 := by decide
/-- `ds (19^2) = ds 361 = 10`. -/
example : ds (19 ^ 2) = 10 := by decide

/-- The defining predicate of `A389000(n)`: `k ≥ 1` and `n` divides both the
digit sum of `k` and the digit sum of `k^2`. -/
def Good (n k : ℕ) : Prop := 0 < k ∧ n ∣ ds k ∧ n ∣ ds (k ^ 2)

/-- Examples `a(5) = 19`: `19` is good for `5`. -/
example : Good 5 19 := by unfold Good; decide
/-- Examples `a(4) = 13`: `13` is good for `4`, while `12` is not. -/
example : Good 4 13 ∧ ¬ Good 4 12 := by unfold Good; decide

/-- Peel the last digit off the digit sum. -/
theorem ds_eq (x : ℕ) : ds x = x % 10 + ds (x / 10) := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp [ds]
  · rw [ds, Nat.digits_def' (by norm_num) hx, List.sum_cons]
    rfl

/-- Digit sum is congruent to the number modulo 9. -/
theorem ds_modEq (x : ℕ) : x ≡ ds x [MOD 9] := Nat.modEq_nine_digits_sum x

/-- A number with zero digit sum is zero. -/
theorem eq_zero_of_ds_eq_zero (x : ℕ) (h : ds x = 0) : x = 0 := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    rw [ds_eq] at h
    rcases Nat.eq_zero_or_pos x with hx | hx
    · exact hx
    · have hq : x / 10 = 0 := ih (x / 10) (Nat.div_lt_self hx (by norm_num)) (by omega)
      omega

/-- If `x < (d+1)*10^M` then `ds x ≤ d + 9M`, with equality only at
`x = (d+1)*10^M - 1`. -/
theorem ds_le_and_eq (d M x : ℕ) (hx : x < (d + 1) * 10 ^ M) :
    ds x ≤ d + 9 * M ∧ (ds x = d + 9 * M → x + 1 = (d + 1) * 10 ^ M) := by
  induction M generalizing x with
  | zero =>
    have hle := Nat.digit_sum_le 10 x
    simp only [pow_zero, mul_one] at hx
    refine ⟨?_, ?_⟩
    · show ds x ≤ d + 9 * 0
      unfold ds; omega
    · intro h
      unfold ds at h
      simp only [pow_zero, mul_one]
      omega
  | succ M ih =>
    have hq : x / 10 < (d + 1) * 10 ^ M := by
      rw [Nat.div_lt_iff_lt_mul (by norm_num)]
      calc x < (d + 1) * 10 ^ (M + 1) := hx
        _ = (d + 1) * 10 ^ M * 10 := by ring
    obtain ⟨h1, h2⟩ := ih (x / 10) hq
    have hr : x % 10 < 10 := Nat.mod_lt x (by norm_num)
    rw [ds_eq]
    refine ⟨by omega, ?_⟩
    intro h
    have hq' := h2 (by omega)
    have hm : x % 10 = 9 := by omega
    have hdiv := Nat.div_add_mod x 10
    calc x + 1 = 10 * (x / 10 + 1) := by omega
      _ = (d + 1) * 10 ^ (M + 1) := by rw [hq']; ring

/-- Digit sums add across a block of `M` low digits. -/
theorem ds_add_mul_pow (a b M : ℕ) (hb : b < 10 ^ M) :
    ds (a * 10 ^ M + b) = ds a + ds b := by
  induction M generalizing b with
  | zero =>
    have hb0 : b = 0 := by simpa using hb
    subst hb0
    simp [ds]
  | succ M ih =>
    have hq : b / 10 < 10 ^ M := by
      rw [Nat.div_lt_iff_lt_mul (by norm_num)]
      calc b < 10 ^ (M + 1) := hb
        _ = 10 ^ M * 10 := by ring
    have hre : a * 10 ^ (M + 1) + b = 10 * (a * 10 ^ M) + b := by ring
    have hmod : (a * 10 ^ (M + 1) + b) % 10 = b % 10 := by
      rw [hre, Nat.mul_add_mod]
    have hdiv : (a * 10 ^ (M + 1) + b) / 10 = a * 10 ^ M + b / 10 := by
      rw [hre, Nat.mul_add_div (by norm_num)]
    rw [ds_eq, hmod, hdiv, ih (b / 10) hq, ds_eq b]
    ring

/-- `ds (10^M - 1) = 9M`, stated without subtraction. -/
theorem ds_nines (M x : ℕ) (hx : x + 1 = 10 ^ M) : ds x = 9 * M := by
  induction M generalizing x with
  | zero =>
    have hx0 : x = 0 := by simpa using hx
    subst hx0; simp [ds]
  | succ M ih =>
    have hpos : 0 < 10 ^ M := by positivity
    obtain ⟨y, hy⟩ : ∃ y, y + 1 = 10 ^ M := ⟨10 ^ M - 1, by omega⟩
    have hxy : x = y * 10 ^ 1 + 9 := by rw [pow_succ] at hx; omega
    rw [hxy, ds_add_mul_pow y 9 1 (by norm_num), ih y hy]
    rw [show ds 9 = 9 by decide]
    ring

/-- The candidate value satisfies `ds K = 2(9m+5)`, where `K + 1 = 2*10^(2m+1)`. -/
theorem ds_witness (m K : ℕ) (hK : K + 1 = 2 * 10 ^ (2 * m + 1)) :
    ds K = 2 * (9 * m + 5) := by
  have hpos : 0 < 10 ^ (2 * m + 1) := by positivity
  obtain ⟨Q, hQ⟩ : ∃ Q, Q + 1 = 10 ^ (2 * m + 1) := ⟨10 ^ (2 * m + 1) - 1, by omega⟩
  have hKQ : K = 1 * 10 ^ (2 * m + 1) + Q := by omega
  rw [hKQ, ds_add_mul_pow 1 Q (2 * m + 1) (by omega), ds_nines (2 * m + 1) Q hQ]
  rw [show ds 1 = 1 by decide]
  ring

/-- The candidate value satisfies `ds (K^2) = 2(9m+5)`, where
`K + 1 = 2*10^(2m+1)`; the decimal digits of `K^2` are `3 9…9 6 0…0 1`. -/
theorem ds_sq_witness (m K : ℕ) (hK : K + 1 = 2 * 10 ^ (2 * m + 1)) :
    ds (K ^ 2) = 2 * (9 * m + 5) := by
  have hpos : 0 < 10 ^ (2 * m) := by positivity
  obtain ⟨Q, hQ⟩ : ∃ Q, Q + 1 = 10 ^ (2 * m) := ⟨10 ^ (2 * m) - 1, by omega⟩
  have hP : 10 ^ (2 * m + 1) = 10 * Q + 10 := by rw [pow_succ]; omega
  have hP2 : 10 ^ (2 * (2 * m + 1)) = (10 * Q + 10) ^ 2 := by
    rw [mul_comm 2 (2 * m + 1), pow_mul, hP]
  have hKQ : K = 20 * Q + 19 := by omega
  have hsplit : K ^ 2 = 3 * 10 ^ (2 * (2 * m + 1))
      + ((10 * Q + 6) * 10 ^ (2 * m + 1) + 1) := by
    rw [hP2, hP, hKQ]; ring
  have hlow : (10 * Q + 6) * 10 ^ (2 * m + 1) + 1 < 10 ^ (2 * (2 * m + 1)) := by
    rw [hP2, hP]; nlinarith
  have hone : 1 < 10 ^ (2 * m + 1) := by rw [hP]; omega
  have hR : 10 * Q + 6 = Q * 10 ^ 1 + 6 := by ring
  rw [hsplit, ds_add_mul_pow 3 _ _ hlow, ds_add_mul_pow _ 1 _ hone, hR,
    ds_add_mul_pow Q 6 1 (by norm_num), ds_nines (2 * m) Q hQ]
  rw [show ds 3 = 3 by decide, show ds 6 = 6 by decide, show ds 1 = 1 by decide]
  ring

/-- **A389000, Wu's conjecture (Oct 01 2025).** For every `m ≥ 0`, with
`n = 9m+5`, the least `k ≥ 1` such that `n` divides both the base-10 digit sum
of `k` and that of `k^2` is `2*10^(2m+1) - 1`. -/
theorem a_nine_mul_add_five (m : ℕ) :
    IsLeast {k : ℕ | Good (9 * m + 5) k} (2 * 10 ^ (2 * m + 1) - 1) := by
  have hpos : 0 < 10 ^ (2 * m + 1) := by positivity
  set K := 2 * 10 ^ (2 * m + 1) - 1 with hKdef
  have hK : K + 1 = 2 * 10 ^ (2 * m + 1) := by omega
  refine ⟨⟨by omega, ?_, ?_⟩, ?_⟩
  · rw [ds_witness m K hK]; exact Dvd.intro_left 2 rfl
  · rw [ds_sq_witness m K hK]; exact Dvd.intro_left 2 rfl
  · rintro k ⟨hk0, ⟨j, hj⟩, ⟨i, hi⟩⟩
    by_contra hlt
    have hkK : k + 2 ≤ 2 * 10 ^ (2 * m + 1) := by omega
    -- bound on the digit sum of `k`
    obtain ⟨hb1, heq1⟩ := ds_le_and_eq 1 (2 * m + 1) k (by omega)
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · interval_cases j
      · -- `j = 0`: `ds k = 0` forces `k = 0`
        have hk00 := eq_zero_of_ds_eq_zero k (by simpa using hj)
        omega
      · -- `j = 1`: `ds k = n`, so `ds (k^2) ≡ n^2 ≡ 7 (mod 9)`
        have hsq : k ^ 2 < (3 + 1) * 10 ^ (2 * (2 * m + 1)) := by
          rw [mul_comm 2 (2 * m + 1), pow_mul]
          have hk2 : k < 2 * 10 ^ (2 * m + 1) := by omega
          calc k ^ 2 < (2 * 10 ^ (2 * m + 1)) ^ 2 := by
                exact Nat.pow_lt_pow_left hk2 (by norm_num)
            _ = (3 + 1) * (10 ^ (2 * m + 1)) ^ 2 := by ring
        obtain ⟨hb2, -⟩ := ds_le_and_eq 3 (2 * (2 * m + 1)) (k ^ 2) hsq
        have hi4 : i ≤ 4 := by
          by_contra hi5
          have h5n : (9 * m + 5) * 5 ≤ (9 * m + 5) * i := Nat.mul_le_mul_left _ (by omega)
          omega
        have hmod : ds (k ^ 2) ≡ (9 * m + 5) ^ 2 [MOD 9] := by
          have h1 : k ≡ 9 * m + 5 [MOD 9] := by
            have hk9 := ds_modEq k
            rw [hj, mul_one] at hk9
            exact hk9
          exact (ds_modEq (k ^ 2)).symm.trans (h1.pow 2)
        rw [hi] at hmod
        unfold Nat.ModEq at hmod
        have h7 : (9 * m + 5) ^ 2 % 9 = 7 := by
          rw [pow_two, Nat.mul_mod]
          have h5 : (9 * m + 5) % 9 = 5 := by omega
          rw [h5]
        rw [h7, Nat.mul_mod] at hmod
        have h5 : (9 * m + 5) % 9 = 5 := by omega
        rw [h5] at hmod
        interval_cases i <;> omega
    · -- `j ≥ 2`: `ds k ≥ 2n = 9(2m+1)+1`, forcing `k = 2*10^(2m+1) - 1`
      have h2n : (9 * m + 5) * 2 ≤ (9 * m + 5) * j := Nat.mul_le_mul_left _ hj2
      have hk1 := heq1 (by omega)
      omega

/-- Instance check: at `m = 1` the theorem gives `a(14) = 1999`, matching the entry. -/
example : IsLeast {k : ℕ | Good 14 k} 1999 := by
  simpa using a_nine_mul_add_five 1

end Candidates.A389000LeastDividesBoth
