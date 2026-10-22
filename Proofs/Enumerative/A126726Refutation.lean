/-
# An index-sensitive identity for A126726

Source: R. J. Mathar's OEIS A126726 formula (May 21 2025),
`a(n)=A190568(n)-(-1)^n` for `n > 0`. With A190568's offset -1,
`A190568(n)=floor(sqrt(2^(n+1)))-floor(sqrt(2^n))`.
The literal formula fails at `n=2`: `a(2)=0`, but the right side is -1.
The shifted identity `a(n)=A190568(n-1)-(-1)^n` is proved for every `n ≥ 2`,
without any claim about authorial intent. Zero has one binary digit,
so `a(1)=2` counts both 0 and 1 and is excluded from the shifted identity.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A126726Refutation

/-! ## Definitions -/

/-- The number of binary digits needed to write `m`; the integer `0` is
written with the single digit `0`. -/
def binLen (m : ℕ) : ℕ := if m = 0 then 1 else (Nat.digits 2 m).length

example : binLen 0 = 1 := by decide
example : binLen 1 = 1 := by decide
example : binLen 4 = 3 := by decide
example : binLen 9 = 4 := by decide

/-- A square with `n` binary digits has a root below `2 ^ n`, so counting
roots in `range (2 ^ n)` counts every such square. -/
theorem lt_two_pow_of_binLen_sq_eq {k n : ℕ} (h : binLen (k ^ 2) = n) : k < 2 ^ n := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    exact Nat.two_pow_pos n
  · have hsq : k ^ 2 ≠ 0 := pow_ne_zero 2 hk.ne'
    have hlen : (Nat.digits 2 (k ^ 2)).length = n := by
      rw [binLen, if_neg hsq] at h
      exact h
    have hlt : k ^ 2 < 2 ^ n := hlen ▸ Nat.lt_base_pow_length_digits (by norm_num)
    have hle : k ≤ k ^ 2 := by nlinarith
    omega

/-- A126726 (offset 0): the number of squares of nonnegative integers that
require exactly `n` binary digits, counted by their roots `k < 2 ^ n`
(see `lt_two_pow_of_binLen_sq_eq`). -/
def a126726 (n : ℕ) : ℕ :=
  ((Finset.range (2 ^ n)).filter (fun k => binLen (k ^ 2) = n)).card

/-- The first nine listed terms of A126726. -/
example : (List.range 9).map a126726 = [0, 2, 0, 1, 1, 2, 2, 4, 4] := by decide

/-- A190568 at an index `n ≥ 0`: `floor(sqrt(2^(n+1))) - floor(sqrt(2^n))`.
The offset `-1` term is not represented; the conjecture only uses `n > 0`.
`floor ∘ sqrt` on natural numbers is `Nat.sqrt` (`a190568_eq_floor_sqrt`). -/
def a190568 (n : ℕ) : ℤ := (Nat.sqrt (2 ^ (n + 1)) : ℤ) - Nat.sqrt (2 ^ n)

/-- The definition agrees with the name of A190568, stated with the real
square root and floor. -/
theorem a190568_eq_floor_sqrt (n : ℕ) :
    a190568 n = ⌊Real.sqrt (2 ^ (n + 1))⌋ - ⌊Real.sqrt (2 ^ n)⌋ := by
  have h1 := @Real.floor_real_sqrt_eq_nat_sqrt (2 ^ (n + 1))
  have h0 := @Real.floor_real_sqrt_eq_nat_sqrt (2 ^ n)
  push_cast at h1 h0
  rw [a190568, h1, h0]

/-- The listed terms `A190568(0), …, A190568(8)` (the OEIS data
starts at index `-1` with `1`). -/
example : (List.range 9).map a190568 = [0, 1, 0, 2, 1, 3, 3, 5, 6] := by decide +kernel

/-! ## The conjecture -/

/-- Mathar's literal A126726 formula at positive indices, with A190568
read at its original offset -1. The subtraction is in `ℤ`. -/
def Conjecture : Prop :=
  ∀ n : ℕ, 0 < n → (a126726 n : ℤ) = a190568 n - (-1) ^ n

/-! ## Refutation -/

/-- Mathar's unshifted formula fails at `n=2`: no square has two binary
digits, but `A190568(2)-(-1)^2=-1`. A separate shifted identity is
`a126726_eq_a190568_pred`. -/
theorem conjecture_false : ¬ Conjecture := by
  intro h
  have h2 := h 2 (by norm_num)
  have ha : a126726 2 = 0 := by decide
  have hs8 : Nat.sqrt 8 = 2 := (Nat.eq_sqrt.2 ⟨by norm_num, by norm_num⟩).symm
  have hs4 : Nat.sqrt 4 = 2 := (Nat.eq_sqrt.2 ⟨by norm_num, by norm_num⟩).symm
  have hb : a190568 2 = 0 := by
    rw [a190568]
    norm_num [hs8, hs4]
  rw [ha, hb] at h2
  norm_num at h2

/-! ## The probable intent: `A190568(n-1)` -/

/-- For `n ≥ 2`, `m` has exactly `n` binary digits iff `2^(n-1) ≤ m < 2^n`. -/
theorem binLen_eq_iff {m n : ℕ} (hn : 2 ≤ n) :
    binLen m = n ↔ 2 ^ (n - 1) ≤ m ∧ m < 2 ^ n := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp only [binLen, if_true, nonpos_iff_eq_zero, pow_eq_zero_iff', OfNat.ofNat_ne_zero,
      false_and, iff_false]
    omega
  · rw [binLen, if_neg hm.ne', Nat.length_digits 2 m (by norm_num) hm.ne']
    have hlog : Nat.log 2 m = n - 1 ↔ 2 ^ (n - 1) ≤ m ∧ m < 2 ^ (n - 1 + 1) :=
      Nat.log_eq_iff (Or.inl (by omega))
    have hn1 : n - 1 + 1 = n := by omega
    rw [hn1] at hlog
    rw [← hlog]
    omega

/-- `k ^ 2 < N ↔ k < sqrt (N - 1) + 1` for `0 < N`: the squares below `N`
have roots `0, …, sqrt (N - 1)`. -/
theorem sq_lt_iff {k N : ℕ} (hN : 0 < N) : k ^ 2 < N ↔ k < Nat.sqrt (N - 1) + 1 := by
  rw [Nat.lt_succ_iff, Nat.le_sqrt']
  omega

/-- An odd power of two is not a perfect square. -/
theorem not_sq_two_pow_odd (s j : ℕ) : s ^ 2 ≠ 2 ^ (2 * j + 1) := by
  intro h
  have hdvd : s ∣ 2 ^ (2 * j + 1) := ⟨s, by rw [← h]; ring⟩
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [← pow_mul] at h
  have hexp := Nat.pow_right_injective (le_refl 2) h
  omega

/-- `sqrt (2^n - 1) + 1` (the number of squares below `2^n`) is
`sqrt (2^n)` for even `n` and `sqrt (2^n) + 1` for odd `n`. -/
theorem sqrt_two_pow_sub_one (n : ℕ) :
    Nat.sqrt (2 ^ n - 1) + 1 = Nat.sqrt (2 ^ n) + if Even n then 0 else 1 := by
  rcases Nat.even_or_odd' n with ⟨j, rfl | rfl⟩
  · have he : Even (2 * j) := even_two_mul j
    rw [if_pos he]
    have hp : 0 < 2 ^ j := Nat.two_pow_pos j
    have hsq : 2 ^ (2 * j) = (2 ^ j) ^ 2 := by ring
    rw [hsq, Nat.sqrt_eq']
    have hs : Nat.sqrt ((2 ^ j) ^ 2 - 1) = 2 ^ j - 1 := by
      apply le_antisymm
      · have hlt : Nat.sqrt ((2 ^ j) ^ 2 - 1) < 2 ^ j := by
          rw [Nat.sqrt_lt']; have hp2 : 0 < (2 ^ j) ^ 2 := by positivity
          omega
        omega
      · rw [Nat.le_sqrt']
        have hsq1 : (2 ^ j - 1) ^ 2 + 1 ≤ (2 ^ j) ^ 2 := by
          obtain ⟨t, ht⟩ : ∃ t, 2 ^ j = t + 1 := ⟨2 ^ j - 1, by omega⟩
          rw [ht, Nat.add_sub_cancel]; nlinarith
        omega
    omega
  · have ho : ¬ Even (2 * j + 1) := Nat.not_even_iff_odd.2 (odd_two_mul_add_one j)
    rw [if_neg ho]
    congr 1
    apply le_antisymm
    · exact Nat.sqrt_le_sqrt (Nat.sub_le _ _)
    · rw [Nat.le_sqrt']
      have h1 := Nat.sqrt_le' (2 ^ (2 * j + 1))
      have h2 := not_sq_two_pow_odd (Nat.sqrt (2 ^ (2 * j + 1))) j
      omega

/-- **Corrected form of Mathar's conjecture.**  For every `n ≥ 2`,
`a(n) = A190568(n-1) - (-1)^n`: the squares with `n` binary digits are those
in `[2^(n-1), 2^n)`, and the floor square roots of the endpoints overcount by
one exactly at the even power of two. -/
theorem a126726_eq_a190568_pred (n : ℕ) (hn : 2 ≤ n) :
    (a126726 n : ℤ) = a190568 (n - 1) - (-1) ^ n := by
  have hpos : ∀ m : ℕ, 0 < 2 ^ m := Nat.two_pow_pos
  have hfilter : (Finset.range (2 ^ n)).filter (fun k => binLen (k ^ 2) = n) =
      Finset.Ico (Nat.sqrt (2 ^ (n - 1) - 1) + 1) (Nat.sqrt (2 ^ n - 1) + 1) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    have hhi := sq_lt_iff (k := k) (hpos n)
    have hlo := sq_lt_iff (k := k) (hpos (n - 1))
    have hle : k ≤ k ^ 2 := by nlinarith
    rw [binLen_eq_iff hn]
    omega
  have hmono : Nat.sqrt (2 ^ (n - 1) - 1) + 1 ≤ Nat.sqrt (2 ^ n - 1) + 1 := by
    have hpow : 2 ^ (n - 1) ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le n 1)
    exact Nat.succ_le_succ (Nat.sqrt_le_sqrt (by omega))
  have hcard : a126726 n = (Nat.sqrt (2 ^ n - 1) + 1) - (Nat.sqrt (2 ^ (n - 1) - 1) + 1) := by
    rw [a126726, hfilter, Nat.card_Ico]
  have hn1 : n - 1 + 1 = n := by omega
  rw [hcard, Nat.cast_sub hmono, sqrt_two_pow_sub_one n, sqrt_two_pow_sub_one (n - 1),
    a190568, hn1]
  rcases Nat.even_or_odd' n with ⟨j, rfl | rfl⟩
  · have he : Even (2 * j) := even_two_mul j
    have ho : ¬ Even (2 * j - 1) := by
      rw [Nat.not_even_iff_odd]; exact ⟨j - 1, by omega⟩
    rw [if_pos he, if_neg ho, he.neg_one_pow]
    push_cast
    ring
  · have ho : ¬ Even (2 * j + 1) := Nat.not_even_iff_odd.2 (odd_two_mul_add_one j)
    have he : Even (2 * j + 1 - 1) := ⟨j, by omega⟩
    rw [if_neg ho, if_pos he, (odd_two_mul_add_one j).neg_one_pow]
    push_cast
    ring

/-- The corrected form at its first instance `n = 2`. -/
example : (a126726 2 : ℤ) = a190568 1 - (-1) ^ 2 := a126726_eq_a190568_pred 2 le_rfl

end Candidates.A126726Refutation
