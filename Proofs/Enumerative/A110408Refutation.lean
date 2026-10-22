/-
# A110408: a counterexample to the palindromic-prime criterion

OEIS A110408, Amarnath Murthy (Jul 30 2005).
For inputs ending in `1, 3, 7, 9`, candidates are the decimal word `rev(n)`
repeated `k ≥ 1` times and followed by `n`; the sequence is the least prime
candidate, or `0` if there is none. The source offset enumerates these
inputs, rather than all natural numbers.
At `n = 121`, every candidate is a proper multiple of `121`, although `121`
is neither prime nor divisible by `3`. A sufficient zero condition is
proved for palindromes `n ≥ 2` or multiples of `3`; its converse is not proved.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A110408Refutation

/-! ## Definitions -/

/-- Decimal reversal `rev(n)`: the number whose decimal digits are those of
`n` in reverse order (leading zeros of the reversed word are dropped). -/
def rev (n : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 10 n).reverse

/-- Decimal concatenation: the number whose decimal word is that of `a`
followed by that of `b`, i.e. `a · 10^(number of digits of b) + b`. -/
def concat (a b : ℕ) : ℕ := a * 10 ^ (Nat.digits 10 b).length + b

/-- The candidate `rev(n)^k n`: the decimal word of `rev(n)` written `k` times,
followed by the decimal word of `n`. -/
def cand (n : ℕ) : ℕ → ℕ
  | 0 => n
  | k + 1 => concat (rev n) (cand n k)

/-- Some candidate `rev(n)^k n` with `k ≥ 1` is prime. -/
def HasPrime (n : ℕ) : Prop := ∃ k, 1 ≤ k ∧ (cand n k).Prime

open Classical in
/-- A110408 as a function of `n` itself: the smallest prime of the form
`rev(n)^k n` with `k ≥ 1`, or `0` if there is none.  The candidates increase
strictly with `k` (`cand_lt_cand_succ`), so the smallest prime is the one with
the least `k`.  The entry restricts `n` to `n ≡ 1, 3, 7, 9 (mod 10)`; outside
that class the value is not part of the sequence. -/
noncomputable def a110408 (n : ℕ) : ℕ :=
  if h : HasPrime n then cand n (Nat.find h) else 0

/-! ## Basic facts -/

/-- The candidates increase strictly once `n ≠ 0` and `rev n ≠ 0`. -/
theorem cand_lt_cand_succ {n : ℕ} (hr : rev n ≠ 0) (k : ℕ) :
    cand n k < cand n (k + 1) := by
  have hpos : 0 < rev n * 10 ^ (Nat.digits 10 (cand n k)).length :=
    Nat.mul_pos (Nat.pos_of_ne_zero hr) (pow_pos (by norm_num) _)
  show cand n k < concat (rev n) (cand n k)
  rw [concat]
  omega

/-- `n ≤ rev(n)^k n`. -/
theorem le_cand (n : ℕ) : ∀ k, n ≤ cand n k
  | 0 => le_rfl
  | k + 1 => (le_cand n k).trans (Nat.le_add_left _ _)

/-- For `1 ≤ n` and `k ≥ 1`, `10 · rev(n) ≤ rev(n)^k n`. -/
theorem ten_mul_rev_le_cand_succ {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    10 * rev n ≤ cand n (k + 1) := by
  have hne : cand n k ≠ 0 := by have := le_cand n k; omega
  have hlen : 1 ≤ (Nat.digits 10 (cand n k)).length :=
    List.length_pos_iff.mpr (Nat.digits_ne_nil_iff_ne_zero.mpr hne)
  have hpow : 10 ≤ 10 ^ (Nat.digits 10 (cand n k)).length := by
    calc 10 = 10 ^ 1 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hlen
  show 10 * rev n ≤ rev n * 10 ^ (Nat.digits 10 (cand n k)).length + cand n k
  calc 10 * rev n ≤ rev n * 10 ^ (Nat.digits 10 (cand n k)).length := by
        rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ hpow
    _ ≤ _ := Nat.le_add_right _ _

/-- A common divisor of `n` and `rev n` divides every candidate. -/
theorem dvd_cand {d n : ℕ} (hn : d ∣ n) (hr : d ∣ rev n) : ∀ k, d ∣ cand n k
  | 0 => hn
  | k + 1 => Dvd.dvd.add (Dvd.dvd.mul_right hr _) (dvd_cand hn hr k)

/-- `rev n ≡ n (mod 3)`: reversal preserves the digit sum. -/
theorem rev_modEq_three (n : ℕ) : rev n ≡ n [MOD 3] := by
  have h1 : rev n ≡ ((Nat.digits 10 n).reverse).sum [MOD 3] := by
    have := Nat.ofDigits_modEq 10 3 (Nat.digits 10 n).reverse
    rwa [show 10 % 3 = 1 by norm_num, Nat.ofDigits_one] at this
  rw [List.sum_reverse] at h1
  exact h1.trans (Nat.modEq_three_digits_sum n).symm

/-- If the last decimal digit of `n` is nonzero, then `rev n ≠ 0`. -/
theorem rev_ne_zero {n : ℕ} (h : n % 10 ≠ 0) : rev n ≠ 0 := by
  have hn : n ≠ 0 := by rintro rfl; exact h rfl
  have hd : Nat.digits 10 n = n % 10 :: Nat.digits 10 (n / 10) :=
    Nat.digits_def' (by norm_num) (Nat.pos_of_ne_zero hn)
  have hdig : Nat.digits 10 (rev n) = (Nat.digits 10 n).reverse := by
    refine Nat.digits_ofDigits 10 (by norm_num) _ ?_ ?_
    · intro l hl
      exact Nat.digits_lt_base (by norm_num) (List.mem_reverse.mp hl)
    · intro hne
      rw [List.getLast_reverse]
      simpa [hd] using h
  intro h0
  rw [h0, Nat.digits_zero, hd] at hdig
  simp at hdig

/-- `a(n) = 0` exactly when no candidate is prime. -/
theorem a110408_eq_zero_iff (n : ℕ) : a110408 n = 0 ↔ ¬ HasPrime n := by
  classical
  constructor
  · intro h0 hp
    have hspec := Nat.find_spec hp
    have hval : a110408 n = cand n (Nat.find hp) := by
      rw [a110408, dif_pos hp]
    exact hspec.2.ne_zero (hval ▸ h0)
  · intro hnp
    rw [a110408, dif_neg hnp]

/-- Evaluation rule: if `rev(n)^k n` is the first prime candidate, it is `a(n)`. -/
theorem a110408_eq_cand {n k : ℕ} (hk : 1 ≤ k) (hp : (cand n k).Prime)
    (hmin : ∀ j < k, 1 ≤ j → ¬ (cand n j).Prime) : a110408 n = cand n k := by
  classical
  have hhp : HasPrime n := ⟨k, hk, hp⟩
  rw [a110408, dif_pos hhp]
  congr 1
  refine le_antisymm (Nat.find_min' hhp ⟨hk, hp⟩) ?_
  by_contra hlt
  obtain ⟨hj1, hjp⟩ := Nat.find_spec hhp
  exact hmin _ (not_le.mp hlt) hj1 hjp

/-! ## Corrected "if" direction -/

/-- **Corrected "if" direction.**  If `n ≡ 1, 3, 7, 9 (mod 10)` and `n` is a
palindrome other than `1`, or `3 ∣ n`, then no candidate `rev(n)^k n` with
`k ≥ 1` is prime, i.e. `a(n) = 0`.  (For `n = 1` the candidate `11` is prime.) -/
theorem a110408_eq_zero_of_palindrome_or_three_dvd {n : ℕ}
    (hn : n % 10 ∈ ({1, 3, 7, 9} : Finset ℕ))
    (h : (rev n = n ∧ 2 ≤ n) ∨ 3 ∣ n) : a110408 n = 0 := by
  have h10 : n % 10 ≠ 0 := by
    intro h0; rw [h0] at hn; simp at hn
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exact absurd rfl h10
    · exact hpos
  have hr : rev n ≠ 0 := rev_ne_zero h10
  rw [a110408_eq_zero_iff]
  rintro ⟨k, hk, hp⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hbig := ten_mul_rev_le_cand_succ hn1 j
  rcases h with ⟨hpal, h2⟩ | h3
  · have hdvd : n ∣ cand n (j + 1) := dvd_cand dvd_rfl (by rw [hpal]) (j + 1)
    rcases hp.eq_one_or_self_of_dvd n hdvd with h1 | hself
    · omega
    · rw [hpal] at hbig; omega
  · have h3r : 3 ∣ rev n :=
      Nat.modEq_zero_iff_dvd.mp ((rev_modEq_three n).trans (Nat.modEq_zero_iff_dvd.mpr h3))
    have hdvd : 3 ∣ cand n (j + 1) := dvd_cand h3 h3r (j + 1)
    have hr1 : 1 ≤ rev n := Nat.pos_of_ne_zero hr
    rcases hp.eq_one_or_self_of_dvd 3 hdvd with h1 | hself
    · omega
    · omega

/-! ## Examples -/

-- Reversal and the candidate words.
example : rev 13 = 31 ∧ rev 121 = 121 ∧ rev 7 = 7 := by norm_num [rev, Nat.ofDigits_cons]

example : cand 1 1 = 11 ∧ cand 17 3 = 71717117 ∧ cand 23 3 = 32323223 ∧
    cand 31 3 = 13131331 := by
  norm_num [cand, concat, rev, Nat.ofDigits_cons]

-- The nonzero DATA terms at `n = 1, 17, 23, 31`.
example : a110408 1 = 11 := by
  have h : cand 1 1 = 11 := by norm_num [cand, concat, rev, Nat.ofDigits_cons]
  rw [a110408_eq_cand (k := 1) le_rfl (by rw [h]; norm_num) (fun j hj hj1 => by omega), h]

example : a110408 17 = 71717117 := by
  have h1 : cand 17 1 = 7117 := by norm_num [cand, concat, rev, Nat.ofDigits_cons]
  have h2 : cand 17 2 = 717117 := by norm_num [cand, concat, rev, Nat.ofDigits_cons]
  have h3 : cand 17 3 = 71717117 := by norm_num [cand, concat, rev, Nat.ofDigits_cons]
  refine (a110408_eq_cand (k := 3) (by norm_num) (by rw [h3]; norm_num) ?_).trans h3
  intro j hj hj1
  interval_cases j
  · rw [h1]; norm_num
  · rw [h2]; norm_num

-- The zero DATA terms at `n = 3, 7, 9, 11, 21, 27, 33, 39` (palindromic
-- primes `7, 11`; multiples of `3`).
example : a110408 7 = 0 ∧ a110408 11 = 0 :=
  ⟨a110408_eq_zero_of_palindrome_or_three_dvd (by decide)
      (Or.inl ⟨by norm_num [rev, Nat.ofDigits_cons], by norm_num⟩),
    a110408_eq_zero_of_palindrome_or_three_dvd (by decide)
      (Or.inl ⟨by norm_num [rev, Nat.ofDigits_cons], by norm_num⟩)⟩

example : ∀ n ∈ [3, 9, 21, 27, 33, 39], a110408 n = 0 := by
  intro n hn
  have hcases : n = 3 ∨ n = 9 ∨ n = 21 ∨ n = 27 ∨ n = 33 ∨ n = 39 := by
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using hn
  have h3 : 3 ∣ n := by omega
  have h10 : n % 10 ∈ ({1, 3, 7, 9} : Finset ℕ) := by
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact a110408_eq_zero_of_palindrome_or_three_dvd h10 (Or.inr h3)

/-! ## The conjecture and its refutation -/

/-- **Murthy's conjecture (A110408, unsigned comment of the entry by Amarnath
Murthy, Jul 30 2005).**

Verbatim: "Conjecture: a(n) is 0 iff n is a palindromic prime == 1,3,7 or 9
(mod 10) and/or n ==0 (mod 3)."

The sequence is only defined for `n ≡ 1, 3, 7, 9 (mod 10)`, which is the
guard; "palindromic" means `rev n = n`. -/
def Conjecture : Prop :=
  ∀ n : ℕ, n % 10 ∈ ({1, 3, 7, 9} : Finset ℕ) →
    (a110408 n = 0 ↔ (rev n = n ∧ n.Prime) ∨ 3 ∣ n)

/-- At `n = 121`, every candidate is a proper multiple of the palindrome
`121`, so `a(121) = 0`; but `121 = 11²` is not prime and `3 ∤ 121`.
The sufficient zero condition for palindromes or multiples of `3` is
`a110408_eq_zero_of_palindrome_or_three_dvd`; no converse is proved. -/
theorem conjecture_false : ¬ Conjecture := by
  intro hconj
  have h10 : (121 : ℕ) % 10 ∈ ({1, 3, 7, 9} : Finset ℕ) := by decide
  have hpal : rev 121 = 121 := by norm_num [rev, Nat.ofDigits_cons]
  have hzero : a110408 121 = 0 :=
    a110408_eq_zero_of_palindrome_or_three_dvd h10 (Or.inl ⟨hpal, by norm_num⟩)
  have hnotprime : ¬ (121 : ℕ).Prime := by norm_num
  have hnot3 : ¬ 3 ∣ (121 : ℕ) := by norm_num
  rcases (hconj 121 h10).mp hzero with ⟨-, hp⟩ | h3
  · exact hnotprime hp
  · exact hnot3 h3

end Candidates.A110408Refutation
