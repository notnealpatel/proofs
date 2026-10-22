/-
# Prime decimal sandwiches (A068689)

Source: Cino Hilliard's OEIS A068689 comment (Jul 11 2005).
For a decimal digit `d`, some number `9 d^k 9` with `k > 0` is prime iff
`d ∈ {1,2,8}`, witnessed by 919, 929 and 9888889.
For every other digit and every `k ≥ 0`, one of 3, 7, 11, 13 divides the
sandwich. Its residue modulo 3003 depends only on `k mod 6`.
The palindrome digit list makes the little-endian `Nat.ofDigits` convention
immaterial; at `k = 0` the sandwich is 99.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A068689DigitDecimalCopies

/-- The repdigit with `k` decimal digits all equal to `d`, i.e. `d·(10ᵏ − 1)/9`. -/
def repdigit (d k : ℕ) : ℕ := Nat.ofDigits 10 (List.replicate k d)

/-- The decimal "sandwich" `9 d…d 9`: a 9, then `k` copies of the digit `d`,
then a 9 (A068689). -/
def sandwich (d k : ℕ) : ℕ := Nat.ofDigits 10 (9 :: (List.replicate k d ++ [9]))

/-! ### Listed terms of A068689 -/

example : repdigit 7 3 = 777 := by decide
example : sandwich 1 1 = 919 := by decide
example : sandwich 2 1 = 929 := by decide
example : sandwich 2 5 = 9222229 := by decide
example : sandwich 8 5 = 9888889 := by decide
example : sandwich 2 11 = 9222222222229 := by decide
example : sandwich 4 3 = 94449 := by decide
example : sandwich 5 0 = 99 := by decide

/-! ### Closed form and period six -/

/-- Closed form: `9 dᵏ 9 = 9 + 10 · (dᵏ) + 9 · 10^(k+1)`. -/
theorem sandwich_eq (d k : ℕ) : sandwich d k = 9 + 10 * repdigit d k + 9 * 10 ^ (k + 1) := by
  simp only [sandwich, repdigit, Nat.ofDigits_cons, Nat.ofDigits_append, List.length_replicate,
    Nat.ofDigits_nil]
  ring

/-- Appending six digits `d` on the left adds `10ᵏ · 111111 · d` to a repdigit. -/
theorem repdigit_add_six (d k : ℕ) :
    repdigit d (k + 6) = repdigit d k + 10 ^ k * (111111 * d) := by
  have h6 : repdigit d 6 = 111111 * d := by
    simp only [repdigit, List.replicate, Nat.ofDigits_cons, Nat.ofDigits_nil]
    ring
  rw [← h6, repdigit, List.replicate_add, Nat.ofDigits_append, List.length_replicate]
  rfl

/-- Six more inner digits change the sandwich by a multiple of `3003 = 3·7·11·13`. -/
theorem sandwich_add_six (d k : ℕ) :
    sandwich d (k + 6) = sandwich d k + 3003 * (37 * (d + 81) * 10 ^ (k + 1)) := by
  rw [sandwich_eq, sandwich_eq, repdigit_add_six]
  ring

/-- The residue of `9 dᵏ 9` modulo `3003` depends only on `k mod 6`. -/
theorem sandwich_mod_3003 (d k : ℕ) : sandwich d k % 3003 = sandwich d (k % 6) % 3003 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.lt_or_ge k 6 with hk | hk
    · rw [Nat.mod_eq_of_lt hk]
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 6 := ⟨k - 6, by omega⟩
      rw [sandwich_add_six, Nat.add_mul_mod_self_left, ih j (by omega), Nat.add_mod_right]

/-- Every sandwich is at least `99`. -/
theorem ninetyNine_le_sandwich (d k : ℕ) : 99 ≤ sandwich d k := by
  have hpow : 10 ≤ 10 ^ (k + 1) := by
    calc 10 = 10 ^ 1 := by norm_num
      _ ≤ 10 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [sandwich_eq]
  omega

/-- Finite covering check: for each inner digit `d ∈ {0, 3, 4, 5, 6, 7, 9}` and each
`r < 6`, one of `3, 7, 11, 13` divides `9 dʳ 9`. -/
theorem covering_base : ∀ d ∈ [0, 3, 4, 5, 6, 7, 9], ∀ r ∈ List.range 6,
    3 ∣ sandwich d r ∨ 7 ∣ sandwich d r ∨ 11 ∣ sandwich d r ∨ 13 ∣ sandwich d r := by
  decide

/-- A prime `p ∣ 3003` dividing `9 d^(k mod 6) 9` divides `9 dᵏ 9`. -/
theorem dvd_sandwich_of_dvd_mod_six {p d k : ℕ} (hp : p ∣ 3003)
    (h : p ∣ sandwich d (k % 6)) : p ∣ sandwich d k := by
  rw [← Nat.dvd_mod_iff hp, sandwich_mod_3003, Nat.dvd_mod_iff hp]
  exact h

/-- The covering: for `d ∈ {0, 3, 4, 5, 6, 7, 9}`, some `p ∈ {3, 7, 11, 13}` divides
`9 dᵏ 9` for every `k`. -/
theorem exists_small_dvd_sandwich {d : ℕ} (hd : d ∈ ({0, 3, 4, 5, 6, 7, 9} : Finset ℕ))
    (k : ℕ) : ∃ p, 3 ≤ p ∧ p ≤ 13 ∧ p ∣ sandwich d k := by
  have hd' : d ∈ [0, 3, 4, 5, 6, 7, 9] := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    exact hd
  have hr : k % 6 ∈ List.range 6 := List.mem_range.mpr (Nat.mod_lt k (by norm_num))
  rcases covering_base d hd' (k % 6) hr with h | h | h | h
  · exact ⟨3, le_rfl, by norm_num, dvd_sandwich_of_dvd_mod_six (by norm_num) h⟩
  · exact ⟨7, by norm_num, by norm_num, dvd_sandwich_of_dvd_mod_six (by norm_num) h⟩
  · exact ⟨11, by norm_num, by norm_num, dvd_sandwich_of_dvd_mod_six (by norm_num) h⟩
  · exact ⟨13, by norm_num, le_rfl, dvd_sandwich_of_dvd_mod_six (by norm_num) h⟩

/-! ## The conjecture -/

/-- Hilliard's composite cases: for `d ∈ {0,3,4,5,6,7,9}` and every `k`,
the sandwich `9 d^k 9` is composite, by a covering with 3, 7, 11 and 13. -/
theorem sandwich_not_prime {d : ℕ} (hd : d ∈ ({0, 3, 4, 5, 6, 7, 9} : Finset ℕ)) (k : ℕ) :
    ¬ (sandwich d k).Prime := by
  obtain ⟨p, hp3, hp13, hdvd⟩ := exists_small_dvd_sandwich hd k
  have hlt : p < sandwich d k := lt_of_le_of_lt hp13 (by linarith [ninetyNine_le_sandwich d k])
  exact Nat.not_prime_of_dvd_of_lt hdvd (by omega) hlt

/-- **Hilliard's conjecture (A068689), full characterization.**

For a decimal digit `d < 10`, some sandwich `9 dᵏ 9` with `k ≥ 1` inner digits is
prime if and only if `d ∈ {1, 2, 8}`.  The witnesses are the listed terms
`919 = 9 1 9`, `929 = 9 2 9` and `9888889 = 9 8⁵ 9`. -/
theorem exists_prime_sandwich_iff {d : ℕ} (hd : d < 10) :
    (∃ k, 0 < k ∧ (sandwich d k).Prime) ↔ d = 1 ∨ d = 2 ∨ d = 8 := by
  constructor
  · rintro ⟨k, -, hprime⟩
    by_contra hne
    have hmem : d ∈ ({0, 3, 4, 5, 6, 7, 9} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    exact sandwich_not_prime hmem k hprime
  · rintro (rfl | rfl | rfl)
    · refine ⟨1, by norm_num, ?_⟩
      rw [show sandwich 1 1 = 919 by decide]
      norm_num
    · refine ⟨1, by norm_num, ?_⟩
      rw [show sandwich 2 1 = 929 by decide]
      norm_num
    · refine ⟨5, by norm_num, ?_⟩
      rw [show sandwich 8 5 = 9888889 by decide]
      norm_num

end Candidates.A068689DigitDecimalCopies
