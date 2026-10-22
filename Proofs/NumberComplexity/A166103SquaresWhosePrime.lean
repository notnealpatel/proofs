/-
# A166103 — Karttunen: `a(n) = A166102(n) / 3`

OEIS A166103, Antti Karttunen: `a(n) = A166102(n)/3`, with exact
natural division. A166103 consists of squares of positive integers
whose prime factors are `3` or `5 mod 6` (A166104). A166102 consists of
odd `k` for which the sum of positive `i ≤ k` with Jacobi symbol
`J(i,k) = 1` is not divisible by `k`.
This follows from `Enumerative.A166102OddJacobiSymbol`; both
enumerations use index `0` for the OEIS index `1`.
-/
import Mathlib
import Enumerative.A166102OddJacobiSymbol

set_option autoImplicit false

namespace Candidates.A166103SquaresWhosePrime

open Candidates.A166102OddJacobiSymbol

/-! ## Definitions

The imported membership predicates are:

* `IsA166104 n := 0 < n ∧ ∀ p ∈ n.primeFactors, p % 6 = 3 ∨ p % 6 = 5`;
* `IsA166103 x := ∃ n, IsA166104 n ∧ x = n ^ 2` (squares of A166104);
* `IsA166102 k := Odd k ∧ ¬ k ∣ A166100 ((k - 1) / 2)`, with
  `A166100 n = ∑_{1 ≤ i ≤ 2n+1, J(i, 2n+1) = 1} i`.

The sequences are their increasing enumerations by `Nat.nth`, indexed from `0`
(OEIS offset `1`; both sequences are shifted by the same amount). -/

/-- **A166103** as a sequence: the `n`-th (from `0`) square of a positive integer all of
whose prime factors are `≡ 3` or `5 (mod 6)`; `A166103 0 = 1` is the OEIS `a(1)`. -/
noncomputable def A166103 (n : ℕ) : ℕ := Nat.nth IsA166103 n

/-- **A166102** as a sequence: the `n`-th (from `0`) odd `k` with `k ∤ A166100((k-1)/2)`;
`A166102 0 = 3` is the OEIS `a(1)`. -/
noncomputable def A166102 (n : ℕ) : ℕ := Nat.nth IsA166102 n

/-- Members of A166103 below `26` are exactly `1, 9, 25`. -/
theorem isA166103_iff_of_lt {x : ℕ} (hx : x < 26) : IsA166103 x ↔ x = 1 ∨ x = 9 ∨ x = 25 := by
  constructor
  · rintro ⟨n, ⟨hn0, hn⟩, rfl⟩
    have hn5 : n ≤ 5 := by nlinarith
    interval_cases n
    · simp
    · exact absurd (hn 2 (by simp [Nat.prime_two.primeFactors])) (by decide)
    · simp
    · have h2 : 2 ∈ (4 : ℕ).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨Nat.prime_two, by norm_num, by norm_num⟩
      exact absurd (hn 2 h2) (by decide)
    · simp
  · rintro (rfl | rfl | rfl)
    · exact ⟨1, ⟨by norm_num, by simp⟩, rfl⟩
    · exact ⟨3, ⟨by norm_num, by simp [Nat.prime_three.primeFactors]⟩, rfl⟩
    · exact ⟨5, ⟨by norm_num, by simp [Nat.prime_five.primeFactors]⟩, rfl⟩

/-! ### Examples against the DATA lines -/

-- A166103: 1, 9, 25, ...
example : A166103 0 = 1 := by
  classical
  have h := Nat.nth_count (p := IsA166103) ((isA166103_iff_of_lt (by norm_num)).mpr
    (Or.inl rfl) : IsA166103 1)
  have hc : Nat.count IsA166103 1 = 0 := by
    rw [Nat.count_eq_card_filter_range, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x hx
    have hx1 : x < 1 := Finset.mem_range.mp hx
    rw [isA166103_iff_of_lt (by omega)]
    omega
  rw [hc] at h
  exact h

example : A166103 1 = 9 := by
  classical
  have h := Nat.nth_count (p := IsA166103) ((isA166103_iff_of_lt (by norm_num)).mpr
    (Or.inr (Or.inl rfl)) : IsA166103 9)
  have hc : Nat.count IsA166103 9 = 1 := by
    rw [Nat.count_eq_card_filter_range, Finset.card_eq_one]
    refine ⟨1, Finset.ext fun x => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, hm⟩
      rcases (isA166103_iff_of_lt (by omega)).mp hm with h1 | h1 | h1 <;> omega
    · rintro rfl
      exact ⟨by norm_num, (isA166103_iff_of_lt (by norm_num)).mpr (Or.inl rfl)⟩
  rw [hc] at h
  exact h

example : A166103 2 = 25 := by
  classical
  have h := Nat.nth_count (p := IsA166103) ((isA166103_iff_of_lt (by norm_num)).mpr
    (Or.inr (Or.inr rfl)) : IsA166103 25)
  have hc : Nat.count IsA166103 25 = 2 := by
    rw [Nat.count_eq_card_filter_range, Finset.card_eq_two]
    refine ⟨1, 9, by norm_num, Finset.ext fun x => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, hm⟩
      rcases (isA166103_iff_of_lt (by omega)).mp hm with h1 | h1 | h1 <;> omega
    · rintro (rfl | rfl)
      · exact ⟨by norm_num, (isA166103_iff_of_lt (by norm_num)).mpr (Or.inl rfl)⟩
      · exact ⟨by norm_num, (isA166103_iff_of_lt (by norm_num)).mpr (Or.inr (Or.inl rfl))⟩
  rw [hc] at h
  exact h

-- 49 = 7² and 4 = 2² are not members (7 ≡ 1 and 2 ≡ 2 mod 6).
example : ¬ IsA166103 4 := by
  rw [isA166103_iff_of_lt (by norm_num)]
  omega

example : ¬ IsA166103 49 := by
  rintro ⟨n, ⟨-, hn⟩, hx⟩
  have h7 : n = 7 := by nlinarith
  subst h7
  exact absurd (hn 7 (by simp [(by norm_num : Nat.Prime 7).primeFactors])) (by decide)

/-! ## The conjecture -/

/-- Every term of A166102 is a multiple of `3`, so `A166102(n) / 3` is exact division. -/
theorem three_dvd_A166102 (n : ℕ) : 3 ∣ A166102 n := by
  rw [A166102, a166102_eq_three_mul_a166103]
  exact dvd_mul_right 3 _

/-- Karttunen’s conjecture (A166103): each term is one third of the
corresponding A166102 term, with both enumerations indexed from `0`
here rather than `1` as in OEIS. Division is exact by `three_dvd_A166102`;
the equality follows from
`Candidates.A166102OddJacobiSymbol.a166102_eq_three_mul_a166103`. -/
theorem a166103_conjecture (n : ℕ) : A166103 n = A166102 n / 3 := by
  rw [A166102, a166102_eq_three_mul_a166103, Nat.mul_div_cancel_left _ (by norm_num), A166103]

end Candidates.A166103SquaresWhosePrime
