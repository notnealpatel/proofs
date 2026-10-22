/-
# A counterexample modulus for A365777

Source: Peter Bala's OEIS A365777 comment (Oct 23 2025).
For the source recurrence, `a(n+2) ≡ 3a(n) (mod 4)` and every term is odd.
Thus no eventual period divides `φ(4)=2`, refuting the proposed totient bound;
period 4 modulo 4 is proved.
The sequence is defined by the entry's recurrence, with finite checks
against its data and Stirling formula. The EGF
`(exp(2x)/(2-exp(2x)))^(3/4)` is not identified formally here.
No assertion about other moduli is made.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A365777Refutation

/-- A365777 via the entry's recurrence: `a(0) = 1` and
`a(n) = 3 a(n-1) + Sum_{k=1..n-1} 2^k binomial(n-1,k) a(n-k)`, written for
`n + 1` with the summation index shifted by one. -/
def a : ℕ → ℕ
  | 0 => 1
  | n + 1 => 3 * a n + ∑ k : Fin n, 2 ^ (k.val + 1) * n.choose (k.val + 1) * a (n - k.val)
decreasing_by all_goals omega

/-- The entry's closed form
`a(n) = Sum_{k=0..n} (-2)^(n-k) (Product_{j=0..k-1} (4j+3)) Stirling2(n,k)`,
used only as an independent cross-check of `a`.  The natural subtraction
`n - k` is guarded by `k ∈ range (n + 1)`. -/
def aStirling (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1),
    (-2 : ℤ) ^ (n - k) * (∏ j ∈ Finset.range k, (4 * (j : ℤ) + 3)) * n.stirlingSecond k

/-! ## Listed terms -/

example : a 0 = 1 := by norm_num [a]
example : a 1 = 3 := by norm_num [a]
example : a 2 = 15 := by norm_num [a, Fin.sum_univ_succ, Nat.choose]
example : a 3 = 117 := by norm_num [a, Fin.sum_univ_succ, Nat.choose]
example : a 4 = 1257 := by norm_num [a, Fin.sum_univ_succ, Nat.choose]
example : a 5 = 17163 := by norm_num [a, Fin.sum_univ_succ, Nat.choose]
example : a 6 = 284055 := by norm_num [a, Fin.sum_univ_succ, Nat.choose]
example : a 7 = 5522877 := by norm_num [a, Fin.sum_univ_succ, Nat.choose]
example : a 8 = 123344817 := by norm_num [a, Fin.sum_univ_succ, Nat.choose]
example : a 9 = 3111071283 := by norm_num [a, Fin.sum_univ_succ, Nat.choose]
example : a 10 = 87454712895 := by norm_num [a, Fin.sum_univ_succ, Nat.choose]

example : aStirling 3 = 117 := by decide
example : aStirling 10 = 87454712895 := by decide

/-! ## The conjecture -/

/-- Bala's A365777 assertion: for every positive modulus there is a
positive eventual period dividing its totient. -/
def Conjecture : Prop :=
  ∀ k : ℕ, 0 < k → ∃ p : ℕ, 0 < p ∧ p ∣ Nat.totient k ∧
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → a (n + p) ≡ a n [MOD k]

/-! ## Residues modulo 4 -/

/-- Modulo 4 only the `k = 1` term of the recurrence survives:
`a(n+1) ≡ (2n+3) a(n) (mod 4)`. -/
theorem a_succ_modEq (n : ℕ) : a (n + 1) ≡ (2 * n + 3) * a n [MOD 4] := by
  cases n with
  | zero => simp [a, Nat.ModEq]
  | succ m =>
    rw [a, Fin.sum_univ_succ]
    have hrest : 4 ∣ ∑ k : Fin m, 2 ^ ((k.succ : Fin (m + 1)).val + 1) *
        (m + 1).choose ((k.succ : Fin (m + 1)).val + 1) *
        a (m + 1 - (k.succ : Fin (m + 1)).val) := by
      apply Finset.dvd_sum
      intro k _
      have h4 : 4 ∣ 2 ^ ((k.succ : Fin (m + 1)).val + 1) := by
        rw [Fin.val_succ]
        exact pow_dvd_pow 2 (by omega : 2 ≤ k.val + 1 + 1)
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_right h4 _) _
    obtain ⟨c, hc⟩ := hrest
    rw [hc]
    simp only [Fin.val_zero, zero_add, pow_one, Nat.choose_one_right, Nat.sub_zero]
    have hring : 3 * a (m + 1) + (2 * (m + 1) * a (m + 1) + 4 * c)
        = (2 * (m + 1) + 3) * a (m + 1) + 4 * c := by ring
    rw [hring]
    exact Nat.add_mul_mod_self_left _ _ _

/-- Every term `a(n)` is odd. -/
theorem a_mod_two (n : ℕ) : a n % 2 = 1 := by
  induction n with
  | zero => simp [a]
  | succ n ih =>
    have h2 : a (n + 1) ≡ (2 * n + 3) * a n [MOD 2] :=
      (a_succ_modEq n).of_dvd (by norm_num)
    have hring : (2 * n + 3) * a n = a n + 2 * ((n + 1) * a n) := by ring
    rw [hring] at h2
    unfold Nat.ModEq at h2
    rw [h2, Nat.add_mul_mod_self_left, ih]

/-- Two steps of the recurrence multiply the residue by `3` modulo 4:
`a(n+2) ≡ 3 a(n) (mod 4)`. -/
theorem a_add_two_modEq (n : ℕ) : a (n + 2) ≡ 3 * a n [MOD 4] := by
  have h1 := a_succ_modEq (n + 1)
  have h0 := (a_succ_modEq n).mul_left (2 * (n + 1) + 3)
  have hring : (2 * (n + 1) + 3) * ((2 * n + 3) * a n)
      = 3 * a n + 4 * ((n ^ 2 + 4 * n + 3) * a n) := by ring
  rw [hring] at h0
  calc a (n + 2) ≡ (2 * (n + 1) + 3) * a (n + 1) [MOD 4] := h1
    _ ≡ 3 * a n + 4 * ((n ^ 2 + 4 * n + 3) * a n) [MOD 4] := h0
    _ ≡ 3 * a n [MOD 4] := Nat.add_mul_mod_self_left _ _ _

/-- For every `n`, `a(n+2) ≢ a(n) (mod 4)`: no period dividing `phi(4) = 2`
holds anywhere in the sequence. -/
theorem a_add_two_not_modEq (n : ℕ) : ¬ a (n + 2) ≡ a n [MOD 4] := by
  intro h
  have h3 : 3 * a n ≡ a n [MOD 4] := (a_add_two_modEq n).symm.trans h
  have hodd := a_mod_two n
  unfold Nat.ModEq at h3
  omega

/-- The sequence is purely periodic modulo 4 with period 4:
`a(n+4) ≡ a(n) (mod 4)` (residues `1, 3, 3, 1, ...`). -/
theorem a_add_four_modEq (n : ℕ) : a (n + 4) ≡ a n [MOD 4] := by
  have h2 : a (n + 2 + 2) ≡ 3 * a (n + 2) [MOD 4] := a_add_two_modEq (n + 2)
  calc a (n + 4) ≡ 3 * a (n + 2) [MOD 4] := h2
    _ ≡ 3 * (3 * a n) [MOD 4] := (a_add_two_modEq n).mul_left 3
    _ = a n + 4 * (2 * a n) := by ring
    _ ≡ a n [MOD 4] := Nat.add_mul_mod_self_left _ _ _

/-! ## The refutation -/

/-- Bala's totient-period bound fails modulo 4. The only positive divisors
of `φ(4)=2` are 1 and 2, but `a(n+2) ≡ 3a(n)` and all terms are odd,
so neither is an eventual period. Period 4 is given by `a_add_four_modEq`. -/
theorem conjecture_false : ¬ Conjecture := by
  intro h
  obtain ⟨p, hp, hpd, N, hN⟩ := h 4 (by norm_num)
  have htot : Nat.totient 4 = 2 := by decide
  rw [htot] at hpd
  have hp2 : p = 1 ∨ p = 2 := by
    have hle := Nat.le_of_dvd (by norm_num) hpd
    interval_cases p <;> simp_all
  have hper2 : a (N + 2) ≡ a N [MOD 4] := by
    rcases hp2 with rfl | rfl
    · exact (hN (N + 1) (by omega)).trans (hN N le_rfl)
    · exact hN N le_rfl
  exact a_add_two_not_modEq N hper2

end Candidates.A365777Refutation
