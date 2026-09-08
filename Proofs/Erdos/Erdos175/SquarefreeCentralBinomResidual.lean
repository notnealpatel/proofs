import Erdos.Erdos175.NotSquarefree

set_option autoImplicit false

namespace Erdos175.A046098.Residual

/-- A natural number with binary digit sum two is the sum of two distinct
powers of two, ordered by exponent. -/
theorem exists_two_pow_add_two_pow_of_sum_digits_eq_two : ∀ {n : ℕ},
    (Nat.digits 2 n).sum = 2 → ∃ a b : ℕ, a < b ∧ n = 2 ^ a + 2 ^ b := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hsum
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp at hsum
    · rw [Nat.digits_def' (by norm_num : (1 : ℕ) < 2) hn, List.sum_cons] at hsum
      rcases Nat.mod_two_eq_zero_or_one n with h2 | h2
      · obtain ⟨a, b, hab, heq⟩ := ih (n / 2)
          (Nat.div_lt_self hn (by norm_num)) (by omega)
        refine ⟨a + 1, b + 1, by omega, ?_⟩
        rw [pow_succ', pow_succ']
        omega
      · obtain ⟨b, hb⟩ := Erdos175.exists_two_pow_of_sum_digits_eq_one
          (n := n / 2) (by omega)
        refine ⟨0, b + 1, by omega, ?_⟩
        rw [pow_zero, pow_succ']
        omega

example : (Nat.digits 2 40).sum = 2 := by decide
example : 3 < 5 ∧ (40 : ℕ) = 2 ^ 3 + 2 ^ 5 := by decide

/-- A power of two at most fifty million has exponent below twenty-six. -/
theorem exponent_lt_twenty_six {a : ℕ} (ha : 2 ^ a ≤ 50000000) : a < 26 := by
  apply (Nat.pow_lt_pow_iff_right (by norm_num : (1 : ℕ) < 2)).mp
  exact lt_of_le_of_lt ha (by norm_num : (50000000 : ℕ) < 2 ^ 26)

example : (2 : ℕ) ^ 25 ≤ 50000000 := by decide

/-- A two-carry digit-sum certificate at one of the odd primes `3`, `5`, or `7`.
Eighteen digits suffice for all inputs up to one hundred million in these bases. -/
def oddCarryCertificate (m : ℕ) : Prop :=
  digitSum 3 18 (2 * m) + 4 ≤ 2 * digitSum 3 18 m ∨
    digitSum 5 18 (2 * m) + 8 ≤ 2 * digitSum 5 18 m ∨
      digitSum 7 18 (2 * m) + 12 ≤ 2 * digitSum 7 18 m

instance (m : ℕ) : Decidable (oddCarryCertificate m) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

example : oddCarryCertificate 40 := by decide
example : oddCarryCertificate 64 := by decide
example : oddCarryCertificate 256 := by decide
example : ¬ oddCarryCertificate 36 := by decide

/-- Below fifty million a truncated certificate is a genuine Kummer digit-sum
certificate at a prime at least three. No binomial coefficient is evaluated. -/
theorem oddCarryCertificate_sound {m : ℕ} (hm : m ≤ 50000000)
    (hc : oddCarryCertificate m) :
    ∃ p : ℕ, 3 ≤ p ∧ p.Prime ∧
      (Nat.digits p (2 * m)).sum + 2 * (p - 1) ≤ 2 * (Nat.digits p m).sum := by
  have hex : ∃ p : ℕ, 3 ≤ p ∧ p.Prime ∧
      digitSum p 18 (2 * m) + 2 * (p - 1) ≤ 2 * digitSum p 18 m := by
    rcases hc with h3 | h5 | h7
    · exact ⟨3, by norm_num, by norm_num, h3⟩
    · exact ⟨5, by norm_num, by norm_num, h5⟩
    · exact ⟨7, by norm_num, by norm_num, h7⟩
  obtain ⟨p, hp3, hp, hcert⟩ := hex
  have hpow : 100000000 < p ^ 18 :=
    lt_of_lt_of_le (by norm_num : 100000000 < (3 : ℕ) ^ 18)
      (Nat.pow_le_pow_left hp3 18)
  have hbase : 1 < p := by omega
  rw [digitSum_eq_sum_digits hbase (by omega : 2 * m < p ^ 18),
    digitSum_eq_sum_digits hbase (by omega : m < p ^ 18)] at hcert
  exact ⟨p, hp3, hp, hcert⟩

example : (40 : ℕ) ≤ 50000000 ∧ oddCarryCertificate 40 := by decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- Kernel-checked carry certificates for the powers of two in the residual range.
The finite domain is the twenty-six exponents `0, ..., 25`, not the binomials. -/
theorem pow_certificate : ∀ a : Fin 26,
    37 ≤ 2 ^ a.val → 2 ^ a.val ≤ 50000000 → oddCarryCertificate (2 ^ a.val) := by
  decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- Kernel-checked carry certificates for sums of two distinct powers of two in
the residual range. Together with `pow_certificate` these cover 331 numbers;
only bounded digit sums are computed, using ordinary kernel reduction. -/
theorem sum_certificate : ∀ a b : Fin 26, a.val < b.val →
    37 ≤ 2 ^ a.val + 2 ^ b.val → 2 ^ a.val + 2 ^ b.val ≤ 50000000 →
      oddCarryCertificate (2 ^ a.val + 2 ^ b.val) := by
  decide

example : (⟨9, by decide⟩ : Fin 72).val = 9 ∧ Odd 9 := by decide
example : (36 : ℕ) < 2 ^ 6 := by decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- For each odd index below `72`, either it is one of the listed A046098
terms, its half-successor has at least three binary ones, or an odd-prime
carry certificate rules it out. This kernel check includes the ten small
residual indices `9, 15, 31, 33, 35, 39, 47, 63, 65, 67`. Six binary digits
suffice because the half-successor is at most `36`. -/
theorem small_odd_certificate : ∀ n : Fin 72, Odd n.val →
    n.val ∈ ([0, 1, 2, 3, 4, 5, 7, 8, 11, 17, 19, 23, 71] : List ℕ) ∨
      3 ≤ digitSum 2 6 (n.val / 2 + 1) ∨ oddCarryCertificate (n.val / 2 + 1) := by
  decide

end Erdos175.A046098.Residual
