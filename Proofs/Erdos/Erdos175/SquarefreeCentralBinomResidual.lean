import Erdos.Erdos175.NotSquarefree

set_option autoImplicit false

namespace Erdos175.A046098.Residual

/-- The sum of the first `fuel` base-`p` digits, computed by structural recursion.
The correctness theorem below assumes `1 < p` and enough fuel. -/
def digitSum (p : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, n => n % p + digitSum p fuel (n / p)

example : digitSum 7 18 40 = 10 := by decide
example : digitSum 7 0 40 = 0 := rfl
example : 1 < 7 ∧ (40 : ℕ) < 7 ^ 18 := by decide

/-- Zero has truncated digit sum zero at every fuel. -/
@[simp] theorem digitSum_zero (p fuel : ℕ) : digitSum p fuel 0 = 0 := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp [digitSum, ih]

/-- With enough fuel and a genuine positional base, the structurally recursive
sum agrees with the sum of Mathlib's digits. -/
theorem digitSum_eq_sum_digits {p fuel n : ℕ} (hp : 1 < p) (hn : n < p ^ fuel) :
    digitSum p fuel n = (Nat.digits p n).sum := by
  induction fuel generalizing n with
  | zero =>
    have hn0 : n = 0 := by simpa using hn
    subst n
    simp [digitSum]
  | succ fuel ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp
    · have hdiv : n / p < p ^ fuel := by
        apply (Nat.div_lt_iff_lt_mul (by omega)).mpr
        simpa only [pow_succ] using hn
      rw [digitSum, Nat.digits_def' hp hn0, List.sum_cons, ih hdiv]

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

end Erdos175.A046098.Residual
