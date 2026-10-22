/-
# A101462 — Zhou: for every prime `p` some `2^k - p` is prime (refuted)

OEIS A101462, Lei Zhou: the sequence need not be defined at every
positive index. The prime `p = 509203` has no prime difference `2^k - p`.
The classes modulo `24` are covered by `3, 5, 7, 13, 17, 241`.
For `k ≥ 19` the positive difference exceeds each covering prime; for
`k ≤ 18` it is negative, represented here by truncated subtraction.
This is the dual of Riesel's covering for `p·2^k - 1`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A101462Refutation

/-! ## Definitions -/

/-- `k` is admissible for the prime `p` in A101462: `k ≥ 1`, the
difference `2^k - p` is positive (so the truncated `ℕ` subtraction is the
true difference), and it is prime. -/
def Admissible (p k : ℕ) : Prop :=
  0 < k ∧ p < 2 ^ k ∧ (2 ^ k - p).Prime

instance (p k : ℕ) : Decidable (Admissible p k) := by
  unfold Admissible; infer_instance

/-- `a` is the term `a(n)` of A101462: the least admissible `k` for
`prime(n) = Nat.nth Nat.Prime (n - 1)` (OEIS offset `1`; the guard
`0 < n` keeps `n - 1` off its junk value). -/
def IsA101462Term (n a : ℕ) : Prop :=
  0 < n ∧ IsLeast {k : ℕ | Admissible (Nat.nth Nat.Prime (n - 1)) k} a

/-! ### Examples against the listed terms `a(1), a(2), a(3), a(5), a(6) = 2, 3, 3, 4, 4` -/

/-- Least-element check by a finite scan below `a`. -/
theorem isA101462Term_of_check (n a : ℕ) (hn : 0 < n)
    (ha : Admissible (Nat.nth Nat.Prime (n - 1)) a)
    (hlt : ∀ k < a, ¬ Admissible (Nat.nth Nat.Prime (n - 1)) k) :
    IsA101462Term n a :=
  ⟨hn, ha, fun k hk => not_lt.mp fun hka => hlt k hka hk⟩

example : IsA101462Term 1 2 := by
  refine isA101462Term_of_check 1 2 (by norm_num) ?_ ?_ <;>
    simp only [Nat.sub_self, Nat.nth_prime_zero_eq_two] <;> decide

example : IsA101462Term 2 3 := by
  refine isA101462Term_of_check 2 3 (by norm_num) ?_ ?_ <;>
    simp only [Nat.add_one_sub_one, Nat.nth_prime_one_eq_three] <;> decide

example : IsA101462Term 3 3 := by
  refine isA101462Term_of_check 3 3 (by norm_num) ?_ ?_ <;>
    simp only [Nat.add_one_sub_one, Nat.nth_prime_two_eq_five] <;> decide

example : IsA101462Term 5 4 := by
  refine isA101462Term_of_check 5 4 (by norm_num) ?_ ?_ <;>
    simp only [Nat.add_one_sub_one, Nat.nth_prime_four_eq_eleven] <;> decide

/-! ## The conjecture -/

/-- **Zhou's conjecture (A101462, Lei Zhou, 2005).**
That is, for every
`n ≥ 1` there is `k ≥ 1` with `2^k - prime(n)` a (positive) prime. -/
def Conjecture : Prop :=
  ∀ n : ℕ, 0 < n → ∃ k : ℕ, Admissible (Nat.nth Nat.Prime (n - 1)) k

/-! ## The counterexample `p = 509203` -/

/-- `509203` is prime. -/
theorem prime_509203 : Nat.Prime 509203 := by norm_num

/-- The covering primes all satisfy `2^24 ≡ 1`. -/
theorem covering_period :
    ∀ q ∈ [3, 5, 7, 13, 17, 241], 2 ^ 24 % q = 1 := by decide

/-- The covering: every residue `r` of `k` modulo `24` has a covering prime
`q` with `2^r ≡ 509203 (mod q)`. -/
theorem covering :
    ∀ r < 24, ∃ q ∈ [3, 5, 7, 13, 17, 241], 2 ^ r % q = 509203 % q := by decide

/-- If `2^24 ≡ 1 (mod q)` then `2^k ≡ 2^(k % 24) (mod q)`. -/
theorem two_pow_mod_of_period (q k : ℕ) (hq : 2 ^ 24 % q = 1) :
    2 ^ k % q = 2 ^ (k % 24) % q := by
  conv_lhs => rw [← Nat.div_add_mod k 24, pow_add, pow_mul]
  rw [Nat.mul_mod, Nat.pow_mod, hq, one_pow, Nat.one_mod_eq_one.mpr ?_, one_mul, Nat.mod_mod]
  rintro rfl
  simp at hq

/-- No `2^k - 509203` is prime (with truncated subtraction; for `2^k ≤ p`
the difference is `0`). -/
theorem not_prime_two_pow_sub (k : ℕ) : ¬ (2 ^ k - 509203).Prime := by
  intro hprime
  have hle : 509203 < 2 ^ k := by
    by_contra hk
    rw [Nat.sub_eq_zero_of_le (not_lt.mp hk)] at hprime
    exact Nat.not_prime_zero hprime
  have hk19 : 19 ≤ k := by
    by_contra hk
    have h18 : 2 ^ k ≤ 2 ^ 18 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hbig : 2 ^ 19 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk19
  obtain ⟨q, hq, hcov⟩ := covering (k % 24) (Nat.mod_lt k (by norm_num))
  have hmod : 2 ^ k % q = 509203 % q := by
    rw [two_pow_mod_of_period q k (covering_period q hq), hcov]
  have hdvd : q ∣ 2 ^ k - 509203 :=
    Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hmod)
  have hqbounds : 1 < q ∧ q ≤ 241 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  rcases hprime.eq_one_or_self_of_dvd q hdvd with h1 | hself
  · omega
  · omega

/-- Riesel’s prime `509203` gives an undefined term of A101462: no
`2^k - 509203` is prime, by the covering classes modulo `24`.
The proof obtains a positive prime index from `Nat.nth_count`,
without evaluating `Nat.count Nat.Prime 509203`. -/
theorem conjecture_false : ¬ Conjecture := by
  intro h
  have hnth : Nat.nth Nat.Prime (Nat.count Nat.Prime 509203) = 509203 :=
    Nat.nth_count prime_509203
  generalize Nat.count Nat.Prime 509203 = m at hnth
  obtain ⟨k, -, -, hk⟩ := h (m + 1) (Nat.add_one_pos m)
  rw [Nat.add_sub_cancel, hnth] at hk
  exact not_prime_two_pow_sub k hk

end Candidates.A101462Refutation
