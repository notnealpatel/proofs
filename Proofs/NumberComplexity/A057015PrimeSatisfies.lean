/-
# A057015 — Dale: every term after the first is divisible by 10

OEIS A057015, Harvey P. Dale: every term greater than `2` is divisible
by `10`. A term has all of `k² + 1, k² + 3, k² + 7, k² + 9` prime.

If `k` is odd then `k^2 + 1` is even and greater than `2`.  Modulo `5`,
`k^2 ≡ 0, 1, 4`.  If `k^2 ≡ 1` then `5 ∣ k^2 + 9 > 5`; if `k^2 ≡ 4` then
`5 ∣ k^2 + 1 > 5` once `k > 2`.  Hence `2 ∣ k` and `5 ∣ k`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A057015PrimeSatisfies

/-- Membership in A057015: `k^2 + 1`, `k^2 + 3`, `k^2 + 7` and `k^2 + 9`
are all prime. -/
def IsTerm (k : ℕ) : Prop :=
  (k ^ 2 + 1).Prime ∧ (k ^ 2 + 3).Prime ∧ (k ^ 2 + 7).Prime ∧ (k ^ 2 + 9).Prime

/-- `IsTerm` is decidable, by deciding primality of the four values. -/
instance (k : ℕ) : Decidable (IsTerm k) := by
  unfold IsTerm
  infer_instance

/-! ## Examples against the DATA line -/

-- The first two listed terms `2, 10` are terms.
example : IsTerm 2 := by unfold IsTerm; norm_num
example : IsTerm 10 := by unfold IsTerm; norm_num
-- The third listed term `1420` is a term.
example : IsTerm 1420 := by unfold IsTerm; norm_num
-- The listed terms are consecutive: nothing in `[0, 10]` besides `2, 10`.
example : ∀ k < 11, IsTerm k → k = 2 ∨ k = 10 := by decide

/-! ## Helper lemmas -/

/-- A term greater than `2` is even: otherwise `k^2 + 1` would be an even
number greater than `2`. -/
theorem two_dvd_of_isTerm {k : ℕ} (hk : 2 < k) (h : IsTerm k) : 2 ∣ k := by
  by_contra hodd
  have hk2 : k % 2 = 1 := by omega
  have hdvd : 2 ∣ k ^ 2 + 1 := by
    rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.pow_mod, hk2]
  have hlt : 2 < k ^ 2 + 1 := by nlinarith
  have heq := (Nat.prime_dvd_prime_iff_eq Nat.prime_two h.1).mp hdvd
  omega

/-- A term greater than `2` is divisible by `5`: otherwise `5` divides
`k^2 + 1` or `k^2 + 9`, both greater than `5`. -/
theorem five_dvd_of_isTerm {k : ℕ} (hk : 2 < k) (h : IsTerm k) : 5 ∣ k := by
  obtain ⟨h1, -, -, h9⟩ := h
  have hlt : 9 ≤ k ^ 2 := by nlinarith
  have hmod : k % 5 = 0 ∨ k % 5 = 1 ∨ k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4 := by
    omega
  rcases hmod with h0 | h0 | h0 | h0 | h0
  · exact Nat.dvd_of_mod_eq_zero h0
  all_goals exfalso
  · -- `k^2 ≡ 1`, so `5 ∣ k^2 + 9`
    have hdvd : 5 ∣ k ^ 2 + 9 := by
      rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.pow_mod, h0]
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_five h9).mp hdvd
    omega
  · -- `k^2 ≡ 4`, so `5 ∣ k^2 + 1`
    have hdvd : 5 ∣ k ^ 2 + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.pow_mod, h0]
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_five h1).mp hdvd
    omega
  · -- `k^2 ≡ 4`, so `5 ∣ k^2 + 1`
    have hdvd : 5 ∣ k ^ 2 + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.pow_mod, h0]
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_five h1).mp hdvd
    omega
  · -- `k^2 ≡ 1`, so `5 ∣ k^2 + 9`
    have hdvd : 5 ∣ k ^ 2 + 9 := by
      rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.pow_mod, h0]
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_five h9).mp hdvd
    omega

/-! ## The conjecture -/

/-- **Dale's conjecture (A057015, Harvey P. Dale, 2026).**

Every `k > 2` with `k^2 + 1`, `k^2 + 3`, `k^2 + 7` and
`k^2 + 9` all prime satisfies `10 ∣ k`.  The first term is `2`; the guard
`2 < k` excludes it and is load-bearing (`IsTerm 2` and `¬ 10 ∣ 2`). -/
theorem dale_ten_dvd (k : ℕ) (hk : 2 < k) (h : IsTerm k) : 10 ∣ k := by
  have h2 : 2 ∣ k := two_dvd_of_isTerm hk h
  have h5 : 5 ∣ k := five_dvd_of_isTerm hk h
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h5

/-! ## Examples -/

-- Non-vacuity: the hypotheses are jointly satisfiable at `k = 10`.
example : 2 < 10 ∧ IsTerm 10 := ⟨by norm_num, by unfold IsTerm; norm_num⟩

-- The guard `2 < k` is load-bearing: `k = 2` is a term not divisible by `10`.
example : IsTerm 2 ∧ ¬ 10 ∣ 2 := ⟨by unfold IsTerm; norm_num, by norm_num⟩

end Candidates.A057015PrimeSatisfies
