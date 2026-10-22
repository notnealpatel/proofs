/-
# A177680 — Dale: every term after the first is a multiple of 5

OEIS A177680, Harvey P. Dale: every term `n > 1` is a multiple of `5`.
For `n ≡ 1,2,3,4 (mod 5)`, respectively `6n-1`, `12n+1`, `12n-1`,
`6n+1` is divisible by `5` and greater than `5`, contradicting primality.
The first term `n = 1` is excluded.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A177680PrimeMultiple

/-- `n` is a term of OEIS A177680: `n` is positive and both `6n` and `12n` are
averages of twin prime pairs, i.e. `6n-1`, `6n+1`, `12n-1`, `12n+1` are all
prime.  The positivity guard keeps the natural subtractions off their junk
value. -/
def IsTerm (n : ℕ) : Prop :=
  0 < n ∧ (6 * n - 1).Prime ∧ (6 * n + 1).Prime ∧ (12 * n - 1).Prime ∧
    (12 * n + 1).Prime

instance : DecidablePred IsTerm := fun n => by
  unfold IsTerm
  infer_instance

/-! ## Examples against the listed terms -/

example : IsTerm 1 := by unfold IsTerm; norm_num
example : IsTerm 5 := by unfold IsTerm; norm_num
example : IsTerm 110 := by unfold IsTerm; norm_num
example : IsTerm 135 := by unfold IsTerm; norm_num
example : ¬ IsTerm 2 := by unfold IsTerm; norm_num
example : ¬ IsTerm 10 := by unfold IsTerm; norm_num

/-- A prime divisible by `5` equals `5`. -/
theorem five_dvd_prime_eq {p : ℕ} (hp : p.Prime) (h5 : 5 ∣ p) : p = 5 :=
  ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp h5).symm

/-- **A177680, Dale's conjecture (Sep 26 2017).**  Every term `n > 1` of
A177680 (so `6n±1` and `12n±1` are all prime) is a multiple of 5. -/
theorem five_dvd_of_isTerm {n : ℕ} (hn : 1 < n) (h : IsTerm n) : 5 ∣ n := by
  obtain ⟨_, h6m, h6p, h12m, h12p⟩ := h
  have hr : n % 5 < 5 := Nat.mod_lt n (by norm_num)
  interval_cases hmod : n % 5
  · exact Nat.dvd_of_mod_eq_zero hmod
  · have h5 : 5 ∣ 6 * n - 1 := by omega
    have heq := five_dvd_prime_eq h6m h5
    omega
  · have h5 : 5 ∣ 12 * n + 1 := by omega
    have heq := five_dvd_prime_eq h12p h5
    omega
  · have h5 : 5 ∣ 12 * n - 1 := by omega
    have heq := five_dvd_prime_eq h12m h5
    omega
  · have h5 : 5 ∣ 6 * n + 1 := by omega
    have heq := five_dvd_prime_eq h6p h5
    omega

/-- Non-vacuity: the hypotheses of `five_dvd_of_isTerm` hold jointly at
`n = 5`, the second listed term. -/
example : 1 < 5 ∧ IsTerm 5 := ⟨by norm_num, by unfold IsTerm; norm_num⟩

end Candidates.A177680PrimeMultiple
