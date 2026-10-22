/-
# A115038 — every prime is `y^k - x^2` with `x ≥ 1`, `k ≥ 2`

OEIS A115038, Cino Hilliard: for every prime `p` there are `x ≥ 1`,
`y` and `k ≥ 2` with `x² + p = y^k`. These bounds follow the entry's
positive search range and perfect-power convention.
For odd `p`, use `((p-1)/2)² + p = ((p+1)/2)²`; for `p = 2`, use
`5² + 2 = 3³`. The least-`x` sequence uses OEIS offset `1`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A115038PrimeThereExist

/-! ## Definitions -/

/-- `m` is a perfect power: `m = y^k` for some `y` and some exponent `k ≥ 2`
(the entry's "perfect power", with exponent `n ≥ 2` in the comment). -/
def IsPerfectPower (m : ℕ) : Prop := ∃ y k : ℕ, 2 ≤ k ∧ y ^ k = m

/-- For `m ≥ 2` the witnesses of `IsPerfectPower m` are bounded by `m`, so
the predicate is a finite search.  Used for the examples. -/
theorem isPerfectPower_iff_bounded {m : ℕ} (hm : 2 ≤ m) :
    IsPerfectPower m ↔
      ∃ y ∈ Finset.range (m + 1), ∃ k ∈ Finset.range (m + 1), 2 ≤ k ∧ y ^ k = m := by
  constructor
  · rintro ⟨y, k, hk, hyk⟩
    have hy2 : 2 ≤ y := by
      rcases Nat.lt_or_ge y 2 with hy | hy
      · interval_cases y
        · rw [zero_pow (by omega)] at hyk; omega
        · rw [one_pow] at hyk; omega
      · exact hy
    have hyle : y ≤ m := by
      calc y = y ^ 1 := (pow_one y).symm
        _ ≤ y ^ k := Nat.pow_le_pow_right (by omega) (by omega)
        _ = m := hyk
    have hkle : k ≤ m := by
      calc k ≤ 2 ^ k := (Nat.lt_two_pow_self).le
        _ ≤ y ^ k := Nat.pow_le_pow_left hy2 k
        _ = m := hyk
    exact ⟨y, Finset.mem_range.mpr (by omega), k, Finset.mem_range.mpr (by omega), hk, hyk⟩
  · rintro ⟨y, _, k, _, hk, hyk⟩
    exact ⟨y, k, hk, hyk⟩

/-! ## The conjecture -/

/-- **Hilliard's conjecture (A115038, Cino Hilliard, 2006).**

With the entry's conventions (`x` searched from `1`,
perfect power exponent at least `2`): for every prime `p` there exist
`x ≥ 1`, `y` and `k ≥ 2` with `x^2 + p = y^k`.

Proof: `p = 2` uses `5^2 + 2 = 3^3`; an odd prime `p = 2m + 1` (so `m ≥ 1`)
uses `m^2 + p = (m + 1)^2`. -/
theorem exists_sq_add_prime_eq_pow (p : ℕ) (hp : p.Prime) :
    ∃ x y k : ℕ, 1 ≤ x ∧ 2 ≤ k ∧ x ^ 2 + p = y ^ k := by
  rcases hp.eq_two_or_odd' with h2 | hodd
  · subst h2
    exact ⟨5, 3, 3, by norm_num, by norm_num, by norm_num⟩
  · obtain ⟨m, hm⟩ := hodd
    have hp3 : 3 ≤ p := by
      have h2 := hp.two_le
      omega
    have hm1 : 1 ≤ m := by omega
    refine ⟨m, m + 1, 2, hm1, le_refl 2, ?_⟩
    subst hm
    ring

/-- The same statement in terms of `IsPerfectPower`: for every prime `p` some
`x ≥ 1` makes `x^2 + p` a perfect power. -/
theorem exists_isPerfectPower_sq_add_prime (p : ℕ) (hp : p.Prime) :
    ∃ x : ℕ, 1 ≤ x ∧ IsPerfectPower (x ^ 2 + p) := by
  obtain ⟨x, y, k, hx, hk, hxyk⟩ := exists_sq_add_prime_eq_pow p hp
  exact ⟨x, hx, y, k, hk, hxyk.symm⟩

/-- The entry's consequence: the set of primes of the form `y^k - x^2`
(`x ≥ 1`, `k ≥ 2`, subtraction carried out in `ℤ`) is infinite — in fact it
is the set of all primes. -/
theorem infinite_primes_eq_pow_sub_sq :
    {p : ℕ | p.Prime ∧ ∃ x y k : ℕ, 1 ≤ x ∧ 2 ≤ k ∧
      (p : ℤ) = (y : ℤ) ^ k - (x : ℤ) ^ 2}.Infinite := by
  refine Nat.infinite_setOfPred_prime.mono ?_
  intro p hp
  obtain ⟨x, y, k, hx, hk, hxyk⟩ := exists_sq_add_prime_eq_pow p hp
  refine ⟨hp, x, y, k, hx, hk, ?_⟩
  have hcast : ((x ^ 2 + p : ℕ) : ℤ) = ((y ^ k : ℕ) : ℤ) := by rw [hxyk]
  push_cast at hcast
  linarith

/-- `a115038 n` for `n ≥ 1`: the least `x ≥ 1` such that `x^2 + prime(n)` is
a perfect power, where `prime(n) = Nat.nth Nat.Prime (n - 1)` (offset 1).
The value at the junk index `n = 0` coincides with `a115038 1`; the
existence proof is `exists_isPerfectPower_sq_add_prime`. -/
noncomputable def a115038 (n : ℕ) : ℕ :=
  open Classical in
  Nat.find (exists_isPerfectPower_sq_add_prime (Nat.nth Nat.Prime (n - 1))
    (Nat.prime_nth_prime (n - 1)))

/-! ## Examples: examples against the DATA line `5, 1, 2, 1, …` -/

/-- `a115038 n = x` without `Nat.find`: `x ≥ 1` makes `x^2 + prime(n)` a
perfect power and no smaller `x' ≥ 1` does. -/
theorem a115038_eq_iff (n x : ℕ) :
    a115038 n = x ↔ (1 ≤ x ∧ IsPerfectPower (x ^ 2 + Nat.nth Nat.Prime (n - 1))) ∧
      ∀ x' < x, ¬ (1 ≤ x' ∧ IsPerfectPower (x' ^ 2 + Nat.nth Nat.Prime (n - 1))) := by
  classical
  unfold a115038
  rw [Nat.find_eq_iff]

-- a(1) = 5: prime(1) = 2, `5^2 + 2 = 27 = 3^3`, and `3, 6, 11, 18` are not
-- perfect powers.
example : a115038 1 = 5 := by
  rw [a115038_eq_iff, show (1 : ℕ) - 1 = 0 from rfl, Nat.nth_prime_zero_eq_two]
  refine ⟨⟨by norm_num, 3, 3, by norm_num, by norm_num⟩, ?_⟩
  intro x' hx' ⟨hx1, hpp⟩
  rw [isPerfectPower_iff_bounded (by nlinarith)] at hpp
  interval_cases x' <;> revert hpp <;> decide

-- a(2) = 1: prime(2) = 3, `1^2 + 3 = 4 = 2^2`.
example : a115038 2 = 1 := by
  rw [a115038_eq_iff, show (2 : ℕ) - 1 = 1 from rfl, Nat.nth_prime_one_eq_three]
  refine ⟨⟨le_refl 1, 2, 2, le_refl 2, by norm_num⟩, ?_⟩
  intro x' hx' ⟨hx1, _⟩
  omega

-- a(3) = 2: prime(3) = 5, `1 + 5 = 6` is not a perfect power, `4 + 5 = 3^2`.
example : a115038 3 = 2 := by
  rw [a115038_eq_iff, show (3 : ℕ) - 1 = 2 from rfl, Nat.nth_prime_two_eq_five]
  refine ⟨⟨by norm_num, 3, 2, le_refl 2, by norm_num⟩, ?_⟩
  intro x' hx' ⟨hx1, hpp⟩
  obtain rfl : x' = 1 := by omega
  rw [isPerfectPower_iff_bounded (by norm_num)] at hpp
  revert hpp
  decide

-- a(4) = 1: prime(4) = 7, `1 + 7 = 8 = 2^3`.
example : a115038 4 = 1 := by
  rw [a115038_eq_iff, show (4 : ℕ) - 1 = 3 from rfl, Nat.nth_prime_three_eq_seven]
  refine ⟨⟨le_refl 1, 2, 3, by norm_num, by norm_num⟩, ?_⟩
  intro x' hx' ⟨hx1, _⟩
  omega

-- Non-vacuity of the conjecture's hypotheses and the `1 ≤ x` guard: the
-- entry's example `498^2 + 997 = 499^2` at the prime `997`.
example : Nat.Prime 997 ∧ 498 ^ 2 + 997 = 499 ^ 2 := ⟨by norm_num, by norm_num⟩

-- The guard `1 ≤ x` is load-bearing in the sense that `x = 0` never works:
-- a prime is not a perfect power (shown here at `p = 2`).
example : ¬ IsPerfectPower (0 ^ 2 + 2) := by
  rw [isPerfectPower_iff_bounded (by norm_num)]
  decide

end Candidates.A115038PrimeThereExist
