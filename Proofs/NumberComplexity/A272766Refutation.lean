/-
# A272766 — refutation of the primorial conjecture

Juri-Stepan Gerasimov's conjecture in OEIS A272766 says that primorials
belong to the sequence `A281363(n) = n-1`, where A281363 is the least positive
`m` with `(2n)²-1 ∣ (2^m)^(2n)-1`.
At the fifth primorial `11# = 2310`, this least exponent is `37`, not `2309`.
The conjecture is stated for positive primorial indices: the zeroth
primorial `1` already fails, whereas `2,6,30,210` satisfy it.
-/
import Mathlib

set_option autoImplicit false
set_option Elab.async false

namespace Candidates.A272766Refutation

/-! ## Definitions -/

/-- `m` is admissible for `n` in A281363: `m > 0` and
`(2n)^2 - 1 ∣ (2^m)^(2n) - 1`.  Both truncated subtractions are harmless:
`(2^m)^(2n) ≥ 1` always, and `(2n)^2 ≥ 1` whenever `n ≥ 1`. -/
def Admissible (n m : ℕ) : Prop :=
  0 < m ∧ (2 * n) ^ 2 - 1 ∣ (2 ^ m) ^ (2 * n) - 1

instance (n : ℕ) : DecidablePred (Admissible n) := fun m =>
  inferInstanceAs (Decidable (0 < m ∧ (2 * n) ^ 2 - 1 ∣ (2 ^ m) ^ (2 * n) - 1))

/-- Every `n` has an admissible `m`, so the infimum defining `a281363` is
never the junk value of an empty set.  For `n ≥ 1` the modulus
`4n^2 - 1` is odd and Euler's theorem gives `m = φ(4n^2 - 1)`. -/
theorem admissible_nonempty (n : ℕ) : ∃ m, Admissible n m := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, Nat.one_pos, by simp⟩
  · set q := (2 * n) ^ 2 - 1 with hq
    have hq_odd : Odd q := by
      have h1 : 1 ≤ (2 * n) ^ 2 := Nat.one_le_pow _ _ (by omega)
      refine ⟨2 * n * n - 1, ?_⟩
      have h2 : (2 * n) ^ 2 = 2 * (2 * n * n) := by ring
      omega
    have hq_pos : 0 < q := hq_odd.pos
    have hcop : Nat.Coprime 2 q := (Nat.coprime_two_left).2 hq_odd
    have hmod : 2 ^ Nat.totient q ≡ 1 [MOD q] := Nat.ModEq.pow_totient hcop
    have hmod' : (2 ^ Nat.totient q) ^ (2 * n) ≡ 1 [MOD q] := by
      simpa using hmod.pow (2 * n)
    refine ⟨Nat.totient q, Nat.totient_pos.2 hq_pos, ?_⟩
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by positivity))).1 hmod'.symm

/-- A281363: the least `m > 0` such that `(2n)^2 - 1` divides
`(2^m)^(2n) - 1`.  The set is nonempty by `admissible_nonempty`. -/
noncomputable def a281363 (n : ℕ) : ℕ :=
  sInf {m | Admissible n m}

/-- A272766 membership: `n ≥ 1` (the entry's offset) and `A281363(n) = n - 1`. -/
def InA272766 (n : ℕ) : Prop :=
  0 < n ∧ a281363 n = n - 1

/-- A002110: the primorial `p_k#`, the product of the first `k` primes
(`Nat.nth Nat.Prime 0 = 2`). -/
noncomputable def a002110 (k : ℕ) : ℕ :=
  ∏ i ∈ Finset.range k, Nat.nth Nat.Prime i

/-- Characterisation used for evaluation: if `v` is admissible and no smaller
`m` is, then `a281363 n = v`. -/
theorem a281363_eq_of_admissible {n v : ℕ} (hv : Admissible n v)
    (hlt : ∀ m < v, ¬ Admissible n m) : a281363 n = v :=
  le_antisymm (Nat.sInf_le hv)
    (le_csInf ⟨v, hv⟩ fun m hm => not_lt.1 fun h => hlt m h hm)

/-! ## Examples -/

example : a281363 1 = 1 := a281363_eq_of_admissible (by decide) (by decide)
example : a281363 2 = 1 := a281363_eq_of_admissible (by decide) (by decide)
example : a281363 3 = 2 := a281363_eq_of_admissible (by decide) (by decide)
example : a281363 4 = 3 := a281363_eq_of_admissible (by decide) (by decide)
example : a281363 6 = 5 := a281363_eq_of_admissible (by decide) (by decide)
example : a281363 12 = 55 := a281363_eq_of_admissible (by decide) (by decide)
example : a281363 13 = 90 := a281363_eq_of_admissible (by decide) (by decide)

example : a002110 0 = 1 := by simp [a002110]
example : a002110 5 = 2310 := by
  simp [a002110, Finset.prod_range_succ, Nat.nth_prime_zero_eq_two,
    Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five,
    Nat.nth_prime_three_eq_seven, Nat.nth_prime_four_eq_eleven]

/-- `n` is a term of A272766 as soon as `n - 1` is admissible and no smaller
`m` is. -/
theorem inA272766_of_admissible {n : ℕ} (hn : 0 < n) (hv : Admissible n (n - 1))
    (hlt : ∀ m < n - 1, ¬ Admissible n m) : InA272766 n :=
  ⟨hn, a281363_eq_of_admissible hv hlt⟩

example : InA272766 2 := inA272766_of_admissible (by decide) (by decide) (by decide)
example : InA272766 3 := inA272766_of_admissible (by decide) (by decide) (by decide)
example : InA272766 4 := inA272766_of_admissible (by decide) (by decide) (by decide)
example : InA272766 6 := inA272766_of_admissible (by decide) (by decide) (by decide)
example : InA272766 7 := inA272766_of_admissible (by decide) (by decide) (by decide)
example : ¬ InA272766 1 := fun h => by
  have h1 : a281363 1 = 1 := a281363_eq_of_admissible (by decide) (by decide)
  have h2 := h.2
  omega
example : ¬ InA272766 5 := fun h => by
  have h1 : a281363 5 = 3 := a281363_eq_of_admissible (by decide) (by decide)
  have h2 := h.2
  omega

/-! ## The conjecture -/

/-- **Gerasimov's primorial conjecture (A272766, Juri-Stepan Gerasimov).**

"Conjecture: primorial numbers (A002110) are terms of this
sequence."  Stated for `p_k#` with `k ≥ 1`, i.e. `A281363(p_k#) = p_k# - 1`
for every `k ≥ 1`. -/
def Conjecture : Prop :=
  ∀ k : ℕ, 0 < k → InA272766 (a002110 k)

/-- The fifth primorial is `11# = 2310`. -/
theorem a002110_five : a002110 5 = 2310 := by
  simp [a002110, Finset.prod_range_succ, Nat.nth_prime_zero_eq_two,
    Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five,
    Nat.nth_prime_three_eq_seven, Nat.nth_prime_four_eq_eleven]

/-- `A281363(2310) = 37`: `21344399 = 4 * 2310^2 - 1` divides
`(2^37)^4620 - 1` and no smaller positive exponent works. -/
theorem a281363_2310 : a281363 2310 = 37 :=
  a281363_eq_of_admissible (by decide +kernel) (by decide +kernel)

/-- **Refutation.**  The conjecture fails at `k = 5`: `p_5# = 11# = 2310`
but `A281363(2310) = 37 ≠ 2309`, so `2310` is not a term of A272766.  It
holds for `k = 1, 2, 3, 4` (`2, 6, 30, 210`). -/
theorem conjecture_false : ¬ Conjecture := by
  intro h
  have hmem : InA272766 (a002110 5) := h 5 (by norm_num)
  rw [a002110_five] at hmem
  have hval : a281363 2310 = 2310 - 1 := hmem.2
  rw [a281363_2310] at hval
  norm_num at hval

/-- The conjecture does hold for the first four primorials
`2, 6, 30, 210` (`k = 1, …, 4`). -/
theorem conjecture_holds_small :
    ∀ k : ℕ, 0 < k → k ≤ 4 → InA272766 (a002110 k) := by
  intro k hk0 hk4
  have h2 : InA272766 2 := inA272766_of_admissible (by decide) (by decide) (by decide)
  have h6 : InA272766 6 := inA272766_of_admissible (by decide) (by decide) (by decide)
  have h30 : InA272766 30 :=
    inA272766_of_admissible (by decide) (by decide +kernel) (by decide +kernel)
  have h210 : InA272766 210 :=
    inA272766_of_admissible (by decide) (by decide +kernel) (by decide +kernel)
  interval_cases k <;>
    simpa [a002110, Finset.prod_range_succ, Nat.nth_prime_zero_eq_two,
      Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five,
      Nat.nth_prime_three_eq_seven]

end Candidates.A272766Refutation
