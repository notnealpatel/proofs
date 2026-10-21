/-
# Euler's theorem on the form of odd perfect numbers

## Source

L. Euler, *Tractatus de numerorum doctrina* (posthumous, 1849), §109;
see also L. E. Dickson, *History of the Theory of Numbers*, Vol. I, Ch. 1.

## Informal statement (verbatim from the target spec, 2026-10-21)

> Every odd perfect number N has the form N = p^k m^2, where p is a prime
> with p ≡ k ≡ 1 (mod 4) and p ∤ m.

## Mathlib check (2026-10-21)

`leandoc` probes `Nat.Perfect`, "odd perfect number Euler form",
"odd perfect number square prime power" find only the even case
(`Theorems100.Nat.eq_two_pow_mul_prime_mersenne_of_even_perfect`, Archive)
and nothing on odd perfect numbers.

## Proof outline

Write `σ = σ 1` (Mathlib's `ArithmeticFunction.sigma 1`).  For odd `n > 0`
we prove simultaneously, by induction over coprime prime-power
decompositions (`Nat.recOnPosPrimePosCoprime`):

* (A) if `σ n` is odd then `n` is a square;
* (B) if `σ n % 4 = 2` then `n = p ^ k * m ^ 2` with `p` prime,
  `p % 4 = 1`, `k % 4 = 1`, `p ∤ m`.

The prime-power base case is the residue computation of
`1 + p + ⋯ + p ^ k` modulo `4`; the coprime step uses multiplicativity of
`σ`.  A perfect odd `n` has `σ n = 2 n ≡ 2 (mod 4)`, so (B) applies.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.EulerOddPerfect

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

/-- For `p ≡ 1 (mod 4)`, `1 + p + ⋯ + p ^ k ≡ k + 1 (mod 4)`. -/
theorem geom_sum_mod_four_of_mod_four_eq_one {p : ℕ} (hp : p % 4 = 1) (k : ℕ) :
    (∑ i ∈ range (k + 1), p ^ i) % 4 = (k + 1) % 4 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hpow : p ^ (k + 1) % 4 = 1 := by
      rw [Nat.pow_mod, hp, one_pow, Nat.one_mod]
    rw [sum_range_succ, Nat.add_mod, ih, hpow]
    omega

/-- For `p ≡ 3 (mod 4)`, `p ^ j` is `1` or `3` modulo `4` according to the
parity of `j`. -/
theorem pow_mod_four_of_mod_four_eq_three {p : ℕ} (hp : p % 4 = 3) (j : ℕ) :
    p ^ j % 4 = if j % 2 = 0 then 1 else 3 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, Nat.mul_mod, ih, hp]
    split_ifs <;> omega

/-- For `p ≡ 3 (mod 4)`, `1 + p + ⋯ + p ^ k` is `1` modulo `4` when `k` is
even and `0` modulo `4` when `k` is odd. -/
theorem geom_sum_mod_four_of_mod_four_eq_three {p : ℕ} (hp : p % 4 = 3) (k : ℕ) :
    (∑ i ∈ range (k + 1), p ^ i) % 4 = if k % 2 = 0 then 1 else 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, Nat.add_mod, ih, pow_mod_four_of_mod_four_eq_three hp]
    split_ifs <;> omega

/-- Prime-power case: for an odd prime `p` and `k > 0`, if `σ (p ^ k)` is odd
then `k` is even, and if `σ (p ^ k) ≡ 2 (mod 4)` then `p ≡ k ≡ 1 (mod 4)`. -/
theorem sigma_prime_pow_mod_four {p k : ℕ} (hp : p.Prime) (hodd : Odd p) :
    (σ 1 (p ^ k) % 2 = 1 → k % 2 = 0) ∧
      (σ 1 (p ^ k) % 4 = 2 → p % 4 = 1 ∧ k % 4 = 1) := by
  rw [sigma_one_apply_prime_pow hp]
  have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by
    rcases hodd with ⟨t, rfl⟩
    omega
  rcases hp4 with h1 | h3
  · have hs := geom_sum_mod_four_of_mod_four_eq_one h1 k
    refine ⟨fun h => ?_, fun h => ⟨h1, ?_⟩⟩ <;> omega
  · have hs := geom_sum_mod_four_of_mod_four_eq_three h3 k
    refine ⟨fun h => ?_, fun h => ?_⟩ <;> split_ifs at hs <;> omega

/-- If a product of naturals is `2` modulo `4`, one factor is `2` modulo `4`
and the other is odd. -/
theorem mul_mod_four_eq_two {x y : ℕ} (h : x * y % 4 = 2) :
    (x % 4 = 2 ∧ y % 2 = 1) ∨ (x % 2 = 1 ∧ y % 4 = 2) := by
  rw [Nat.mul_mod] at h
  have hx : x % 4 < 4 := Nat.mod_lt x (by norm_num)
  have hy : y % 4 < 4 := Nat.mod_lt y (by norm_num)
  have hx2 : x % 2 = x % 4 % 2 := (Nat.mod_mod_of_dvd x (by norm_num)).symm
  have hy2 : y % 2 = y % 4 % 2 := (Nat.mod_mod_of_dvd y (by norm_num)).symm
  generalize x % 4 = u at *
  generalize y % 4 = v at *
  interval_cases u <;> interval_cases v <;> simp_all

/-- Euler's form, simultaneous induction: for every odd `n > 0`,
(A) `σ n` odd implies `n` is a square, and (B) `σ n ≡ 2 (mod 4)` implies
`n = p ^ k * m ^ 2` with `p` prime, `p ≡ k ≡ 1 (mod 4)` and `p ∤ m`. -/
theorem sigma_mod_four_structure (n : ℕ) (hn : 0 < n) (hodd : Odd n) :
    (σ 1 n % 2 = 1 → ∃ m : ℕ, n = m ^ 2) ∧
      (σ 1 n % 4 = 2 → ∃ p k m : ℕ, p.Prime ∧ p % 4 = 1 ∧ k % 4 = 1 ∧ ¬ p ∣ m ∧
        n = p ^ k * m ^ 2) := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    have hpodd : Odd p := Odd.of_dvd_nat hodd (dvd_pow_self p hk.ne')
    obtain ⟨hA, hB⟩ := sigma_prime_pow_mod_four (k := k) hp hpodd
    refine ⟨fun h => ⟨p ^ (k / 2), ?_⟩, fun h => ?_⟩
    · have hk2 : k = 2 * (k / 2) := by have := hA h; omega
      rw [← pow_mul, mul_comm, ← hk2]
    · obtain ⟨h1, hk1⟩ := hB h
      exact ⟨p, k, 1, hp, h1, hk1, hp.not_dvd_one, by simp⟩
  | zero => exact absurd hn (lt_irrefl 0)
  | one => exact ⟨fun _ => ⟨1, rfl⟩, fun h => by simp at h⟩
  | coprime a b ha hb hab iha ihb =>
    obtain ⟨hao, hbo⟩ := Nat.odd_mul.mp hodd
    obtain ⟨hA_a, hB_a⟩ := iha (by omega) hao
    obtain ⟨hA_b, hB_b⟩ := ihb (by omega) hbo
    have hmul : σ 1 (a * b) = σ 1 a * σ 1 b := isMultiplicative_sigma.map_mul_of_coprime hab
    rw [hmul]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have hodd' : Odd (σ 1 a * σ 1 b) := Nat.odd_iff.mpr h
      obtain ⟨hsa, hsb⟩ := Nat.odd_mul.mp hodd'
      obtain ⟨m, rfl⟩ := hA_a (Nat.odd_iff.mp hsa)
      obtain ⟨m', rfl⟩ := hA_b (Nat.odd_iff.mp hsb)
      exact ⟨m * m', by ring⟩
    · -- a prime dividing one coprime factor does not divide the other
      have hnd : ∀ {p x y : ℕ}, p.Prime → Nat.Coprime x y → p ∣ x → ¬ p ∣ y := by
        intro p x y hp hxy hpx hpy
        have hg : p ∣ Nat.gcd x y := Nat.dvd_gcd hpx hpy
        rw [hxy] at hg
        exact hp.not_dvd_one hg
      rcases mul_mod_four_eq_two h with ⟨h2, h1⟩ | ⟨h1, h2⟩
      · obtain ⟨p, k, m, hp, hp4, hk4, hpm, rfl⟩ := hB_a h2
        obtain ⟨m', rfl⟩ := hA_b h1
        have hpa : p ∣ p ^ k * m ^ 2 :=
          Dvd.dvd.mul_right (dvd_pow_self p (by omega)) _
        have hpm' : ¬ p ∣ m' := fun hd =>
          hnd hp hab hpa (Dvd.dvd.mul_left hd m' |>.trans (by rw [sq]))
        refine ⟨p, k, m * m', hp, hp4, hk4, fun hd => ?_, by ring⟩
        rcases hp.dvd_mul.mp hd with hd | hd
        · exact hpm hd
        · exact hpm' hd
      · obtain ⟨p, k, m, hp, hp4, hk4, hpm, rfl⟩ := hB_b h2
        obtain ⟨m', rfl⟩ := hA_a h1
        have hpb : p ∣ p ^ k * m ^ 2 :=
          Dvd.dvd.mul_right (dvd_pow_self p (by omega)) _
        have hpm' : ¬ p ∣ m' := fun hd =>
          hnd hp hab.symm hpb (Dvd.dvd.mul_left hd m' |>.trans (by rw [sq]))
        refine ⟨p, k, m' * m, hp, hp4, hk4, fun hd => ?_, by ring⟩
        rcases hp.dvd_mul.mp hd with hd | hd
        · exact hpm' hd
        · exact hpm hd

/-- Non-vacuity of hypothesis (B) of `sigma_mod_four_structure`:
`σ 5 = 6 ≡ 2 (mod 4)`. -/
example : σ 1 5 % 4 = 2 := by
  rw [sigma_one_apply]
  decide

/-- **Euler's theorem on odd perfect numbers.** Every odd perfect number `n`
has the form `n = p ^ k * m ^ 2` where `p` is a prime with
`p ≡ k ≡ 1 (mod 4)` and `p ∤ m`.

Whether any odd perfect number exists is open, so the hypotheses
`n.Perfect ∧ Odd n` are not known to be satisfiable; this is the classical
statement exactly as Euler gave it. -/
theorem eq_prime_pow_mul_sq_of_perfect_of_odd {n : ℕ} (h : n.Perfect) (hodd : Odd n) :
    ∃ p k m : ℕ, p.Prime ∧ p % 4 = 1 ∧ k % 4 = 1 ∧ ¬ p ∣ m ∧ n = p ^ k * m ^ 2 := by
  have hn : 0 < n := h.2
  have hsig : σ 1 n = 2 * n := by
    rw [sigma_one_apply]
    exact (Nat.perfect_iff_sum_divisors_eq_two_mul hn).mp h
  have hmod : σ 1 n % 4 = 2 := by
    obtain ⟨t, rfl⟩ := hodd
    rw [hsig]
    omega
  exact (sigma_mod_four_structure n hn hodd).2 hmod

end Candidates.EulerOddPerfect
