/-
# MO 287011 — the primes `≤ n` not dividing `n` determine `n` iff Dressler's conjecture

MathOverflow 287011, BRP, 'A conjecture regarding prime numbers',
<https://mathoverflow.net/questions/287011> (cross-posted from
math.stackexchange 2536176). Lucia's accepted answer, following a comment
by H. Pasten, identifies the claim with Dressler's conjecture; see
Cochrane–Dressler, Math. Comp. 68 (1999), and Erdős–Selfridge (1971).

For `n,m ≥ 3`, the MO claim says the set of primes `p ≤ n` not dividing `n`
determines `n`. Dressler's conjecture says that if `0 < n < m` have the same
prime factors, some prime lies strictly between them. This file proves the
equivalence `MOClaim ↔ DresslerConjecture`, not either conjecture.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.DresslerPrimeSetEquivalence

/-! ## Definitions -/

/-- MO 287011's `P_n`: the set of primes `p ≤ n` with `p ∤ n`. -/
def primesNotDividing (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun p => p.Prime ∧ ¬ p ∣ n)

/-- The MO 287011 claim (BRP): for `n, m ≥ 3`, `P_n = P_m` forces `n = m`
(equivalently `P_n ≠ P_m` whenever `n ≠ m`). -/
def MOClaim : Prop :=
  ∀ n m : ℕ, 3 ≤ n → 3 ≤ m → primesNotDividing n = primesNotDividing m → n = m

/-- Dressler's conjecture: if `0 < n < m` have the same set of prime factors,
then some prime `p` lies strictly between them, `n < p < m`. -/
def DresslerConjecture : Prop :=
  ∀ n m : ℕ, 0 < n → n < m → n.primeFactors = m.primeFactors →
    ∃ p, p.Prime ∧ n < p ∧ p < m

/-! ## Examples (the examples from the MO question) -/

example : primesNotDividing 3 = {2} := by decide
example : primesNotDividing 4 = {3} := by decide
example : primesNotDividing 5 = {2, 3} := by decide
example : primesNotDividing 6 = {5} := by decide

/-- Non-vacuity of Dressler's hypothesis: `2` and `4` share the prime factor
set `{2}`, and `3` lies strictly between them. -/
example : (2 : ℕ).primeFactors = (4 : ℕ).primeFactors ∧
    ∃ p, p.Prime ∧ 2 < p ∧ p < 4 := by
  refine ⟨?_, 3, by norm_num, by norm_num, by norm_num⟩
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.primeFactors_prime_pow two_ne_zero Nat.prime_two,
    Nat.Prime.primeFactors Nat.prime_two]

/-! ## Helper lemmas -/

/-- Membership in `P_n`. -/
theorem mem_primesNotDividing {n p : ℕ} :
    p ∈ primesNotDividing n ↔ p.Prime ∧ p ≤ n ∧ ¬ p ∣ n := by
  simp only [primesNotDividing, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
  tauto

/-- A divisor `q` of `m > 0` with `m < 2 q` equals `m`. -/
theorem eq_of_dvd_of_lt_two_mul {q m : ℕ} (hm : 0 < m) (hqm : q ∣ m) (hlt : m < 2 * q) :
    q = m := by
  obtain ⟨k, rfl⟩ := hqm
  rcases k with _ | _ | k
  · simp at hm
  · simp
  · nlinarith

/-- Key lemma of the (Dressler ⟹ MO) direction: if `3 ≤ n < m` and
`P_n = P_m`, then no prime lies in `(n, m]`. -/
theorem no_prime_Ioc_of_primesNotDividing_eq {n m : ℕ} (hn : 3 ≤ n) (hnm : n < m)
    (h : primesNotDividing n = primesNotDividing m) :
    ∀ q, q.Prime → n < q → q ≤ m → False := by
  -- every prime in `(n, m]` divides `m`
  have hdivm : ∀ q, q.Prime → n < q → q ≤ m → q ∣ m := by
    intro q hq hnq hqm
    by_contra hnd
    have hmem : q ∈ primesNotDividing n := h ▸ mem_primesNotDividing.mpr ⟨hq, hqm, hnd⟩
    exact absurd (mem_primesNotDividing.mp hmem).2.1 (by omega)
  -- every prime factor of `n` divides `m`
  have hfac : ∀ r, r.Prime → r ∣ n → r ∣ m := by
    intro r hr hrn
    have hrle : r ≤ n := Nat.le_of_dvd (by omega) hrn
    by_contra hnd
    have hmem : r ∈ primesNotDividing n :=
      h ▸ mem_primesNotDividing.mpr ⟨hr, by omega, hnd⟩
    exact (mem_primesNotDividing.mp hmem).2.2 hrn
  -- a prime `q ∈ (n, m]` with `m < 2 q` is impossible
  have hcollapse : ∀ q, q.Prime → n < q → q ≤ m → m < 2 * q → False := by
    intro q hq hnq hqm hlt
    have hqeq : q = m := eq_of_dvd_of_lt_two_mul (by omega) (hdivm q hq hnq hqm) hlt
    have hr : n.minFac.Prime := Nat.minFac_prime (by omega)
    have hrm : n.minFac ∣ q := hqeq ▸ hfac _ hr (Nat.minFac_dvd n)
    have hrq : n.minFac = q := (Nat.prime_dvd_prime_iff_eq hr hq).mp hrm
    have hrle : n.minFac ≤ n := Nat.minFac_le (by omega)
    omega
  -- Bertrand: a prime `p` with `m < 2 p ≤ 2 m`
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (m / 2) (by omega)
  have hpm : p ≤ m := by omega
  have hmp : m < 2 * p := by omega
  intro q hq hnq hqm
  by_cases hnp : n < p
  · exact hcollapse p hp hnp hpm hmp
  · exact hcollapse q hq hnq hqm (by omega)

/-- If `3 ≤ n < m` and `P_n = P_m`, then `n` and `m` have the same prime
factors. -/
theorem primeFactors_eq_of_primesNotDividing_eq {n m : ℕ} (hn : 3 ≤ n) (hnm : n < m)
    (h : primesNotDividing n = primesNotDividing m) :
    n.primeFactors = m.primeFactors := by
  have hno := no_prime_Ioc_of_primesNotDividing_eq hn hnm h
  ext r
  simp only [Nat.mem_primeFactors]
  constructor
  · rintro ⟨hr, hrn, -⟩
    have hrle : r ≤ n := Nat.le_of_dvd (by omega) hrn
    refine ⟨hr, ?_, by omega⟩
    by_contra hnd
    have hmem : r ∈ primesNotDividing n :=
      h ▸ mem_primesNotDividing.mpr ⟨hr, by omega, hnd⟩
    exact (mem_primesNotDividing.mp hmem).2.2 hrn
  · rintro ⟨hr, hrm, -⟩
    have hrle : r ≤ m := Nat.le_of_dvd (by omega) hrm
    have hrn : r ≤ n := by
      by_contra hgt
      exact hno r hr (by omega) hrle
    refine ⟨hr, ?_, by omega⟩
    by_contra hnd
    have hmem : r ∈ primesNotDividing m :=
      h ▸ mem_primesNotDividing.mpr ⟨hr, hrn, hnd⟩
    exact (mem_primesNotDividing.mp hmem).2.2 hrm

/-- Dressler's conjecture implies the MO 287011 claim. -/
theorem moClaim_of_dressler (hD : DresslerConjecture) : MOClaim := by
  -- reduce to `n < m`
  have key : ∀ n m : ℕ, 3 ≤ n → n < m → primesNotDividing n ≠ primesNotDividing m := by
    intro n m hn hnm h
    obtain ⟨p, hp, hnp, hpm⟩ :=
      hD n m (by omega) hnm (primeFactors_eq_of_primesNotDividing_eq hn hnm h)
    exact no_prime_Ioc_of_primesNotDividing_eq hn hnm h p hp hnp hpm.le
  intro n m hn hm h
  rcases lt_trichotomy n m with hlt | heq | hgt
  · exact absurd h (key n m hn hlt)
  · exact heq
  · exact absurd h.symm (key m n hm hgt)

/-- The MO 287011 claim implies Dressler's conjecture. -/
theorem dressler_of_moClaim (hMO : MOClaim) : DresslerConjecture := by
  intro n m hn hnm hpf
  by_contra hno
  push Not at hno
  have hm0 : m ≠ 0 := by omega
  have hn0 : n ≠ 0 := by omega
  -- `m` has a prime factor, hence so does `n`, so `n ≠ 1`
  have hmf : m.minFac ∈ n.primeFactors :=
    hpf ▸ Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd m, hm0⟩
  have hn1 : n ≠ 1 := by
    rintro rfl
    simp at hmf
  -- `m` is not prime: otherwise `m ∣ n` with `n < m`
  have hmnp : ¬ m.Prime := by
    intro hmp
    have hmem : m ∈ n.primeFactors := hpf ▸ Nat.mem_primeFactors.mpr ⟨hmp, dvd_rfl, hm0⟩
    have hle : m ≤ n := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hmem)
    omega
  -- hence no prime lies in `(n, m]`
  have hIoc : ∀ q, q.Prime → n < q → q ≤ m → False := by
    intro q hq hnq hqm
    have hmq : m ≤ q := hno q hq hnq
    exact hmnp (show q = m by omega ▸ hq)
  -- the case `n = 2`: then `3 ∈ (n, m]`
  have hn3 : 3 ≤ n := by
    by_contra hlt
    have hn2 : n = 2 := by omega
    subst hn2
    exact hIoc 3 Nat.prime_three (by norm_num) (by
      by_contra h3
      have hm3 : m = 3 := by omega
      exact hmnp (hm3 ▸ Nat.prime_three))
  -- prime divisibility agrees on `n` and `m`
  have hdvd : ∀ p, p.Prime → (p ∣ n ↔ p ∣ m) := by
    intro p hp
    have hiff := congrArg (p ∈ ·) hpf
    simp only [Nat.mem_primeFactors, hn0, hm0, ne_eq, not_false_eq_true, and_true,
      eq_iff_iff] at hiff
    exact ⟨fun h => (hiff.mp ⟨hp, h⟩).2, fun h => (hiff.mpr ⟨hp, h⟩).2⟩
  have hP : primesNotDividing n = primesNotDividing m := by
    ext p
    rw [mem_primesNotDividing, mem_primesNotDividing]
    constructor
    · rintro ⟨hp, hpn, hnd⟩
      exact ⟨hp, by omega, fun h => hnd ((hdvd p hp).mpr h)⟩
    · rintro ⟨hp, hpm, hnd⟩
      have hpn : p ≤ n := by
        by_contra hgt
        exact hIoc p hp (by omega) hpm
      exact ⟨hp, hpn, fun h => hnd ((hdvd p hp).mp h)⟩
  have hnm' : n = m := hMO n m hn3 (by omega) hP
  omega

/-- **MO 287011 ⟺ Dressler's conjecture.**  The claim of BRP (MathOverflow
287011) that for `n, m ≥ 3` the set `P_n` of primes `p ≤ n` with `p ∤ n`
determines `n` is equivalent to Dressler's conjecture (if `0 < n < m` have
the same prime factors then a prime lies strictly between them), as asserted
in Lucia's accepted answer after Pasten's comment. -/
theorem moClaim_iff_dressler : MOClaim ↔ DresslerConjecture :=
  ⟨dressler_of_moClaim, moClaim_of_dressler⟩

end Candidates.DresslerPrimeSetEquivalence
