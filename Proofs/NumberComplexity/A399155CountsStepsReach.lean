/-
# A399155 — Dilkhush: subtracting the largest prime factor never takes more steps

The unsigned conjecture in OEIS A399155, an entry by Jaylen Dilkhush
(2026): for `n ≥ 2`, subtracting the largest prime factor takes no more
steps to reach zero than subtracting the smallest. The difference is zero
exactly at primes and `4`, and equals `p-2` at `2p` for odd prime `p`.

* `f` is explicit: for even `n` the smallest prime factor stays `2`, so
  `f(n) = n / 2`; for odd `n ≥ 3` with `p = minFac n`, `n - p` is even, so
  `f(n) = 1 + (n - p) / 2`.
* Every decrement of the `g`-orbit of `n ≥ 2` is a prime `P ∣ m`, so the
  orbit avoids `1` (`P ∣ m - P`) and each step removes at least `2`:
  `g(n) ≤ n / 2` for every `n ≠ 1`.
* Even `n`: `g(n) ≤ n / 2 = f(n)`.  Odd `n`: the first decrement is
  `P(n) ≥ p`, so `g(n) ≤ 1 + (n - P) / 2 ≤ 1 + (n - p) / 2 = f(n)`.
* Strictness: an even `m` with an odd prime factor has `g(m) < m / 2`
  (its first decrement is `≥ 3`).  This settles every composite `n ≠ 4`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A399155CountsStepsReach

/-! ## Definitions -/

/-- The decrement used by `g`: the largest prime factor of `m` for `2 ≤ m`.
At `m ≤ 1` (where `m` has no prime factor) it is `1`; this matches
Mathematica's `FactorInteger[1] = {{1, 1}}` in the entry's program and
Mathlib's `Nat.minFac 1 = 1`, and it is never reached from `n ≥ 2`. -/
def maxPrimeFac (m : ℕ) : ℕ := max 1 (m.primeFactors.sup id)

/-- `f(n)` of A399155: the number of steps to reach `0` from `n` under
`m ↦ m - minFac m` (the smallest prime factor of `m`). -/
def stepsMin : ℕ → ℕ
  | 0 => 0
  | m + 1 => stepsMin (m + 1 - (m + 1).minFac) + 1
decreasing_by have := Nat.minFac_pos (m + 1); omega

/-- `g(n)` of A399155: the number of steps to reach `0` from `n` under
`m ↦ m - P(m)`, where `P(m)` is the largest prime factor of `m`. -/
def stepsMax : ℕ → ℕ
  | 0 => 0
  | m + 1 => stepsMax (m + 1 - maxPrimeFac (m + 1)) + 1
decreasing_by
  have := le_max_left 1 ((m + 1).primeFactors.sup id)
  unfold maxPrimeFac
  omega

/-- A399155: `a(n) = f(n) - g(n)`, as an integer (the entry's offset is `2`). -/
def a (n : ℕ) : ℤ := (stepsMin n : ℤ) - (stepsMax n : ℤ)

/-! ## Examples -/

-- The largest prime factor of `60 = 2^2 · 3 · 5` is `5`.
example : maxPrimeFac 60 = 5 := by decide +kernel

-- The first 75 terms `a(2), …, a(76)` reproduce the DATA line.
example : (List.range' 2 75).map a =
    [0,0,0,0,1,0,1,1,3,0,2,0,5,4,5,0,5,0,6,7,9,0,8,6,11,8,10,0,9,0,9,13,15,11,14,0,17,16,14,0,15,0,18,15,21,0,16,15,17,22,22,0,23,21,20,25,27,0,24,0,29,22,29,26,27,0,30,31,25,0,32,0,35,26,34] := by
  decide +kernel

/-! ## The decrement `maxPrimeFac` -/

/-- One step of the `f`-orbit: for `0 < m`, `f(m) = f(m - minFac m) + 1`. -/
theorem stepsMin_of_pos {m : ℕ} (hm : 0 < m) :
    stepsMin m = stepsMin (m - m.minFac) + 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hm
  simp only [zero_add]
  rw [stepsMin]

/-- One step of the `g`-orbit: for `0 < m`, `g(m) = g(m - P(m)) + 1`. -/
theorem stepsMax_of_pos {m : ℕ} (hm : 0 < m) :
    stepsMax m = stepsMax (m - maxPrimeFac m) + 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hm
  simp only [zero_add]
  rw [stepsMax]

/-- For `2 ≤ m`, `maxPrimeFac m` is a prime factor of `m`. -/
theorem maxPrimeFac_mem {m : ℕ} (hm : 2 ≤ m) : maxPrimeFac m ∈ m.primeFactors := by
  have hne : m.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr hm
  obtain ⟨p, hp, hsup⟩ := Finset.exists_mem_eq_sup m.primeFactors hne id
  have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
  unfold maxPrimeFac
  rw [hsup, id, max_eq_right (by omega)]
  exact hp

/-- Every prime factor of `m` is at most `maxPrimeFac m`. -/
theorem le_maxPrimeFac {m q : ℕ} (hq : q ∈ m.primeFactors) : q ≤ maxPrimeFac m :=
  (Finset.le_sup (f := id) hq).trans (le_max_right _ _)

/-- For `2 ≤ m`, `maxPrimeFac m` is prime. -/
theorem maxPrimeFac_prime {m : ℕ} (hm : 2 ≤ m) : (maxPrimeFac m).Prime :=
  Nat.prime_of_mem_primeFactors (maxPrimeFac_mem hm)

/-- For `2 ≤ m`, `maxPrimeFac m` divides `m`. -/
theorem maxPrimeFac_dvd {m : ℕ} (hm : 2 ≤ m) : maxPrimeFac m ∣ m :=
  Nat.dvd_of_mem_primeFactors (maxPrimeFac_mem hm)

/-- Every prime divisor of a nonzero `m` is at most `maxPrimeFac m`. -/
theorem le_maxPrimeFac_of_dvd {m q : ℕ} (hm : m ≠ 0) (hq : q.Prime) (hqm : q ∣ m) :
    q ≤ maxPrimeFac m :=
  le_maxPrimeFac (Nat.mem_primeFactors.mpr ⟨hq, hqm, hm⟩)

/-- The largest prime factor of a prime `p` is `p`. -/
theorem maxPrimeFac_of_prime {p : ℕ} (hp : p.Prime) : maxPrimeFac p = p := by
  have hmem := maxPrimeFac_mem hp.two_le
  rwa [hp.primeFactors, Finset.mem_singleton] at hmem

/-- The `g`-orbit never visits `1`: for `2 ≤ m`, `m - P(m) ≠ 1`, since
`P(m) ∣ m - P(m)`. -/
theorem sub_maxPrimeFac_ne_one {m : ℕ} (hm : 2 ≤ m) : m - maxPrimeFac m ≠ 1 := by
  intro h1
  have hd : maxPrimeFac m ∣ m - maxPrimeFac m := Nat.dvd_sub (maxPrimeFac_dvd hm) dvd_rfl
  rw [h1] at hd
  exact (maxPrimeFac_prime hm).one_lt.ne' (Nat.dvd_one.mp hd)

/-! ## The two step counts -/

/-- `f(n) = n / 2` for even `n`: the smallest prime factor stays `2`. -/
theorem stepsMin_even {n : ℕ} (hn : Even n) : stepsMin n = n / 2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp [stepsMin]
    · have h2 : n.minFac = 2 := (Nat.minFac_eq_two_iff n).mpr (even_iff_two_dvd.mp hn)
      have hn2 : 2 ≤ n := by obtain ⟨k, hk⟩ := hn; omega
      have heven : Even (n - 2) := by obtain ⟨k, hk⟩ := hn; exact ⟨k - 1, by omega⟩
      rw [stepsMin_of_pos hpos, h2, ih (n - 2) (by omega) heven]
      omega

/-- `f(p) = 1` for a prime `p`. -/
theorem stepsMin_prime {p : ℕ} (hp : p.Prime) : stepsMin p = 1 := by
  rw [stepsMin_of_pos hp.pos, hp.minFac_eq, Nat.sub_self]
  simp [stepsMin]

/-- `g(p) = 1` for a prime `p`. -/
theorem stepsMax_prime {p : ℕ} (hp : p.Prime) : stepsMax p = 1 := by
  rw [stepsMax_of_pos hp.pos, maxPrimeFac_of_prime hp, Nat.sub_self]
  simp [stepsMax]

/-- `g(n) ≤ n / 2` for every `n ≠ 1`: each decrement is a prime, hence `≥ 2`,
and the orbit never visits `1`. -/
theorem stepsMax_le_half {n : ℕ} (hn : n ≠ 1) : stepsMax n ≤ n / 2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp [stepsMax]
    · have hn2 : 2 ≤ n := by omega
      have hP2 := (maxPrimeFac_prime hn2).two_le
      have hPn : maxPrimeFac n ≤ n := Nat.le_of_dvd hpos (maxPrimeFac_dvd hn2)
      have hrec := ih (n - maxPrimeFac n) (by omega) (sub_maxPrimeFac_ne_one hn2)
      rw [stepsMax_of_pos hpos]
      omega

/-- Strict bound: an even `m > 0` with an odd prime factor `q` has
`g(m) < m / 2`, since its first decrement is at least `q ≥ 3`. -/
theorem stepsMax_lt_half {m q : ℕ} (hm : Even m) (hm0 : 0 < m) (hq : q.Prime)
    (hq2 : q ≠ 2) (hqm : q ∣ m) : stepsMax m < m / 2 := by
  have hm2 : 2 ≤ m := by obtain ⟨k, hk⟩ := hm; omega
  have hPn : maxPrimeFac m ≤ m := Nat.le_of_dvd hm0 (maxPrimeFac_dvd hm2)
  have hq3 : 3 ≤ q := by have := hq.two_le; omega
  have hqP : q ≤ maxPrimeFac m := le_maxPrimeFac_of_dvd (by omega) hq hqm
  have hrec := stepsMax_le_half (sub_maxPrimeFac_ne_one hm2)
  rw [stepsMax_of_pos hm0]
  obtain ⟨k, hk⟩ := hm
  omega

/-! ## The conjecture -/

/-- Step-count form of **Dilkhush's conjecture (A399155)**: for every `n ≥ 2`,
the number `g(n)` of steps to reach `0` by repeatedly subtracting the largest
prime factor is at most the number `f(n)` of steps when subtracting the
smallest prime factor. -/
theorem stepsMax_le_stepsMin {n : ℕ} (hn : 2 ≤ n) : stepsMax n ≤ stepsMin n := by
  rcases Nat.even_or_odd n with he | ho
  · rw [stepsMin_even he]
    exact stepsMax_le_half (by omega)
  · have hpos : 0 < n := by omega
    have hp := Nat.minFac_prime (show n ≠ 1 by omega)
    have hpd := Nat.minFac_dvd n
    have hpodd : Odd n.minFac := Odd.of_dvd_nat ho hpd
    have hpn : n.minFac ≤ n := Nat.minFac_le hpos
    have hPn : maxPrimeFac n ≤ n := Nat.le_of_dvd hpos (maxPrimeFac_dvd hn)
    have hpP : n.minFac ≤ maxPrimeFac n := le_maxPrimeFac_of_dvd (by omega) hp hpd
    have heven : Even (n - n.minFac) := Nat.Odd.sub_odd ho hpodd
    have hrec := stepsMax_le_half (sub_maxPrimeFac_ne_one hn)
    rw [stepsMax_of_pos hpos, stepsMin_of_pos hpos, stepsMin_even heven]
    omega

/-- **Dilkhush's conjecture (A399155, Jaylen Dilkhush, 2026).**

Here `a n = f(n) - g(n)` is computed in `ℤ`, so the statement is not about
truncated subtraction.  The guard `2 ≤ n` is the entry's offset. -/
theorem a_nonneg {n : ℕ} (hn : 2 ≤ n) : 0 ≤ a n := by
  have hle := stepsMax_le_stepsMin hn
  unfold a
  omega

/-! ## Further identities from the entry -/

/-- `g(4) = 2`: `4 → 2 → 0`. -/
theorem stepsMax_four : stepsMax 4 = 2 := by
  have hP := maxPrimeFac_prime (m := 4) (by norm_num)
  have hPd : maxPrimeFac 4 ∣ 2 ^ 2 := maxPrimeFac_dvd (by norm_num)
  have h2 : maxPrimeFac 4 = 2 :=
    (Nat.prime_dvd_prime_iff_eq hP Nat.prime_two).mp (hP.dvd_of_dvd_pow hPd)
  rw [stepsMax_of_pos (by norm_num), h2, show 4 - 2 = 2 by rfl, stepsMax_prime Nat.prime_two]

/-- Step-count form of the entry's comment "a(n) = 0 if and only if n = 4 or
n is prime": for `n ≥ 2`, `g(n) = f(n)` iff `n` is prime or `n = 4`. -/
theorem stepsMax_eq_stepsMin_iff {n : ℕ} (hn : 2 ≤ n) :
    stepsMax n = stepsMin n ↔ n.Prime ∨ n = 4 := by
  constructor
  · intro heq
    by_contra hcon
    push Not at hcon
    obtain ⟨hnp, hn4⟩ := hcon
    have hpos : 0 < n := by omega
    suffices hlt : stepsMax n < stepsMin n by omega
    rcases Nat.even_or_odd n with he | ho
    · rw [stepsMin_even he]
      have hn6 : 6 ≤ n := by
        have hn2' : n ≠ 2 := fun h => hnp (h ▸ Nat.prime_two)
        obtain ⟨k, hk⟩ := he
        omega
      by_cases hP2 : maxPrimeFac n = 2
      · -- every prime factor of `n` is `2`, so `n / 2` is even and
        -- `n - 2 = 2 (n / 2 - 1)` has the odd prime factor `minFac (n / 2 - 1)`
        have hhalf : Even (n / 2) := by
          by_contra hodd
          rw [Nat.not_even_iff_odd] at hodd
          have hq := Nat.minFac_prime (show n / 2 ≠ 1 by omega)
          have hqodd : Odd (n / 2).minFac := Odd.of_dvd_nat hodd (Nat.minFac_dvd _)
          have hqn : (n / 2).minFac ∣ n :=
            (Nat.minFac_dvd _).trans (Nat.div_dvd_of_dvd (even_iff_two_dvd.mp he))
          have hle := le_maxPrimeFac_of_dvd (by omega) hq hqn
          rw [hP2] at hle
          have hq2 := hq.two_le
          obtain ⟨k, hk⟩ := hqodd
          omega
        have hodd1 : Odd (n / 2 - 1) := by
          obtain ⟨k, hk⟩ := hhalf
          exact ⟨k - 1, by omega⟩
        have hh1 : n / 2 - 1 ≠ 1 := by
          obtain ⟨k, hk⟩ := hhalf
          omega
        have hq := Nat.minFac_prime hh1
        have hqodd : Odd (n / 2 - 1).minFac := Odd.of_dvd_nat hodd1 (Nat.minFac_dvd _)
        have hq2 : (n / 2 - 1).minFac ≠ 2 := by
          intro h
          rw [h] at hqodd
          exact absurd hqodd (by decide)
        have hqn : (n / 2 - 1).minFac ∣ n - 2 :=
          (Nat.minFac_dvd _).trans ⟨2, by obtain ⟨k, hk⟩ := he; omega⟩
        have heven2 : Even (n - 2) := by
          obtain ⟨k, hk⟩ := he
          exact ⟨k - 1, by omega⟩
        have hlt := stepsMax_lt_half heven2 (by omega) hq hq2 hqn
        rw [stepsMax_of_pos hpos, hP2]
        omega
      · exact stepsMax_lt_half he hpos (maxPrimeFac_prime hn) hP2 (maxPrimeFac_dvd hn)
    · have hp := Nat.minFac_prime (show n ≠ 1 by omega)
      have hpd := Nat.minFac_dvd n
      have hpodd : Odd n.minFac := Odd.of_dvd_nat ho hpd
      have hpn : n.minFac ≤ n := Nat.minFac_le hpos
      have hP := maxPrimeFac_prime hn
      have hPd := maxPrimeFac_dvd hn
      have hPodd : Odd (maxPrimeFac n) := Odd.of_dvd_nat ho hPd
      have hPn : maxPrimeFac n < n := by
        refine lt_of_le_of_ne (Nat.le_of_dvd hpos hPd) ?_
        intro h
        rw [h] at hP
        exact hnp hP
      have hpP : n.minFac ≤ maxPrimeFac n := le_maxPrimeFac_of_dvd (by omega) hp hpd
      have hP2 : maxPrimeFac n ≠ 2 := by
        intro h
        rw [h] at hPodd
        exact absurd hPodd (by decide)
      have hevenP : Even (n - maxPrimeFac n) := Nat.Odd.sub_odd ho hPodd
      have hevenp : Even (n - n.minFac) := Nat.Odd.sub_odd ho hpodd
      have hlt := stepsMax_lt_half hevenP (by omega) hP hP2 (Nat.dvd_sub hPd dvd_rfl)
      rw [stepsMax_of_pos hpos, stepsMin_of_pos hpos, stepsMin_even hevenp]
      omega
  · rintro (hp | rfl)
    · rw [stepsMax_prime hp, stepsMin_prime hp]
    · rw [stepsMax_four, stepsMin_even (by decide)]

/-- The entry's comment "a(n) = 0 if and only if n = 4 or n is prime", for
`n ≥ 2` (the entry's offset). -/
theorem a_eq_zero_iff {n : ℕ} (hn : 2 ≤ n) : a n = 0 ↔ n.Prime ∨ n = 4 := by
  rw [← stepsMax_eq_stepsMin_iff hn]
  unfold a
  omega

/-- The entry's comment "a(2*p) = p - 2 for odd primes p". -/
theorem a_two_mul_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    a (2 * p) = (p : ℤ) - 2 := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have h2p : 2 ≤ 2 * p := by omega
  have hP := maxPrimeFac_prime h2p
  have hpP : p ≤ maxPrimeFac (2 * p) := le_maxPrimeFac_of_dvd (by omega) hp (dvd_mul_left p 2)
  have hPp : maxPrimeFac (2 * p) = p := by
    rcases (Nat.Prime.dvd_mul hP).mp (maxPrimeFac_dvd h2p) with h | h
    · have := Nat.le_of_dvd (by norm_num) h
      omega
    · exact (Nat.prime_dvd_prime_iff_eq hP hp).mp h
  have hmax : stepsMax (2 * p) = 2 := by
    rw [stepsMax_of_pos (by omega), hPp, show 2 * p - p = p by omega, stepsMax_prime hp]
  have hmin : stepsMin (2 * p) = p := by
    rw [stepsMin_even (even_two_mul p)]
    omega
  unfold a
  rw [hmax, hmin]
  push_cast
  ring

/-! ## Examples -/

-- The hypotheses of `a_nonneg` and `a_eq_zero_iff` hold at `n = 2`, and the
-- inequality is strict at a composite: `a 6 = 1`.
example : 0 ≤ a 2 := a_nonneg le_rfl
example : a 6 = 1 := by decide +kernel
-- The hypotheses of `a_two_mul_prime` hold at `p = 3`: `a 6 = 3 - 2`.
example : a (2 * 3) = (3 : ℤ) - 2 := a_two_mul_prime Nat.prime_three (by norm_num)

end Candidates.A399155CountsStepsReach
