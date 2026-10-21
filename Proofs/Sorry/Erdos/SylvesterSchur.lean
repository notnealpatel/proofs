/-
# Sylvester–Schur theorem

## Source

* J. J. Sylvester, "On arithmetical series", Messenger of Mathematics 21
  (1892), 1–19 and 87–120 (the consecutive-integers form).
* I. Schur (1929), independent rediscovery.
* P. Erdős, "A theorem of Sylvester and Schur", J. London Math. Soc. 9
  (1934), 282–288, where the theorem is stated in the binomial form used here.

Informal statement (Erdős 1934 form): *for positive integers `n` and `k`
with `n ≥ 2k`, the binomial coefficient `C(n, k)` has a prime factor greater
than `k`.*  Equivalently, a product of `k` consecutive integers each greater
than `k` has a prime factor greater than `k`.

Date: 2026-10-21.

## Mathlib status

`leandoc` searches ("Sylvester Schur binomial prime factor", "binomial prime
divisor greater than k") and `grep -ri sylvester` over Mathlib found only
Sylvester matrices and Sylvester's law of inertia; the theorem is absent.

## Proof outline (Erdős-style, with an explicit finite window)

Suppose every prime factor of `C(n,k)` is at most `k` (hypothesis `H`).
Every prime power `p ^ v_p(C(n,k))` is at most `n`; primes above `√n` occur at
most once; primes in `(n/3, k]` do not occur.  Hence
* (U1) `C(n,k) ≤ n ^ π(k)`;
* (U2) `C(n,k) ≤ n ^ π(√n) * 4 ^ min(k, n/3)` (via `primorial_le_four_pow`).
Together with `(n+1-k)^k ≤ k^k C(n,k)`, the ratio identity
`C(n,j+1)(j+1) = C(n,j)(n-j)`, the bound `6^q ≤ 3 C(3q,q)`, the elementary
estimate `3 π(x) ≤ x + 9`, and one real inequality
`(√x + 10) log x ≤ (x - 2)/3` for `x ≥ 2500`, this gives a contradiction for
`n ≥ 2500`, `k ≥ 36`.  Small `k` use (U1) with the exact value of `π(k)`;
the remaining window `n < 2500` is covered by explicit chains of primes
(a prime in `(n-k, n]` divides `C(n,k)`) and a decidable check.
-/
import Mathlib

set_option autoImplicit false

namespace Erdos.SylvesterSchur

open Finset

/-! ## Primes in the window `(n - k, n]` -/

/-- A prime `p > k` dividing some `m` with `n - k < m ≤ n`, `0 < m`, divides `C(n, k)`. -/
theorem prime_dvd_choose_of_dvd_window {n k p m : ℕ} (hp : p.Prime) (hkp : k < p)
    (hmn : m ≤ n) (hkm : n < m + k) (hpm : p ∣ m) : p ∣ n.choose k := by
  have hmem : n - m ∈ Finset.range k := Finset.mem_range.2 (by omega)
  have h1 : n - (n - m) ∣ ∏ i ∈ Finset.range k, (n - i) :=
    Finset.dvd_prod_of_mem (fun i => n - i) hmem
  rw [Nat.sub_sub_self hmn, ← Nat.descFactorial_eq_prod_range,
    Nat.descFactorial_eq_factorial_mul_choose] at h1
  rcases (Nat.Prime.dvd_mul hp).1 (hpm.trans h1) with h | h
  · exact absurd ((hp.dvd_factorial).1 h) (by omega)
  · exact h

/-- A prime `p` with `n - k < p ≤ n` and `2k ≤ n` is a prime factor of `C(n,k)`
exceeding `k`. -/
theorem exists_of_prime_window {n k p : ℕ} (hkn : 2 * k ≤ n) (hp : p.Prime)
    (hpn : p ≤ n) (hnp : n < p + k) : ∃ q, q.Prime ∧ k < q ∧ q ∣ n.choose k :=
  ⟨p, hp, by omega, prime_dvd_choose_of_dvd_window hp (by omega) hpn hnp dvd_rfl⟩

/-- A prime `p > k` with `n % p < k` divides `C(n,k)` (the multiple
`n - n % p` of `p` lies in the window `(n - k, n]`). -/
theorem prime_dvd_choose_of_mod_lt {n k p : ℕ} (hp : p.Prime) (hkp : k < p)
    (hmod : n % p < k) : p ∣ n.choose k := by
  have hdiv : p * (n / p) + n % p = n := Nat.div_add_mod n p
  refine prime_dvd_choose_of_dvd_window (m := p * (n / p)) hp hkp (by omega) (by omega)
    (dvd_mul_right p _)

/-! ## Factorization of `C(n,k)` when all its prime factors are `≤ k` -/

/-- Hypothesis `H`: every prime factor of `C(n,k)` is at most `k`. -/
def AllPrimeFactorsLE (n k : ℕ) : Prop :=
  ∀ p, p.Prime → p ∣ n.choose k → p ≤ k

/-- Ground truth: `C(10, 9) = 10 = 2 · 5` has all prime factors `≤ 9` (here `2k > n`). -/
example : AllPrimeFactorsLE 10 9 := by
  intro p hp hd
  rw [show Nat.choose 10 9 = 10 by decide] at hd
  have hle := Nat.le_of_dvd (by norm_num) hd
  rcases Nat.lt_or_ge p 10 with h | h
  · omega
  · have h10 : p = 10 := by omega
    subst h10
    norm_num at hp

/-- Ground truth: `C(10, 5) = 252 = 2² · 3² · 7` has the prime factor `7 > 5`. -/
example : ¬ AllPrimeFactorsLE 10 5 := fun H =>
  absurd (H 7 (by norm_num) (by decide)) (by norm_num)

/-- Under `H`, primes above `k` have exponent `0` in `C(n,k)`. -/
theorem factorization_eq_zero_of_lt {n k p : ℕ} (H : AllPrimeFactorsLE n k) (hkp : k < p) :
    (n.choose k).factorization p = 0 := by
  by_cases hpp : p.Prime
  · exact Nat.factorization_eq_zero_of_not_dvd fun hd => absurd (H p hpp hd) (by omega)
  · exact Nat.factorization_eq_zero_of_not_prime _ hpp

/-- Under `H`, `C(n,k)` is the product of `p ^ v_p(C(n,k))` over primes `p ≤ k`. -/
theorem choose_eq_prod_primes {n k : ℕ} (hkn : k ≤ n) (H : AllPrimeFactorsLE n k) :
    n.choose k = ∏ p ∈ (Finset.range (k + 1)).filter Nat.Prime,
      p ^ (n.choose k).factorization p := by
  conv_lhs => rw [← Nat.prod_pow_factorization_choose n k hkn]
  symm
  refine Finset.prod_subset ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
    omega
  · intro p _ hp
    simp only [Finset.mem_filter, Finset.mem_range, not_and] at hp
    by_cases hpp : p.Prime
    · have hkp : k < p := by
        by_contra hle
        exact hp (by omega) hpp
      rw [factorization_eq_zero_of_lt H hkp, pow_zero]
    · rw [Nat.factorization_eq_zero_of_not_prime _ hpp, pow_zero]

/-- The primes `≤ k`, as a filtered range, have cardinality `π(k)`. -/
theorem card_filter_prime_range (k : ℕ) :
    ((Finset.range (k + 1)).filter Nat.Prime).card = Nat.primeCounting k := by
  rw [Nat.primeCounting, ← Nat.primesBelow_card_eq_primeCounting']
  rfl

/-- **(U1)** Under `H`, `C(n,k) ≤ n ^ π(k)`. -/
theorem choose_le_pow_primeCounting {n k : ℕ} (hkn : k ≤ n) (hn : 0 < n)
    (H : AllPrimeFactorsLE n k) : n.choose k ≤ n ^ Nat.primeCounting k := by
  rw [choose_eq_prod_primes hkn H, ← card_filter_prime_range, ← Finset.prod_const]
  exact Finset.prod_le_prod' fun p _ => Nat.pow_factorization_choose_le hn

/-- **(U2)** Under `H` with `2k ≤ n` and `4 ≤ n`:
`C(n,k) ≤ n ^ π(⌊√n⌋) * 4 ^ min k ⌊n/3⌋`.  Primes `p ≤ ⌊√n⌋` contribute at most `n`
each; larger primes occur at most once, and not at all when `3p > n`. -/
theorem choose_le_sqrt_bound {n k : ℕ} (hkn : 2 * k ≤ n) (hn : 4 ≤ n)
    (H : AllPrimeFactorsLE n k) :
    n.choose k ≤ n ^ Nat.primeCounting (Nat.sqrt n) * 4 ^ min k (n / 3) := by
  set S := (Finset.range (k + 1)).filter Nat.Prime with hS
  have hs2 : 2 ≤ Nat.sqrt n := Nat.le_sqrt.2 (by omega)
  rw [choose_eq_prod_primes (by omega) H,
    ← Finset.prod_filter_mul_prod_filter_not S (· ≤ Nat.sqrt n)]
  apply Nat.mul_le_mul
  · calc ∏ p ∈ S.filter (· ≤ Nat.sqrt n), p ^ (n.choose k).factorization p
          ≤ ∏ p ∈ S.filter (· ≤ Nat.sqrt n), n :=
            Finset.prod_le_prod' fun p _ => Nat.pow_factorization_choose_le (by omega)
      _ = n ^ (S.filter (· ≤ Nat.sqrt n)).card := Finset.prod_const n
      _ ≤ n ^ Nat.primeCounting (Nat.sqrt n) := by
          apply Nat.pow_le_pow_right (by omega)
          rw [← card_filter_prime_range]
          apply Finset.card_le_card
          intro p hp
          simp only [hS, Finset.mem_filter, Finset.mem_range] at hp ⊢
          exact ⟨by omega, hp.1.2⟩
  · calc ∏ p ∈ S.filter (fun p => ¬ p ≤ Nat.sqrt n), p ^ (n.choose k).factorization p
          ≤ ∏ p ∈ S.filter (fun p => ¬ p ≤ Nat.sqrt n), (if p ≤ n / 3 then p else 1) := by
            apply Finset.prod_le_prod'
            intro p hp
            simp only [hS, Finset.mem_filter, Finset.mem_range] at hp
            obtain ⟨⟨hpk, hpp⟩, hps⟩ := hp
            have hsq : n < p ^ 2 := Nat.sqrt_lt'.1 (by omega)
            have hle1 := Nat.factorization_choose_le_one (k := k) hsq
            split_ifs with h3
            · calc p ^ (n.choose k).factorization p ≤ p ^ 1 :=
                    Nat.pow_le_pow_right hpp.pos hle1
                _ = p := pow_one p
            · have h0 : (n.choose k).factorization p = 0 :=
                Nat.factorization_choose_of_lt_three_mul (by omega) (by omega) (by omega)
                  (by omega)
              rw [h0, pow_zero]
      _ = ∏ p ∈ (S.filter (fun p => ¬ p ≤ Nat.sqrt n)).filter (· ≤ n / 3), p :=
            (Finset.prod_filter _ _).symm
      _ ≤ primorial (min k (n / 3)) := by
            apply Finset.prod_le_prod_of_subset_of_one_le'
            · intro p hp
              simp only [hS, Finset.mem_filter, Finset.mem_range] at hp ⊢
              exact ⟨by omega, hp.1.1.2⟩
            · intro p hp _
              simp only [Finset.mem_filter, Finset.mem_range] at hp
              exact hp.2.one_lt.le
      _ ≤ 4 ^ min k (n / 3) := primorial_le_four_pow _

/-! ## Elementary estimates -/

/-- Elementary prime-counting bound `3 π(x) ≤ x + 9` (primes other than `2, 3`
are coprime to `6`; via `Nat.primeCounting'_add_le`). -/
theorem three_mul_primeCounting_le (x : ℕ) : 3 * Nat.primeCounting x ≤ x + 9 := by
  rcases Nat.lt_or_ge x 6 with hx | hx
  · interval_cases x <;> decide
  · have h := Nat.primeCounting'_add_le (a := 6) (k := 7) (by norm_num) (by norm_num) (x - 6)
    have h7 : Nat.primeCounting' 7 = 3 := by decide
    have h6 : Nat.totient 6 = 2 := by decide
    rw [h7, h6, show 7 + (x - 6) = x + 1 by omega] at h
    rw [Nat.primeCounting]
    omega

/-- `(n + 1 - k)^k ≤ k^k * C(n,k)`, i.e. `C(n,k) ≥ ((n+1-k)/k)^k`. -/
theorem pow_le_pow_mul_choose (n k : ℕ) : (n + 1 - k) ^ k ≤ k ^ k * n.choose k :=
  (Nat.pow_sub_le_descFactorial n k).trans (by
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.mul_le_mul_right _ (Nat.factorial_le_pow k))

/-- Monotonicity in `n`: if `A * N^p < (N + 1 - k)^k` with `1 ≤ k`, `p ≤ k ≤ N` and
`0 < N`, then `A * n^p < (n + 1 - k)^k` for every `n ≥ N`. -/
theorem mul_pow_lt_of_le {A N n p k : ℕ} (hk : 1 ≤ k) (hpk : p ≤ k) (hkN : k ≤ N)
    (hN : 0 < N) (hNn : N ≤ n) (h : A * N ^ p < (N + 1 - k) ^ k) :
    A * n ^ p < (n + 1 - k) ^ k := by
  have key : (N + 1 - k) * n ≤ (n + 1 - k) * N := by
    have h1 : k ≤ N + 1 := by omega
    have h2 : k ≤ n + 1 := by omega
    zify [h1, h2]
    have h3 : (0 : ℤ) ≤ ((k : ℤ) - 1) * ((n : ℤ) - N) := by
      apply mul_nonneg <;> omega
    nlinarith
  have hpow : (N + 1 - k) ^ k * n ^ k ≤ (n + 1 - k) ^ k * N ^ k := by
    rw [← mul_pow, ← mul_pow]
    exact Nat.pow_le_pow_left key k
  have hNk : n ^ p * N ^ k ≤ N ^ p * n ^ k := by
    have hle : N ^ (k - p) ≤ n ^ (k - p) := Nat.pow_le_pow_left hNn _
    have e1 : N ^ k = N ^ p * N ^ (k - p) := by rw [← pow_add, Nat.add_sub_cancel' hpk]
    have e2 : n ^ k = n ^ p * n ^ (k - p) := by rw [← pow_add, Nat.add_sub_cancel' hpk]
    rw [e1, e2]
    calc n ^ p * (N ^ p * N ^ (k - p)) = n ^ p * N ^ p * N ^ (k - p) := by ring
      _ ≤ n ^ p * N ^ p * n ^ (k - p) := Nat.mul_le_mul_left _ hle
      _ = N ^ p * (n ^ p * n ^ (k - p)) := by ring
  have hnk : 0 < n ^ k := pow_pos (by omega) k
  refine Nat.lt_of_mul_lt_mul_right (a := N ^ k) ?_
  calc A * n ^ p * N ^ k = A * (n ^ p * N ^ k) := by ring
    _ ≤ A * (N ^ p * n ^ k) := Nat.mul_le_mul_left _ hNk
    _ = A * N ^ p * n ^ k := by ring
    _ < (N + 1 - k) ^ k * n ^ k := Nat.mul_lt_mul_of_pos_right h hnk
    _ ≤ (n + 1 - k) ^ k * N ^ k := hpow

/-- One chain step: if `n (j+1)^3 ≤ (n - j)^3` then `n * C(n,j)^3 ≤ C(n,j+1)^3`. -/
theorem choose_step {n j : ℕ} (h : n * (j + 1) ^ 3 ≤ (n - j) ^ 3) :
    n * n.choose j ^ 3 ≤ n.choose (j + 1) ^ 3 := by
  have hid := Nat.choose_succ_right_eq n j
  have hpos : 0 < (j + 1) ^ 3 := by positivity
  refine le_of_mul_le_mul_right ?_ hpos
  calc n * n.choose j ^ 3 * (j + 1) ^ 3 = n.choose j ^ 3 * (n * (j + 1) ^ 3) := by ring
    _ ≤ n.choose j ^ 3 * (n - j) ^ 3 := Nat.mul_le_mul_left _ h
    _ = (n.choose j * (n - j)) ^ 3 := by ring
    _ = (n.choose (j + 1) * (j + 1)) ^ 3 := by rw [hid]
    _ = n.choose (j + 1) ^ 3 * (j + 1) ^ 3 := by ring

/-- Chain: if every step `j → j+1` with `a ≤ j < b` satisfies `n (j+1)^3 ≤ (n-j)^3`, then
`n^(b-a) * C(n,a)^3 ≤ C(n,b)^3`. -/
theorem choose_chain {n a b : ℕ} (hab : a ≤ b)
    (hstep : ∀ j, a ≤ j → j < b → n * (j + 1) ^ 3 ≤ (n - j) ^ 3) :
    n ^ (b - a) * n.choose a ^ 3 ≤ n.choose b ^ 3 := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    have h1 := ih (fun j hj hjb => hstep j hj (by omega))
    have h2 := choose_step (hstep b hab (by omega))
    calc n ^ (b + 1 - a) * n.choose a ^ 3 = n * (n ^ (b - a) * n.choose a ^ 3) := by
          rw [show b + 1 - a = (b - a) + 1 by omega, pow_succ]; ring
      _ ≤ n * n.choose b ^ 3 := Nat.mul_le_mul_left _ h1
      _ ≤ _ := h2

/-- `C(n,·)` is monotone on `[0, n/2]`. -/
theorem choose_le_choose_of_le_half {n a b : ℕ} (hab : a ≤ b) (hb : 2 * b ≤ n) :
    n.choose a ≤ n.choose b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b _ ih => exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

/-- Ratio step for `C(3q, q)`: `6 C(3q,q) ≤ C(3q+3, q+1)` for `q ≥ 4`. -/
theorem six_mul_choose_three_mul_le {q : ℕ} (hq : 4 ≤ q) :
    6 * (3 * q).choose q ≤ (3 * q + 3).choose (q + 1) := by
  have e1 := Nat.choose_mul_succ_eq (3 * q) q
  have e2 := Nat.choose_mul_succ_eq (3 * q + 1) q
  have e3 := Nat.choose_mul_succ_eq (3 * q + 2) q
  have e4 := Nat.choose_succ_right_eq (3 * q + 3) q
  rw [show 3 * q + 1 - q = 2 * q + 1 by omega] at e1
  rw [show 3 * q + 1 + 1 - q = 2 * q + 2 by omega, show 3 * q + 1 + 1 = 3 * q + 2 by omega] at e2
  rw [show 3 * q + 2 + 1 - q = 2 * q + 3 by omega, show 3 * q + 2 + 1 = 3 * q + 3 by omega] at e3
  rw [show 3 * q + 3 - q = 2 * q + 3 by omega] at e4
  set c0 := (3 * q).choose q
  set c1 := (3 * q + 1).choose q
  set c2 := (3 * q + 2).choose q
  set c3 := (3 * q + 3).choose q
  set d := (3 * q + 3).choose (q + 1)
  -- d (q+1) = c3 (2q+3) and c2 (3q+3) = c3 (2q+3), so d (q+1) = c2 (3q+3)
  have f1 : d * (q + 1) = c2 * (3 * q + 3) := by rw [e4, e3]
  have hpoly : 6 * ((q + 1) * (2 * q + 1) * (2 * q + 2)) ≤
      (3 * q + 1) * (3 * q + 2) * (3 * q + 3) := by
    have h4 : 3 * q + 2 ≤ q * q := by nlinarith
    nlinarith [Nat.mul_le_mul_left (q + 1) h4]
  have hkey : d * ((q + 1) * (2 * q + 1) * (2 * q + 2)) =
      c0 * ((3 * q + 1) * (3 * q + 2) * (3 * q + 3)) := by
    calc d * ((q + 1) * (2 * q + 1) * (2 * q + 2))
        = (d * (q + 1)) * (2 * q + 2) * (2 * q + 1) := by ring
      _ = c2 * (2 * q + 2) * (3 * q + 3) * (2 * q + 1) := by rw [f1]; ring
      _ = c1 * (3 * q + 2) * (3 * q + 3) * (2 * q + 1) := by rw [← e2]
      _ = (c1 * (2 * q + 1)) * (3 * q + 2) * (3 * q + 3) := by ring
      _ = c0 * ((3 * q + 1) * (3 * q + 2) * (3 * q + 3)) := by rw [← e1]; ring
  have hpos : 0 < (q + 1) * (2 * q + 1) * (2 * q + 2) := by positivity
  refine le_of_mul_le_mul_right ?_ hpos
  calc 6 * c0 * ((q + 1) * (2 * q + 1) * (2 * q + 2))
      = c0 * (6 * ((q + 1) * (2 * q + 1) * (2 * q + 2))) := by ring
    _ ≤ c0 * ((3 * q + 1) * (3 * q + 2) * (3 * q + 3)) := Nat.mul_le_mul_left _ hpoly
    _ = d * ((q + 1) * (2 * q + 1) * (2 * q + 2)) := hkey.symm

/-- Exponential lower bound `6^q ≤ 3 C(3q, q)`. -/
theorem six_pow_le_three_mul_choose (q : ℕ) : 6 ^ q ≤ 3 * (3 * q).choose q := by
  induction q with
  | zero => simp
  | succ q ih =>
    rcases Nat.lt_or_ge q 4 with hq | hq
    · interval_cases q <;> decide
    · have h := six_mul_choose_three_mul_le hq
      rw [show 3 * (q + 1) = 3 * q + 3 by ring]
      calc 6 ^ (q + 1) = 6 * 6 ^ q := by ring
        _ ≤ 6 * (3 * (3 * q).choose q) := Nat.mul_le_mul_left _ ih
        _ = 3 * (6 * (3 * q).choose q) := by ring
        _ ≤ 3 * (3 * q + 3).choose (q + 1) := Nat.mul_le_mul_left _ h

/-! ## The analytic inequality -/

/-- Real inequality `(√x + 10) log x ≤ (x - 2)/3` for `x ≥ 2500`
(via `w = x^(1/4)`, `log w ≤ w/e`). -/
theorem sqrt_add_ten_mul_log_le {x : ℝ} (hx : 2500 ≤ x) :
    (√x + 10) * Real.log x ≤ (x - 2) / 3 := by
  have hx0 : 0 ≤ x := by linarith
  set y := √x with hy
  set w := √y with hw
  have hy0 : 0 ≤ y := Real.sqrt_nonneg x
  have hw0 : 0 ≤ w := Real.sqrt_nonneg y
  have hyy : y ^ 2 = x := Real.sq_sqrt hx0
  have hww : w ^ 2 = y := Real.sq_sqrt hy0
  have hy49 : 49 ≤ y := by nlinarith
  have hw7 : 7 ≤ w := by nlinarith
  have hwpos : 0 < w := by linarith
  have hx4 : x = w ^ 4 := by rw [← hyy, ← hww]; ring
  have hlogx : Real.log x = 4 * Real.log w := by
    rw [hx4, Real.log_pow]; norm_num
  have hlogw : Real.log w ≤ w / Real.exp 1 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < w / Real.exp 1 by positivity)
    rw [Real.log_div hwpos.ne' (Real.exp_pos 1).ne', Real.log_exp] at h
    linarith
  have he : 2.7182818283 < Real.exp 1 := Real.exp_one_gt_d9
  have hwe : w / Real.exp 1 ≤ 0.37 * w := by
    rw [div_le_iff₀ (Real.exp_pos 1)]; nlinarith
  have hL : Real.log x ≤ 1.48 * w := by rw [hlogx]; linarith
  have hw3 : 343 ≤ w ^ 3 := by nlinarith
  calc (y + 10) * Real.log x ≤ (y + 10) * (1.48 * w) :=
        mul_le_mul_of_nonneg_left hL (by linarith)
    _ ≤ (x - 2) / 3 := by
        rw [← hww, hx4]
        nlinarith [mul_le_mul_of_nonneg_left hw7 (show (0 : ℝ) ≤ w ^ 3 by positivity)]

/-- Nat form of the analytic inequality: `n^(⌊√n⌋+10) * 8^⌊n/3⌋ < 27^⌊n/3⌋` for `n ≥ 2500`. -/
theorem pow_sqrt_mul_eight_pow_lt {n : ℕ} (hn : 2500 ≤ n) :
    n ^ (Nat.sqrt n + 10) * 8 ^ (n / 3) < 27 ^ (n / 3) := by
  have hnR : (2500 : ℝ) ≤ n := by exact_mod_cast hn
  have hq : (((n : ℝ) - 2) / 3) ≤ ((n / 3 : ℕ) : ℝ) := by
    have h3 : n ≤ 3 * (n / 3) + 2 := by omega
    have h3R : (n : ℝ) ≤ 3 * ((n / 3 : ℕ) : ℝ) + 2 := by exact_mod_cast h3
    linarith
  have hqpos : (0 : ℝ) < ((n / 3 : ℕ) : ℝ) := by
    have : 0 < n / 3 := by omega
    exact_mod_cast this
  have hs : ((Nat.sqrt n : ℕ) : ℝ) ≤ √(n : ℝ) := Real.nat_sqrt_le_real_sqrt
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hmain := sqrt_add_ten_mul_log_le hnR
  have h278 : 1 < Real.log 27 - Real.log 8 := by
    rw [← Real.log_div (by norm_num) (by norm_num), Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9
    norm_num at this ⊢
    linarith
  have hpos1 : (0 : ℝ) < (n : ℝ) ^ (Nat.sqrt n + 10) * 8 ^ (n / 3) := by positivity
  have hpos2 : (0 : ℝ) < (27 : ℝ) ^ (n / 3) := by positivity
  rw [← Nat.cast_lt (α := ℝ)]
  push_cast
  rw [← Real.log_lt_log_iff hpos1 hpos2, Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow]
  push_cast
  have hA : ((Nat.sqrt n : ℝ) + 10) * Real.log n ≤ (√(n : ℝ) + 10) * Real.log n :=
    mul_le_mul_of_nonneg_right (by linarith) hlogn
  nlinarith

/-- **(E2)** For `n ≥ 2500`, with `q = ⌊n/3⌋` and `s = ⌊√n⌋`:
`n^(s+9) * 64^q < C(n,q)^3`. -/
theorem pow_mul_sixtyfour_pow_lt_choose_cube {n : ℕ} (hn : 2500 ≤ n) :
    n ^ (Nat.sqrt n + 9) * 64 ^ (n / 3) < n.choose (n / 3) ^ 3 := by
  set q := n / 3 with hqdef
  have h1 : (3 * q).choose q ≤ n.choose q := Nat.choose_le_choose q (by omega)
  have h2 : 6 ^ q ≤ 3 * (3 * q).choose q := six_pow_le_three_mul_choose q
  have h216 : 216 ^ q ≤ 27 * n.choose q ^ 3 := by
    calc 216 ^ q = (6 ^ q) ^ 3 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      _ ≤ (3 * (3 * q).choose q) ^ 3 := Nat.pow_le_pow_left h2 3
      _ ≤ (3 * n.choose q) ^ 3 := Nat.pow_le_pow_left (Nat.mul_le_mul_left 3 h1) 3
      _ = 27 * n.choose q ^ 3 := by ring
  have h3 := pow_sqrt_mul_eight_pow_lt hn
  rw [← hqdef] at h3
  have h4 : 27 * (n ^ (Nat.sqrt n + 9) * 64 ^ q) < 27 * n.choose q ^ 3 := by
    calc 27 * (n ^ (Nat.sqrt n + 9) * 64 ^ q) ≤ n * (n ^ (Nat.sqrt n + 9) * 64 ^ q) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = (n ^ (Nat.sqrt n + 10) * 8 ^ q) * 8 ^ q := by
          rw [show (64 : ℕ) = 8 * 8 by norm_num, mul_pow]; ring
      _ < 27 ^ q * 8 ^ q := Nat.mul_lt_mul_of_pos_right h3 (by positivity)
      _ = 216 ^ q := by rw [← mul_pow]; norm_num
      _ ≤ 27 * n.choose q ^ 3 := h216
  omega

/-! ## The case `n ≥ 2500`, `k ≥ 36` -/

/-- For `n ≥ 2500` and `lo = 3(⌊√n⌋+1)`: `n * lo^3 ≤ (n - lo + 1)^3`, so the chain
condition holds up to `lo`. -/
theorem lo_step_ok {n : ℕ} (hn : 2500 ≤ n) :
    n * (3 * (Nat.sqrt n + 1)) ^ 3 ≤ (n - 3 * (Nat.sqrt n + 1) + 1) ^ 3 := by
  set s := Nat.sqrt n with hsdef
  have hs50 : 50 ≤ s := Nat.le_sqrt.2 (by omega)
  have hss : s * s ≤ n := Nat.sqrt_le n
  have hle : 3 * (s + 1) ≤ n := by nlinarith
  zify [hle]
  have hssZ : (s : ℤ) * s ≤ n := by exact_mod_cast hss
  have hs50Z : (50 : ℤ) ≤ s := by exact_mod_cast hs50
  set T : ℤ := (s : ℤ) + 1 with hT
  set a : ℤ := (n : ℤ) - 3 * T + 1 with ha
  have hT51 : 51 ≤ T := by omega
  have hb : T ^ 2 - 5 * T + 2 ≤ a := by nlinarith
  have hn' : (n : ℤ) = a + 3 * T - 1 := by ring
  set b : ℤ := T ^ 2 - 5 * T + 2 with hbdef
  have hb46 : 46 * T ≤ b := by nlinarith
  have hb0 : 0 ≤ b := by nlinarith
  have hT3 : 0 ≤ T ^ 3 := by positivity
  have h1 : 14 * T ^ 3 ≤ b ^ 2 - 27 * T ^ 3 := by
    have : 51 * T ^ 3 ≤ T ^ 4 := by nlinarith
    nlinarith
  have h2 : b ^ 2 ≤ a ^ 2 := by nlinarith
  have ha0 : 0 ≤ a := by linarith
  have h3 : a * b ^ 2 ≤ a ^ 3 := by nlinarith
  have h4 : a * (14 * T ^ 3) ≤ a * (b ^ 2 - 27 * T ^ 3) := mul_le_mul_of_nonneg_left h1 ha0
  have h5 : (46 * T) * (14 * T ^ 3) ≤ a * (14 * T ^ 3) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  rw [hn']
  nlinarith

/-- Increasing steps compose: if `a j ≤ a (j+1)` for `lo ≤ j < k` then `a lo ≤ a k`. -/
theorem le_of_steps_up (a : ℕ → ℕ) {lo k : ℕ} (hlo : lo ≤ k)
    (h : ∀ j, lo ≤ j → j < k → a j ≤ a (j + 1)) : a lo ≤ a k := by
  induction k, hlo using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih => exact (ih fun j hj hjk => h j hj (by omega)).trans (h k hk (by omega))

/-- Decreasing steps compose: if `a (j+1) ≤ a j` for `k ≤ j < m` then `a m ≤ a k`. -/
theorem le_of_steps_down (a : ℕ → ℕ) {k m : ℕ} (hkm : k ≤ m)
    (h : ∀ j, k ≤ j → j < m → a (j + 1) ≤ a j) : a m ≤ a k := by
  induction m, hkm using Nat.le_induction with
  | base => exact le_rfl
  | succ m hm ih => exact (h m hm (by omega)).trans (ih fun j hj hjm => h j hj (by omega))

/-- Unimodality of `j ↦ C(n,j) 4^(m-j)` on `[lo, m]` (its step ratio
`(n-j)/(4(j+1))` decreases): the minimum over `[lo, m]` is at an endpoint. -/
theorem choose_mul_four_pow_unimodal {n m lo k : ℕ} (hlo : lo ≤ k) (hkm : k ≤ m)
    (hmn : m < n) :
    min (n.choose lo * 4 ^ (m - lo)) (n.choose m * 4 ^ (m - m)) ≤
      n.choose k * 4 ^ (m - k) := by
  set a : ℕ → ℕ := fun j => n.choose j * 4 ^ (m - j) with ha
  have hrel : ∀ j, j < m → a (j + 1) * (4 * (j + 1)) = a j * (n - j) := by
    intro j hj
    have hid := Nat.choose_succ_right_eq n j
    have he : 4 ^ (m - j) = 4 ^ (m - (j + 1)) * 4 := by
      rw [← pow_succ]; congr 1; omega
    simp only [ha]
    rw [he]
    calc n.choose (j + 1) * 4 ^ (m - (j + 1)) * (4 * (j + 1))
        = (n.choose (j + 1) * (j + 1)) * (4 ^ (m - (j + 1)) * 4) := by ring
      _ = (n.choose j * (n - j)) * (4 ^ (m - (j + 1)) * 4) := by rw [hid]
      _ = n.choose j * (4 ^ (m - (j + 1)) * 4) * (n - j) := by ring
  change min (a lo) (a m) ≤ a k
  by_cases hcase : 4 * k ≤ n - k + 1
  · refine min_le_of_left_le (le_of_steps_up a hlo fun j hj hjk => ?_)
    have hr := hrel j (by omega)
    have hnj : 0 < n - j := by omega
    have h4 : 4 * (j + 1) ≤ n - j := by omega
    refine le_of_mul_le_mul_right ?_ hnj
    calc a j * (n - j) = a (j + 1) * (4 * (j + 1)) := hr.symm
      _ ≤ a (j + 1) * (n - j) := Nat.mul_le_mul_left _ h4
  · refine min_le_of_right_le (le_of_steps_down a hkm fun j hj hjm => ?_)
    have hr := hrel j hjm
    have hpos : 0 < 4 * (j + 1) := by omega
    have h4 : n - j ≤ 4 * (j + 1) := by omega
    refine le_of_mul_le_mul_right ?_ hpos
    calc a (j + 1) * (4 * (j + 1)) = a j * (n - j) := hr
      _ ≤ a j * (4 * (j + 1)) := Nat.mul_le_mul_left _ h4

/-- `C(n,36)^3 > n^45` for `n ≥ 2500`. -/
theorem pow_lt_choose_thirtysix_cube {n : ℕ} (hn : 2500 ≤ n) : n ^ 45 < n.choose 36 ^ 3 := by
  have hnum : 36 ^ 36 * 2500 ^ 15 < (2500 + 1 - 36) ^ 36 := by norm_num
  have h1 := mul_pow_lt_of_le (A := 36 ^ 36) (N := 2500) (n := n) (p := 15) (k := 36)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hn hnum
  have h2 := pow_le_pow_mul_choose n 36
  have h3 : n ^ 15 < n.choose 36 := by
    have : 36 ^ 36 * n ^ 15 < 36 ^ 36 * n.choose 36 := lt_of_lt_of_le h1 h2
    exact Nat.lt_of_mul_lt_mul_left this
  calc n ^ 45 = (n ^ 15) ^ 3 := by rw [← pow_mul]
    _ < n.choose 36 ^ 3 := Nat.pow_lt_pow_left h3 (by norm_num)

/-- **Large case.** For `n ≥ 2500`, `36 ≤ k`, `2k ≤ n`, the hypothesis `H` fails. -/
theorem not_allPrimeFactorsLE_large {n k : ℕ} (hn : 2500 ≤ n) (hk : 36 ≤ k)
    (hkn : 2 * k ≤ n) : ¬ AllPrimeFactorsLE n k := by
  intro H
  set s := Nat.sqrt n with hsdef
  have hs50 : 50 ≤ s := Nat.le_sqrt.2 (by omega)
  have hss : s * s ≤ n := Nat.sqrt_le n
  have hbase := pow_lt_choose_thirtysix_cube hn
  have hpis := three_mul_primeCounting_le s
  have hn0 : 0 < n := by omega
  by_cases hR1 : n * k ^ 3 ≤ (n - k + 1) ^ 3
  · -- regime (R1): chain from 36 to k, against (U1)
    have hchain := choose_chain (n := n) (a := 36) (b := k) hk fun j _ hjk => by
      calc n * (j + 1) ^ 3 ≤ n * k ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hjk 3)
        _ ≤ (n - k + 1) ^ 3 := hR1
        _ ≤ (n - j) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have hU1 := choose_le_pow_primeCounting (by omega) hn0 H
    have hpik := three_mul_primeCounting_le k
    have hupper : n.choose k ^ 3 ≤ n ^ (k + 9) := by
      calc n.choose k ^ 3 ≤ (n ^ Nat.primeCounting k) ^ 3 := Nat.pow_le_pow_left hU1 3
        _ = n ^ (3 * Nat.primeCounting k) := by rw [← pow_mul, mul_comm]
        _ ≤ n ^ (k + 9) := Nat.pow_le_pow_right hn0 hpik
    have hlower : n ^ (k + 9) < n.choose k ^ 3 := by
      calc n ^ (k + 9) = n ^ (k - 36) * n ^ 45 := by rw [← pow_add]; congr 1; omega
        _ < n ^ (k - 36) * n.choose 36 ^ 3 :=
            Nat.mul_lt_mul_of_pos_left hbase (pow_pos hn0 _)
        _ ≤ n.choose k ^ 3 := hchain
    omega
  · -- regime (R2): unimodality on `[lo, n/3]`, against (U2)
    set lo := 3 * (s + 1) with hlodef
    have hc1 : n * lo ^ 3 ≤ (n - lo + 1) ^ 3 := lo_step_ok hn
    have hle : lo ≤ n / 3 := by
      have : 3 * lo ≤ n := by nlinarith
      omega
    have hklo : lo < k := by
      by_contra hcon
      apply hR1
      calc n * k ^ 3 ≤ n * lo ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
        _ ≤ (n - lo + 1) ^ 3 := hc1
        _ ≤ (n - k + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have hchain := choose_chain (n := n) (a := 36) (b := lo) (by omega) fun j _ hjk => by
      calc n * (j + 1) ^ 3 ≤ n * lo ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hjk 3)
        _ ≤ (n - lo + 1) ^ 3 := hc1
        _ ≤ (n - j) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    set P := n ^ Nat.primeCounting s with hP
    have hP3 : P ^ 3 ≤ n ^ (s + 9) := by
      calc P ^ 3 = n ^ (3 * Nat.primeCounting s) := by rw [hP, ← pow_mul, mul_comm]
        _ ≤ n ^ (s + 9) := Nat.pow_le_pow_right hn0 hpis
    -- lower endpoint `lo`
    have h64 : 64 ^ lo ≤ n ^ (2 * s + 3) := by
      have hn2 : 64 ^ 3 ≤ n ^ 2 := by nlinarith
      calc 64 ^ lo = (64 ^ 3) ^ (s + 1) := by rw [hlodef, pow_mul]
        _ ≤ (n ^ 2) ^ (s + 1) := Nat.pow_le_pow_left hn2 _
        _ = n ^ (2 * s + 2) := by rw [← pow_mul]; ring_nf
        _ ≤ n ^ (2 * s + 3) := Nat.pow_le_pow_right hn0 (by omega)
    have hlo_big : P * 4 ^ lo < n.choose lo := by
      refine lt_of_pow_lt_pow_left₀ 3 (Nat.zero_le _) ?_
      calc (P * 4 ^ lo) ^ 3 = P ^ 3 * 64 ^ lo := by
            rw [mul_pow]; congr 1; rw [← pow_mul, mul_comm lo 3, pow_mul]; norm_num
        _ ≤ n ^ (s + 9) * n ^ (2 * s + 3) := Nat.mul_le_mul hP3 h64
        _ = n ^ (lo - 36) * n ^ 45 := by rw [← pow_add, ← pow_add]; congr 1; omega
        _ < n ^ (lo - 36) * n.choose 36 ^ 3 :=
            Nat.mul_lt_mul_of_pos_left hbase (pow_pos hn0 _)
        _ ≤ n.choose lo ^ 3 := hchain
    -- upper endpoint `m = n/3`
    set m := n / 3 with hmdef
    have hm_big : P * 4 ^ m < n.choose m := by
      refine lt_of_pow_lt_pow_left₀ 3 (Nat.zero_le _) ?_
      calc (P * 4 ^ m) ^ 3 = P ^ 3 * 64 ^ m := by
            rw [mul_pow]; congr 1; rw [← pow_mul, mul_comm m 3, pow_mul]; norm_num
        _ ≤ n ^ (s + 9) * 64 ^ m := Nat.mul_le_mul_right _ hP3
        _ < n.choose m ^ 3 := pow_mul_sixtyfour_pow_lt_choose_cube hn
    have hU2 := choose_le_sqrt_bound hkn (by omega) H
    rw [← hsdef, ← hP] at hU2
    by_cases hkm : k ≤ m
    · rw [min_eq_left hkm] at hU2
      have huni := choose_mul_four_pow_unimodal (n := n) (m := m) (lo := lo) (k := k)
        hklo.le hkm (by omega)
      rw [Nat.sub_self, pow_zero, mul_one] at huni
      have hak : n.choose k * 4 ^ (m - k) ≤ P * 4 ^ m := by
        calc n.choose k * 4 ^ (m - k) ≤ P * 4 ^ k * 4 ^ (m - k) := Nat.mul_le_mul_right _ hU2
          _ = P * 4 ^ m := by rw [mul_assoc, ← pow_add]; congr 2; omega
      have hlo' : P * 4 ^ m < n.choose lo * 4 ^ (m - lo) := by
        calc P * 4 ^ m = P * 4 ^ lo * 4 ^ (m - lo) := by
              rw [mul_assoc, ← pow_add]; congr 2; omega
          _ < n.choose lo * 4 ^ (m - lo) := Nat.mul_lt_mul_of_pos_right hlo_big (by positivity)
      rcases min_le_iff.1 huni with h | h <;> omega
    · replace hkm : m < k := not_le.1 hkm
      rw [min_eq_right hkm.le] at hU2
      have hmono : n.choose m ≤ n.choose k := choose_le_choose_of_le_half hkm.le hkn
      omega

/-! ## The finite window -/

/-- Chain step for prime-gap certificates: if `p` is prime, `n < p + g`, and the claim
holds whenever `n < p`, then some prime `r ≤ n` has `n < r + g`. -/
theorem gap_step {g n : ℕ} (p : ℕ) (hp : p.Prime)
    (H : n < p → ∃ r, r.Prime ∧ r ≤ n ∧ n < r + g) (hn : n < p + g) :
    ∃ r, r.Prime ∧ r ≤ n ∧ n < r + g := by
  by_cases h : n < p
  · exact H h
  · exact ⟨p, hp, by omega, hn⟩

/-- Every `n` with `2 ≤ n < 537` has a prime `r ≤ n` with `n < r + 14` (explicit chain of primes). -/
theorem exists_prime_gap_fourteen {n : ℕ} (h2 : 2 ≤ n) (hn : n < 537) :
    ∃ r, r.Prime ∧ r ≤ n ∧ n < r + 14 := by
  refine gap_step 523 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 509 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 503 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 491 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 479 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 467 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 457 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 443 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 433 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 421 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 409 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 397 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 383 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 373 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 359 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 349 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 337 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 331 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 317 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 307 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 293 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 283 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 277 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 263 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 251 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 241 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 233 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 223 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 211 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 199 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 193 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 181 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 173 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 163 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 151 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 139 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 127 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 113 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 109 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 97 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 83 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 73 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 61 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 47 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 37 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 23 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 13 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 2 (by norm_num) ?_ (by omega)
  intro hlt
  omega

/-- Every `n` with `2 ≤ n < 2500` has a prime `r ≤ n` with `n < r + 34` (explicit chain of primes). -/
theorem exists_prime_gap_thirtyfour {n : ℕ} (h2 : 2 ≤ n) (hn : n < 2500) :
    ∃ r, r.Prime ∧ r ≤ n ∧ n < r + 34 := by
  refine gap_step 2477 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 2447 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 2423 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 2399 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 2371 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 2341 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 2311 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 2297 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 2273 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 2243 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 2213 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 2179 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 2161 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 2131 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 2099 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 2069 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 2039 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 2011 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 1979 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 1951 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 1933 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 1913 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 1879 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 1847 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 1823 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 1789 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 1759 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 1733 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 1699 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 1669 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 1637 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 1613 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 1583 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 1559 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 1531 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 1499 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 1471 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 1439 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 1409 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 1381 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 1361 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 1327 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 1307 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 1283 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 1249 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 1223 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 1193 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 1163 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 1129 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 1103 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 1069 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 1039 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 1013 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 983 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 953 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 919 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 887 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 863 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 829 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 797 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 773 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 743 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 709 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 683 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 653 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 619 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 587 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 557 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 523 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 499 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 467 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 443 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 409 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 383 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 349 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 317 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 293 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 263 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 233 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 199 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 173 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 139 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 113 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 89 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 61 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 31 (by norm_num) ?_ (by omega)
  intro hlt
  refine gap_step 2 (by norm_num) ?_ (by omega)
  intro hlt
  omega

/-- The primes below `140`, used by the decidable check of the window `n < 140`, `k ≤ 13`. -/
def smallPrimes : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139]

/-- Ground truth: `smallPrimes` lists the `π(139) = 34` primes below `140`. -/
example : smallPrimes.length = Nat.primeCounting 139 := by decide +kernel

/-- Every element of `smallPrimes` is prime. -/
theorem smallPrimes_prime : ∀ p ∈ smallPrimes, p.Prime := by decide +kernel

/-- Decidable check of the window `n < 140`, `1 ≤ k ≤ 13`, `2k ≤ n`: some prime `p > k`
in `smallPrimes` has a multiple in `(n - k, n]`. -/
theorem small_window_check : ∀ n < 140, ∀ k < 14, 1 ≤ k → 2 * k ≤ n →
    ∃ p ∈ smallPrimes, k < p ∧ n % p < k := by decide

/-- Numerical inputs for small `k`: with `N = 140` for `k ≤ 13` and `N = 537` for
`14 ≤ k ≤ 35`, `k^k N^π(k) < (N + 1 - k)^k` and `π(k) ≤ k`. -/
theorem small_k_numeric : ∀ k < 36, 1 ≤ k →
    k ^ k * (if k ≤ 13 then 140 else 537) ^ Nat.primeCounting k <
      ((if k ≤ 13 then 140 else 537) + 1 - k) ^ k ∧ Nat.primeCounting k ≤ k := by decide

/-- **Small `k`.** For `1 ≤ k ≤ 35` and `n ≥ N` (`N = 140` if `k ≤ 13`, else `N = 537`),
`H` fails: `(n+1-k)^k ≤ k^k C(n,k) ≤ k^k n^π(k)` contradicts `small_k_numeric`. -/
theorem not_allPrimeFactorsLE_small_k {n k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ 35)
    (hn : (if k ≤ 13 then 140 else 537) ≤ n) : ¬ AllPrimeFactorsLE n k := by
  intro H
  obtain ⟨hnum, hpik⟩ := small_k_numeric k (by omega) hk1
  have hN : k ≤ (if k ≤ 13 then 140 else 537) := by split_ifs <;> omega
  have hN0 : 0 < (if k ≤ 13 then 140 else 537) := by split_ifs <;> norm_num
  have h1 := mul_pow_lt_of_le hk1 hpik hN hN0 hn hnum
  have hU1 := choose_le_pow_primeCounting (by omega) (by omega : 0 < n) H
  have h2 := pow_le_pow_mul_choose n k
  have h3 : k ^ k * n.choose k ≤ k ^ k * n ^ Nat.primeCounting k := Nat.mul_le_mul_left _ hU1
  omega

/-! ## The theorem -/

/-- **Sylvester–Schur theorem** (Sylvester 1892, Schur 1929; binomial form of Erdős 1934):
for positive integers `n, k` with `n ≥ 2k`, the binomial coefficient `C(n, k)` has a prime
factor `p > k`. -/
theorem sylvester_schur (n k : ℕ) (hk : 1 ≤ k) (hkn : 2 * k ≤ n) :
    ∃ p, p.Prime ∧ k < p ∧ p ∣ n.choose k := by
  have hH : ¬ AllPrimeFactorsLE n k → ∃ p, p.Prime ∧ k < p ∧ p ∣ n.choose k := by
    intro h
    simp only [AllPrimeFactorsLE, not_forall, not_le] at h
    obtain ⟨p, hp, hd, hlt⟩ := h
    exact ⟨p, hp, hlt, hd⟩
  rcases Nat.lt_or_ge n 2500 with hn | hn
  · rcases Nat.lt_or_ge k 34 with hk34 | hk34
    · rcases Nat.lt_or_ge k 14 with hk14 | hk14
      · rcases Nat.lt_or_ge n 140 with hn140 | hn140
        · obtain ⟨p, hpL, hkp, hmod⟩ := small_window_check n hn140 k hk14 hk hkn
          have hp := smallPrimes_prime p hpL
          exact ⟨p, hp, hkp, prime_dvd_choose_of_mod_lt hp hkp hmod⟩
        · refine hH (not_allPrimeFactorsLE_small_k hk (by omega) ?_)
          rw [if_pos (by omega)]
          exact hn140
      · rcases Nat.lt_or_ge n 537 with hn537 | hn537
        · obtain ⟨r, hr, hrn, hnr⟩ := exists_prime_gap_fourteen (by omega) hn537
          exact exists_of_prime_window hkn hr hrn (by omega)
        · refine hH (not_allPrimeFactorsLE_small_k hk (by omega) ?_)
          rw [if_neg (by omega)]
          exact hn537
    · obtain ⟨r, hr, hrn, hnr⟩ := exists_prime_gap_thirtyfour (by omega) hn
      exact exists_of_prime_window hkn hr hrn (by omega)
  · rcases Nat.lt_or_ge k 36 with hk36 | hk36
    · exact hH (not_allPrimeFactorsLE_small_k hk (by omega) (by split_ifs <;> omega))
    · exact hH (not_allPrimeFactorsLE_large hn hk36 hkn)

/-- Non-vacuity: the hypotheses are jointly satisfiable, e.g. at `(n, k) = (10, 5)`. -/
example : ∃ p, p.Prime ∧ 5 < p ∧ p ∣ Nat.choose 10 5 :=
  sylvester_schur 10 5 (by norm_num) (by norm_num)

/-- **Sylvester's theorem, consecutive-integers form**: if `k ≤ m` and `1 ≤ k`, the `k`
consecutive integers `m + 1, …, m + k` (each greater than `k`) include a multiple of some
prime `p > k`. -/
theorem sylvester_consecutive (m k : ℕ) (hk : 1 ≤ k) (hkm : k ≤ m) :
    ∃ p, p.Prime ∧ k < p ∧ ∃ i < k, p ∣ m + 1 + i := by
  obtain ⟨p, hp, hkp, hd⟩ := sylvester_schur (m + k) k hk (by omega)
  have hdesc : p ∣ ∏ i ∈ Finset.range k, (m + k - i) := by
    rw [← Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_factorial_mul_choose]
    exact Dvd.dvd.mul_left hd _
  obtain ⟨i, hi, hpi⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 hdesc
  rw [Finset.mem_range] at hi
  refine ⟨p, hp, hkp, k - 1 - i, by omega, ?_⟩
  rw [show m + 1 + (k - 1 - i) = m + k - i by omega]
  exact hpi

end Erdos.SylvesterSchur
