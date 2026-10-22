/-
# A302975 — the reduced denominator of `tau(n)^n / n^tau(n)` is a square

The unsigned conjecture in OEIS A302975, an entry by Jaroslav Krizek
(2018): the reduced denominator of `τ(n)^n / n^τ(n)` is a square for `n ≥ 1`.
Here `τ(n)` is the number of divisors, not Ramanujan's tau function.

## Proof outline

Write `t = tau(n)`, `e = v_p(n)`, `b = v_p(t)`.  The reduced denominator is
`n^t / gcd(n^t, t^n)`, so its `p`-adic valuation is `e*t - min(e*t, n*b)`.

* `e*t` is always even, because `e + 1` divides `t` and `e*(e+1)` is even.
* If `n*b` is even, the valuation is a difference of even numbers or `0`.
* If `n*b` is odd, then `n` is odd and `b ≥ 1`; if `e ≥ 1` then `p` is an odd
  prime divisor of `n`, and `t*e ≤ n ≤ n*b` (from `n = p^e*m`,
  `t = (e+1)tau(m) ≤ (e+1)m`, `e(e+1) ≤ 3^e ≤ p^e`), so the valuation is `0`.

A natural number all of whose prime exponents are even is a square.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A302975ReducedDenominatorTau

open Finset

/-! ## Definitions -/

/-- `tau n`, the number of divisors of `n` (OEIS A000005). -/
def tau (n : ℕ) : ℕ := #n.divisors

/-- OEIS A302975: `a n` is the reduced denominator of the rational number
`tau(n)^n / n^tau(n)`. -/
def a (n : ℕ) : ℕ := (((tau n : ℚ) ^ n / (n : ℚ) ^ tau n).den)

example : tau 12 = 6 := by decide

/-! ## Helper lemmas -/

/-- A nonzero natural number whose prime exponents are all even is a perfect
square. -/
theorem isSquare_of_even_factorization {m : ℕ} (hm : m ≠ 0)
    (h : ∀ p, Even (m.factorization p)) : IsSquare m := by
  refine ⟨m.factorization.prod (fun p k => p ^ (k / 2)), ?_⟩
  rw [← Finsupp.prod_mul]
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hm]
  refine Finsupp.prod_congr fun p _ => ?_
  rw [← pow_add]
  congr 1
  obtain ⟨j, hj⟩ := h p
  omega

/-- `e * (e + 1) ≤ 3 ^ e` for every natural `e`. -/
theorem mul_succ_le_three_pow (e : ℕ) : e * (e + 1) ≤ 3 ^ e := by
  induction e with
  | zero => simp
  | succ k ih =>
    have hk : k + 1 ≤ 3 ^ k := Nat.lt_pow_self (by norm_num)
    rw [pow_succ]
    nlinarith

/-- For `n ≠ 0` and any `p`, `v_p(n) + 1` divides the number of divisors of
`n`. -/
theorem succ_factorization_dvd_tau {n : ℕ} (hn : n ≠ 0) (p : ℕ) :
    n.factorization p + 1 ∣ tau n := by
  unfold tau
  by_cases hp : p ∈ n.primeFactors
  · rw [Nat.card_divisors hn]
    exact Finset.dvd_prod_of_mem (fun q => n.factorization q + 1) hp
  · rw [← Nat.support_factorization, Finsupp.notMem_support_iff] at hp
    simp [hp]

/-- For `n ≠ 0`, `tau(n) * v_p(n)` is even. -/
theorem even_tau_mul_factorization {n : ℕ} (hn : n ≠ 0) (p : ℕ) :
    Even (tau n * n.factorization p) := by
  obtain ⟨k, hk⟩ := succ_factorization_dvd_tau hn p
  rw [hk, mul_comm, ← mul_assoc]
  exact (Nat.even_mul_succ_self _).mul_right k

/-- For `n ≠ 0` and a prime `p ≥ 3`, `tau(n) * v_p(n) ≤ n`. -/
theorem tau_mul_factorization_le {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime)
    (hp3 : 3 ≤ p) : tau n * n.factorization p ≤ n := by
  unfold tau
  set e := n.factorization p
  set m := n / p ^ e
  have hsplit : p ^ e * m = n := Nat.ordProj_mul_ordCompl_eq_self n p
  have hcop : Nat.Coprime (p ^ e) m :=
    Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hp hn)
  have hcard : #n.divisors = (e + 1) * #m.divisors := by
    rw [← hsplit, Nat.Coprime.card_divisors_mul hcop, Nat.divisors_prime_pow hp,
      card_map, card_range]
  have hm : #m.divisors ≤ m := Nat.card_divisors_le_self m
  have hpow : e * (e + 1) ≤ p ^ e :=
    (mul_succ_le_three_pow e).trans (Nat.pow_le_pow_left hp3 e)
  calc #n.divisors * e = (e * (e + 1)) * #m.divisors := by rw [hcard]; ring
    _ ≤ p ^ e * m := Nat.mul_le_mul hpow hm
    _ = n := hsplit

/-- For `n ≠ 0`, `a n = n^tau(n) / gcd(n^tau(n), tau(n)^n)`. -/
theorem a_eq (n : ℕ) (hn : n ≠ 0) :
    a n = n ^ tau n / Nat.gcd (n ^ tau n) (tau n ^ n) := by
  have hb : ((n ^ tau n : ℕ) : ℤ) ≠ 0 := by positivity
  have hq : ((tau n : ℚ) ^ n / (n : ℚ) ^ tau n) =
      Rat.divInt ((tau n ^ n : ℕ) : ℤ) ((n ^ tau n : ℕ) : ℤ) := by
    rw [Rat.divInt_eq_div]
    push_cast
    rfl
  rw [a, hq, Rat.den_divInt, if_neg hb]
  simp only [Int.natAbs_natCast, Int.gcd_natCast_natCast]

/-! ## Examples against the listed terms (via `a_eq`) -/

example : a 1 = 1 := by rw [a_eq 1 (by norm_num)]; decide
example : a 2 = 1 := by rw [a_eq 2 (by norm_num)]; decide
example : a 3 = 9 := by rw [a_eq 3 (by norm_num)]; decide
example : a 4 = 64 := by rw [a_eq 4 (by norm_num)]; decide
example : a 5 = 25 := by rw [a_eq 5 (by norm_num)]; decide
example : a 6 = 81 := by rw [a_eq 6 (by norm_num)]; decide
example : a 7 = 49 := by rw [a_eq 7 (by norm_num)]; decide
example : a 8 = 1 := by rw [a_eq 8 (by norm_num)]; decide
example : a 9 = 1 := by rw [a_eq 9 (by norm_num)]; decide
example : a 10 = 625 := by rw [a_eq 10 (by norm_num)]; decide
example : a 15 = 50625 := by rw [a_eq 15 (by norm_num)]; decide
example : a 16 = 1048576 := by rw [a_eq 16 (by norm_num)]; decide

/-- For `n ≠ 0`, `v_p(a n) = tau(n) v_p(n) - min(tau(n) v_p(n), n v_p(tau(n)))`. -/
theorem factorization_a (n : ℕ) (hn : n ≠ 0) (p : ℕ) :
    (a n).factorization p =
      tau n * n.factorization p -
        min (tau n * n.factorization p) (n * (tau n).factorization p) := by
  have hd : tau n ≠ 0 := (Finset.card_pos.mpr (Nat.nonempty_divisors.mpr hn)).ne'
  rw [a_eq n hn, Nat.factorization_div (Nat.gcd_dvd_left _ _),
    Nat.factorization_gcd (pow_ne_zero _ hn) (pow_ne_zero _ hd)]
  simp [Nat.factorization_pow]

/-- For `n ≠ 0`, every prime exponent of `a n` is even. -/
theorem even_factorization_a (n : ℕ) (hn : n ≠ 0) (p : ℕ) :
    Even ((a n).factorization p) := by
  rw [factorization_a n hn p]
  set e := n.factorization p with he
  set b := (tau n).factorization p with hb
  have hD : Even (tau n * e) := even_tau_mul_factorization hn p
  by_cases hle : tau n * e ≤ n * b
  · rw [min_eq_left hle, Nat.sub_self]
    exact ⟨0, rfl⟩
  · rw [not_le] at hle
    rw [min_eq_right hle.le]
    have hN : Even (n * b) := by
      by_contra hodd
      rw [Nat.not_even_iff_odd, Nat.odd_mul] at hodd
      obtain ⟨hnodd, hbodd⟩ := hodd
      have hb0 : b ≠ 0 := fun h0 => by rw [h0] at hbodd; exact absurd hbodd (by decide)
      have hpprime : p.Prime := Nat.prime_of_mem_primeFactors
        (Finsupp.mem_support_iff.mpr hb0)
      have he0 : e ≠ 0 := by
        rintro h0
        rw [h0, mul_zero] at hle
        exact absurd hle (Nat.not_lt_zero _)
      have hpn : p ∣ n := Nat.dvd_of_factorization_pos he0
      have hp2 : p ≠ 2 := by
        rintro rfl
        exact (Nat.not_even_iff_odd.mpr hnodd) (even_iff_two_dvd.mpr hpn)
      have hp3 : 3 ≤ p := by
        have h2 := hpprime.two_le
        omega
      have hbound : tau n * e ≤ n := tau_mul_factorization_le hn hpprime hp3
      have hnb : n ≤ n * b := Nat.le_mul_of_pos_right n (Nat.pos_of_ne_zero hb0)
      omega
    exact (Nat.even_sub hle.le).mpr (iff_of_true hD hN)

/-! ## The conjecture -/

/-- **A302975 conjecture (OEIS entry by Jaroslav Krizek, 2018).**

"Conjecture: all terms are squares."  That is, for every `n ≥ 1`,
the reduced denominator of `tau(n)^n / n^tau(n)` is a perfect square.  The
`0 < n` guard is the entry's offset. -/
theorem a_isSquare (n : ℕ) (hn : 0 < n) : IsSquare (a n) :=
  isSquare_of_even_factorization (Rat.den_ne_zero _) (even_factorization_a n hn.ne')

end Candidates.A302975ReducedDenominatorTau
