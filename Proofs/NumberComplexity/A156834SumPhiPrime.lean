/-
# A156834 — Adamson: the totient-weighted divisor sum equals `n` exactly at primes

Gary W. Adamson's conjecture in OEIS A156834 (2009), using Seiichi
Manyama's formula (2021): `a(n) = Σ_{d∣n} φ(d) C(d+n/d-2,d-1)`.

For `1 < n`, `a(n)=n` iff `n` is prime. Since `Σ_{d∣n} φ(d)=n`, it
suffices that each binomial weight is at least one; any divisor `1 < d < n`
has weight at least two.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A156834SumPhiPrime

/-! ## Definitions -/

/-- OEIS A156834 via Manyama's formula:
`a(n) = Σ_{d ∣ n} φ(d) · C(d + n/d − 2, d − 1)`.

For the natural-number subtractions, for `d ∈ n.divisors` we have `1 ≤ d` and `1 ≤ n / d`, so
`d + n / d - 2` and `d - 1` never hit the `ℕ`-subtraction floor, and `n / d`
is exact division. At `n = 0` the divisor set is empty and the value is `0`;
the entry's offset is `1`, so `n = 0` is outside the sequence. -/
def a (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors, Nat.totient d * (d + n / d - 2).choose (d - 1)

example : a 1 = 1 := by decide
example : a 2 = 2 := by decide
example : a 3 = 3 := by decide
example : a 4 = 5 := by decide
example : a 5 = 5 := by decide
example : a 6 = 12 := by decide
example : a 8 = 17 := by decide
example : a 9 = 19 := by decide
example : a 12 = 63 := by decide

/-! ## Helper lemmas -/

/-- For `1 ≤ k` and `1 ≤ j`, the binomial coefficient `C(k + j, k)` is at
least `2` (Pascal: it is `C(k+j-1, k-1) + C(k+j-1, k)`, both positive). -/
theorem two_le_choose_add {k j : ℕ} (hk : 1 ≤ k) (hj : 1 ≤ j) :
    2 ≤ (k + j).choose k := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hsplit : (k' + 1 + (j' + 1)).choose (k' + 1)
      = (k' + 1 + j').choose k' + (k' + 1 + j').choose (k' + 1) := by
    rw [show k' + 1 + (j' + 1) = (k' + 1 + j') + 1 by omega]
    exact Nat.choose_succ_succ _ _
  have h1 : 0 < (k' + 1 + j').choose k' := Nat.choose_pos (by omega)
  have h2 : 0 < (k' + 1 + j').choose (k' + 1) := Nat.choose_pos (by omega)
  omega

/-- Each binomial weight in `a n` is positive at a divisor `d` of `n ≠ 0`. -/
theorem choose_pos_of_mem_divisors {n d : ℕ} (hd : d ∈ n.divisors) :
    0 < (d + n / d - 2).choose (d - 1) := by
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hn : n ≠ 0 := (Nat.mem_divisors.mp hd).2
  have hq : 0 < n / d :=
    Nat.div_pos (Nat.divisor_le hd) hdpos
  exact Nat.choose_pos (by omega)

/-- Lower bound: `n ≤ a n`, since `Σ_{d ∣ n} φ(d) = n` and each weight is
at least `1`. -/
theorem le_a (n : ℕ) : n ≤ a n := by
  calc n = ∑ d ∈ n.divisors, Nat.totient d := (Nat.sum_totient n).symm
    _ ≤ a n := by
      unfold a
      refine Finset.sum_le_sum fun d hd => ?_
      exact Nat.le_mul_of_pos_right _ (choose_pos_of_mem_divisors hd)

/-- At a prime `p`, `a p = p`: the divisors are `1` and `p`, contributing
`φ(1)·C(p−1, 0) + φ(p)·C(p−1, p−1) = 1 + (p − 1)`. -/
theorem a_prime {p : ℕ} (hp : p.Prime) : a p = p := by
  have hp1 : 1 < p := hp.one_lt
  have hne : (1 : ℕ) ≠ p := by omega
  unfold a
  rw [hp.divisors, Finset.sum_insert (by simpa using hne), Finset.sum_singleton,
    Nat.totient_prime hp, Nat.div_self (by omega), Nat.div_one]
  rw [show 1 + p - 2 = p - 1 by omega, show p + 1 - 2 = p - 1 by omega]
  simp only [Nat.totient_one, Nat.sub_self, Nat.choose_zero_right, Nat.choose_self,
    mul_one]
  omega

/-- At a composite `n` (with `1 < n`, not prime), `n < a n`: a divisor
`1 < d < n` has weight `C(d + n/d − 2, d − 1) ≥ 2` and `φ(d) ≥ 1`. -/
theorem lt_a_of_not_prime {n : ℕ} (hn : 1 < n) (hnp : ¬ n.Prime) : n < a n := by
  obtain ⟨d, hdn, hd2, hdlt⟩ := Nat.exists_dvd_of_not_prime2 (by omega) hnp
  have hdmem : d ∈ n.divisors := Nat.mem_divisors.mpr ⟨hdn, by omega⟩
  obtain ⟨e, rfl⟩ := hdn
  have hdpos : 0 < d := by omega
  have he2 : 2 ≤ e := by
    by_contra hcon
    interval_cases e <;> omega
  have hq : d * e / d = e := Nat.mul_div_cancel_left e hdpos
  have hweight : 2 ≤ (d + d * e / d - 2).choose (d - 1) := by
    rw [hq, show d + e - 2 = (d - 1) + (e - 1) by omega]
    exact two_le_choose_add (by omega) (by omega)
  have htot : 0 < Nat.totient d := Nat.totient_pos.mpr hdpos
  calc d * e = ∑ x ∈ (d * e).divisors, Nat.totient x := (Nat.sum_totient _).symm
    _ < a (d * e) := by
      unfold a
      refine Finset.sum_lt_sum (fun x hx => ?_) ⟨d, hdmem, ?_⟩
      · exact Nat.le_mul_of_pos_right _ (choose_pos_of_mem_divisors hx)
      · calc Nat.totient d = Nat.totient d * 1 := (mul_one _).symm
          _ < Nat.totient d * (d + d * e / d - 2).choose (d - 1) :=
            Nat.mul_lt_mul_of_pos_left (by omega) htot

/-! ## The conjecture -/

/-- **Adamson's conjecture (A156834, Gary W. Adamson, 2009).**

Here `a n = Σ_{d ∣ n} φ(d) · C(d + n/d − 2, d − 1)` (Manyama's formula for the
entry). The guard `1 < n` is from the source; at `n = 1` the identity
`a 1 = 1` holds while `1` is not prime. -/
theorem a_eq_self_iff_prime {n : ℕ} (hn : 1 < n) : a n = n ↔ n.Prime := by
  constructor
  · intro heq
    by_contra hnp
    exact absurd heq (lt_a_of_not_prime hn hnp).ne'
  · exact a_prime

/-- Non-vacuity: both sides of the equivalence occur (`n = 7` prime with
`a 7 = 7`, `n = 6` composite with `a 6 ≠ 6`). -/
example : a 7 = 7 ∧ (7 : ℕ).Prime ∧ a 6 ≠ 6 ∧ ¬ (6 : ℕ).Prime :=
  ⟨by decide, by norm_num, by decide, by norm_num⟩

end Candidates.A156834SumPhiPrime
