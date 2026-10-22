/-
# A137328 — "every prime appears" fails at the prime `2`

Ctibor O. Zizka's conjecture in OEIS A137328 (2008). Here `primorial(k)`
(A002110) is the product of the first `k` primes, not the primes at most `k`.

The prime `2` never occurs: for `n ≥ 1`, the chosen primorial index is at
least one, hence the chosen primorial is even. If `a(n)=2`, the prime
`prime(n)` would be even and at least `4`. The variant that every odd prime
occurs is not formalized here.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A137328Refutation

noncomputable section

/-- `primorialFirst k` is A002110: the product of the first `k` primes
(`primorialFirst 0 = 1`).  This is *not* Mathlib's `primorial n`, which is the
product of the primes `≤ n`. -/
def primorialFirst (k : ℕ) : ℕ := ∏ i ∈ Finset.range k, Nat.nth Nat.Prime i

/-- `primeAt n` is `prime(n)`, the `n`-th prime, `1`-indexed as in the OEIS
(`primeAt 1 = 2`). -/
def primeAt (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- `primorialIndex p` is the greatest `k` with `primorialFirst k ≤ p`.  The
search bound `p` loses nothing, since `k < primorialFirst k`
(`lt_primorialFirst`). -/
def primorialIndex (p : ℕ) : ℕ := Nat.findGreatest (fun k => primorialFirst k ≤ p) p

/-- A137328: `a(n) = prime(n) - primorial(k)` with `k` the greatest index such
that `primorial(k) ≤ prime(n)`.  The subtraction is taken in `ℤ`, so no
truncation is involved. -/
def a (n : ℕ) : ℤ := (primeAt n : ℤ) - (primorialFirst (primorialIndex (primeAt n)) : ℤ)

/-! ## Basic facts about `primorialFirst` -/

/-- The recursion `primorial(k+1) = primorial(k) * prime(k+1)`. -/
theorem primorialFirst_succ (k : ℕ) :
    primorialFirst (k + 1) = primorialFirst k * Nat.nth Nat.Prime k :=
  Finset.prod_range_succ _ _

/-- The primorial sequence is monotone. -/
theorem primorialFirst_mono : Monotone primorialFirst := by
  refine monotone_nat_of_le_succ fun k => ?_
  rw [primorialFirst_succ]
  exact Nat.le_mul_of_pos_right _ (Nat.prime_nth_prime k).pos

/-- `k < primorial(k)`, so `primorialIndex p ≤ p` loses no candidate. -/
theorem lt_primorialFirst (k : ℕ) : k < primorialFirst k := by
  induction k with
  | zero => simp [primorialFirst]
  | succ k ih =>
    rw [primorialFirst_succ]
    have h2 : 2 ≤ Nat.nth Nat.Prime k := (Nat.prime_nth_prime k).two_le
    nlinarith

/-- For `k ≥ 1`, `primorial(k)` is even (it contains the factor `prime(1) = 2`). -/
theorem two_dvd_primorialFirst {k : ℕ} (hk : 1 ≤ k) : 2 ∣ primorialFirst k := by
  have h0 : 0 ∈ Finset.range k := Finset.mem_range.mpr hk
  have hdvd := Finset.dvd_prod_of_mem (fun i => Nat.nth Nat.Prime i) h0
  rwa [Nat.nth_prime_zero_eq_two] at hdvd

/-- `primorial(k)` is positive. -/
theorem primorialFirst_pos (k : ℕ) : 0 < primorialFirst k :=
  Nat.zero_le k |>.trans_lt (lt_primorialFirst k)

/-- `primorial(1) = 2`. -/
theorem primorialFirst_one : primorialFirst 1 = 2 := by
  simp [primorialFirst, Nat.nth_prime_zero_eq_two]

/-! ## Facts about `primorialIndex` -/

/-- Characterization: if `primorial(k) ≤ p < primorial(k+1)` then the index is `k`. -/
theorem primorialIndex_eq {p k : ℕ} (hk : primorialFirst k ≤ p)
    (hk' : p < primorialFirst (k + 1)) : primorialIndex p = k := by
  rw [primorialIndex, Nat.findGreatest_eq_iff]
  refine ⟨(lt_primorialFirst k).le.trans hk, fun _ => hk, fun m hkm _ hm => ?_⟩
  have hmono : primorialFirst (k + 1) ≤ primorialFirst m := primorialFirst_mono hkm
  omega

/-- For `p ≥ 2` the chosen index is at least `1`. -/
theorem one_le_primorialIndex {p : ℕ} (hp : 2 ≤ p) : 1 ≤ primorialIndex p :=
  Nat.le_findGreatest (by omega) (by rw [primorialFirst_one]; exact hp)

/-- For `p ≥ 2` the chosen primorial is at most `p`. -/
theorem primorialFirst_primorialIndex_le {p : ℕ} (hp : 2 ≤ p) :
    primorialFirst (primorialIndex p) ≤ p :=
  Nat.findGreatest_spec (P := fun k => primorialFirst k ≤ p) (m := 1) (by omega)
    (by rw [primorialFirst_one]; exact hp)

/-! ## Examples against the DATA line -/

/-- Small values of `prime(n)` used by the examples. -/
theorem nth_prime_ten : Nat.nth Nat.Prime 10 = 31 := by
  have hc : Nat.count Nat.Prime 31 = 10 := by
    rw [Nat.count_eq_card_filter_range]
    decide
  rw [← hc]
  exact Nat.nth_count (p := Nat.Prime) (by norm_num)

/-- `primorial(2) = 6`, `primorial(3) = 30`, `primorial(4) = 210`. -/
theorem primorialFirst_two_three_four :
    primorialFirst 2 = 6 ∧ primorialFirst 3 = 30 ∧ primorialFirst 4 = 210 := by
  simp [primorialFirst, Finset.prod_range_succ, Nat.nth_prime_zero_eq_two,
    Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five, Nat.nth_prime_three_eq_seven]

/-- Examples: `a(1), …, a(5) = 0, 1, 3, 1, 5` and `a(11) = 31 - 30 = 1`. -/
example : a 1 = 0 ∧ a 2 = 1 ∧ a 3 = 3 ∧ a 4 = 1 ∧ a 5 = 5 ∧ a 11 = 1 := by
  obtain ⟨h2, h3, h4⟩ := primorialFirst_two_three_four
  have hp1 : primeAt 1 = 2 := Nat.nth_prime_zero_eq_two
  have hp2 : primeAt 2 = 3 := Nat.nth_prime_one_eq_three
  have hp3 : primeAt 3 = 5 := Nat.nth_prime_two_eq_five
  have hp4 : primeAt 4 = 7 := Nat.nth_prime_three_eq_seven
  have hp5 : primeAt 5 = 11 := Nat.nth_prime_four_eq_eleven
  have hp11 : primeAt 11 = 31 := nth_prime_ten
  have hi2 : primorialIndex 2 = 1 :=
    primorialIndex_eq (k := 1) (by rw [primorialFirst_one]) (by norm_num [h2])
  have hi3 : primorialIndex 3 = 1 :=
    primorialIndex_eq (k := 1) (by rw [primorialFirst_one]; omega) (by norm_num [h2])
  have hi5 : primorialIndex 5 = 1 :=
    primorialIndex_eq (k := 1) (by rw [primorialFirst_one]; omega) (by norm_num [h2])
  have hi7 : primorialIndex 7 = 2 := primorialIndex_eq (k := 2) (by omega) (by norm_num [h3])
  have hi11 : primorialIndex 11 = 2 := primorialIndex_eq (k := 2) (by omega) (by norm_num [h3])
  have hi31 : primorialIndex 31 = 3 := primorialIndex_eq (k := 3) (by omega) (by norm_num [h4])
  simp only [a, hp1, hp2, hp3, hp4, hp5, hp11, hi2, hi3, hi5, hi7, hi11, hi31,
    primorialFirst_one, h2, h3]
  norm_num

/-! ## The conjecture and its refutation -/

/-- Zizka's conjecture (OEIS A137328, 2008): every prime occurs as `a(n)`
for some `n ≥ 1`, the entry's offset. -/
def Conjecture : Prop := ∀ q : ℕ, q.Prime → ∃ n : ℕ, 1 ≤ n ∧ a n = q

/-- No term of A137328 equals `2`: `primorial(k)` is even for the chosen
`k ≥ 1`, so `prime(n) = primorial(k) + 2` would be an even number `≥ 4`. -/
theorem a_ne_two (n : ℕ) : a n ≠ 2 := by
  intro h
  set p := primeAt n with hpdef
  have hprime : p.Prime := Nat.prime_nth_prime (n - 1)
  have hp2 : 2 ≤ p := hprime.two_le
  have hle : primorialFirst (primorialIndex p) ≤ p := primorialFirst_primorialIndex_le hp2
  have heven : 2 ∣ primorialFirst (primorialIndex p) :=
    two_dvd_primorialFirst (one_le_primorialIndex hp2)
  have hpos : 0 < primorialFirst (primorialIndex p) := primorialFirst_pos _
  have ha : (p : ℤ) - (primorialFirst (primorialIndex p) : ℤ) = 2 := h
  have hsum : p = primorialFirst (primorialIndex p) + 2 := by omega
  have hpeven : 2 ∣ p := hsum ▸ dvd_add heven (dvd_refl 2)
  have hpeq : p = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hprime).mp hpeven).symm
  omega

/-- **Refutation of A137328's conjecture.**  Counterexample: the prime `q = 2`
never occurs (`a_ne_two`).  The variant "every odd prime appears" is not proved here. -/
theorem conjecture_false : ¬ Conjecture := by
  intro hconj
  obtain ⟨n, -, hn⟩ := hconj 2 Nat.prime_two
  exact a_ne_two n (by exact_mod_cast hn)

end

end Candidates.A137328Refutation
