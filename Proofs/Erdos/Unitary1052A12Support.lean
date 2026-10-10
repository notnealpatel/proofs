import Erdos.Unitary1052C81Support

set_option autoImplicit false

namespace Erdos1052

/-- A finite period whose residues avoid minus one excludes divisibility of a
power successor. The positive period makes the residue index nonempty. -/
theorem not_dvd_pow_successor_of_period (b r k c : ℕ) (hk : 0 < k)
    (hperiod : (b : ZMod r) ^ k = 1)
    (hres : ∀ i : Fin k, (b : ZMod r) ^ i.val + 1 ≠ 0) :
    ¬ r ∣ b ^ c + 1 := by
  intro hd
  have hz : (b : ZMod r) ^ c + 1 = 0 := by
    simpa using (ZMod.natCast_eq_zero_iff (b ^ c + 1) r).mpr hd
  rw [pow_eq_pow_mod c hperiod] at hz
  exact hres ⟨c % k, Nat.mod_lt _ hk⟩ hz

/-- None of the odd fixed primes on the a=12 canceled right side divides the
61-square successor, for any exponent parameter. -/
theorem a12_fixed_odd_primes_not_dvd_successor (c : ℕ) :
    ¬ 5 ∣ 61 ^ (2 * c) + 1 ∧ ¬ 11 ∣ 61 ^ (2 * c) + 1 ∧
      ¬ 13 ∣ 61 ^ (2 * c) + 1 ∧ ¬ 61 ∣ 61 ^ (2 * c) + 1 := by
  have h5 := not_dvd_pow_successor_of_period (61 ^ 2) 5 1 c
    (by decide) (by decide) (by decide)
  have h11 := not_dvd_pow_successor_of_period (61 ^ 2) 11 5 c
    (by decide) (by decide) (by decide)
  have h13 := not_dvd_pow_successor_of_period (61 ^ 2) 13 3 c
    (by decide) (by decide) (by decide)
  have h61 : ¬ 61 ∣ 61 ^ (2 * c) + 1 := by
    intro hd
    have hz : (61 : ZMod 61) ^ (2 * c) + 1 = 0 := by
      simpa using (ZMod.natCast_eq_zero_iff (61 ^ (2 * c) + 1) 61).mpr hd
    by_cases hc : c = 0
    · subst c
      norm_num at hz
      exact (by decide : (2 : ZMod 61) ≠ 0) hz
    · have hexp : 2 * c ≠ 0 := by omega
      have hbase : (61 : ZMod 61) = 0 := by decide
      rw [hbase, zero_pow hexp, zero_add] at hz
      exact (by decide : (1 : ZMod 61) ≠ 0) hz
  exact ⟨by simpa [pow_mul] using h5, by simpa [pow_mul] using h11,
    by simpa [pow_mul] using h13, h61⟩

/-- The natural half successor is an exact divisor of the numerator and is odd;
its division by two is not a truncation artifact. -/
theorem a12_half_successor_exact_and_odd (c : ℕ) :
    2 * ((61 ^ (2 * c) + 1) / 2) = 61 ^ (2 * c) + 1 ∧
      ¬ 2 ∣ (61 ^ (2 * c) + 1) / 2 := by
  have hodd : Odd (61 ^ (2 * c)) := (by decide : Odd (61 : ℕ)).pow
  have htwo : 2 ∣ 61 ^ (2 * c) + 1 := by
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k + 1, by omega⟩
  have heq : 2 * ((61 ^ (2 * c) + 1) / 2) = 61 ^ (2 * c) + 1 :=
    Nat.mul_div_cancel' htwo
  refine ⟨heq, ?_⟩
  intro hd
  have hfour : 4 ∣ 61 ^ (2 * c) + 1 := by
    obtain ⟨k, hk⟩ := hd
    exact ⟨k, by omega⟩
  have hz : (61 : ZMod 4) ^ (2 * c) + 1 = 0 := by
    simpa using (ZMod.natCast_eq_zero_iff (61 ^ (2 * c) + 1) 4).mpr hfour
  have hbase : (61 : ZMod 4) = 1 := by decide
  rw [hbase, one_pow] at hz
  exact (by decide : (1 : ZMod 4) + 1 ≠ 0) hz

/-- Divisibility by the full canceled right side leaves at most the four variable
prime bases as recipients for the 61 half-successor's prime support. -/
theorem a12_half_successor_primeFactors_subset_of_dvd_rhs
    (p e c q1 q2 q3 d1 d2 d3 : ℕ)
    (hp : p.Prime) (hq1 : q1.Prime) (hq2 : q2.Prime) (hq3 : q3.Prime)
    (hdiv : 61 ^ (2 * c) + 1 ∣
      2 ^ 6 * 65 * p ^ e * 11 ^ 2 * 61 ^ (2 * c) *
        q1 ^ (2 * d1) * q2 ^ (2 * d2) * q3 ^ (2 * d3)) :
    ((61 ^ (2 * c) + 1) / 2).primeFactors ⊆ {p, q1, q2, q3} := by
  intro r hrmem
  obtain ⟨hr, hrhalf, _⟩ := Nat.mem_primeFactors.mp hrmem
  have hexact := (a12_half_successor_exact_and_odd c).1
  have hhalf : (61 ^ (2 * c) + 1) / 2 ∣ 61 ^ (2 * c) + 1 :=
    ⟨2, by omega⟩
  have hrnum : r ∣ 61 ^ (2 * c) + 1 := hrhalf.trans hhalf
  have hright := hrnum.trans hdiv
  have hnot2 : r ≠ 2 := by
    intro heq
    subst r
    exact (a12_half_successor_exact_and_odd c).2 hrhalf
  have hfixed := a12_fixed_odd_primes_not_dvd_successor c
  have hnot5 : r ≠ 5 := by intro heq; subst r; exact hfixed.1 hrnum
  have hnot11 : r ≠ 11 := by intro heq; subst r; exact hfixed.2.1 hrnum
  have hnot13 : r ≠ 13 := by intro heq; subst r; exact hfixed.2.2.1 hrnum
  have hnot61 : r ≠ 61 := by intro heq; subst r; exact hfixed.2.2.2 hrnum
  have h65 : (65 : ℕ) = 5 * 13 := by decide
  rw [h65] at hright
  simp only [hr.dvd_mul] at hright
  have heq_of_pow {b k : ℕ} (hb : b.Prime) (hd : r ∣ b ^ k) : r = b :=
    (Nat.prime_dvd_prime_iff_eq hr hb).mp (hr.dvd_of_dvd_pow hd)
  rcases hright with (((((((h2 | h5 | h13) | hpdiv) | h11) | h61) | hq1div) | hq2div) | hq3div)
  · exact False.elim (hnot2 (heq_of_pow (by decide) h2))
  · exact False.elim (hnot5 ((Nat.prime_dvd_prime_iff_eq hr (by decide)).mp h5))
  · exact False.elim (hnot13 ((Nat.prime_dvd_prime_iff_eq hr (by decide)).mp h13))
  · simp [heq_of_pow hp hpdiv]
  · exact False.elim (hnot11 (heq_of_pow (by decide) h11))
  · exact False.elim (hnot61 (heq_of_pow (by decide) h61))
  · simp [heq_of_pow hq1 hq1div]
  · simp [heq_of_pow hq2 hq2div]
  · simp [heq_of_pow hq3 hq3div]

/-- In the actual a=12, five-square-slot branch, the full canceled identity
forces the 61 half-successor to have at most four distinct prime divisors.
The distinct odd-prime and congruence data are preserved from the fixed-core source. -/
theorem a12_five_slot_primeFactors_card_le_four
    (p e c q1 q2 q3 d1 d2 d3 : ℕ)
    (hp : p.Prime) (_hp13 : 13 < p) (_hp24 : p % 24 = 1)
    (_he : 0 < e) (_heodd : Odd e) (_hc : 0 < c)
    (_hd1 : 0 < d1) (_hd2 : 0 < d2) (_hd3 : 0 < d3)
    (hcomponents : ∀ q ∈ ({q1, q2, q3} : Finset ℕ),
      q.Prime ∧ Odd q ∧ q ≠ 3 ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≠ 13)
    (_hdistinct : List.Pairwise (· ≠ ·) [p, 11, 61, q1, q2, q3])
    (hid : (2 ^ 12 + 1) * (p ^ e + 1) * (11 ^ 2 + 1) *
        (61 ^ (2 * c) + 1) * (q1 ^ (2 * d1) + 1) *
        (q2 ^ (2 * d2) + 1) * (q3 ^ (2 * d3) + 1) =
      2 ^ 6 * 65 * p ^ e * 11 ^ 2 * 61 ^ (2 * c) *
        q1 ^ (2 * d1) * q2 ^ (2 * d2) * q3 ^ (2 * d3)) :
    ((61 ^ (2 * c) + 1) / 2).primeFactors.card ≤ 4 := by
  have hnum : 61 ^ (2 * c) + 1 ∣
      (2 ^ 12 + 1) * (p ^ e + 1) * (11 ^ 2 + 1) *
        (61 ^ (2 * c) + 1) * (q1 ^ (2 * d1) + 1) *
        (q2 ^ (2 * d2) + 1) * (q3 ^ (2 * d3) + 1) := by
    refine ⟨(2 ^ 12 + 1) * (p ^ e + 1) * (11 ^ 2 + 1) *
      (q1 ^ (2 * d1) + 1) * (q2 ^ (2 * d2) + 1) * (q3 ^ (2 * d3) + 1), ?_⟩
    ring
  rw [hid] at hnum
  have hq1 : q1.Prime := (hcomponents q1 (by simp)).1
  have hq2 : q2.Prime := (hcomponents q2 (by simp)).1
  have hq3 : q3.Prime := (hcomponents q3 (by simp)).1
  have hsubset := a12_half_successor_primeFactors_subset_of_dvd_rhs
    p e c q1 q2 q3 d1 d2 d3 hp hq1 hq2 hq3 hnum
  exact (Finset.card_le_card hsubset).trans Finset.card_le_four

/-- The actual a=12, five-square-slot full canceled identity excludes every
positive c divisible by 81, by its derived four-prime support bound. -/
theorem a12_five_slot_not_dvd_eighty_one
    (p e c q1 q2 q3 d1 d2 d3 : ℕ)
    (hp : p.Prime) (hp13 : 13 < p) (hp24 : p % 24 = 1)
    (he : 0 < e) (heodd : Odd e) (hc : 0 < c)
    (hd1 : 0 < d1) (hd2 : 0 < d2) (hd3 : 0 < d3)
    (hcomponents : ∀ q ∈ ({q1, q2, q3} : Finset ℕ),
      q.Prime ∧ Odd q ∧ q ≠ 3 ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≠ 13)
    (hdistinct : List.Pairwise (· ≠ ·) [p, 11, 61, q1, q2, q3])
    (hid : (2 ^ 12 + 1) * (p ^ e + 1) * (11 ^ 2 + 1) *
        (61 ^ (2 * c) + 1) * (q1 ^ (2 * d1) + 1) *
        (q2 ^ (2 * d2) + 1) * (q3 ^ (2 * d3) + 1) =
      2 ^ 6 * 65 * p ^ e * 11 ^ 2 * 61 ^ (2 * c) *
        q1 ^ (2 * d1) * q2 ^ (2 * d2) * q3 ^ (2 * d3)) :
    ¬ 81 ∣ c := by
  have hcard := a12_five_slot_primeFactors_card_le_four p e c q1 q2 q3 d1 d2 d3
    hp hp13 hp24 he heodd hc hd1 hd2 hd3 hcomponents hdistinct hid
  exact not_dvd_eighty_one_of_primeFactors_card_le_four c hc hcard

example : (0 : ℕ) < 5 ∧ ((61 ^ 2 : ℕ) : ZMod 11) ^ 5 = 1 ∧
    (∀ i : Fin 5, ((61 ^ 2 : ℕ) : ZMod 11) ^ i.val + 1 ≠ 0) := by decide

example : 2 * ((61 ^ (2 * 0) + 1) / 2) = (61 : ℕ) ^ (2 * 0) + 1 ∧
    ¬ 2 ∣ ((61 : ℕ) ^ (2 * 0) + 1) / 2 := by decide

example : Nat.Prime 1861 ∧ Nat.Prime 17 ∧ Nat.Prime 19 ∧ Nat.Prime 23 ∧
    (61 : ℕ) ^ (2 * 1) + 1 ∣
      2 ^ 6 * 65 * 1861 ^ 1 * 11 ^ 2 * 61 ^ (2 * 1) *
        17 ^ (2 * 0) * 19 ^ (2 * 0) * 23 ^ (2 * 0) := by norm_num

example : Nat.Prime 73 ∧ 13 < (73 : ℕ) ∧ (73 : ℕ) % 24 = 1 ∧
    0 < (3 : ℕ) ∧ Odd (3 : ℕ) ∧ 0 < (1 : ℕ) ∧
    (∀ q ∈ ({17, 19, 23} : Finset ℕ),
      q.Prime ∧ Odd q ∧ q ≠ 3 ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≠ 13) ∧
    List.Pairwise (· ≠ ·) ([73, 11, 61, 17, 19, 23] : List ℕ) := by decide

end Erdos1052
