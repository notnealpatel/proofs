import Erdos.InfinitaryReverseResidues
import Erdos.InfinitarySupportSaturation
import Erdos.InfinitaryCanonicalSupport

set_option autoImplicit false

namespace InfinitarySuperperfect

/-- An even whole square with canonical odd bit budget two has an actual reverse
prime divisor which does not divide its canonical infinitary sum. -/
theorem exists_prime_dvd_reverse_not_dvd_sigma_of_budget_two (n m : ℕ)
    (hn : 0 < n) (heven : 2 ∣ n) (hsquare : IsSquare n) (hmpos : 0 < m)
    (hm2 : m.factorization 2 = 2) (hreverse : sigma m = 2 * n)
    (hmod : ∀ q ∈ m.primeFactors, q ≠ 2 → q % 4 = 1)
    (hbudget : (∑ p ∈ n.primeFactors,
      if p = 2 then 0 else (binarySupport (n.factorization p)).card) = 2) :
    ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ∣ m ∧ ¬ q ∣ sigma n := by
  obtain ⟨hthree, hfive⟩ :=
    three_and_five_dvd_of_reverse n m hn heven hsquare hmpos hm2 hreverse hmod
  obtain ⟨j, k, hj, hk, _he3, _he5, hshape⟩ :=
    mixed_shape_of_budget_two n hn heven hsquare hthree hfive hbudget
  have hsupport :=
    support_two_three_five_of_budget_two n hn heven hsquare hthree hfive hbudget
  obtain ⟨q, hq, hq2, hdiv, hq4, hq3, hq5, hq16⟩ :=
    exists_reverse_prime_residues n m j k hn hmpos hm2 hreverse hmod hj hk hshape
  have hevenvals : ∀ p ∈ n.primeFactors, Even (n.factorization p) := by
    intro p _hp
    exact (isSquare_iff_even_factorization n hn).mp hsquare p
  exact ⟨q, hq, hq2, hdiv,
    not_dvd_sigma_of_support_two_three_five n q hsupport hevenvals hq hq4 hq3 hq5 hq16⟩

/-- In an infinitary superperfect cycle starting at a positive even whole square,
the second member cannot have ordinary two-adic valuation two. -/
theorem factorization_sigma_two_ne_two_of_even_square (n m : ℕ) (hn : 0 < n)
    (heven : 2 ∣ n) (hsquare : IsSquare n) (hm : m = sigma n)
    (hcycle : sigma m = 2 * n) : m.factorization 2 ≠ 2 := by
  intro hf2
  have hmpos : 0 < m := by rw [hm]; exact sigma_pos n
  have hevenvals : ∀ p ∈ n.primeFactors, Even (n.factorization p) := by
    intro p _hp
    exact (isSquare_iff_even_factorization n hn).mp hsquare p
  have hmod : ∀ q ∈ m.primeFactors, q ≠ 2 → q % 4 = 1 := by
    intro q hmem hq2
    obtain ⟨hq, hdiv, _hm0⟩ := Nat.mem_primeFactors.mp hmem
    rw [hm] at hdiv
    exact prime_mod_four_of_dvd_sigma_of_even n q hevenvals hq hq2 hdiv
  have hbudget : (∑ p ∈ n.primeFactors,
      if p = 2 then 0 else (binarySupport (n.factorization p)).card) = 2 := by
    rw [← factorization_sigma_two_of_isSquare n hn hsquare, ← hm]
    exact hf2
  obtain ⟨q, _hq, _hq2, hdiv, hnotdiv⟩ :=
    exists_prime_dvd_reverse_not_dvd_sigma_of_budget_two n m hn heven hsquare
      hmpos hf2 hcycle hmod hbudget
  rw [hm] at hdiv
  exact hnotdiv hdiv

/-- Independent factor support and ordinary valuations of the square input. -/
private theorem model_n_data : (8100 : ℕ).primeFactors = {2, 3, 5} ∧
    (8100 : ℕ).factorization =
      Finsupp.single 2 2 + Finsupp.single 3 4 + Finsupp.single 5 2 := by
  have hrepr : (8100 : ℕ) = 2 ^ 2 * 3 ^ 4 * 5 ^ 2 := by decide
  constructor
  · rw [hrepr, Nat.primeFactors_mul (by decide) (by decide),
      Nat.primeFactors_mul (by decide) (by decide),
      Nat.primeFactors_prime_pow (by decide) (by decide : Nat.Prime 2),
      Nat.primeFactors_prime_pow (by decide) (by decide : Nat.Prime 3),
      Nat.primeFactors_prime_pow (by decide) (by decide : Nat.Prime 5)]
    decide
  · rw [hrepr, Nat.factorization_mul (by decide) (by decide),
      Nat.factorization_mul (by decide) (by decide),
      Nat.Prime.factorization_pow (by decide : Nat.Prime 2),
      Nat.Prime.factorization_pow (by decide : Nat.Prime 3),
      Nat.Prime.factorization_pow (by decide : Nat.Prime 5)]

/-- Independent support and ordinary valuations of the reverse member. -/
private theorem model_m_data : (9860 : ℕ).primeFactors = {2, 5, 17, 29} ∧
    (9860 : ℕ).factorization =
      Finsupp.single 2 2 + Finsupp.single 5 1 +
        Finsupp.single 17 1 + Finsupp.single 29 1 := by
  have hrepr : (9860 : ℕ) = 2 ^ 2 * 5 * 17 * 29 := by decide
  constructor
  · rw [hrepr, Nat.primeFactors_mul (by decide) (by decide),
      Nat.primeFactors_mul (by decide) (by decide),
      Nat.primeFactors_mul (by decide) (by decide),
      Nat.primeFactors_prime_pow (by decide) (by decide : Nat.Prime 2),
      Nat.Prime.primeFactors (by decide : Nat.Prime 5),
      Nat.Prime.primeFactors (by decide : Nat.Prime 17),
      Nat.Prime.primeFactors (by decide : Nat.Prime 29)]
    decide
  · rw [hrepr, Nat.factorization_mul (by decide) (by decide),
      Nat.factorization_mul (by decide) (by decide),
      Nat.factorization_mul (by decide) (by decide),
      Nat.Prime.factorization_pow (by decide : Nat.Prime 2),
      Nat.Prime.factorization (by decide : Nat.Prime 5),
      Nat.Prime.factorization (by decide : Nat.Prime 17),
      Nat.Prime.factorization (by decide : Nat.Prime 29)]

/-- The two canonical sums are computed independently of both exports. -/
private theorem model_sums : sigma 8100 = 10660 ∧ sigma 9860 = 16200 := by
  constructor
  · rw [sigma, model_n_data.1]
    norm_num [model_n_data.2]
    decide
  · rw [sigma, model_m_data.1]
    norm_num [model_m_data.2]
    decide

/-- All strict hypotheses hold jointly at a positive even whole square, without
using the strict theorem or assuming a forward equation. -/
private theorem model_strict_premises :
    0 < (8100 : ℕ) ∧ 2 ∣ (8100 : ℕ) ∧ IsSquare (8100 : ℕ) ∧
    0 < (9860 : ℕ) ∧ (9860 : ℕ).factorization 2 = 2 ∧
    sigma 9860 = 2 * 8100 ∧
    (∀ q ∈ (9860 : ℕ).primeFactors, q ≠ 2 → q % 4 = 1) ∧
    (∑ p ∈ (8100 : ℕ).primeFactors,
      if p = 2 then 0 else (binarySupport ((8100 : ℕ).factorization p)).card) = 2 := by
  have hm2 : (9860 : ℕ).factorization 2 = 2 := by simp [model_m_data.2]
  have hreverse : sigma 9860 = 2 * 8100 := by rw [model_sums.2]
  have hmod : ∀ q ∈ (9860 : ℕ).primeFactors, q ≠ 2 → q % 4 = 1 := by
    rw [model_m_data.1]
    intro q hmem hq2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h
    · exact (hq2 h).elim
    · subst q; decide
    · subst q; decide
    · subst q; decide
  have hbudget : (∑ p ∈ (8100 : ℕ).primeFactors,
      if p = 2 then 0 else (binarySupport ((8100 : ℕ).factorization p)).card) = 2 := by
    rw [model_n_data.1]
    norm_num [model_n_data.2, binarySupport]
    decide
  exact ⟨by decide, by decide, ⟨90, by decide⟩, by decide,
    hm2, hreverse, hmod, hbudget⟩

example : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ∣ 9860 ∧ ¬ q ∣ sigma 8100 := by
  obtain ⟨hn, heven, hsquare, hmpos, hm2, hreverse, hmod, hbudget⟩ := model_strict_premises
  exact exists_prime_dvd_reverse_not_dvd_sigma_of_budget_two 8100 9860 hn heven
    hsquare hmpos hm2 hreverse hmod hbudget

example : Nat.Prime 29 ∧ (29 : ℕ) ≠ 2 ∧ 29 ∣ 9860 ∧ ¬29 ∣ sigma 8100 := by
  rw [model_sums.1]
  decide

example : sigma 8100 ≠ 9860 := by rw [model_sums.1]; decide

example : ¬ IsSquare (2 : ℕ) := by
  rintro ⟨a, ha⟩
  have hbound : a ≤ 2 := Nat.le_mul_self a |>.trans (le_of_eq ha.symm)
  interval_cases a <;> norm_num at ha

example : IsSquare (9 : ℕ) ∧ ¬2 ∣ (9 : ℕ) := ⟨⟨3, rfl⟩, by decide⟩

end InfinitarySuperperfect
