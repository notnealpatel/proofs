import Erdos.InfinitarySuperperfect

set_option autoImplicit false

namespace InfinitarySuperperfect

/-- Every actual prime of a positive integer has an occupied valuation bit. -/
private theorem binarySupport_card_pos_of_mem_primeFactors (n p : ℕ) (hn : 0 < n)
    (hp : p ∈ n.primeFactors) : 0 < (binarySupport (n.factorization p)).card := by
  have hpdata := (Nat.mem_primeFactors_of_ne_zero (ne_of_gt hn)).mp hp
  have hval := hpdata.1.factorization_pos_of_dvd (ne_of_gt hn) hpdata.2
  by_contra h
  have hempty : binarySupport (n.factorization p) = ∅ :=
    Finset.card_eq_zero.mp (by omega)
  have hsum := sum_binarySupport (n.factorization p)
  simp only [hempty, Finset.sum_empty] at hsum
  omega

/-- The two odd primes consume the whole two-bit budget: both have one bit,
    and no further actual odd prime occurs. -/
private theorem odd_support_saturation (n : ℕ) (hn : 0 < n)
    (hthree : 3 ∣ n) (hfive : 5 ∣ n)
    (hbudget : (∑ p ∈ n.primeFactors,
      if p = 2 then 0 else (binarySupport (n.factorization p)).card) = 2) :
    (binarySupport (n.factorization 3)).card = 1 ∧
    (binarySupport (n.factorization 5)).card = 1 ∧
    ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3 ∨ p = 5 := by
  let f : ℕ → ℕ := fun p => if p = 2 then 0 else (binarySupport (n.factorization p)).card
  have hsum : ∑ p ∈ n.primeFactors, f p = 2 := hbudget
  have h3 : 3 ∈ n.primeFactors :=
    (Nat.mem_primeFactors_of_ne_zero (ne_of_gt hn)).mpr ⟨by decide, hthree⟩
  have h5 : 5 ∈ n.primeFactors :=
    (Nat.mem_primeFactors_of_ne_zero (ne_of_gt hn)).mpr ⟨by decide, hfive⟩
  have h3pos : 1 ≤ f 3 := by
    simpa [f] using binarySupport_card_pos_of_mem_primeFactors n 3 hn h3
  have h5pos : 1 ≤ f 5 := by
    simpa [f] using binarySupport_card_pos_of_mem_primeFactors n 5 hn h5
  have h5erase : 5 ∈ n.primeFactors.erase 3 := by simp [h5]
  have hsplit3 := Finset.sum_erase_add n.primeFactors f h3
  have hsplit5 := Finset.sum_erase_add (n.primeFactors.erase 3) f h5erase
  have hcards : f 3 = 1 ∧ f 5 = 1 := by omega
  have hrest : ∑ p ∈ (n.primeFactors.erase 3).erase 5, f p = 0 := by omega
  refine ⟨by simpa [f] using hcards.1, by simpa [f] using hcards.2, ?_⟩
  intro p hp
  by_cases hp2 : p = 2
  · exact Or.inl hp2
  by_cases hp3 : p = 3
  · exact Or.inr (Or.inl hp3)
  by_cases hp5 : p = 5
  · exact Or.inr (Or.inr hp5)
  have hprest : p ∈ (n.primeFactors.erase 3).erase 5 := by simp [hp, hp3, hp5]
  have hle : f p ≤ 0 := by
    calc
      f p ≤ ∑ q ∈ (n.primeFactors.erase 3).erase 5, f q :=
        Finset.single_le_sum (fun q _ => Nat.zero_le (f q)) hprest
      _ = 0 := hrest
  have hpos : 0 < f p := by
    simpa [f, hp2] using binarySupport_card_pos_of_mem_primeFactors n p hn hp
  omega

/-- A positive whole square divisible by two, three and five with canonical
    odd-bit budget two has actual prime support exactly `{2,3,5}`. -/
theorem primeFactors_eq_two_three_five_of_budget_two (n : ℕ) (hn : 0 < n)
    (htwo : 2 ∣ n) (_hsquare : IsSquare n) (hthree : 3 ∣ n) (hfive : 5 ∣ n)
    (hbudget : (∑ p ∈ n.primeFactors,
      if p = 2 then 0 else (binarySupport (n.factorization p)).card) = 2) :
    n.primeFactors = {2, 3, 5} := by
  have hsupport := (odd_support_saturation n hn hthree hfive hbudget).2.2
  apply Finset.ext
  intro p
  constructor
  · intro hp
    rcases hsupport p hp with h | h | h <;> simp [h]
  · intro hp
    have hcases : p = 2 ∨ p = 3 ∨ p = 5 := by simpa using hp
    rcases hcases with rfl | rfl | rfl
    · exact (Nat.mem_primeFactors_of_ne_zero (ne_of_gt hn)).mpr ⟨by decide, htwo⟩
    · exact (Nat.mem_primeFactors_of_ne_zero (ne_of_gt hn)).mpr ⟨by decide, hthree⟩
    · exact (Nat.mem_primeFactors_of_ne_zero (ne_of_gt hn)).mpr ⟨by decide, hfive⟩

/-- The support-saturation hypotheses supply the inclusion required by the
    canonical support consumer. -/
theorem support_two_three_five_of_budget_two (n : ℕ) (hn : 0 < n)
    (htwo : 2 ∣ n) (hsquare : IsSquare n) (hthree : 3 ∣ n) (hfive : 5 ∣ n)
    (hbudget : (∑ p ∈ n.primeFactors,
      if p = 2 then 0 else (binarySupport (n.factorization p)).card) = 2) :
    ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3 ∨ p = 5 := by
  rw [primeFactors_eq_two_three_five_of_budget_two n hn htwo hsquare hthree hfive hbudget]
  simp

/-- Whole-square evenness turns a singleton valuation bit into a higher bit. -/
private theorem exists_higher_bit_of_card_eq_one (n p : ℕ) (hn : 0 < n)
    (hsquare : IsSquare n) (hcard : (binarySupport (n.factorization p)).card = 1) :
    ∃ j : ℕ, 1 ≤ j ∧ n.factorization p = 2 ^ j := by
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard
  have hjmem : j ∈ binarySupport (n.factorization p) := by simp [hj]
  have hjpos := one_le_of_mem_binarySupport_of_even (n.factorization p) j
    ((isSquare_iff_even_factorization n hn).mp hsquare p) hjmem
  refine ⟨j, hjpos, ?_⟩
  have hbits := sum_binarySupport (n.factorization p)
  simpa [hj] using hbits.symm

/-- Under the support-saturation hypotheses the two odd valuations are single
    higher powers of two, and positive factorization reconstructs the mixed shape. -/
theorem mixed_shape_of_budget_two (n : ℕ) (hn : 0 < n)
    (htwo : 2 ∣ n) (hsquare : IsSquare n) (hthree : 3 ∣ n) (hfive : 5 ∣ n)
    (hbudget : (∑ p ∈ n.primeFactors,
      if p = 2 then 0 else (binarySupport (n.factorization p)).card) = 2) :
    ∃ j k : ℕ, 1 ≤ j ∧ 1 ≤ k ∧ n.factorization 3 = 2 ^ j ∧
      n.factorization 5 = 2 ^ k ∧
      n = 2 ^ (n.factorization 2) * 3 ^ (2 ^ j) * 5 ^ (2 ^ k) := by
  have hsat := odd_support_saturation n hn hthree hfive hbudget
  obtain ⟨j, hj, he3⟩ := exists_higher_bit_of_card_eq_one n 3 hn hsquare hsat.1
  obtain ⟨k, hk, he5⟩ := exists_higher_bit_of_card_eq_one n 5 hn hsquare hsat.2.1
  refine ⟨j, k, hj, hk, he3, he5, ?_⟩
  have hprod := Nat.prod_primeFactors_pow_factorization (ne_of_gt hn)
  rw [primeFactors_eq_two_three_five_of_budget_two n hn htwo hsquare hthree hfive hbudget] at hprod
  simpa [he3, he5, mul_assoc] using hprod

/-- The concrete integer `900 = 2² * 3² * 5²` jointly realizes all six
    support-saturation hypotheses, including the exact canonical budget. -/
private theorem support_saturation_hypotheses_900 :
    0 < (900 : ℕ) ∧ 2 ∣ (900 : ℕ) ∧ IsSquare (900 : ℕ) ∧
      3 ∣ (900 : ℕ) ∧ 5 ∣ (900 : ℕ) ∧
      (∑ p ∈ (900 : ℕ).primeFactors,
        if p = 2 then 0 else (binarySupport ((900 : ℕ).factorization p)).card) = 2 := by
  have hdecomp : (900 : ℕ) = 2 ^ 2 * 3 ^ 2 * 5 ^ 2 := by norm_num
  have hsupport : (900 : ℕ).primeFactors = {2, 3, 5} := by
    rw [hdecomp, Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_prime_pow (by decide : (2 : ℕ) ≠ 0) (by decide : Nat.Prime 2),
      Nat.primeFactors_prime_pow (by decide : (2 : ℕ) ≠ 0) (by decide : Nat.Prime 3),
      Nat.primeFactors_prime_pow (by decide : (2 : ℕ) ≠ 0) (by decide : Nat.Prime 5)]
    decide
  have hval : (900 : ℕ).factorization =
      Finsupp.single 2 2 + Finsupp.single 3 2 + Finsupp.single 5 2 := by
    rw [hdecomp, Nat.factorization_mul (by norm_num) (by norm_num),
      Nat.factorization_mul (by norm_num) (by norm_num),
      Nat.Prime.factorization_pow (by decide : Nat.Prime 2),
      Nat.Prime.factorization_pow (by decide : Nat.Prime 3),
      Nat.Prime.factorization_pow (by decide : Nat.Prime 5)]
  refine ⟨by decide, by decide, ⟨30, by norm_num⟩, by decide, by decide, ?_⟩
  rw [hsupport]
  norm_num [hval, binarySupport]
  decide

example : (900 : ℕ).primeFactors = {2, 3, 5} := by
  obtain ⟨hn, htwo, hsquare, hthree, hfive, hbudget⟩ := support_saturation_hypotheses_900
  exact primeFactors_eq_two_three_five_of_budget_two 900 hn htwo hsquare hthree hfive hbudget

example : ∀ p ∈ (900 : ℕ).primeFactors, p = 2 ∨ p = 3 ∨ p = 5 := by
  obtain ⟨hn, htwo, hsquare, hthree, hfive, hbudget⟩ := support_saturation_hypotheses_900
  exact support_two_three_five_of_budget_two 900 hn htwo hsquare hthree hfive hbudget

example : ∃ j k : ℕ, 1 ≤ j ∧ 1 ≤ k ∧ (900 : ℕ).factorization 3 = 2 ^ j ∧
    (900 : ℕ).factorization 5 = 2 ^ k ∧
    900 = 2 ^ ((900 : ℕ).factorization 2) * 3 ^ (2 ^ j) * 5 ^ (2 ^ k) := by
  obtain ⟨hn, htwo, hsquare, hthree, hfive, hbudget⟩ := support_saturation_hypotheses_900
  exact mixed_shape_of_budget_two 900 hn htwo hsquare hthree hfive hbudget

end InfinitarySuperperfect
