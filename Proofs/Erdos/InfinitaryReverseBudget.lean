import Erdos.InfinitarySuperperfectSquareInput
import Mathlib.Algebra.BigOperators.ModEq

set_option autoImplicit false

namespace InfinitarySuperperfect

/-- Actual odd prime support for the reverse equation. -/
def reverseOddSupport (m : ℕ) : Finset ℕ :=
  m.primeFactors.filter (fun q => q ≠ 2)

/-- Tagged occupied positions at actual odd primes; equal factor values retain their tags. -/
def reverseTags (m : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (reverseOddSupport m).sigma (fun q => binarySupport (m.factorization q))

/-- Number of tagged odd-prime successor occurrences in the reverse product. -/
def reverseCount (m : ℕ) : ℕ := (reverseTags m).card

/-- A successor divided by two; exactness and positivity are proved under the mod-four guard. -/
def normalizedSlot (q h : ℕ) : ℕ := (1 + q ^ (2 ^ h)) / 2

/-- Product of normalized successors over tagged occurrences, not distinct numerical values. -/
def reverseProduct (m : ℕ) : ℕ :=
  ∏ i ∈ reverseTags m, normalizedSlot i.1 i.2

example : reverseOddSupport 1 = ∅ := by norm_num [reverseOddSupport]
example : reverseTags 1 = ∅ := by norm_num [reverseTags, reverseOddSupport]
example : reverseCount 1 = 0 := by norm_num [reverseCount, reverseTags, reverseOddSupport]
example : normalizedSlot 5 0 = 3 := by decide
example : reverseProduct 1 = 1 := by norm_num [reverseProduct, reverseTags, reverseOddSupport]

/-- Every successor at a base one modulo four is two modulo four, including height zero. -/
theorem raw_slot_mod_four (q h : ℕ) (hq : q % 4 = 1) :
    (1 + q ^ (2 ^ h)) % 4 = 2 := by
  simp [Nat.add_mod, Nat.pow_mod, hq]

/-- Exact division, positivity, and oddness of the normalized successor. -/
theorem normalizedSlot_spec (q h : ℕ) (hq : q % 4 = 1) :
    1 + q ^ (2 ^ h) = 2 * normalizedSlot q h ∧
      0 < normalizedSlot q h ∧ Odd (normalizedSlot q h) := by
  have hmod := raw_slot_mod_four q h hq
  have hdiv : 2 ∣ 1 + q ^ (2 ^ h) := by omega
  have heq : 1 + q ^ (2 ^ h) = 2 * normalizedSlot q h := by
    unfold normalizedSlot
    rw [mul_comm, Nat.div_mul_cancel hdiv]
  have hpos : 0 < normalizedSlot q h := by
    have hraw : 0 < 1 + q ^ (2 ^ h) := by positivity
    omega
  have hodd : normalizedSlot q h % 2 = 1 := by
    have hmulmod : (2 * normalizedSlot q h) % 4 = 2 := by rw [← heq]; exact hmod
    omega
  exact ⟨heq, hpos, Nat.odd_iff.mpr hodd⟩

example : 1 + 5 ^ (2 ^ 0) = 2 * normalizedSlot 5 0 ∧
    0 < normalizedSlot 5 0 ∧ Odd (normalizedSlot 5 0) :=
  normalizedSlot_spec 5 0 (by decide)

/-- Each guarded raw occurrence has exact two-adic valuation one. -/
theorem factorization_raw_slot_two (q h : ℕ) (hq : q % 4 = 1) :
    (1 + q ^ (2 ^ h)).factorization 2 = 1 := by
  have hmod := raw_slot_mod_four q h hq
  have hne : 1 + q ^ (2 ^ h) ≠ 0 := by positivity
  have hdiv : 2 ∣ 1 + q ^ (2 ^ h) := by omega
  have hlo : 1 ≤ (1 + q ^ (2 ^ h)).factorization 2 := by
    apply (Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 2) hne).mp
    simpa using hdiv
  have hhi : ¬ 2 ≤ (1 + q ^ (2 ^ h)).factorization 2 := by
    intro hh
    have hd := (Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 2) hne).mpr hh
    have hz : (1 + q ^ (2 ^ h)) % 4 = 0 := Nat.mod_eq_zero_of_dvd hd
    omega
  omega

/-- A tag carries actual prime membership, exclusion of two, and an occupied bit. -/
theorem mem_reverseTags (m : ℕ) (i : Σ _ : ℕ, ℕ) :
    i ∈ reverseTags m ↔ i.1 ∈ m.primeFactors ∧ i.1 ≠ 2 ∧
      i.2 ∈ binarySupport (m.factorization i.1) := by
  simp [reverseTags, reverseOddSupport, and_assoc]

/-- Valuation two at two ensures that two is an actual supported prime. -/
theorem two_mem_primeFactors_of_factorization_eq_two (m : ℕ) (hm : 0 < m)
    (hm2 : m.factorization 2 = 2) : 2 ∈ m.primeFactors := by
  apply (Nat.mem_primeFactors_of_ne_zero (ne_of_gt hm)).mpr
  refine ⟨by decide, ?_⟩
  change 2 ^ 1 ∣ m
  apply (Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 2) (ne_of_gt hm)).mpr
  simp [hm2]

/-- Splitting at the actual prime two and flattening gives the raw tagged reverse product. -/
theorem sigma_eq_five_mul_raw_product (m : ℕ) (hm : 0 < m)
    (hm2 : m.factorization 2 = 2) :
    sigma m = 5 * ∏ i ∈ reverseTags m, (1 + i.1 ^ (2 ^ i.2)) := by
  have htwo := two_mem_primeFactors_of_factorization_eq_two m hm hm2
  have hsupport : reverseOddSupport m = m.primeFactors.erase 2 := by
    ext q
    simp [reverseOddSupport, and_comm]
  have hlocal : localSigma 2 (m.factorization 2) = 5 := by rw [hm2]; decide
  rw [reverseTags, Finset.prod_sigma]
  change sigma m = 5 * ∏ q ∈ reverseOddSupport m, localSigma q (m.factorization q)
  rw [hsupport, ← hlocal]
  exact (Finset.mul_prod_erase m.primeFactors (fun q => localSigma q (m.factorization q)) htwo).symm

/-- All normalized tagged factors form a positive odd product under actual mod-four support. -/
theorem reverseProduct_pos_odd (m : ℕ)
    (hmod : ∀ q ∈ m.primeFactors, q ≠ 2 → q % 4 = 1) :
    0 < reverseProduct m ∧ Odd (reverseProduct m) := by
  have hspec : ∀ i ∈ reverseTags m, 0 < normalizedSlot i.1 i.2 ∧
      Odd (normalizedSlot i.1 i.2) := by
    intro i hi
    obtain ⟨hp, hp2, hb⟩ := (mem_reverseTags m i).mp hi
    exact (normalizedSlot_spec i.1 i.2 (hmod i.1 hp hp2)).2
  constructor
  · exact Finset.prod_pos (fun i hi => (hspec i hi).1)
  · unfold reverseProduct
    apply Nat.odd_iff.mpr
    have hh : (∏ i ∈ reverseTags m, normalizedSlot i.1 i.2) ≡
        (∏ _i ∈ reverseTags m, 1) [MOD 2] := by
      apply Nat.ModEq.prod
      intro i hi
      exact Nat.odd_iff.mp (hspec i hi).2
    simpa [Nat.ModEq] using hh

/-- Exact reverse factorization with all tagged multiplicities and positive odd cofactor. -/
theorem sigma_eq_five_mul_two_pow_reverseCount (m : ℕ) (hm : 0 < m)
    (hm2 : m.factorization 2 = 2)
    (hmod : ∀ q ∈ m.primeFactors, q ≠ 2 → q % 4 = 1) :
    sigma m = 5 * 2 ^ reverseCount m * reverseProduct m := by
  rw [sigma_eq_five_mul_raw_product m hm hm2]
  have heq : (∏ i ∈ reverseTags m, (1 + i.1 ^ (2 ^ i.2))) =
      ∏ i ∈ reverseTags m, (2 * normalizedSlot i.1 i.2) := by
    apply Finset.prod_congr rfl
    intro i hi
    obtain ⟨hp, hp2, hb⟩ := (mem_reverseTags m i).mp hi
    exact (normalizedSlot_spec i.1 i.2 (hmod i.1 hp hp2)).1
  rw [heq, Finset.prod_mul_distrib, Finset.prod_const]
  simp only [reverseCount, reverseProduct, mul_assoc]

/-- The reverse two-adic budget counts every tagged raw occurrence once. -/
theorem factorization_sigma_two_eq_reverseCount (m : ℕ) (hm : 0 < m)
    (hm2 : m.factorization 2 = 2)
    (hmod : ∀ q ∈ m.primeFactors, q ≠ 2 → q % 4 = 1) :
    (sigma m).factorization 2 = reverseCount m := by
  rw [sigma_eq_five_mul_raw_product m hm hm2,
    Nat.factorization_mul (by decide : (5 : ℕ) ≠ 0)
      (ne_of_gt (Finset.prod_pos (fun i hi => by positivity)))]
  have hnonzero : ∀ i ∈ reverseTags m, 1 + i.1 ^ (2 ^ i.2) ≠ 0 := by
    intro i hi
    positivity
  rw [Nat.factorization_prod hnonzero, Finsupp.add_apply, Finsupp.finsetSum_apply]
  have hval : ∀ i ∈ reverseTags m, (1 + i.1 ^ (2 ^ i.2)).factorization 2 = 1 := by
    intro i hi
    obtain ⟨hp, hp2, hb⟩ := (mem_reverseTags m i).mp hi
    exact factorization_raw_slot_two i.1 i.2 (hmod i.1 hp hp2)
  have hfive : (5 : ℕ).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by decide)
  simp [Finset.sum_congr rfl hval, reverseCount, hfive]

/-- The reverse equation equates the tagged budget to the input two-valuation plus one. -/
theorem reverseCount_eq_factorization_two_add_one (n m : ℕ) (hn : 0 < n)
    (hm : 0 < m) (hm2 : m.factorization 2 = 2) (hreverse : sigma m = 2 * n)
    (hmod : ∀ q ∈ m.primeFactors, q ≠ 2 → q % 4 = 1) :
    reverseCount m = n.factorization 2 + 1 := by
  rw [← factorization_sigma_two_eq_reverseCount m hm hm2 hmod, hreverse,
    Nat.factorization_mul (by decide : (2 : ℕ) ≠ 0) (ne_of_gt hn), Finsupp.add_apply]
  norm_num [Nat.Prime.factorization (by decide : Nat.Prime 2), add_comm]

/-- Under the reverse equation, a whole square has an odd tagged reverse budget. -/
theorem odd_reverseCount_of_isSquare (n m : ℕ) (hn : 0 < n)
    (hsquare : IsSquare n) (hm : 0 < m) (hm2 : m.factorization 2 = 2)
    (hreverse : sigma m = 2 * n)
    (hmod : ∀ q ∈ m.primeFactors, q ≠ 2 → q % 4 = 1) : Odd (reverseCount m) := by
  rw [reverseCount_eq_factorization_two_add_one n m hn hm hm2 hreverse hmod]
  exact ((isSquare_iff_even_factorization n hn).mp hsquare 2).add_odd (by decide)

/-- A positive even whole square has at least two factors of two. -/
theorem two_le_factorization_two_of_even_isSquare (n : ℕ) (hn : 0 < n)
    (heven : 2 ∣ n) (hsquare : IsSquare n) : 2 ≤ n.factorization 2 := by
  have hpos := (by decide : Nat.Prime 2).factorization_pos_of_dvd (ne_of_gt hn) heven
  have he := (isSquare_iff_even_factorization n hn).mp hsquare 2
  obtain ⟨k, hk⟩ := he
  omega

example : 2 ≤ (4 : ℕ).factorization 2 :=
  two_le_factorization_two_of_even_isSquare 4 (by decide) (by decide) ⟨2, rfl⟩

/-- The local factor at two forces five into the input on the right of the reverse equation. -/
theorem five_dvd_of_reverse (n m : ℕ) (hm : 0 < m)
    (hm2 : m.factorization 2 = 2) (hreverse : sigma m = 2 * n) : 5 ∣ n := by
  have hdiv : 5 ∣ sigma m := by
    rw [sigma_eq_five_mul_raw_product m hm hm2]
    exact dvd_mul_right 5 _
  rw [hreverse] at hdiv
  exact ((by decide : Nat.Prime 5).dvd_mul.mp hdiv).resolve_left (by decide)

/-- A prime one modulo four with a raw successor not divisible by three
has raw successor residue two modulo three at every height. -/
theorem raw_slot_mod_three (q h : ℕ) (hq : q.Prime) (hq4 : q % 4 = 1)
    (hnot : ¬ 3 ∣ 1 + q ^ (2 ^ h)) : (1 + q ^ (2 ^ h)) % 3 = 2 := by
  have hq3 : q % 3 ≠ 0 := by
    intro hz
    have hd : 3 ∣ q := Nat.dvd_of_mod_eq_zero hz
    have heq : q = 3 := (hq.dvd_iff_eq (by decide : (3 : ℕ) ≠ 1)).mp hd
    rw [heq] at hq4
    norm_num at hq4
  have hres : q % 3 = 1 ∨ q % 3 = 2 := by omega
  cases h with
  | zero =>
    have hnz : (1 + q) % 3 ≠ 0 := by
      simpa using (mt Nat.dvd_of_mod_eq_zero hnot)
    simp only [pow_zero, pow_one]
    have hadd := Nat.add_mod 1 q 3
    omega
  | succ k =>
    have hsq : q ^ 2 % 3 = 1 := by
      rcases hres with hr | hr <;> norm_num [Nat.pow_mod, hr]
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, pow_mul]
    simp [Nat.add_mod, Nat.pow_mod, hsq]

example : (1 + 5 ^ (2 ^ 1)) % 3 = 2 :=
  raw_slot_mod_three 5 1 (by decide) (by decide) (by decide)
example : (1 + 13 ^ (2 ^ 0)) % 3 = 2 :=
  raw_slot_mod_three 13 0 (by decide) (by decide) (by decide)

/-- In absence of a factor three, the raw tagged reverse product has the
residue of one extra factor two beyond the tagged count. -/
theorem sigma_mod_three_eq_two_pow_reverseCount (m : ℕ) (hm : 0 < m)
    (hm2 : m.factorization 2 = 2)
    (hmod : ∀ q ∈ m.primeFactors, q ≠ 2 → q % 4 = 1)
    (hnot : ¬ 3 ∣ sigma m) : sigma m % 3 = (2 * 2 ^ reverseCount m) % 3 := by
  have hslots : ∀ i ∈ reverseTags m, (1 + i.1 ^ (2 ^ i.2)) ≡ 2 [MOD 3] := by
    intro i hi
    obtain ⟨hp, hp2, hb⟩ := (mem_reverseTags m i).mp hi
    have hprime := ((Nat.mem_primeFactors_of_ne_zero (ne_of_gt hm)).mp hp).1
    have hslotnot : ¬ 3 ∣ 1 + i.1 ^ (2 ^ i.2) := by
      intro hd
      exact hnot (hd.trans (slot_dvd_sigma m i.1 i.2 hp hb))
    exact raw_slot_mod_three i.1 i.2 hprime (hmod i.1 hp hp2) hslotnot
  have hprod := Nat.ModEq.prod hslots
  have hall := (show (5 : ℕ) ≡ 2 [MOD 3] by decide).mul hprod
  rw [← sigma_eq_five_mul_raw_product m hm hm2, Finset.prod_const] at hall
  exact hall

/-- An odd exponent of two has residue two modulo three. -/
theorem two_pow_mod_three_of_odd (t : ℕ) (ht : Odd t) : 2 ^ t % 3 = 2 := by
  obtain ⟨k, hk⟩ := ht
  rw [hk, pow_add, pow_mul]
  norm_num [Nat.mul_mod, Nat.pow_mod]

example : 2 ^ (3 : ℕ) % 3 = 2 := two_pow_mod_three_of_odd 3 (by decide)

/-- A natural whole square not divisible by three is one modulo three. -/
theorem square_mod_three_of_not_dvd (n : ℕ) (hsquare : IsSquare n)
    (hnot : ¬ 3 ∣ n) : n % 3 = 1 := by
  obtain ⟨x, hx⟩ := hsquare
  have hnz : n % 3 ≠ 0 := mt Nat.dvd_of_mod_eq_zero hnot
  have hcases : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by omega
  rw [hx, Nat.mul_mod] at hnz ⊢
  rcases hcases with h | h | h <;> simp_all

example : (4 : ℕ) % 3 = 1 := square_mod_three_of_not_dvd 4 ⟨2, rfl⟩ (by decide)

/-- The exact reverse budget forces three into a whole-square input. -/
theorem three_dvd_of_reverse_isSquare (n m : ℕ) (hn : 0 < n)
    (hsquare : IsSquare n) (hm : 0 < m) (hm2 : m.factorization 2 = 2)
    (hreverse : sigma m = 2 * n)
    (hmod : ∀ q ∈ m.primeFactors, q ≠ 2 → q % 4 = 1) : 3 ∣ n := by
  by_contra hnot
  have hsigmanot : ¬ 3 ∣ sigma m := by
    rw [hreverse]
    intro hd
    exact hnot (((by decide : Nat.Prime 3).dvd_mul.mp hd).resolve_left (by decide))
  have ht := odd_reverseCount_of_isSquare n m hn hsquare hm hm2 hreverse hmod
  have hbudget := sigma_mod_three_eq_two_pow_reverseCount m hm hm2 hmod hsigmanot
  have hpow := two_pow_mod_three_of_odd (reverseCount m) ht
  have hnmod := square_mod_three_of_not_dvd n hsquare hnot
  norm_num [hreverse, Nat.mul_mod, hnmod, hpow] at hbudget

/-- With positive even whole-square input, actual valuation two at two in the
reverse input, the canonical reverse equation, and mod-four odd support,
both three and five divide the input. No forward equation or support cap is used. -/
theorem three_and_five_dvd_of_reverse (n m : ℕ) (hn : 0 < n) (heven : 2 ∣ n)
    (hsquare : IsSquare n) (hmpos : 0 < m) (hm2 : m.factorization 2 = 2)
    (hreverse : sigma m = 2 * n)
    (hmod : ∀ q ∈ m.primeFactors, q ≠ 2 → q % 4 = 1) : 3 ∣ n ∧ 5 ∣ n := by
  have _ha := two_le_factorization_two_of_even_isSquare n hn heven hsquare
  exact ⟨three_dvd_of_reverse_isSquare n m hn hsquare hmpos hm2 hreverse hmod,
    five_dvd_of_reverse n m hmpos hm2 hreverse⟩

example : localSigma 2 2 = 5 := by decide

example : reverseOddSupport 4 = ∅ := by
  rw [reverseOddSupport, show (4 : ℕ) = 2 ^ 2 by decide,
    Nat.primeFactors_prime_pow (by decide) (by decide : Nat.Prime 2)]
  simp
example : reverseTags 4 = ∅ := by
  have ho : reverseOddSupport 4 = ∅ := by
    rw [reverseOddSupport, show (4 : ℕ) = 2 ^ 2 by decide,
      Nat.primeFactors_prime_pow (by decide) (by decide : Nat.Prime 2)]
    simp
  simp [reverseTags, ho]
/-- Concrete actual support and valuations at twenty for the realizable reverse-budget tests. -/
private theorem twenty_data : (20 : ℕ).primeFactors = {2, 5} ∧
    (20 : ℕ).factorization 2 = 2 ∧ (20 : ℕ).factorization 5 = 1 := by
  have hrepr : (20 : ℕ) = 2 ^ 2 * 5 := by decide
  have htwo : Nat.Prime 2 := by decide
  have hfive : Nat.Prime 5 := by decide
  rw [hrepr, Nat.primeFactors_mul (by decide) (by decide),
    Nat.primeFactors_prime_pow (by decide) htwo, hfive.primeFactors,
    Nat.factorization_mul (by decide) (by decide), htwo.factorization_pow, hfive.factorization]
  norm_num
/-- Twenty has exactly the actual odd-prime tag consisting of base five and height zero. -/
private theorem twenty_tags : reverseTags 20 = {⟨5, 0⟩} := by
  obtain ⟨hp, htwo, hfive⟩ := twenty_data
  ext ⟨q, h⟩
  have hb : binarySupport 1 = {0} := by decide
  by_cases hq : q = 5
  · subst q
    simp [mem_reverseTags, hp, hfive, hb]
  · simp only [mem_reverseTags, hp, Finset.mem_insert, Finset.mem_singleton]
    aesop
example : reverseCount 20 = 1 := by simp [reverseCount, twenty_tags]
example : reverseProduct 20 = 3 := by simp [reverseProduct, twenty_tags, normalizedSlot]
/-- The canonical sum at twenty is thirty, realizing the reverse equation with input fifteen. -/
private theorem twenty_sigma : sigma 20 = 30 := by
  rw [sigma_eq_five_mul_raw_product 20 (by decide) twenty_data.2.1, twenty_tags]
  norm_num
example : reverseCount 20 = (15 : ℕ).factorization 2 + 1 := by
  apply reverseCount_eq_factorization_two_add_one 15 20 (by decide) (by decide) twenty_data.2.1
  · simpa using twenty_sigma
  · intro q hq hq2
    rw [twenty_data.1] at hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with h | h
    · exact (hq2 h).elim
    · subst q
      decide

end InfinitarySuperperfect
