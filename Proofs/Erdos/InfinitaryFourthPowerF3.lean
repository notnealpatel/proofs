import Erdos.InfinitaryReverseBudget
import Mathlib.FieldTheory.Finite.Basic

set_option autoImplicit false

/-!
# Infinitary fourth-power parity obstruction

This module works with the canonical infinitary `sigma`, `binarySupport`,
`Nat.factorization`, and actual `Nat.primeFactors` in `InfinitarySuperperfect`.
Its public contracts `factorization_sigma_two_even_of_four_dvd` and
`factorization_sigma_two_even_of_fourth_power` preserve the positive-input,
four-divisibility, odd-part, forward, and reverse hypotheses and conclude that
the second member has even two-adic valuation; the existing corresponding
`ne_three` contracts remain available as corollaries.  The proof derives
actual odd support modulo eight from successor orders, reconstructs `sigma m`
from the two-local factor, `2 ^ reverseCount m`, and tagged `reverseProduct m`,
and compares odd parts modulo four.  The checked boundary model at `m = 17`
exercises absent two, while `m = 136` exercises valuation three; these are
separate hypothesis-block models, not a positive fourth-power cycle.  The
module does not classify or establish cycles, global f3 exclusion, or the
upstream shape/ratio/free-prime bridges.  This docstring consolidates the
former companion mathematical note and the actual declarations below.
-/

namespace InfinitarySuperperfect

/-- Every occupied bit of a multiple of four has height at least two. -/
theorem two_le_of_mem_binarySupport_of_four_dvd (e j : ℕ)
    (he : 4 ∣ e) (hj : j ∈ binarySupport e) : 2 ≤ j := by
  have hb := (mem_binarySupport_iff e j).mp hj
  have hm : e % 4 = 0 := Nat.mod_eq_zero_of_dvd he
  by_contra hh
  have hc : j = 0 ∨ j = 1 := by omega
  rcases hc with rfl | rfl
  · rw [Nat.testBit_eq_decide_div_mod_eq] at hb
    simp only [pow_zero, Nat.div_one] at hb
    have hemod : e % 2 = 0 := by omega
    simp [hemod] at hb
  · rw [Nat.testBit_eq_decide_div_mod_eq] at hb
    norm_num at hb
    omega

/-- An odd prime dividing a successor of height at least two is one modulo eight. -/
theorem prime_mod_eight_of_dvd_successor (p j r : ℕ)
    (hj : 2 ≤ j) (hr : r.Prime) (hr2 : r ≠ 2)
    (hdiv : r ∣ 1 + p ^ (2 ^ j)) : r % 8 = 1 := by
  letI : Fact r.Prime := ⟨hr⟩
  letI : Fact (2 < r) := ⟨by have hrlo := hr.two_le; omega⟩
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hz : 1 + (p : ZMod r) ^ (2 ^ j) = 0 := by
    exact_mod_cast (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
  have hp : (p : ZMod r) ^ (2 ^ j) = -1 := by linear_combination hz
  have hnot : (p : ZMod r) ^ (2 ^ j) ≠ 1 := by
    rw [hp]
    exact ZMod.neg_one_ne_one
  have hfin : (p : ZMod r) ^ (2 ^ (j + 1)) = 1 := by
    rw [pow_succ, pow_mul, hp]
    ring
  have hord : orderOf (p : ZMod r) = 2 ^ (j + 1) :=
    orderOf_eq_prime_pow hnot hfin
  have hp0 : (p : ZMod r) ≠ 0 := by
    intro h
    simp [h] at hp
  have hd : 2 ^ (j + 1) ∣ r - 1 := by
    rw [← hord]
    exact ZMod.orderOf_dvd_card_sub_one hp0
  have h8 : 8 ∣ r - 1 :=
    (show 2 ^ 3 ∣ 2 ^ (j + 1) from pow_dvd_pow 2 (by omega)).trans hd
  have hrpos := hr.two_le
  omega

/-- Actual forward prime support is one modulo eight when all valuations are multiples of four. -/
theorem prime_mod_eight_of_dvd_sigma_of_four_dvd (n r : ℕ)
    (he : ∀ p ∈ n.primeFactors, 4 ∣ n.factorization p)
    (hr : r.Prime) (hr2 : r ≠ 2) (hdiv : r ∣ sigma n) : r % 8 = 1 := by
  obtain ⟨p, hp, hlocal⟩ := (hr.prime.dvd_finsetProd_iff
    (fun p => localSigma p (n.factorization p))).mp hdiv
  obtain ⟨j, hj, hslot⟩ := (hr.prime.dvd_finsetProd_iff
    (fun j => 1 + p ^ (2 ^ j))).mp hlocal
  exact prime_mod_eight_of_dvd_successor p j r
    (two_le_of_mem_binarySupport_of_four_dvd _ _ (he p hp) hj) hr hr2 hslot

/-- A base one modulo eight gives a normalized successor one modulo four at every height. -/
theorem normalizedSlot_mod_four_of_mod_eight (q h : ℕ) (hq : q % 8 = 1) :
    normalizedSlot q h % 4 = 1 := by
  have hraw : (1 + q ^ (2 ^ h)) % 8 = 2 := by
    simp [Nat.add_mod, Nat.pow_mod, hq]
  unfold normalizedSlot
  omega

/-- All tagged normalized occurrences multiply to one modulo four under mod-eight support. -/
theorem reverseProduct_mod_four_of_mod_eight (m : ℕ)
    (hmod : ∀ q ∈ m.primeFactors, q ≠ 2 → q % 8 = 1) :
    reverseProduct m % 4 = 1 := by
  have hslots : ∀ i ∈ reverseTags m, normalizedSlot i.1 i.2 ≡ 1 [MOD 4] := by
    intro i hi
    obtain ⟨hp, hp2, _hb⟩ := (mem_reverseTags m i).mp hi
    exact normalizedSlot_mod_four_of_mod_eight i.1 i.2 (hmod i.1 hp hp2)
  have hprod := Nat.ModEq.prod hslots
  simpa [Nat.ModEq, reverseProduct] using hprod

/-- The local factor at two is one modulo four for even valuations and three for odd ones. -/
theorem localSigma_two_mod_four (b : ℕ) :
    localSigma 2 b % 4 = if b % 2 = 0 then 1 else 3 := by
  have hrest : (∏ j ∈ (binarySupport b).erase 0, (1 + 2 ^ (2 ^ j))) % 4 = 1 := by
    have hslots : ∀ j ∈ (binarySupport b).erase 0,
        (1 + 2 ^ (2 ^ j)) ≡ 1 [MOD 4] := by
      intro j hj
      have hj0 := (Finset.mem_erase.mp hj).1
      have hexp : 2 ≤ 2 ^ j := by
        exact (show 2 ^ 1 ≤ 2 ^ j from Nat.pow_le_pow_right (by decide) (by omega))
      have hd : 4 ∣ 2 ^ (2 ^ j) :=
        show 2 ^ 2 ∣ 2 ^ (2 ^ j) from pow_dvd_pow 2 hexp
      simp [Nat.ModEq, Nat.add_mod, Nat.mod_eq_zero_of_dvd hd]
    simpa [Nat.ModEq] using Nat.ModEq.prod hslots
  have hzero : 0 ∈ binarySupport b ↔ b % 2 = 1 := by
    rw [mem_binarySupport_iff, Nat.testBit_eq_decide_div_mod_eq]
    simp
  unfold localSigma
  by_cases hz : 0 ∈ binarySupport b
  · rw [← Finset.mul_prod_erase _ (fun j => 1 + 2 ^ (2 ^ j)) hz]
    have hb := hzero.mp hz
    simp [Nat.mul_mod, hrest, hb]
  · rw [← Finset.erase_eq_of_notMem hz]
    have hbne : b % 2 ≠ 1 := fun hh => hz (hzero.mpr hh)
    have hb : b % 2 = 0 := by omega
    simp [hrest, hb]

/-- Splitting off two works at every valuation, including zero when two is absent. -/
theorem sigma_eq_localSigma_two_mul_raw_product (m : ℕ) (hm : 0 < m) :
    sigma m = localSigma 2 (m.factorization 2) *
      ∏ i ∈ reverseTags m, (1 + i.1 ^ (2 ^ i.2)) := by
  have hsupport : reverseOddSupport m = m.primeFactors.erase 2 := by
    ext q
    simp [reverseOddSupport, and_comm]
  rw [reverseTags, Finset.prod_sigma]
  change sigma m = localSigma 2 (m.factorization 2) *
    ∏ q ∈ reverseOddSupport m, localSigma q (m.factorization q)
  rw [hsupport]
  by_cases htwo : 2 ∈ m.primeFactors
  · exact (Finset.mul_prod_erase m.primeFactors
      (fun q => localSigma q (m.factorization q)) htwo).symm
  · have hnot : ¬ 2 ∣ m := by
      intro hd
      exact htwo ((Nat.mem_primeFactors_of_ne_zero (ne_of_gt hm)).mpr ⟨by decide, hd⟩)
    have hb : m.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd hnot
    rw [Finset.erase_eq_of_notMem htwo, hb]
    have hlocal : localSigma 2 0 = 1 := by decide
    simp [hlocal, sigma]

/-- Exact reconstruction with the general local factor at two and every tagged odd occurrence. -/
theorem sigma_eq_localSigma_two_mul_two_pow_reverseCount (m : ℕ) (hm : 0 < m)
    (hmod : ∀ q ∈ m.primeFactors, q ≠ 2 → q % 4 = 1) :
    sigma m = localSigma 2 (m.factorization 2) *
      2 ^ reverseCount m * reverseProduct m := by
  rw [sigma_eq_localSigma_two_mul_raw_product m hm]
  have heq : (∏ i ∈ reverseTags m, (1 + i.1 ^ (2 ^ i.2))) =
      ∏ i ∈ reverseTags m, (2 * normalizedSlot i.1 i.2) := by
    apply Finset.prod_congr rfl
    intro i hi
    obtain ⟨hp, hp2, _hb⟩ := (mem_reverseTags m i).mp hi
    exact (normalizedSlot_spec i.1 i.2 (hmod i.1 hp hp2)).1
  rw [heq, Finset.prod_mul_distrib, Finset.prod_const]
  simp only [reverseCount, reverseProduct, mul_assoc]

/-- Valuation three at two contributes fifteen, with the actual tagged raw odd-prime product. -/
theorem sigma_eq_fifteen_mul_raw_product (m : ℕ) (hm : 0 < m)
    (hm3 : m.factorization 2 = 3) :
    sigma m = 15 * ∏ i ∈ reverseTags m, (1 + i.1 ^ (2 ^ i.2)) := by
  have htwo : 2 ∈ m.primeFactors := by
    apply (Nat.mem_primeFactors_of_ne_zero (ne_of_gt hm)).mpr
    refine ⟨by decide, ?_⟩
    change 2 ^ 1 ∣ m
    apply (Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 2) (ne_of_gt hm)).mpr
    simp [hm3]
  have hsupport : reverseOddSupport m = m.primeFactors.erase 2 := by
    ext q
    simp [reverseOddSupport, and_comm]
  have hlocal : localSigma 2 (m.factorization 2) = 15 := by rw [hm3]; decide
  rw [reverseTags, Finset.prod_sigma]
  change sigma m = 15 * ∏ q ∈ reverseOddSupport m, localSigma q (m.factorization q)
  rw [hsupport, ← hlocal]
  exact (Finset.mul_prod_erase m.primeFactors (fun q => localSigma q (m.factorization q)) htwo).symm

/-- Exact reconstruction for valuation three, not a reuse of the valuation-two bridge. -/
theorem sigma_eq_fifteen_mul_two_pow_reverseCount (m : ℕ) (hm : 0 < m)
    (hm3 : m.factorization 2 = 3)
    (hmod : ∀ q ∈ m.primeFactors, q ≠ 2 → q % 4 = 1) :
    sigma m = 15 * 2 ^ reverseCount m * reverseProduct m := by
  rw [sigma_eq_fifteen_mul_raw_product m hm hm3]
  have heq : (∏ i ∈ reverseTags m, (1 + i.1 ^ (2 ^ i.2))) =
      ∏ i ∈ reverseTags m, (2 * normalizedSlot i.1 i.2) := by
    apply Finset.prod_congr rfl
    intro i hi
    obtain ⟨hp, hp2, _hb⟩ := (mem_reverseTags m i).mp hi
    exact (normalizedSlot_spec i.1 i.2 (hmod i.1 hp hp2)).1
  rw [heq, Finset.prod_mul_distrib, Finset.prod_const]
  simp only [reverseCount, reverseProduct, mul_assoc]

/-- With valuation three and mod-eight odd support, the odd part of the reverse sum is three modulo four. -/
theorem oddPart_sigma_mod_four_of_factorization_two_eq_three (m : ℕ) (hm : 0 < m)
    (hm3 : m.factorization 2 = 3)
    (hmod : ∀ q ∈ m.primeFactors, q ≠ 2 → q % 8 = 1) :
    oddPart (sigma m) % 4 = 3 := by
  have hmod4 : ∀ q ∈ m.primeFactors, q ≠ 2 → q % 4 = 1 := by
    intro q hq hq2
    have hh := hmod q hq hq2
    omega
  have hpmod := reverseProduct_mod_four_of_mod_eight m hmod
  have hcofactor : ¬ 2 ∣ 15 * reverseProduct m := by
    have hh : (15 * reverseProduct m) % 4 = 3 := by
      simp [Nat.mul_mod, hpmod]
    omega
  have heq : sigma m = 2 ^ reverseCount m * (15 * reverseProduct m) := by
    rw [sigma_eq_fifteen_mul_two_pow_reverseCount m hm hm3 hmod4]
    ring
  have hop : oddPart (sigma m) = 15 * reverseProduct m := by
    rw [heq]
    exact Nat.ordCompl_pow_mul_of_not_dvd (reverseCount m) (by decide) hcofactor
  rw [hop]
  simp [Nat.mul_mod, hpmod]

/-- Multiplication by two does not change the odd part. -/
theorem oddPart_two_mul (n : ℕ) : oddPart (2 * n) = oddPart n := by
  simpa only [oddPart, pow_one] using
    (Nat.ordCompl_self_pow_mul n 1 (by decide : Nat.Prime 2))

/-- The odd part of a positive whole square is one modulo four. -/
theorem oddPart_mod_four_of_isSquare (n : ℕ) (hn : 0 < n) (hsquare : IsSquare n) :
    oddPart n % 4 = 1 := by
  have hpart : IsSquare (oddPart n) := by
    apply (isSquare_oddPart_iff n hn).mpr
    intro p _hp
    exact (isSquare_iff_even_factorization n hn).mp hsquare p
  have hodd : ¬ 2 ∣ oddPart n :=
    Nat.not_dvd_ordCompl (by decide) (ne_of_gt hn)
  obtain ⟨a, ha⟩ := hpart
  have hamod : a % 4 = 1 ∨ a % 4 = 3 := by
    have hanot : ¬ 2 ∣ a := by
      intro hd
      apply hodd
      rw [ha]
      exact dvd_mul_of_dvd_left hd a
    omega
  rw [ha, Nat.mul_mod]
  rcases hamod with hh | hh <;> simp [hh]

/-- Under mod-eight odd-prime support, the odd part of the reverse sum detects the parity
of its input two-valuation: residue one for even valuations and three for odd valuations. -/
theorem oddPart_sigma_mod_four_of_mod_eight (m : ℕ) (hm : 0 < m)
    (hmod : ∀ q ∈ m.primeFactors, q ≠ 2 → q % 8 = 1) :
    oddPart (sigma m) % 4 = if m.factorization 2 % 2 = 0 then 1 else 3 := by
  have hmod4 : ∀ q ∈ m.primeFactors, q ≠ 2 → q % 4 = 1 := by
    intro q hq hq2
    have hh := hmod q hq hq2
    omega
  have hpmod := reverseProduct_mod_four_of_mod_eight m hmod
  have hlmod := localSigma_two_mod_four (m.factorization 2)
  have hcofactor : ¬ 2 ∣ localSigma 2 (m.factorization 2) * reverseProduct m := by
    have hh : (localSigma 2 (m.factorization 2) * reverseProduct m) % 4 =
        if m.factorization 2 % 2 = 0 then 1 else 3 := by
      rw [Nat.mul_mod, hpmod, hlmod]
      split <;> decide
    split at hh <;> omega
  have heq : sigma m = 2 ^ reverseCount m *
      (localSigma 2 (m.factorization 2) * reverseProduct m) := by
    rw [sigma_eq_localSigma_two_mul_two_pow_reverseCount m hm hmod4]
    ring
  have hop : oddPart (sigma m) = localSigma 2 (m.factorization 2) * reverseProduct m := by
    rw [heq]
    exact Nat.ordCompl_pow_mul_of_not_dvd (reverseCount m) (by decide) hcofactor
  rw [hop, Nat.mul_mod, hpmod, hlmod]
  split <;> decide

/-- Actual forward and reverse equations force an even two-valuation in the second member
when forward valuations are multiples of four and the input odd part is one modulo four. -/
theorem factorization_sigma_two_even_of_four_dvd (n m : ℕ) (_hn : 0 < n)
    (he : ∀ p ∈ n.primeFactors, 4 ∣ n.factorization p)
    (hop : oddPart n % 4 = 1) (hm : m = sigma n)
    (hcycle : sigma m = 2 * n) : Even (m.factorization 2) := by
  have hmpos : 0 < m := by rw [hm]; exact sigma_pos n
  have hmod : ∀ q ∈ m.primeFactors, q ≠ 2 → q % 8 = 1 := by
    intro q hq hq2
    obtain ⟨hprime, hd, _hm0⟩ := Nat.mem_primeFactors.mp hq
    rw [hm] at hd
    exact prime_mod_eight_of_dvd_sigma_of_four_dvd n q he hprime hq2 hd
  have hres := oddPart_sigma_mod_four_of_mod_eight m hmpos hmod
  rw [hcycle, oddPart_two_mul, hop] at hres
  apply Nat.even_iff.mpr
  split at hres <;> rename_i hparity
  · exact hparity
  · contradiction

/-- A cycle starting at a positive fourth power has even two-valuation in its second member.
Both sums are canonical infinitary divisor sums; the root may be odd. -/
theorem factorization_sigma_two_even_of_fourth_power (n m t : ℕ)
    (ht : 0 < t) (hfourth : n = t ^ 4) (hm : m = sigma n)
    (hcycle : sigma m = 2 * n) : Even (m.factorization 2) := by
  have hn : 0 < n := by rw [hfourth]; positivity
  have he : ∀ p ∈ n.primeFactors, 4 ∣ n.factorization p := by
    intro p _hp
    rw [hfourth, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    exact dvd_mul_right 4 _
  have hsquare : IsSquare n := by
    refine ⟨t ^ 2, ?_⟩
    rw [hfourth, ← pow_two, ← pow_mul]
  exact factorization_sigma_two_even_of_four_dvd n m hn he
    (oddPart_mod_four_of_isSquare n hn hsquare) hm hcycle

/-- Actual forward and reverse equations exclude valuation three when forward valuations
are multiples of four and the input odd part is one modulo four. -/
theorem factorization_sigma_two_ne_three_of_four_dvd (n m : ℕ) (_hn : 0 < n)
    (he : ∀ p ∈ n.primeFactors, 4 ∣ n.factorization p)
    (hop : oddPart n % 4 = 1) (hm : m = sigma n)
    (hcycle : sigma m = 2 * n) : m.factorization 2 ≠ 3 := by
  intro hf3
  have hmpos : 0 < m := by rw [hm]; exact sigma_pos n
  have hmod : ∀ q ∈ m.primeFactors, q ≠ 2 → q % 8 = 1 := by
    intro q hq hq2
    obtain ⟨hprime, hd, _hm0⟩ := Nat.mem_primeFactors.mp hq
    rw [hm] at hd
    exact prime_mod_eight_of_dvd_sigma_of_four_dvd n q he hprime hq2 hd
  have hbad := oddPart_sigma_mod_four_of_factorization_two_eq_three m hmpos hf3 hmod
  rw [hcycle, oddPart_two_mul, hop] at hbad
  contradiction

/-- A cycle starting at an actual positive fourth power cannot have valuation three at two
in its second member. Both sums are the canonical infinitary divisor sum; the root may be odd. -/
theorem factorization_sigma_two_ne_three_of_fourth_power (n m t : ℕ)
    (ht : 0 < t) (hfourth : n = t ^ 4) (hm : m = sigma n)
    (hcycle : sigma m = 2 * n) : m.factorization 2 ≠ 3 := by
  have hn : 0 < n := by rw [hfourth]; positivity
  have he : ∀ p ∈ n.primeFactors, 4 ∣ n.factorization p := by
    intro p _hp
    rw [hfourth, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    exact dvd_mul_right 4 _
  have hsquare : IsSquare n := by
    refine ⟨t ^ 2, ?_⟩
    rw [hfourth, ← pow_two, ← pow_mul]
  exact factorization_sigma_two_ne_three_of_four_dvd n m hn he
    (oddPart_mod_four_of_isSquare n hn hsquare) hm hcycle

example : localSigma 2 0 = 1 ∧ localSigma 2 1 = 3 ∧
    localSigma 2 2 = 5 ∧ localSigma 2 3 = 15 := by decide

example : 0 < (17 : ℕ) ∧ (17 : ℕ).factorization 2 = 0 ∧
    (∀ q ∈ (17 : ℕ).primeFactors, q ≠ 2 → q % 8 = 1) ∧
    sigma 17 = 18 ∧ oddPart (sigma 17) % 4 = 1 := by
  have hp : Nat.Prime 17 := by decide
  have hmod : ∀ q ∈ (17 : ℕ).primeFactors, q ≠ 2 → q % 8 = 1 := by
    rw [hp.primeFactors]
    intro q hq _hq2
    have hq17 : q = 17 := Finset.mem_singleton.mp hq
    subst q
    decide
  have hb : (17 : ℕ).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by decide)
  have hsum : sigma 17 = 18 := by
    rw [sigma, hp.primeFactors, Finset.prod_singleton, hp.factorization_self]
    decide
  have hres := oddPart_sigma_mod_four_of_mod_eight 17 (by decide) hmod
  simp only [hb] at hres
  exact ⟨by decide, hb, hmod, hsum, hres⟩

example : 4 ∣ (4 : ℕ) ∧ 2 ∈ binarySupport 4 := by decide
example : 2 ≤ (2 : ℕ) ∧ Nat.Prime 17 ∧ (17 : ℕ) ≠ 2 ∧
    17 ∣ 1 + 2 ^ (2 ^ 2) := by decide
example : normalizedSlot 17 0 % 4 = 1 :=
  normalizedSlot_mod_four_of_mod_eight 17 0 (by decide)
example : 0 < (9 : ℕ) ∧ IsSquare (9 : ℕ) ∧ oddPart 9 % 4 = 1 := by
  refine ⟨by decide, ⟨3, rfl⟩, ?_⟩
  exact oddPart_mod_four_of_isSquare 9 (by decide) ⟨3, rfl⟩

/-- Independent actual prime support and valuations for a nonempty reverse-support test. -/
private theorem model136_data : (136 : ℕ).primeFactors = {2, 17} ∧
    (136 : ℕ).factorization 2 = 3 ∧ (136 : ℕ).factorization 17 = 1 := by
  have hrepr : (136 : ℕ) = 2 ^ 3 * 17 := by decide
  have htwo : Nat.Prime 2 := by decide
  have hseventeen : Nat.Prime 17 := by decide
  rw [hrepr, Nat.primeFactors_mul (by decide) (by decide),
    Nat.primeFactors_prime_pow (by decide) htwo, hseventeen.primeFactors,
    Nat.factorization_mul (by decide) (by decide), htwo.factorization_pow,
    hseventeen.factorization]
  norm_num

/-- The test member has a genuine odd tag at height zero, the reverse boundary case. -/
private theorem model136_tags : reverseTags 136 = {⟨17, 0⟩} := by
  obtain ⟨hp, _htwo, hseventeen⟩ := model136_data
  ext ⟨q, h⟩
  have hb : binarySupport 1 = {0} := by decide
  by_cases hq : q = 17
  · subst q
    simp [mem_reverseTags, hp, hseventeen, hb]
  · simp only [mem_reverseTags, hp, Finset.mem_insert, Finset.mem_singleton]
    aesop

/-- All reverse reconstruction hypotheses hold at 136, with an actual reverse equation
for input 135. This is not a cycle or a fourth-power input. -/
private theorem model136_reverse : 0 < (136 : ℕ) ∧ (136 : ℕ).factorization 2 = 3 ∧
    (∀ q ∈ (136 : ℕ).primeFactors, q ≠ 2 → q % 8 = 1) ∧
    sigma 136 = 2 * 135 := by
  have hmod : ∀ q ∈ (136 : ℕ).primeFactors, q ≠ 2 → q % 8 = 1 := by
    rw [model136_data.1]
    intro q hq hq2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with hh | hh
    · exact (hq2 hh).elim
    · subst q
      decide
  have hsum : sigma 136 = 270 := by
    rw [sigma_eq_fifteen_mul_raw_product 136 (by decide) model136_data.2.1,
      model136_tags]
    norm_num
  exact ⟨by decide, model136_data.2.1, hmod, hsum⟩

example : oddPart (sigma 136) % 4 = 3 := by
  obtain ⟨hm, hf3, hmod, _hreverse⟩ := model136_reverse
  exact oddPart_sigma_mod_four_of_factorization_two_eq_three 136 hm hf3 hmod
example : reverseCount 136 = 1 := by simp [reverseCount, model136_tags]
example : reverseProduct 136 = 9 := by
  simp [reverseProduct, model136_tags, normalizedSlot]
example : localSigma 2 3 = 15 := by decide

example : 0 < (3 : ℕ) ∧ (81 : ℕ) = 3 ^ 4 ∧ sigma 81 = 82 := by
  refine ⟨by decide, by decide, ?_⟩
  rw [sigma, show (81 : ℕ) = 3 ^ 4 by decide,
    Nat.primeFactors_prime_pow (by decide) (by decide : Nat.Prime 3),
    (by decide : Nat.Prime 3).factorization_pow]
  norm_num
  decide
example : sigma 1 = 1 ∧ sigma (sigma 1) ≠ 2 * 1 ^ 4 := by
  have hs : sigma 1 = 1 := by simp [sigma]
  simp [hs]

end InfinitarySuperperfect
