import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace InfinitarySuperperfect

/-- The occupied binary positions of an exponent, with a finite arithmetic bound. -/
def binarySupport (e : ℕ) : Finset ℕ :=
  (Finset.range e).filter (fun j => e.testBit j)

/-- The infinitary divisor sum on a single prime-power component. -/
def localSigma (p e : ℕ) : ℕ :=
  ∏ j ∈ binarySupport e, (1 + p ^ (2 ^ j))

/-- The infinitary divisor sum: one successor factor for each occupied binary
position of each prime valuation. The value at zero is the empty product, one;
all number-theoretic consumers require a positive input. -/
def sigma (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, localSigma p (n.factorization p)

/-- The odd part obtained by removing the complete two-primary factor. -/
def oddPart (n : ℕ) : ℕ := n / 2 ^ (n.factorization 2)

example : binarySupport 0 = ∅ := by decide
example : binarySupport 1 = {0} := by decide
example : binarySupport 2 = {1} := by decide
example : binarySupport 3 = {0, 1} := by decide
example : localSigma 2 1 = 3 := by decide
example : localSigma 3 1 = 4 := by decide
example : localSigma 5 2 = 26 := by decide
example : sigma 2 = 3 := by
  norm_num [sigma, localSigma, binarySupport, Finset.filter_insert,
    Nat.testBit_eq_decide_div_mod_eq]
  decide
example : sigma 3 = 4 := by
  norm_num [sigma, localSigma, binarySupport, Finset.filter_insert,
    Nat.testBit_eq_decide_div_mod_eq]
  decide
example : oddPart 2 = 1 := by norm_num [oddPart]
example : oddPart 3 = 3 := by norm_num [oddPart]

/-- The finite cutoff omits no occupied binary position. -/
theorem mem_binarySupport_iff (e j : ℕ) :
    j ∈ binarySupport e ↔ e.testBit j = true := by
  constructor
  · intro hj
    exact (Finset.mem_filter.mp hj).2
  · intro hj
    have hpow : 2 ^ j ≤ e := Nat.ge_two_pow_of_testBit hj
    have hlt : j < e := (Nat.lt_two_pow_self (n := j)).trans_le hpow
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, hj⟩

/-- In an even exponent, every occupied position is strictly above bit zero. -/
theorem one_le_of_mem_binarySupport_of_even (e j : ℕ)
    (he : Even e) (hj : j ∈ binarySupport e) : 1 ≤ j := by
  have hbit := (mem_binarySupport_iff e j).mp hj
  have hmod : e % 2 = 0 := Nat.mod_eq_zero_of_dvd he.two_dvd
  by_contra hsmall
  have hj0 : j = 0 := by omega
  rw [hj0, Nat.testBit_eq_decide_div_mod_eq] at hbit
  simp [hmod] at hbit

/-- Every odd prime divisor of a higher-bit successor is one modulo four,
including successors with base two. -/
theorem prime_mod_four_of_dvd_higher_successor (p j r : ℕ)
    (hr : r.Prime) (hr2 : r ≠ 2) (hdiv : r ∣ 1 + p ^ (2 ^ (j + 1))) :
    r % 4 = 1 := by
  letI : Fact r.Prime := ⟨hr⟩
  have hzero : (1 + (p : ZMod r) ^ (2 ^ (j + 1))) = 0 := by
    exact_mod_cast (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
  have hsquare : ((p : ZMod r) ^ (2 ^ j)) ^ 2 = -1 := by
    rw [Nat.pow_succ] at hzero
    rw [← pow_mul]
    linear_combination hzero
  have hnot3 : r % 4 ≠ 3 := ZMod.mod_four_ne_three_of_sq_eq_neg_one hsquare
  have hodd : r % 2 = 1 := hr.eq_two_or_odd.resolve_left hr2
  omega

example : 13 ∣ 1 + 5 ^ (2 ^ (0 + 1)) ∧ Nat.Prime 13 ∧ (13 : ℕ) ≠ 2 := by
  decide

/-- The standard even solution jointly satisfies every ambient equation
hypothesis; no square-odd-part assumptions are imposed in this witness. -/
theorem ambient_two_three :
    0 < (2 : ℕ) ∧ 2 ∣ (2 : ℕ) ∧ 3 = sigma 2 ∧ sigma 3 = 2 * 2 := by
  norm_num [sigma, localSigma, binarySupport, Finset.filter_insert,
    Nat.testBit_eq_decide_div_mod_eq]
  decide

/-- Local even exponents produce only odd prime divisors one modulo four. -/
theorem prime_mod_four_of_dvd_localSigma (p e r : ℕ)
    (he : Even e) (hr : r.Prime) (hr2 : r ≠ 2) (hdiv : r ∣ localSigma p e) :
    r % 4 = 1 := by
  obtain ⟨j, hj, hslot⟩ := (hr.prime.dvd_finsetProd_iff
    (fun j => 1 + p ^ (2 ^ j))).mp hdiv
  have hjpos := one_le_of_mem_binarySupport_of_even e j he hj
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  exact prime_mod_four_of_dvd_higher_successor p k r hr hr2 hslot

/-- If every occupied prime valuation is even, every odd prime divisor of the
actual infinitary sum is one modulo four. -/
theorem prime_mod_four_of_dvd_sigma_of_even (n r : ℕ)
    (he : ∀ p ∈ n.primeFactors, Even (n.factorization p))
    (hr : r.Prime) (hr2 : r ≠ 2) (hdiv : r ∣ sigma n) : r % 4 = 1 := by
  obtain ⟨p, hp, hlocal⟩ := (hr.prime.dvd_finsetProd_iff
    (fun p => localSigma p (n.factorization p))).mp hdiv
  exact prime_mod_four_of_dvd_localSigma p (n.factorization p) r (he p hp) hr hr2 hlocal

example : Even (2 : ℕ) ∧ Nat.Prime 13 ∧ (13 : ℕ) ≠ 2 ∧ 13 ∣ localSigma 5 2 := by
  norm_num [localSigma, binarySupport]
  decide

private theorem sum_testBit_range (e K : ℕ) :
    (∑ j ∈ Finset.range K, if e.testBit j then 2 ^ j else 0) = e % 2 ^ K := by
  induction K with
  | zero => simp [Nat.mod_one]
  | succ K ih =>
    rw [Finset.sum_range_succ, ih, Nat.pow_succ, Nat.mod_mul,
      Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (e / 2 ^ K) with hzero | hone
    · simp [hzero]
    · simp [hone]

/-- The occupied slots reconstruct the exponent exactly, including exponent
zero and arbitrarily large, sparse binary expansions. -/
theorem sum_binarySupport (e : ℕ) : (∑ j ∈ binarySupport e, 2 ^ j) = e := by
  rw [binarySupport, Finset.sum_filter, sum_testBit_range]
  exact Nat.mod_eq_of_lt (Nat.lt_two_pow_self (n := e))

/-- Multiplying the prime powers associated with the occupied binary slots
recovers the original prime power. -/
theorem prod_binarySupport_pow (p e : ℕ) :
    (∏ j ∈ binarySupport e, p ^ (2 ^ j)) = p ^ e := by
  rw [Finset.prod_pow_eq_pow_sum, sum_binarySupport]

/-- A positive natural number is a square exactly when all its prime valuations
are even. Nonprimes have valuation zero, so the universal quantifier is harmless. -/
theorem isSquare_iff_even_factorization (n : ℕ) (hn : 0 < n) :
    IsSquare n ↔ ∀ p : ℕ, Even (n.factorization p) := by
  constructor
  · rintro ⟨c, hc⟩ p
    have hc0 : c ≠ 0 := by
      intro hzero
      subst c
      simp only [mul_zero] at hc
      omega
    rw [hc, Nat.factorization_mul hc0 hc0, Finsupp.add_apply]
    exact ⟨c.factorization p, rfl⟩
  · intro he
    let c := n.factorization.prod (fun p e => p ^ (e / 2))
    refine ⟨c, ?_⟩
    rw [← pow_two]
    dsimp only [c, Finsupp.prod]
    rw [← Finset.prod_pow]
    calc
      n = n.factorization.prod (fun p e => p ^ e) :=
        (Nat.prod_factorization_pow_eq_self (ne_of_gt hn)).symm
      _ = ∏ p ∈ n.factorization.support, (p ^ (n.factorization p / 2)) ^ 2 := by
        unfold Finsupp.prod
        apply Finset.prod_congr rfl
        intro p hp
        rw [← pow_mul, Nat.div_mul_cancel (he p).two_dvd]

/-- Removing the two-primary factor erases exactly the valuation at two. -/
theorem factorization_oddPart (n : ℕ) :
    (oddPart n).factorization = n.factorization.erase 2 :=
  Nat.factorization_ordCompl n 2

/-- The odd part of a positive integer remains positive. -/
theorem oddPart_pos (n : ℕ) (hn : 0 < n) : 0 < oddPart n :=
  Nat.ordCompl_pos 2 (ne_of_gt hn)

/-- The specified odd part is a square exactly when every valuation away from
two is even. This checks the valuation formulation against the quotient definition. -/
theorem isSquare_oddPart_iff (n : ℕ) (hn : 0 < n) :
    IsSquare (oddPart n) ↔ ∀ p : ℕ, p ≠ 2 → Even (n.factorization p) := by
  rw [isSquare_iff_even_factorization (oddPart n) (oddPart_pos n hn),
    factorization_oddPart]
  constructor
  · intro he p hp
    simpa only [Finsupp.erase_ne hp] using he p
  · intro he p
    by_cases hp : p = 2
    · subst p
      simp
    · simpa only [Finsupp.erase_ne hp] using he p hp

example : 0 < (9 : ℕ) ∧ IsSquare (9 : ℕ) := by
  exact ⟨by decide, ⟨3, rfl⟩⟩
example : 0 < (2 : ℕ) ∧ IsSquare (oddPart 2) := by
  refine ⟨by decide, ?_⟩
  have hpart : oddPart 2 = 1 := by norm_num [oddPart]
  rw [hpart]
  exact ⟨1, rfl⟩

/-- Every local infinitary divisor sum is positive, including exponent zero. -/
theorem localSigma_pos (p e : ℕ) : 0 < localSigma p e := by
  unfold localSigma
  exact Finset.prod_pos (fun j hj => by omega)

/-- The actual global infinitary sum is positive, including an empty support. -/
theorem sigma_pos (n : ℕ) : 0 < sigma n := by
  unfold sigma
  exact Finset.prod_pos (fun p hp => localSigma_pos p (n.factorization p))

/-- An even local exponent has no factor three, at any base. -/
theorem factorization_localSigma_three_of_even (p e : ℕ) (he : Even e) :
    (localSigma p e).factorization 3 = 0 := by
  apply Nat.factorization_eq_zero_of_not_dvd
  intro hdiv
  have hmod := prime_mod_four_of_dvd_localSigma p e 3 he (by decide) (by decide) hdiv
  norm_num at hmod

private theorem factorization_two_slot_three (j : ℕ) :
    (1 + 2 ^ (2 ^ j)).factorization 3 = if j = 0 then 1 else 0 := by
  cases j with
  | zero => norm_num
  | succ k =>
    simp only [Nat.succ_ne_zero, if_false]
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hdiv
    have hmod := prime_mod_four_of_dvd_higher_successor 2 k 3
      (by decide) (by decide) hdiv
    norm_num at hmod

/-- At base two, the three-adic valuation is exactly its occupied bit zero. -/
theorem factorization_localSigma_two_three (e : ℕ) :
    (localSigma 2 e).factorization 3 = if e.testBit 0 then 1 else 0 := by
  unfold localSigma
  have hslots : ∀ j ∈ binarySupport e, (1 : ℕ) + 2 ^ (2 ^ j) ≠ 0 := by
    intro j hj
    exact Nat.ne_of_gt (by positivity)
  rw [Nat.factorization_prod hslots]
  simp only [Finsupp.finsetSum_apply]
  simp [factorization_two_slot_three, mem_binarySupport_iff]

example : Even (2 : ℕ) ∧ (localSigma 5 2).factorization 3 = 0 := by
  exact ⟨by decide, factorization_localSigma_three_of_even 5 2 (by decide)⟩
example : (localSigma 2 0).factorization 3 = 0 ∧
    (localSigma 2 1).factorization 3 = 1 := by
  norm_num [factorization_localSigma_two_three, Nat.testBit_eq_decide_div_mod_eq]

/-- Under even valuations away from two, the three-adic valuation of the
actual sum is exactly the parity bit of the two-adic exponent. -/
theorem factorization_sigma_three (n : ℕ) (hn : 0 < n)
    (he : ∀ p : ℕ, p ≠ 2 → Even (n.factorization p)) :
    (sigma n).factorization 3 = if (n.factorization 2).testBit 0 then 1 else 0 := by
  unfold sigma
  have hlocal : ∀ p ∈ n.primeFactors, localSigma p (n.factorization p) ≠ 0 := by
    intro p hp
    exact ne_of_gt (localSigma_pos p (n.factorization p))
  rw [Nat.factorization_prod hlocal]
  have hslot : ∀ p : ℕ, (localSigma p (n.factorization p)).factorization 3 =
      if p = 2 then (if (n.factorization 2).testBit 0 then 1 else 0) else 0 := by
    intro p
    by_cases hp : p = 2
    · subst p
      simp only [if_true, factorization_localSigma_two_three]
    · simp only [hp, if_false]
      exact factorization_localSigma_three_of_even p (n.factorization p) (he p hp)
  simp only [Finsupp.finsetSum_apply, hslot, Finset.sum_ite_eq']
  by_cases htwo : 2 ∈ n.primeFactors
  · simp [htwo]
  · have hnotdvd : ¬ 2 ∣ n := by
      intro hdvd
      exact htwo ((Nat.mem_primeFactors_of_ne_zero (ne_of_gt hn)).mpr ⟨by decide, hdvd⟩)
    have hzero := Nat.factorization_eq_zero_of_not_dvd hnotdvd
    simp [htwo, hzero]

private theorem even_of_even_parity_indicator (e : ℕ)
    (he : Even (if e.testBit 0 then 1 else 0)) : Even e := by
  rw [Nat.even_iff]
  rw [Nat.testBit_eq_decide_div_mod_eq] at he
  rcases Nat.mod_two_eq_zero_or_one e with hzero | hone
  · exact hzero
  · simp [hone] at he

/-- In a positive two-step infinitary superperfect pair whose odd parts are
squares, both two-adic exponents are even. The exact three-adic valuation,
not an assumed support restriction, supplies the parity obstruction. -/
theorem even_two_exponents (n m : ℕ) (hn : 0 < n)
    (hm : m = sigma n) (hcycle : sigma m = 2 * n)
    (hsn : IsSquare (oddPart n)) (hsm : IsSquare (oddPart m)) :
    Even (n.factorization 2) ∧ Even (m.factorization 2) := by
  have hmpos : 0 < m := by rw [hm]; exact sigma_pos n
  have hen := (isSquare_oddPart_iff n hn).mp hsn
  have hem := (isSquare_oddPart_iff m hmpos).mp hsm
  have hthree_n := factorization_sigma_three n hn hen
  have hthree_m := factorization_sigma_three m hmpos hem
  have hmn : Even (if (n.factorization 2).testBit 0 then 1 else 0) := by
    rw [← hthree_n, ← hm]
    exact hem 3 (by decide)
  have htwo_n : Even (n.factorization 2) :=
    even_of_even_parity_indicator (n.factorization 2) hmn
  have hmn' : Even (if (m.factorization 2).testBit 0 then 1 else 0) := by
    rw [← hthree_m, hcycle, Nat.factorization_mul (by decide) (ne_of_gt hn),
      Finsupp.add_apply]
    norm_num
    exact hen 3 (by decide)
  exact ⟨htwo_n, even_of_even_parity_indicator (m.factorization 2) hmn'⟩

/-- The square-odd-part hypotheses and the actual pair equations force both
odd prime supports into the residue class one modulo four. -/
theorem odd_prime_supports_mod_four (n m : ℕ) (hn : 0 < n)
    (hm : m = sigma n) (hcycle : sigma m = 2 * n)
    (hsn : IsSquare (oddPart n)) (hsm : IsSquare (oddPart m)) :
    (∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ n → p % 4 = 1) ∧
    (∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ m → p % 4 = 1) := by
  have hmpos : 0 < m := by rw [hm]; exact sigma_pos n
  obtain ⟨htn, htm⟩ := even_two_exponents n m hn hm hcycle hsn hsm
  have hen := (isSquare_oddPart_iff n hn).mp hsn
  have hem := (isSquare_oddPart_iff m hmpos).mp hsm
  have halln : ∀ p ∈ n.primeFactors, Even (n.factorization p) := by
    intro p hp
    by_cases htwo : p = 2
    · subst p; exact htn
    · exact hen p htwo
  have hallm : ∀ p ∈ m.primeFactors, Even (m.factorization p) := by
    intro p hp
    by_cases htwo : p = 2
    · subst p; exact htm
    · exact hem p htwo
  constructor
  · intro p hp hp2 hdvd
    have hdiv : p ∣ sigma m := by rw [hcycle]; exact dvd_mul_of_dvd_right hdvd 2
    exact prime_mod_four_of_dvd_sigma_of_even m p hallm hp hp2 hdiv
  · intro p hp hp2 hdvd
    rw [hm] at hdvd
    exact prime_mod_four_of_dvd_sigma_of_even n p halln hp hp2 hdvd

private theorem binary_product_identity (x : ℚ) (K : ℕ) :
    (1 - x) * (∏ j ∈ Finset.range K, (1 + x ^ (2 ^ j))) =
      1 - x ^ (2 ^ K) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.prod_range_succ, ← mul_assoc, ih, Nat.pow_succ, pow_mul]
    ring

private theorem higher_binary_product_identity (x : ℚ) (K : ℕ) :
    (1 - x ^ 2) * (∏ j ∈ Finset.Ico 1 (K + 1), (1 + x ^ (2 ^ j))) =
      1 - x ^ (2 ^ (K + 1)) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.prod_Ico_succ_top (by omega), ← mul_assoc, ih,
      Nat.pow_succ, pow_mul]
    ring

/-- Every finite product of higher binary factors is bounded by its telescoping
geometric envelope. There is no limit or infinite product in this estimate. -/
theorem higher_binary_product_le (x : ℚ) (hx : 0 ≤ x) (hx1 : x < 1) (K : ℕ) :
    (∏ j ∈ Finset.Ico 1 (K + 1), (1 + x ^ (2 ^ j))) ≤ 1 / (1 - x ^ 2) := by
  have hden : 0 < 1 - x ^ 2 := by nlinarith
  apply (le_div_iff₀ hden).mpr
  rw [mul_comm, higher_binary_product_identity]
  have hpow : 0 ≤ x ^ (2 ^ (K + 1)) := pow_nonneg hx _
  linarith

/-- The local abundance for any even exponent is bounded by the full geometric
square-power envelope, including the empty exponent. -/
theorem localSigma_abundance_le (p e : ℕ) (hp : 1 < p) (he : Even e) :
    (localSigma p e : ℚ) / (p : ℚ) ^ e ≤ 1 / (1 - (1 / (p : ℚ)) ^ 2) := by
  have hpq : 1 < (p : ℚ) := by exact_mod_cast hp
  have hp0 : (p : ℚ) ≠ 0 := by linarith
  have hx : 0 ≤ 1 / (p : ℚ) := by positivity
  have hx1 : 1 / (p : ℚ) < 1 := (div_lt_one (by linarith)).mpr hpq
  have hratio : (localSigma p e : ℚ) / (p : ℚ) ^ e =
      ∏ j ∈ binarySupport e, (1 + (1 / (p : ℚ)) ^ (2 ^ j)) := by
    have hprod : (∏ j ∈ binarySupport e, (p : ℚ) ^ (2 ^ j)) = (p : ℚ) ^ e := by
      rw [Finset.prod_pow_eq_pow_sum, sum_binarySupport]
    rw [← hprod]
    unfold localSigma
    push_cast
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro j hj
    rw [div_pow]
    field_simp
    simp [add_comm]
  rw [hratio]
  calc
    _ ≤ ∏ j ∈ Finset.Ico 1 (e + 1), (1 + (1 / (p : ℚ)) ^ (2 ^ j)) := by
      apply Finset.prod_le_prod_of_subset_of_one_le
      · intro j hj
        exact Finset.mem_Ico.mpr ⟨one_le_of_mem_binarySupport_of_even e j he hj,
          by have hlt := (Finset.mem_filter.mp hj).1; simp only [Finset.mem_range] at hlt; omega⟩
      · intro j hj; positivity
      · intro j hj hnot; have hpow := pow_nonneg hx (2 ^ j); linarith
    _ ≤ _ := higher_binary_product_le (1 / (p : ℚ)) hx hx1 e

private theorem progression_step_le (t : ℚ) (ht : 0 < t) (k : ℕ) :
    1 / (t + 12 * ((k : ℚ) + 1)) ^ 2 ≤
      (1 / (t + 12 * k) - 1 / (t + 12 * ((k : ℚ) + 1))) / 12 := by
  have hk : 0 ≤ (k : ℚ) := by positivity
  have ha : 0 < t + 12 * k := by positivity
  have hb : 0 < t + 12 * ((k : ℚ) + 1) := by positivity
  field_simp
  nlinarith

private theorem progression_tail_le (t : ℚ) (ht : 0 < t) (K : ℕ) :
    (∑ k ∈ Finset.range K, 1 / (t + 12 * ((k : ℚ) + 1)) ^ 2) ≤
      (1 / t - 1 / (t + 12 * K)) / 12 := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ]
    have hstep := progression_step_le t ht K
    push_cast
    linarith

/-- A finite initial segment of either covering progression has a rational
bound obtained by telescoping reciprocals, uniformly in the segment length. -/
theorem progression_sum_le (t : ℚ) (ht : 0 < t) (K : ℕ) :
    (∑ k ∈ Finset.range K, 1 / (t + 12 * k) ^ 2) ≤ 1 / t ^ 2 + 1 / (12 * t) := by
  cases K with
  | zero => simp; positivity
  | succ K =>
    rw [Finset.sum_range_succ']
    have htail := progression_tail_le t ht K
    have hrecip : 0 ≤ 1 / (t + 12 * K) := by positivity
    have hid : 1 / (12 * t) = (1 / t) / 12 := by ring
    push_cast
    simp only [mul_zero, add_zero]
    rw [hid]
    linarith

/-- All primes one modulo four lie in six explicit small primes or in the
two arithmetic progressions beginning at 53 and 61 with step twelve. -/
theorem prime_mod_four_cover (p : ℕ) (hp : p.Prime) (hmod : p % 4 = 1) :
    p ∈ ({5, 13, 17, 29, 37, 41} : Finset ℕ) ∨
      (∃ k : ℕ, p = 53 + 12 * k) ∨ (∃ k : ℕ, p = 61 + 12 * k) := by
  by_cases hsmall : p < 53
  · interval_cases p <;> norm_num at *
  · have h3 : p % 3 ≠ 0 := by
      intro hzero
      have hdvd : 3 ∣ p := Nat.dvd_of_mod_eq_zero hzero
      have heq := hp.eq_one_or_self_of_dvd 3 hdvd
      omega
    have hres : p % 12 = 1 ∨ p % 12 = 5 := by omega
    rcases hres with hone | hfive
    · right; right
      refine ⟨(p - 61) / 12, ?_⟩
      omega
    · right; left
      refine ⟨(p - 53) / 12, ?_⟩
      omega

example : Nat.Prime 61 ∧ (61 : ℕ) % 4 = 1 := by decide
example : (∑ k ∈ Finset.range 0, 1 / ((53 : ℚ) + 12 * k) ^ 2) = 0 := by simp

private theorem sum_union_le_nonneg (s t : Finset ℕ) (f : ℕ → ℚ)
    (hf : ∀ i : ℕ, 0 ≤ f i) :
    (∑ i ∈ s ∪ t, f i) ≤ (∑ i ∈ s, f i) + ∑ i ∈ t, f i := by
  have hid : (∑ i ∈ s ∪ t, f i) + (∑ i ∈ s ∩ t, f i) =
      (∑ i ∈ s, f i) + ∑ i ∈ t, f i := Finset.sum_union_inter
  have hnon : 0 ≤ ∑ i ∈ s ∩ t, f i := Finset.sum_nonneg (fun i hi => hf i)
  linarith

/-- Any finite set of primes one modulo four has reciprocal-square sum below
one eighteenth. The covering progressions are bounded uniformly, without any
cardinality or largest-prime hypothesis on the given set. -/
theorem prime_reciprocal_square_sum_lt (C : Finset ℕ)
    (hC : ∀ p ∈ C, p.Prime ∧ p % 4 = 1) :
    (∑ p ∈ C, 1 / (p : ℚ) ^ 2) < 1 / 18 := by
  let E : Finset ℕ := {5, 13, 17, 29, 37, 41}
  let K : ℕ := C.sup id + 1
  let A : Finset ℕ := (Finset.range K).image (fun k => 53 + 12 * k)
  let B : Finset ℕ := (Finset.range K).image (fun k => 61 + 12 * k)
  have hcover : C ⊆ E ∪ A ∪ B := by
    intro p hp
    have hpK : p < K := by
      have hbound : p ≤ C.sup id := Finset.le_sup (f := id) hp
      dsimp only [K]
      omega
    rcases prime_mod_four_cover p (hC p hp).1 (hC p hp).2 with he | ha | hb
    · exact Finset.mem_union_left B (Finset.mem_union_left A he)
    · obtain ⟨k, hk⟩ := ha
      have hkr : k ∈ Finset.range K := Finset.mem_range.mpr (by omega)
      exact Finset.mem_union_left B (Finset.mem_union_right E
        (Finset.mem_image.mpr ⟨k, hkr, hk.symm⟩))
    · obtain ⟨k, hk⟩ := hb
      have hkr : k ∈ Finset.range K := Finset.mem_range.mpr (by omega)
      exact Finset.mem_union_right (E ∪ A) (Finset.mem_image.mpr ⟨k, hkr, hk.symm⟩)
  have hnon : ∀ p : ℕ, 0 ≤ 1 / (p : ℚ) ^ 2 := by intro p; positivity
  have hbound := Finset.sum_le_sum_of_subset_of_nonneg hcover
    (fun p hp hnot => hnon p)
  have hunion := sum_union_le_nonneg (E ∪ A) B (fun p => 1 / (p : ℚ) ^ 2) hnon
  have hunion' := sum_union_le_nonneg E A (fun p => 1 / (p : ℚ) ^ 2) hnon
  have hA : (∑ p ∈ A, 1 / (p : ℚ) ^ 2) ≤ 1 / (53 : ℚ) ^ 2 + 1 / (12 * 53) := by
    dsimp only [A]
    rw [Finset.sum_image (by intro a ha b hb hab; dsimp only at hab; omega)]
    push_cast
    exact progression_sum_le 53 (by norm_num) K
  have hB : (∑ p ∈ B, 1 / (p : ℚ) ^ 2) ≤ 1 / (61 : ℚ) ^ 2 + 1 / (12 * 61) := by
    dsimp only [B]
    rw [Finset.sum_image (by intro a ha b hb hab; dsimp only at hab; omega)]
    push_cast
    exact progression_sum_le 61 (by norm_num) K
  have hsmall : (∑ p ∈ E, 1 / (p : ℚ) ^ 2) +
      (1 / (53 : ℚ) ^ 2 + 1 / (12 * 53)) +
      (1 / (61 : ℚ) ^ 2 + 1 / (12 * 61)) < 1 / 18 := by
    norm_num [E]
  linarith

example : (∑ p ∈ ({5, 13} : Finset ℕ), 1 / (p : ℚ) ^ 2) < 1 / 18 := by norm_num

private theorem one_sub_sum_le_prod (C : Finset ℕ) (x : ℕ → ℚ)
    (hx : ∀ p ∈ C, 0 ≤ x p ∧ x p ≤ 1) :
    1 - (∑ p ∈ C, x p) ≤ ∏ p ∈ C, (1 - x p) := by
  induction C using Finset.induction_on with
  | empty => simp
  | @insert p C hp ih =>
    have hxp := hx p (Finset.mem_insert_self p C)
    have hC : ∀ q ∈ C, 0 ≤ x q ∧ x q ≤ 1 := by
      intro q hq
      exact hx q (Finset.mem_insert_of_mem hq)
    have hprod := mul_le_mul_of_nonneg_left (ih hC) (by linarith : 0 ≤ 1 - x p)
    have hsum : 0 ≤ ∑ q ∈ C, x q := Finset.sum_nonneg (fun q hq => (hC q hq).1)
    rw [Finset.sum_insert hp, Finset.prod_insert hp]
    nlinarith

/-- The product of geometric envelopes over an arbitrary finite set of primes
one modulo four is strictly smaller than eighteen seventeenths. -/
theorem odd_prime_envelope_prod_lt (C : Finset ℕ)
    (hC : ∀ p ∈ C, p.Prime ∧ p % 4 = 1) :
    (∏ p ∈ C, 1 / (1 - (1 / (p : ℚ)) ^ 2)) < 18 / 17 := by
  have hx : ∀ p ∈ C, 0 ≤ (1 / (p : ℚ)) ^ 2 ∧ (1 / (p : ℚ)) ^ 2 ≤ 1 := by
    intro p hp
    have hgt : 1 < (p : ℚ) := by exact_mod_cast (hC p hp).1.one_lt
    have hrec : 0 ≤ 1 / (p : ℚ) := by positivity
    have hrec1 : 1 / (p : ℚ) < 1 := (div_lt_one (by linarith)).mpr hgt
    constructor
    · positivity
    · nlinarith
  have hsum := prime_reciprocal_square_sum_lt C hC
  have hprod := one_sub_sum_le_prod C (fun p => (1 / (p : ℚ)) ^ 2) hx
  have hsame : (∑ p ∈ C, (1 / (p : ℚ)) ^ 2) = ∑ p ∈ C, 1 / (p : ℚ) ^ 2 := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [div_pow, one_pow]
  rw [hsame] at hprod
  have hbound : 17 / 18 < ∏ p ∈ C, (1 - (1 / (p : ℚ)) ^ 2) := by linarith
  have hpos : 0 < ∏ p ∈ C, (1 - (1 / (p : ℚ)) ^ 2) := by linarith
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const_one]
  apply (div_lt_iff₀ hpos).mpr
  linarith

example : (∏ p ∈ ({5, 13} : Finset ℕ), 1 / (1 - (1 / (p : ℚ)) ^ 2)) < 18 / 17 := by
  norm_num

example : (1 : ℕ) < 5 ∧ Even (2 : ℕ) := by decide
example : 0 ≤ (1 / 5 : ℚ) ∧ (1 / 5 : ℚ) < 1 := by norm_num
example : ∀ p ∈ ({5, 13} : Finset ℕ), p.Prime ∧ p % 4 = 1 := by
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl <;> norm_num

/-- For a positive integer, its infinitary abundance factors into the canonical
local abundances at precisely its prime support. -/
theorem sigma_div_eq_prod (n : ℕ) (hn : 0 < n) :
    (sigma n : ℚ) / (n : ℚ) =
      ∏ p ∈ n.primeFactors, (localSigma p (n.factorization p) : ℚ) /
        (p : ℚ) ^ n.factorization p := by
  have hden : (n : ℚ) = ∏ p ∈ n.primeFactors, (p : ℚ) ^ n.factorization p := by
    exact_mod_cast Nat.prod_primeFactors_pow_factorization (ne_of_gt hn)
  rw [hden]
  unfold sigma
  push_cast
  rw [Finset.prod_div_distrib]

/-- Even valuations and residue-one odd prime support force infinitary abundance
strictly below twenty-four seventeenths, without a support-size bound. -/
theorem sigma_abundance_lt (n : ℕ) (hn : 0 < n)
    (he : ∀ p ∈ n.primeFactors, Even (n.factorization p))
    (hmod : ∀ p ∈ n.primeFactors, p ≠ 2 → p % 4 = 1) :
    (sigma n : ℚ) / (n : ℚ) < 24 / 17 := by
  let C : Finset ℕ := n.primeFactors.erase 2
  let g : ℕ → ℚ := fun p => 1 / (1 - (1 / (p : ℚ)) ^ 2)
  have hprime : ∀ p ∈ n.primeFactors, p.Prime := by
    intro p hp
    exact (Nat.mem_primeFactors.mp hp).1
  have hC : ∀ p ∈ C, p.Prime ∧ p % 4 = 1 := by
    intro p hp
    have hmem := Finset.mem_erase.mp hp
    exact ⟨hprime p hmem.2, hmod p hmem.2 hmem.1⟩
  have hodd : (∏ p ∈ C, g p) < 18 / 17 := odd_prime_envelope_prod_lt C hC
  have hnon : 0 ≤ ∏ p ∈ C, g p := by
    apply Finset.prod_nonneg
    intro p hp
    have hgt : 1 < (p : ℚ) := by exact_mod_cast (hC p hp).1.one_lt
    have hrec : 0 ≤ 1 / (p : ℚ) := by positivity
    have hrec1 : 1 / (p : ℚ) < 1 := (div_lt_one (by linarith)).mpr hgt
    dsimp only [g]
    have hden : 0 < 1 - (1 / (p : ℚ)) ^ 2 := by nlinarith
    positivity
  have hgeom : (∏ p ∈ n.primeFactors, g p) ≤ (4 / 3) * ∏ p ∈ C, g p := by
    by_cases htwo : 2 ∈ n.primeFactors
    · have hid := Finset.prod_erase_mul n.primeFactors g htwo
      have hg : g 2 = 4 / 3 := by norm_num [g]
      change (∏ p ∈ n.primeFactors, g p) ≤ (4 / 3) *
        ∏ p ∈ n.primeFactors.erase 2, g p
      rw [← hid, hg, mul_comm]
    · have hCeq : C = n.primeFactors := by simp [C, htwo]
      rw [← hCeq]
      nlinarith
  have hlocal : (sigma n : ℚ) / (n : ℚ) ≤ ∏ p ∈ n.primeFactors, g p := by
    rw [sigma_div_eq_prod n hn]
    apply Finset.prod_le_prod
    · intro p hp
      have hpq : 0 < (p : ℚ) := by exact_mod_cast (hprime p hp).pos
      have hsig : 0 < (localSigma p (n.factorization p) : ℚ) := by
        exact_mod_cast localSigma_pos p (n.factorization p)
      positivity
    · intro p hp
      exact localSigma_abundance_le p (n.factorization p) (hprime p hp).one_lt (he p hp)
  linarith

example : 0 < (25 : ℕ) ∧
    (∀ p ∈ (25 : ℕ).primeFactors, Even ((25 : ℕ).factorization p)) ∧
    (∀ p ∈ (25 : ℕ).primeFactors, p ≠ 2 → p % 4 = 1) := by
  have hfive : Nat.Prime 5 := by decide
  have hsupport : (25 : ℕ).primeFactors = {5} := by
    change (5 ^ 2 : ℕ).primeFactors = {5}
    rw [Nat.primeFactors_pow 5 (by decide)]
    simp [hfive]
  have hval : (25 : ℕ).factorization 5 = 2 := by
    change (5 ^ 2 : ℕ).factorization 5 = 2
    rw [hfive.factorization_pow]
    simp
  norm_num [hsupport, hval]

/-- A positive even canonical infinitary superperfect pair cannot have square
odd parts on both sides. The two actual divisor-sum equations force abundance
product two, while square odd parts force each abundance below 24/17. -/
theorem not_both_isSquare_oddPart (n m : ℕ) (hn : 0 < n) (heven : 2 ∣ n)
    (hm : m = sigma n) (hcycle : sigma m = 2 * n) :
    ¬ (IsSquare (oddPart n) ∧ IsSquare (oddPart m)) := by
  rintro ⟨hsn, hsm⟩
  have hn2 : 2 ≤ n := Nat.le_of_dvd hn heven
  have hnq : 0 < (n : ℚ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hn2)
  have hmpos : 0 < m := by rw [hm]; exact sigma_pos n
  have hmq : 0 < (m : ℚ) := by exact_mod_cast hmpos
  obtain ⟨htn, htm⟩ := even_two_exponents n m hn hm hcycle hsn hsm
  obtain ⟨hmodn, hmodm⟩ := odd_prime_supports_mod_four n m hn hm hcycle hsn hsm
  have hen := (isSquare_oddPart_iff n hn).mp hsn
  have hem := (isSquare_oddPart_iff m hmpos).mp hsm
  have halln : ∀ p ∈ n.primeFactors, Even (n.factorization p) := by
    intro p hp
    by_cases hp2 : p = 2
    · subst p; exact htn
    · exact hen p hp2
  have hallm : ∀ p ∈ m.primeFactors, Even (m.factorization p) := by
    intro p hp
    by_cases hp2 : p = 2
    · subst p; exact htm
    · exact hem p hp2
  have hresn : ∀ p ∈ n.primeFactors, p ≠ 2 → p % 4 = 1 := by
    intro p hp hp2
    obtain ⟨hprime, hdvd, hne⟩ := Nat.mem_primeFactors.mp hp
    exact hmodn p hprime hp2 hdvd
  have hresm : ∀ p ∈ m.primeFactors, p ≠ 2 → p % 4 = 1 := by
    intro p hp hp2
    obtain ⟨hprime, hdvd, hne⟩ := Nat.mem_primeFactors.mp hp
    exact hmodm p hprime hp2 hdvd
  have hboundn := sigma_abundance_lt n hn halln hresn
  have hboundm := sigma_abundance_lt m hmpos hallm hresm
  have hprod : ((sigma n : ℚ) / (n : ℚ)) * ((sigma m : ℚ) / (m : ℚ)) = 2 := by
    rw [← hm, hcycle, Nat.cast_mul, Nat.cast_ofNat]
    field_simp
  have hratio_m : 0 < (sigma m : ℚ) / (m : ℚ) := by
    have hsig : 0 < (sigma m : ℚ) := by exact_mod_cast sigma_pos m
    exact div_pos hsig hmq
  have hfirst := mul_lt_mul_of_pos_right hboundn hratio_m
  have hsecond := mul_lt_mul_of_pos_left hboundm (by norm_num : (0 : ℚ) < 24 / 17)
  have himpossible : (2 : ℚ) < (24 / 17) * (24 / 17) := by
    rw [← hprod]
    exact hfirst.trans hsecond
  norm_num at himpossible

/-- A positive number with nonsquare odd part has an odd prime divisor whose
valuation is odd. The witness belongs to the actual factorization support. -/
theorem exists_odd_prime_odd_factorization_of_not_isSquare_oddPart (n : ℕ)
    (hn : 0 < n) (hnot : ¬ IsSquare (oddPart n)) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ n ∧ Odd (n.factorization p) := by
  classical
  have hnot_even : ¬ ∀ p : ℕ, p ≠ 2 → Even (n.factorization p) := by
    intro he
    exact hnot ((isSquare_oddPart_iff n hn).mpr he)
  push Not at hnot_even
  obtain ⟨p, hp2, he⟩ := hnot_even
  have hodd : Odd (n.factorization p) := (Nat.even_or_odd (n.factorization p)).resolve_left he
  have hval : n.factorization p ≠ 0 := by
    intro hzero
    apply he
    rw [hzero]
    exact ⟨0, rfl⟩
  have hmem : p ∈ n.primeFactors := by
    rw [← Nat.support_factorization]
    exact Finsupp.mem_support_iff.mpr hval
  obtain ⟨hprime, hdvd, hne⟩ := Nat.mem_primeFactors.mp hmem
  exact ⟨p, hprime, hp2, hdvd, hodd⟩

example : 0 < (3 : ℕ) ∧ ¬ IsSquare (oddPart 3) := by
  constructor
  · decide
  · intro hs
    have he := (isSquare_oddPart_iff 3 (by decide)).mp hs 3 (by decide)
    norm_num at he

/-- Every positive even canonical infinitary superperfect pair has an odd prime
whose exponent is odd in at least one member, with divisibility recorded on
that same member. No restriction on the size of either prime support is assumed. -/
theorem exists_odd_prime_odd_factorization (n m : ℕ) (hn : 0 < n) (heven : 2 ∣ n)
    (hm : m = sigma n) (hcycle : sigma m = 2 * n) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
      ((p ∣ n ∧ Odd (n.factorization p)) ∨ (p ∣ m ∧ Odd (m.factorization p))) := by
  classical
  have hnot := not_both_isSquare_oddPart n m hn heven hm hcycle
  by_cases hsn : IsSquare (oddPart n)
  · have hmpos : 0 < m := by rw [hm]; exact sigma_pos n
    have hsmnot : ¬ IsSquare (oddPart m) := by
      intro hsm
      exact hnot ⟨hsn, hsm⟩
    obtain ⟨p, hprime, hp2, hdvd, hodd⟩ :=
      exists_odd_prime_odd_factorization_of_not_isSquare_oddPart m hmpos hsmnot
    exact ⟨p, hprime, hp2, Or.inr ⟨hdvd, hodd⟩⟩
  · obtain ⟨p, hprime, hp2, hdvd, hodd⟩ :=
      exists_odd_prime_odd_factorization_of_not_isSquare_oddPart n hn hsn
    exact ⟨p, hprime, hp2, Or.inl ⟨hdvd, hodd⟩⟩

example : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
    ((p ∣ 2 ∧ Odd ((2 : ℕ).factorization p)) ∨
      (p ∣ 3 ∧ Odd ((3 : ℕ).factorization p))) := by
  obtain ⟨hn, heven, hm, hcycle⟩ := ambient_two_three
  exact exists_odd_prime_odd_factorization 2 3 hn heven hm hcycle

end InfinitarySuperperfect
