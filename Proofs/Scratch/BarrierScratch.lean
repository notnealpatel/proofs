import Enumerative.PowerOfTwoDigitsCount
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Algebra.Group.Subgroup.Finite

set_option autoImplicit false
set_option exponentiation.threshold 2000

namespace Scratch406

open Erdos406

-- §0 ground truths
#eval Nat.digits 7 (18 ^ 3)   -- expect [1,0,0,3,2] (brief said [1,0,0,3,2,2])
#eval 18 ^ 3 % 343            -- 1
#eval 18 ^ 3 % 2401           -- 1030
#eval 18 ^ 3 % 49             -- 1
#eval 18 ^ 3 % 7              -- 1
#eval Nat.digits 7 18         -- [4,2]
#eval Nat.digits 7 324        -- [2,4,6]
#eval Nat.digits 7 1          -- [1]
#eval 2 ^ 6 % 27              -- 10
#eval Nat.digits 3 10         -- [1,0,1]
#eval 18 ^ 5 % 343            -- 324?

example : ((Finset.range 18).filter fun n => SieveAt 2 n) = {0, 2, 6, 8, 12, 14} := by
  decide
example : ((Finset.range 18).filter fun n => SieveAt 3 n) = {0, 2, 6, 8} := by decide
example : (18 : ℕ) ^ 3 % 343 = 1 ∧ (18 : ℕ) ^ 3 % 49 = 1 ∧ (18 : ℕ) ^ 3 % 7 = 1 ∧
    (18 : ℕ) ^ 3 % 2401 = 1030 := by decide
example : Nat.digits 7 (18 ^ 3) = [1, 0, 0, 3, 2] := by decide
example : 18 ^ 5 % 343 = 324 := by decide

-- §1 helper: odd exponents mod 3
theorem two_pow_odd_mod_three {k : ℕ} (hk : Odd k) : 2 ^ k % 3 = 2 := by
  obtain ⟨m, rfl⟩ := hk
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

-- §2 the ZMod bridge
theorem two_pow_zmod_eq_one_iff (j d : ℕ) :
    (2 : ZMod (3 ^ (j + 1))) ^ d = 1 ↔ 2 ^ d % 3 ^ (j + 1) = 1 % 3 ^ (j + 1) := by
  have h := ZMod.natCast_eq_natCast_iff' (2 ^ d) 1 (3 ^ (j + 1))
  simpa using h

-- §3 the order
theorem orderOf_two_zmod_three_pow (j : ℕ) :
    orderOf (2 : ZMod (3 ^ (j + 1))) = 2 * 3 ^ j := by
  refine orderOf_eq_of_pow_and_pow_div_prime (by positivity) ?_ ?_
  · rw [two_pow_zmod_eq_one_iff]
    exact two_pow_two_mul_three_pow_mod j
  · intro p hp hpd
    have hp23 : p = 2 ∨ p = 3 := by
      rcases (Nat.Prime.dvd_mul hp).mp hpd with h2 | h3
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
      · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
          (hp.dvd_of_dvd_pow h3))
    rcases hp23 with rfl | rfl
    · -- p = 2 : 2 ^ (3 ^ j) ≢ 1, because 3^j is odd so 2^(3^j) ≡ 2 (mod 3)
      rw [Nat.mul_div_cancel_left _ (by norm_num : (0:ℕ) < 2)]
      intro heq
      rw [two_pow_zmod_eq_one_iff] at heq
      have hdvd : (3 : ℕ) ∣ 3 ^ (j + 1) := dvd_pow_self 3 (Nat.succ_ne_zero j)
      have h1 : 2 ^ 3 ^ j % 3 = 1 % 3 ^ (j + 1) % 3 := by
        rw [← Nat.mod_mod_of_dvd _ hdvd, heq]
      have h2 : 2 ^ 3 ^ j % 3 = 2 := two_pow_odd_mod_three (Odd.pow ⟨1, by norm_num⟩)
      rw [Nat.mod_mod_of_dvd _ hdvd] at h1
      omega
    · -- p = 3 : need j = i + 1; the crux at i gives 2^(2·3^i) = 1 + c·3^(i+1), 3 ∤ c
      rcases j with - | i
      · norm_num at hpd
      · have hdiv : 2 * 3 ^ (i + 1) / 3 = 2 * 3 ^ i := by
          rw [pow_succ, ← mul_assoc, Nat.mul_div_cancel _ (by norm_num : (0:ℕ) < 3)]
        rw [hdiv]
        intro heq
        rw [two_pow_zmod_eq_one_iff] at heq
        obtain ⟨c, hc, hc3⟩ := two_pow_two_mul_three_pow i
        rw [hc] at heq
        -- heq : (1 + c * 3 ^ (i+1)) % 3 ^ (i+2) = 1 % 3 ^ (i+2)
        have hdvd2 : 3 ^ (i + 2) ∣ c * 3 ^ (i + 1) := by
          have hmodeq : (1 + c * 3 ^ (i + 1)) ≡ 1 [MOD 3 ^ (i + 2)] := heq
          have h := (Nat.modEq_iff_dvd' (Nat.le_add_right 1 _)).mp hmodeq.symm
          simpa using h
        have h3c : (3 : ℕ) ∣ c := by
          have h1 : 3 ^ (i + 1) * 3 ∣ 3 ^ (i + 1) * c := by
            rw [← pow_succ] at *
            calc 3 ^ (i + 2) ∣ c * 3 ^ (i + 1) := hdvd2
              _ = 3 ^ (i + 1) * c := by ring
          exact (Nat.mul_dvd_mul_iff_left (by positivity : (0:ℕ) < 3 ^ (i + 1))).mp h1
        exact hc3 h3c

-- §4 the ℕ iff
theorem two_pow_mod_eq_one_iff (j d : ℕ) :
    2 ^ d % 3 ^ (j + 1) = 1 % 3 ^ (j + 1) ↔ 2 * 3 ^ j ∣ d := by
  rw [← two_pow_zmod_eq_one_iff, ← orderOf_two_zmod_three_pow j,
    orderOf_dvd_iff_pow_eq_one]

-- §5 unit surjectivity
theorem exists_two_pow_mod_eq_of_not_dvd (j v : ℕ) (hv : ¬ 3 ∣ v) :
    ∃ n : ℕ, 2 ^ n % 3 ^ (j + 1) = v % 3 ^ (j + 1) := by
  haveI : NeZero (3 ^ (j + 1)) := NeZero.of_pos (by positivity)
  have hcop2 : Nat.Coprime 2 (3 ^ (j + 1)) :=
    Nat.Coprime.pow_right _ (by norm_num)
  have hcopv : Nat.Coprime v (3 ^ (j + 1)) :=
    (Nat.Coprime.pow_left _
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hv)).symm
  have hord : orderOf (ZMod.unitOfCoprime 2 hcop2) = 2 * 3 ^ j := by
    rw [← orderOf_units, ZMod.coe_unitOfCoprime]
    have : ((2 : ℕ) : ZMod (3 ^ (j + 1))) = (2 : ZMod (3 ^ (j + 1))) := by push_cast; rfl
    rw [this, orderOf_two_zmod_three_pow]
  have hcard : Nat.card (ZMod (3 ^ (j + 1)))ˣ = 2 * 3 ^ j := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime_pow Nat.prime_three (Nat.succ_pos j), Nat.succ_sub_one]
    norm_num [mul_comm]
  have htop : Subgroup.zpowers (ZMod.unitOfCoprime 2 hcop2) = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hord, hcard]
  have hmem : ZMod.unitOfCoprime v hcopv ∈
      Submonoid.powers (ZMod.unitOfCoprime 2 hcop2) := by
    rw [mem_powers_iff_mem_zpowers, htop]
    exact Subgroup.mem_top _
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp hmem
  refine ⟨n, ?_⟩
  have hcast : ((2 ^ n : ℕ) : ZMod (3 ^ (j + 1))) = ((v : ℕ) : ZMod (3 ^ (j + 1))) := by
    have hval := congrArg (Units.val) hn
    simpa [ZMod.coe_unitOfCoprime] using hval
  exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp hcast

-- §6 digit membership bridge
theorem div_pow_mod_mem_digits {b m i : ℕ} (hb : 1 < b) (him : b ^ i ≤ m) :
    m / b ^ i % b ∈ Nat.digits b m := by
  have hlen : i < (Nat.digits b m).length := by
    by_contra hcon
    have hlt : m < b ^ i :=
      (Nat.digits_length_le_iff hb m).mp (Nat.le_of_not_lt hcon)
    omega
  rw [← Nat.getD_digits m i (by omega)]
  rw [List.getD_eq_getElem _ 0 hlen]
  exact List.getElem_mem hlen

-- §7 generic-base digit congruence
theorem digit_eq_digit_of_mod_pow_eq_base {b m m' : ℕ} (D : ℕ)
    (h : m % b ^ D = m' % b ^ D) {i : ℕ} (hi : i < D) :
    m / b ^ i % b = m' / b ^ i % b := by
  have key : ∀ x : ℕ, x / b ^ i % b = x % b ^ (i + 1) / b ^ i := fun x => by
    rw [pow_succ, Nat.mod_mul_right_div_self]
  have hdvd : b ^ (i + 1) ∣ b ^ D := pow_dvd_pow b (by omega)
  rw [key, key, ← Nat.mod_mod_of_dvd m hdvd, h, Nat.mod_mod_of_dvd m' hdvd]

-- §8 generic periodicity (parent's proof, base generalized)
theorem pow_mod_eq_of_pow_mod_one {a M d : ℕ} (hd : a ^ d % M = 1 % M) (n : ℕ) :
    a ^ n % M = a ^ (n % d) % M := by
  conv_lhs => rw [← Nat.div_add_mod n d, pow_add, pow_mul]
  rw [Nat.mul_mod, Nat.pow_mod, hd, ← Nat.pow_mod, one_pow, ← Nat.mul_mod, one_mul]

end Scratch406

namespace Part2
open Erdos406 Scratch406

-- §9 B2 realization
theorem sieveAt_iff_mod_mem_sieveClasses (j n : ℕ) :
    SieveAt (j + 1) n ↔ n % (2 * 3 ^ j) ∈ sieveClasses j := by
  constructor
  · exact mod_mem_sieveClasses_of_sieveAt
  · intro h
    obtain ⟨-, hs⟩ := mem_sieveClasses.mp h
    exact (sieveAt_mod_period j n).mpr hs

theorem sieveAt_of_mem_sieveClasses_of_modEq {j r : ℕ} (hr : r ∈ sieveClasses j)
    {n : ℕ} (hn : n ≡ r [MOD 2 * 3 ^ j]) : SieveAt (j + 1) n := by
  obtain ⟨hrlt, hrs⟩ := mem_sieveClasses.mp hr
  have hmod : n % (2 * 3 ^ j) = r := by
    have h' : n % (2 * 3 ^ j) = r % (2 * 3 ^ j) := hn
    rwa [Nat.mod_eq_of_lt hrlt] at h'
  rw [sieveAt_mod_period, hmod]
  exact hrs

-- §10 B3
theorem sieveAt_zero (D : ℕ) : SieveAt D 0 := by
  intro i _
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · norm_num
  · have h1 : 1 < 3 ^ i := Nat.one_lt_pow (by omega) (by norm_num)
    norm_num [Nat.div_eq_of_lt h1]

theorem zero_mem_sieveClasses (j : ℕ) : 0 ∈ sieveClasses j :=
  mem_sieveClasses.mpr ⟨by positivity, sieveAt_zero _⟩

theorem setOf_sieveAt_infinite (j : ℕ) : {n : ℕ | SieveAt (j + 1) n}.Infinite :=
  Set.infinite_of_injective_forall_mem (f := fun k : ℕ => k * (2 * 3 ^ j))
    (fun a b hab => Nat.eq_of_mul_eq_mul_right (by positivity) hab)
    (fun k => sieveAt_of_mem_sieveClasses_of_modEq (zero_mem_sieveClasses j)
      (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_left _ _)))

theorem card_range_mul_filter_sieveAt (j m : ℕ) :
    ((Finset.range (m * (2 * 3 ^ j))).filter fun n => SieveAt (j + 1) n).card
      = m * 2 ^ j := by
  have hP : 0 < 2 * 3 ^ j := by positivity
  have hcard : ((Finset.range (m * (2 * 3 ^ j))).filter fun n => SieveAt (j + 1) n).card
      = (sieveClasses j ×ˢ Finset.range m).card := by
    refine Finset.card_bij' (fun n _ => (n % (2 * 3 ^ j), n / (2 * 3 ^ j)))
      (fun p _ => p.1 + p.2 * (2 * 3 ^ j)) ?_ ?_ ?_ ?_
    · intro n hn
      obtain ⟨hnr, hns⟩ := Finset.mem_filter.mp hn
      rw [Finset.mem_range] at hnr
      refine Finset.mem_product.mpr ⟨mod_mem_sieveClasses_of_sieveAt hns,
        Finset.mem_range.mpr ?_⟩
      rw [Nat.div_lt_iff_lt_mul hP]
      exact hnr
    · intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      rw [Finset.mem_range] at hp2
      obtain ⟨hplt, -⟩ := mem_sieveClasses.mp hp1
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
      · have hstep : p.1 + p.2 * (2 * 3 ^ j) < (1 + p.2) * (2 * 3 ^ j) := by
          rw [add_mul, one_mul]
          omega
        exact lt_of_lt_of_le hstep (Nat.mul_le_mul_right _ (by omega))
      · exact sieveAt_of_mem_sieveClasses_of_modEq hp1
          (show (p.1 + p.2 * (2 * 3 ^ j)) % (2 * 3 ^ j) = p.1 % (2 * 3 ^ j) from
            Nat.add_mul_mod_self_right p.1 p.2 (2 * 3 ^ j))
    · intro n hn
      exact Nat.mod_add_div' n (2 * 3 ^ j)
    · intro p hp
      obtain ⟨hp1, -⟩ := Finset.mem_product.mp hp
      obtain ⟨hplt, -⟩ := mem_sieveClasses.mp hp1
      have h1 : (p.1 + p.2 * (2 * 3 ^ j)) % (2 * 3 ^ j) = p.1 := by
        rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hplt]
      have h2 : (p.1 + p.2 * (2 * 3 ^ j)) / (2 * 3 ^ j) = p.2 := by
        rw [Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt hplt, Nat.zero_add]
      rw [h1, h2]
  rw [hcard, Finset.card_product, card_sieveClasses, Finset.card_range, mul_comm]

-- §11 B4 corollaries
theorem exists_two_pow_mod_eq (j v : ℕ) (hlt : v < 3 ^ (j + 1)) (hv : ¬ 3 ∣ v) :
    ∃ n : ℕ, 2 ^ n % 3 ^ (j + 1) = v := by
  obtain ⟨n, hn⟩ := exists_two_pow_mod_eq_of_not_dvd j v hv
  exact ⟨n, by rw [hn, Nat.mod_eq_of_lt hlt]⟩

theorem exists_two_pow_mod_eq_of_base3ZeroOne (j v : ℕ) (hlt : v < 3 ^ (j + 1))
    (hv1 : v % 3 = 1) (hdig : Base3ZeroOne v) :
    ∃ n : ℕ, 2 ^ n % 3 ^ (j + 1) = v ∧ SieveAt (j + 1) n := by
  obtain ⟨n, hn⟩ := exists_two_pow_mod_eq j v hlt (by omega)
  refine ⟨n, hn, fun i hi => ?_⟩
  have hvmod : 2 ^ n % 3 ^ (j + 1) = v % 3 ^ (j + 1) := by
    rw [hn, Nat.mod_eq_of_lt hlt]
  rw [digit_eq_digit_of_mod_pow_eq (j + 1) hvmod hi]
  exact (base3ZeroOne_iff_forall_index v).mp hdig i

-- §12 B5
def Base7TwoFour (m : ℕ) : Prop := ∀ d ∈ Nat.digits 7 m, d = 2 ∨ d = 4

instance (m : ℕ) : Decidable (Base7TwoFour m) := by
  unfold Base7TwoFour; infer_instance

theorem not_base7TwoFour_eighteen_pow_of_three_le {n : ℕ} (hn : 3 ≤ n) :
    ¬ Base7TwoFour (18 ^ n) := by
  intro h
  have hper : 18 ^ n % 7 ^ 3 = 18 ^ (n % 3) % 7 ^ 3 :=
    pow_mod_eq_of_pow_mod_one (by decide) n
  have h49 : 7 ^ 2 ≤ 18 ^ n :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn)
  rcases (by omega : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2) with h0 | h1 | h2
  · have hm : 18 ^ n % 7 ^ 3 = 1 % 7 ^ 3 := by rw [hper, h0, pow_zero]
    have hd : 18 ^ n / 7 ^ 0 % 7 = 1 / 7 ^ 0 % 7 :=
      digit_eq_digit_of_mod_pow_eq_base 3 hm (by norm_num)
    have hmem : 18 ^ n / 7 ^ 0 % 7 ∈ Nat.digits 7 (18 ^ n) :=
      div_pow_mod_mem_digits (by norm_num)
        (le_trans (by norm_num) (Nat.one_le_pow _ _ (by norm_num)))
    have hval : (1 : ℕ) / 7 ^ 0 % 7 = 1 := by norm_num
    rw [hd, hval] at hmem
    rcases h 1 hmem with h' | h' <;> omega
  · have hm : 18 ^ n % 7 ^ 3 = 18 % 7 ^ 3 := by rw [hper, h1, pow_one]
    have hd : 18 ^ n / 7 ^ 2 % 7 = 18 / 7 ^ 2 % 7 :=
      digit_eq_digit_of_mod_pow_eq_base 3 hm (by norm_num)
    have hmem : 18 ^ n / 7 ^ 2 % 7 ∈ Nat.digits 7 (18 ^ n) :=
      div_pow_mod_mem_digits (by norm_num) h49
    have hval : (18 : ℕ) / 7 ^ 2 % 7 = 0 := by norm_num
    rw [hd, hval] at hmem
    rcases h 0 hmem with h' | h' <;> omega
  · have hm : 18 ^ n % 7 ^ 3 = 324 % 7 ^ 3 := by
      rw [hper, h2]
      norm_num
    have hd : 18 ^ n / 7 ^ 2 % 7 = 324 / 7 ^ 2 % 7 :=
      digit_eq_digit_of_mod_pow_eq_base 3 hm (by norm_num)
    have hmem : 18 ^ n / 7 ^ 2 % 7 ∈ Nat.digits 7 (18 ^ n) :=
      div_pow_mod_mem_digits (by norm_num) h49
    have hval : (324 : ℕ) / 7 ^ 2 % 7 = 6 := by norm_num
    rw [hd, hval] at hmem
    rcases h 6 hmem with h' | h' <;> omega

theorem base7TwoFour_eighteen_pow_iff (n : ℕ) : Base7TwoFour (18 ^ n) ↔ n = 1 := by
  constructor
  · intro h
    rcases n with - | - | - | k
    · exact absurd h (by decide)
    · rfl
    · exact absurd h (by decide)
    · exact absurd h (not_base7TwoFour_eighteen_pow_of_three_le (by omega))
  · rintro rfl
    decide

theorem eighteen_wieferich_window :
    18 ^ 3 % 7 = 1 ∧ 18 ^ 3 % 49 = 1 ∧ 18 ^ 3 % 343 = 1 ∧ 18 ^ 3 % 2401 = 1030 := by
  decide

-- §13 instantiation checks
example : SieveAt 2 8 :=
  sieveAt_of_mem_sieveClasses_of_modEq (j := 1) (r := 2) (by decide) (by decide)

example : ((Finset.range (3 * (2 * 3 ^ 1))).filter fun n => SieveAt (1 + 1) n).card
    = 3 * 2 ^ 1 := card_range_mul_filter_sieveAt 1 3

example : ∃ n : ℕ, 2 ^ n % 3 ^ (2 + 1) = 10 ∧ SieveAt (2 + 1) n :=
  exists_two_pow_mod_eq_of_base3ZeroOne 2 10 (by norm_num) (by norm_num) (by decide)

example : 2 ^ 6 % 3 ^ 3 = 10 := by decide

example : 2 ^ 12 % 3 ^ (1 + 1) = 1 % 3 ^ (1 + 1) ↔ 2 * 3 ^ 1 ∣ 12 :=
  two_pow_mod_eq_one_iff 1 12

example : 18 ^ 5 % 7 ^ 3 = 18 ^ (5 % 3) % 7 ^ 3 :=
  pow_mod_eq_of_pow_mod_one (by decide) 5

end Part2
