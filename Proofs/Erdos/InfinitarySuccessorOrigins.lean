import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

set_option autoImplicit false

namespace Erdos.InfinitarySuccessorOrigins

/-- An odd prime divisor of a successor at bit position `h` gives order exactly
`2^(h+1)` for the base modulo that prime. -/
theorem orderOf_eq_two_pow_succ (q b h : ℕ) (hq : q.Prime) (hqodd : 2 < q)
    (hd : q ∣ b ^ (2 ^ h) + 1) : orderOf (b : ZMod q) = 2 ^ (h + 1) := by
  letI : Fact q.Prime := ⟨hq⟩
  letI : Fact (2 < q) := ⟨hqodd⟩
  have hz : (b : ZMod q) ^ (2 ^ h) + 1 = 0 := by
    have hc := (ZMod.natCast_eq_zero_iff (b ^ (2 ^ h) + 1) q).mpr hd
    simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_one] using hc
  have hp : (b : ZMod q) ^ (2 ^ h) = -1 := eq_neg_of_add_eq_zero_left hz
  apply orderOf_eq_prime_pow (p := 2) (n := h)
  · rw [hp]
    exact ZMod.neg_one_ne_one
  · rw [pow_succ, pow_mul, hp]
    norm_num

/-- If the prime is `9` or `13` modulo `16`, every positive successor bit
position at which it divides a base successor is at most two. -/
theorem position_le_two (q b h : ℕ) (hq : q.Prime) (hq16 : q % 16 = 9 ∨ q % 16 = 13)
    (hd : q ∣ b ^ (2 ^ h) + 1) : h ≤ 2 := by
  have hqodd : 2 < q := by omega
  letI : Fact q.Prime := ⟨hq⟩
  have hp := orderOf_eq_two_pow_succ q b h hq hqodd hd
  have hb : (b : ZMod q) ≠ 0 := by
    intro hz
    have hpzero : (b : ZMod q) ^ (2 ^ h) = 0 := by
      rw [hz, zero_pow (by positivity : 2 ^ h ≠ 0)]
    have hc := (ZMod.natCast_eq_zero_iff (b ^ (2 ^ h) + 1) q).mpr hd
    have hone : (1 : ZMod q) = 0 := by
      simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_one, hpzero, zero_add] using hc
    exact one_ne_zero hone
  have hord : 2 ^ (h + 1) ∣ q - 1 := by
    rw [← hp]
    exact ZMod.orderOf_dvd_card_sub_one hb
  by_contra hh
  have hfour : 4 ≤ h + 1 := by omega
  have hsixteen : 16 ∣ q - 1 := (by norm_num : 16 = 2 ^ 4) ▸
    (Nat.dvd_trans (Nat.pow_dvd_pow 2 hfour) hord)
  have hmod := Nat.mod_eq_zero_of_dvd hsixteen
  omega

private theorem not_dvd_prime_of_mod_five (q r : ℕ) (hq : q.Prime)
    (hq5 : q % 5 = 4) (hr : r.Prime) (hr5 : r % 5 ≠ 4) : ¬q ∣ r := by
  intro hd
  rcases (Nat.dvd_prime hr).mp hd with hone | heq
  · exact hq.ne_one hone
  · subst q
    exact hr5 hq5

private theorem not_dvd_twice_prime_of_mod_five (q r : ℕ) (hq : q.Prime)
    (hq5 : q % 5 = 4) (hr : r.Prime) (hr5 : r % 5 ≠ 4) : ¬q ∣ 2 * r := by
  intro hd
  rcases hq.dvd_mul.mp hd with htwo | hrdiv
  · exact not_dvd_prime_of_mod_five q 2 hq hq5 Nat.prime_two (by norm_num) htwo
  · exact not_dvd_prime_of_mod_five q r hq hq5 hr hr5 hrdiv

/-- A prime that is `4` modulo `5` divides none of the six successor factors
for bases `2`, `3`, and `5` at bit positions one and two. -/
theorem not_dvd_small_successor (q b h : ℕ) (hq : q.Prime) (hq5 : q % 5 = 4)
    (hb : b = 2 ∨ b = 3 ∨ b = 5) (hh : h = 1 ∨ h = 2) :
    ¬q ∣ b ^ (2 ^ h) + 1 := by
  rcases hb with hb | hb | hb <;> subst b
  · rcases hh with hh | hh <;> subst h
    · exact not_dvd_prime_of_mod_five q 5 hq hq5 (by norm_num) (by norm_num)
    · exact not_dvd_prime_of_mod_five q 17 hq hq5 (by norm_num) (by norm_num)
  · rcases hh with hh | hh <;> subst h
    · exact not_dvd_twice_prime_of_mod_five q 5 hq hq5 (by norm_num) (by norm_num)
    · exact not_dvd_twice_prime_of_mod_five q 41 hq hq5 (by norm_num) (by norm_num)
  · rcases hh with hh | hh <;> subst h
    · exact not_dvd_twice_prime_of_mod_five q 13 hq hq5 (by norm_num) (by norm_num)
    · exact not_dvd_twice_prime_of_mod_five q 313 hq hq5 (by norm_num) (by norm_num)

/-- The congruence core for the strict-support witness: a prime that is `1`
modulo `4`, `2` modulo `3`, `4` modulo `5`, and `9` or `13` modulo `16`
has no forward successor origin among bases `2`, `3`, and `5`, at any positive
bit position. The actual exponent of each base is `2^h`. -/
theorem not_dvd_successors (q : ℕ) (hq : q.Prime) (_hq4 : q % 4 = 1)
    (_hq3 : q % 3 = 2) (hq5 : q % 5 = 4) (hq16 : q % 16 = 9 ∨ q % 16 = 13) :
    ∀ h : ℕ, 1 ≤ h →
      ¬q ∣ 2 ^ (2 ^ h) + 1 ∧ ¬q ∣ 3 ^ (2 ^ h) + 1 ∧ ¬q ∣ 5 ^ (2 ^ h) + 1 := by
  intro h hh
  have hexclude : ∀ b : ℕ, (b = 2 ∨ b = 3 ∨ b = 5) → ¬q ∣ b ^ (2 ^ h) + 1 := by
    intro b hb hd
    have hbound : h ≤ 2 := position_le_two q b h hq hq16 hd
    have hsmall : h = 1 ∨ h = 2 := by omega
    exact not_dvd_small_successor q b h hq hq5 hb hsmall hd
  exact ⟨hexclude 2 (Or.inl rfl), hexclude 3 (Or.inr (Or.inl rfl)),
    hexclude 5 (Or.inr (Or.inr rfl))⟩

example : Nat.Prime 29 ∧ 29 % 4 = 1 ∧ 29 % 3 = 2 ∧ 29 % 5 = 4 ∧
    (29 % 16 = 9 ∨ 29 % 16 = 13) := by norm_num

example : Nat.Prime 29 ∧ 2 < 29 ∧ 29 ∣ 12 ^ (2 ^ 1) + 1 := by norm_num

example : Nat.Prime 29 ∧ (29 % 16 = 9 ∨ 29 % 16 = 13) ∧
    29 ∣ 12 ^ (2 ^ 1) + 1 := by norm_num

example : ∀ h : ℕ, 1 ≤ h →
    ¬29 ∣ 2 ^ (2 ^ h) + 1 ∧ ¬29 ∣ 3 ^ (2 ^ h) + 1 ∧ ¬29 ∣ 5 ^ (2 ^ h) + 1 :=
  not_dvd_successors 29 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

end Erdos.InfinitarySuccessorOrigins
