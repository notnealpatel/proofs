/-
# A331021 — every k with gcd(k^2, 2^(k-1) - 1) > k is a multiple of a Wieferich prime

The conjecture in OEIS A331021 (Amiram Eldar and Thomas Ordowski) says that
every positive `k` with `gcd(k²,2^(k-1)-1) > k` is divisible by a Wieferich
prime (A001220).

Let g = gcd(k^2, 2^(k-1) - 1) > k.  Then g ∤ k, so some prime p has
v_p(g) > v_p(k).  As p ∣ g ∣ k^2, p ∣ k, so v_p(g) ≥ 2 and
p^2 ∣ 2^(k-1) - 1; p is odd because k ≥ p ≥ 2 makes 2^(k-1) - 1 odd.  In
(ℤ/p^2)^× the order of 2 divides k - 1 and φ(p^2) = p(p - 1); since p ∣ k,
gcd(k - 1, p) = 1, so the order divides p - 1, i.e. p^2 ∣ 2^(p-1) - 1.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A331021GcdTherePrime

/-! ## Definitions -/

/-- Membership in A331021: `k` is a positive integer with
`k < gcd(k^2, 2^(k-1) - 1)`.  For `0 < k` the natural subtraction
`2^(k-1) - 1` never truncates, since `1 ≤ 2^(k-1)`. -/
def IsTerm (k : ℕ) : Prop :=
  0 < k ∧ k < Nat.gcd (k ^ 2) (2 ^ (k - 1) - 1)

instance : DecidablePred IsTerm := fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- A Wieferich prime (A001220): a prime `p` with `p^2 ∣ 2^(p-1) - 1`. -/
def IsWieferich (p : ℕ) : Prop :=
  p.Prime ∧ p ^ 2 ∣ 2 ^ (p - 1) - 1

/-! ## Examples -/

/-- The first term `1093` is in the sequence (also witnesses that the
hypothesis of the conjecture is satisfiable). -/
example : IsTerm 1093 := by decide +kernel

example : IsTerm 3511 := by decide +kernel

example : IsTerm 398945 := by decide +kernel

/-- The even term `6165316 = 4 · 3511 · 439`. -/
example : IsTerm 6165316 := by decide +kernel

example : ¬ IsTerm 1092 := by decide +kernel

example : ¬ IsTerm 1 := by decide +kernel

/-- `1093` is a Wieferich prime. -/
example : IsWieferich 1093 := ⟨by norm_num, by decide +kernel⟩

/-- `3511` is a Wieferich prime. -/
example : IsWieferich 3511 := ⟨by norm_num, by decide +kernel⟩

/-- `1093` is the least term: no `k < 1093` is in the sequence. -/
example : ∀ k < 1093, ¬ IsTerm k := by decide +kernel

/-! ## Proof -/

/-- **Valuation step.** If `k < gcd(k^2, 2^(k-1) - 1)`, then some prime `p`
divides `k` and `p^2` divides `2^(k-1) - 1`. -/
theorem exists_prime_dvd_sq_dvd_of_lt_gcd {k : ℕ}
    (h : k < Nat.gcd (k ^ 2) (2 ^ (k - 1) - 1)) :
    ∃ p, p.Prime ∧ p ∣ k ∧ p ^ 2 ∣ 2 ^ (k - 1) - 1 := by
  set g := Nat.gcd (k ^ 2) (2 ^ (k - 1) - 1) with hg
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp [g] at h
  have hg0 : g ≠ 0 := by omega
  -- `g ∤ k`, since `k < g` and `0 < k`
  have hgk : ¬ g ∣ k := fun hd =>
    absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) hd) (by omega)
  rw [← Nat.factorization_le_iff_dvd hg0 hk0, Finsupp.le_def] at hgk
  push Not at hgk
  obtain ⟨p, hp⟩ := hgk
  have hpp : p.Prime := by
    by_contra hnp
    rw [Nat.factorization_eq_zero_of_not_prime g hnp] at hp
    omega
  have hpg : p ∣ g := (hpp.dvd_iff_one_le_factorization hg0).mpr (by omega)
  have hpk : p ∣ k := hpp.dvd_of_dvd_pow (hpg.trans (Nat.gcd_dvd_left _ _))
  have hk1 : 1 ≤ k.factorization p := (hpp.dvd_iff_one_le_factorization hk0).mp hpk
  have hp2g : p ^ 2 ∣ g := (hpp.pow_dvd_iff_le_factorization hg0).mpr (by omega)
  exact ⟨p, hpp, hpk, hp2g.trans (Nat.gcd_dvd_right _ _)⟩

/-- **Parity step.** A prime `p` dividing a positive `k` with
`p^2 ∣ 2^(k-1) - 1` is odd: `k ≥ 2` makes `2^(k-1) - 1` odd. -/
theorem ne_two_of_sq_dvd {p k : ℕ} (hp : p.Prime) (hpk : p ∣ k) (hk : 0 < k)
    (h : p ^ 2 ∣ 2 ^ (k - 1) - 1) : p ≠ 2 := by
  rintro rfl
  have hk2 : 2 ≤ k := Nat.le_of_dvd hk hpk
  have hpow : 2 ∣ 2 ^ (k - 1) := dvd_pow_self 2 (by omega)
  have hodd : 2 ∣ 2 ^ (k - 1) - 1 := (Dvd.intro_left _ rfl).trans h
  have hone : 1 ≤ 2 ^ (k - 1) := Nat.one_le_two_pow
  have h1 : 2 ∣ 2 ^ (k - 1) - (2 ^ (k - 1) - 1) := Nat.dvd_sub hpow hodd
  rw [Nat.sub_sub_self hone] at h1
  omega

/-- **Order step.** If an odd prime `p` divides `k > 0` and
`p^2 ∣ 2^(k-1) - 1`, then `p` is a Wieferich prime: the order of `2` modulo
`p^2` divides both `k - 1` and `φ(p^2) = p(p - 1)`, and `gcd(k - 1, p) = 1`. -/
theorem sq_dvd_two_pow_pred_sub_one {p k : ℕ} (hp : p.Prime) (hpk : p ∣ k)
    (hk : 0 < k) (h : p ^ 2 ∣ 2 ^ (k - 1) - 1) (hp2 : p ≠ 2) :
    p ^ 2 ∣ 2 ^ (p - 1) - 1 := by
  have hcop2 : Nat.Coprime 2 (p ^ 2) :=
    Nat.Coprime.pow_right 2 ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  have hcast : ∀ m : ℕ, p ^ 2 ∣ 2 ^ m - 1 ↔ (2 : ZMod (p ^ 2)) ^ m = 1 := by
    intro m
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub Nat.one_le_two_pow, sub_eq_zero]
    push_cast
    rfl
  have hk1 : (2 : ZMod (p ^ 2)) ^ (k - 1) = 1 := (hcast _).mp h
  have htot : (2 : ZMod (p ^ 2)) ^ (p * (p - 1)) = 1 := by
    have hmod := Nat.ModEq.pow_totient hcop2
    rw [Nat.totient_prime_pow hp (by norm_num), pow_one] at hmod
    have hz := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
    push_cast at hz
    exact hz
  have hcop : Nat.Coprime p (k - 1) := by
    have hkk : Nat.Coprime (1 + (k - 1)) (k - 1) :=
      Nat.coprime_add_self_left.mpr (Nat.coprime_one_left _)
    rw [show 1 + (k - 1) = k by omega] at hkk
    exact Nat.Coprime.coprime_dvd_left hpk hkk
  have hord1 : orderOf (2 : ZMod (p ^ 2)) ∣ k - 1 := orderOf_dvd_of_pow_eq_one hk1
  have hord2 : orderOf (2 : ZMod (p ^ 2)) ∣ p * (p - 1) := orderOf_dvd_of_pow_eq_one htot
  have hord : orderOf (2 : ZMod (p ^ 2)) ∣ p - 1 :=
    (Nat.Coprime.coprime_dvd_right hord1 hcop).symm.dvd_of_dvd_mul_left hord2
  exact (hcast _).mpr (orderOf_dvd_iff_pow_eq_one.mp hord)

/-- **A331021 conjecture (OEIS comment, entry by Amiram Eldar and Thomas
Ordowski).**

For every positive integer `k` with `gcd(k^2, 2^(k-1) - 1) > k` there is a
prime `p` with `p ∣ k` and `p^2 ∣ 2^(p-1) - 1`. -/
theorem exists_wieferich_dvd_of_isTerm {k : ℕ} (hk : IsTerm k) :
    ∃ p, IsWieferich p ∧ p ∣ k := by
  obtain ⟨hk0, hlt⟩ := hk
  obtain ⟨p, hp, hpk, hsq⟩ := exists_prime_dvd_sq_dvd_of_lt_gcd hlt
  have hp2 : p ≠ 2 := ne_two_of_sq_dvd hp hpk hk0 hsq
  exact ⟨p, ⟨hp, sq_dvd_two_pow_pred_sub_one hp hpk hk0 hsq hp2⟩, hpk⟩

end Candidates.A331021GcdTherePrime
