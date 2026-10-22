import Mathlib
import Sorry.Quarantine.Enumerative.Practical

set_option autoImplicit false

namespace SwitkayParity

/-- Any prime-plus-practical representation of an odd number at least five
has an odd prime summand and an even practical summand. -/
theorem switkay_parity_reduction (n : ℕ) (hodd : Odd n) (hn : 5 ≤ n)
    (h : ∃ p q : ℕ, p.Prime ∧ q.Practical ∧ p + q = n) :
    ∃ p q : ℕ, p.Prime ∧ Odd p ∧ q.Practical ∧ Even q ∧ p + q = n := by
  obtain ⟨p, q, hp, hq, hsum⟩ := h
  have hqpos : 0 < q := hq.1
  have hqgt : 1 < q := by
    by_contra hnot
    have hqone : q = 1 := by omega
    have hpeven : Even p := by
      obtain ⟨k, hk⟩ := hodd
      refine ⟨k, ?_⟩
      omega
    have hptwo : p = 2 := hp.even_iff.mp hpeven
    omega
  have hqeven : Even q := even_iff_two_dvd.mpr (hq.two_dvd hqgt)
  have hpodd : Odd p := by
    obtain ⟨k, hk⟩ := hodd
    obtain ⟨j, hj⟩ := hqeven
    refine ⟨k - j, ?_⟩
    omega
  exact ⟨p, q, hp, hpodd, hq, hqeven, hsum⟩

example : Odd (5 : ℕ) ∧ 5 ≤ (5 : ℕ) ∧
    (∃ p q : ℕ, p.Prime ∧ q.Practical ∧ p + q = 5) :=
  ⟨by decide, by decide, 3, 2, Nat.prime_three, Nat.practical_two, rfl⟩

example : ∃ p q : ℕ, p.Prime ∧ Odd p ∧ q.Practical ∧ Even q ∧ p + q = 5 :=
  switkay_parity_reduction 5 (by decide) (by decide)
    ⟨3, 2, Nat.prime_three, Nat.practical_two, rfl⟩

end SwitkayParity
