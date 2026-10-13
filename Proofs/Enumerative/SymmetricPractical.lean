import Enumerative.Practical

set_option autoImplicit false

namespace SymmetricPractical

/-- Hasler's parity split: a practical offset greater than one forces the
prime-pair branch to have odd center and the practical-pair branch even center. -/
theorem hasler_parity {n p : ℕ} (hp : p.Practical) (hp1 : 1 < p) (hpn : p < n) :
    ((n - p).Prime ∧ (n + p).Prime ∧ 2 < n + p → Odd n) ∧
    ((n - p).Practical ∧ (n + p).Practical ∧ 1 < n + p → Even n) := by
  have hp_even : 2 ∣ p := hp.two_dvd hp1
  constructor
  · intro hprime
    have hsum_odd : Odd (n + p) :=
      hprime.2.1.odd_of_ne_two (by omega)
    apply Nat.odd_iff.mpr
    have hsum_mod := Nat.odd_iff.mp hsum_odd
    omega
  · intro hpractical
    have hsum_even : 2 ∣ n + p := hpractical.2.1.two_dvd hpractical.2.2
    apply Nat.even_iff.mpr
    omega

-- Both branches have concrete models with nonempty natural-number domains.
example : (2 : ℕ).Practical ∧ 1 < (2 : ℕ) ∧ 2 < (5 : ℕ) ∧
    (5 - 2).Prime ∧ (5 + 2).Prime ∧ 2 < (5 + 2) := by
  exact ⟨Nat.practical_two, by decide, by decide, by decide, by decide, by decide⟩

example : (2 : ℕ).Practical ∧ 1 < (2 : ℕ) ∧ 2 < (4 : ℕ) ∧
    (4 - 2).Practical ∧ (4 + 2).Practical ∧ 1 < (4 + 2) := by
  decide

end SymmetricPractical
