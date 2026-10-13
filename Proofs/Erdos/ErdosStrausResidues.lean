import Erdos.ErdosStraus

set_option autoImplicit false

namespace ErdosStraus

/-- For `p = 4k + 3`, the denominators `a`, `p*a+1`, and `p*a*(p*a+1)`
with `a = k+1` are positive and satisfy the cleared Egyptian fraction identity. -/
theorem witnesses_four_mul_add_three (k : ℕ) :
    let p := 4 * k + 3
    let a := k + 1
    let M := p * a
    0 < a ∧ 0 < M + 1 ∧ 0 < M * (M + 1) ∧
      4 * a * (M + 1) * (M * (M + 1)) =
        p * ((M + 1) * (M * (M + 1)) + a * (M * (M + 1)) + a * (M + 1)) := by
  dsimp only
  refine ⟨by omega, by omega, Nat.mul_pos (Nat.mul_pos (by omega) (by omega))
    (by omega), ?_⟩
  ring

/-- For `p = 3k + 2`, the denominators `k+1`, `p`, and `p*(k+1)`
are positive and satisfy the cleared Egyptian fraction identity. -/
theorem witnesses_three_mul_add_two (k : ℕ) :
    let p := 3 * k + 2
    let m := k + 1
    0 < m ∧ 0 < p ∧ 0 < p * m ∧
      4 * m * p * (p * m) = p * (p * (p * m) + m * (p * m) + m * p) := by
  dsimp only
  refine ⟨by omega, by omega, Nat.mul_pos (by omega) (by omega), ?_⟩
  ring

/-- For `p = 8k + 5`, the denominators `2*(k+1)`, `p*(k+1)`,
and `2*p*(k+1)` are positive and satisfy the cleared identity. -/
theorem witnesses_eight_mul_add_five (k : ℕ) :
    let p := 8 * k + 5
    let a := k + 1
    0 < 2 * a ∧ 0 < p * a ∧ 0 < 2 * p * a ∧
      4 * (2 * a) * (p * a) * (2 * p * a) =
        p * ((p * a) * (2 * p * a) + (2 * a) * (2 * p * a) + (2 * a) * (p * a)) := by
  dsimp only
  refine ⟨Nat.mul_pos (by decide) (by omega), Nat.mul_pos (by omega) (by omega),
    Nat.mul_pos (Nat.mul_pos (by decide) (by omega)) (by omega), ?_⟩
  ring

example :
    0 < (1 : ℕ) ∧ 0 < (4 : ℕ) ∧ 0 < (12 : ℕ) ∧
      4 * 1 * 4 * 12 = 3 * (4 * 12 + 1 * 12 + 1 * 4) := by decide

example :
    0 < (1 : ℕ) ∧ 0 < (2 : ℕ) ∧ 0 < (2 : ℕ) ∧
      4 * 1 * 2 * 2 = 2 * (2 * 2 + 1 * 2 + 1 * 2) := by decide

example :
    0 < (2 : ℕ) ∧ 0 < (5 : ℕ) ∧ 0 < (10 : ℕ) ∧
      4 * 2 * 5 * 10 = 5 * (5 * 10 + 2 * 10 + 2 * 5) := by decide

/-- A prime outside residue `1` modulo `24` belongs to one of the three
explicit Egyptian fraction families. The primes `2` and `3` are included. -/
theorem prime_residue_families (p : ℕ) (hp : p.Prime) (hres : p % 24 ≠ 1) :
    p % 4 = 3 ∨ p % 3 = 2 ∨ p % 8 = 5 := by
  by_cases htwo : p = 2
  · subst p
    norm_num
  by_cases hthree : p = 3
  · subst p
    norm_num
  have hmodtwo : p % 2 ≠ 0 := by
    intro hz
    exact htwo ((hp.dvd_iff_eq (by decide : 2 ≠ 1)).mp
      (Nat.dvd_iff_mod_eq_zero.mpr hz))
  have hmodthree : p % 3 ≠ 0 := by
    intro hz
    exact hthree ((hp.dvd_iff_eq (by decide : 3 ≠ 1)).mp
      (Nat.dvd_iff_mod_eq_zero.mpr hz))
  omega

example : (2 : ℕ).Prime ∧ 2 % 24 ≠ 1 := by decide
example : (3 : ℕ).Prime ∧ 3 % 24 ≠ 1 := by decide
example : (13 : ℕ).Prime ∧ 13 % 24 ≠ 1 := by decide

/-- Every natural number congruent to `3` modulo `4` has the cleared
Erdős–Straus representation given by the first explicit family. -/
theorem hasEgyptian4Cleared_of_mod_four (n : ℕ) (hn : n % 4 = 3) :
    HasEgyptian4Cleared n := by
  let k := n / 4
  have hform : n = 4 * k + 3 := by
    have hdivision := Nat.mod_add_div n 4
    omega
  rw [hform]
  exact ⟨k + 1, (4 * k + 3) * (k + 1) + 1,
    ((4 * k + 3) * (k + 1)) * ((4 * k + 3) * (k + 1) + 1),
    witnesses_four_mul_add_three k⟩

/-- Every natural number congruent to `2` modulo `3` has the cleared
Erdős–Straus representation given by the second explicit family. -/
theorem hasEgyptian4Cleared_of_mod_three (n : ℕ) (hn : n % 3 = 2) :
    HasEgyptian4Cleared n := by
  let k := n / 3
  have hform : n = 3 * k + 2 := by
    have hdivision := Nat.mod_add_div n 3
    omega
  rw [hform]
  exact ⟨k + 1, 3 * k + 2, (3 * k + 2) * (k + 1),
    witnesses_three_mul_add_two k⟩

/-- Every natural number congruent to `5` modulo `8` has the cleared
Erdős–Straus representation given by the third explicit family. -/
theorem hasEgyptian4Cleared_of_mod_eight (n : ℕ) (hn : n % 8 = 5) :
    HasEgyptian4Cleared n := by
  let k := n / 8
  have hform : n = 8 * k + 5 := by
    have hdivision := Nat.mod_add_div n 8
    omega
  rw [hform]
  exact ⟨2 * (k + 1), (8 * k + 5) * (k + 1), 2 * (8 * k + 5) * (k + 1),
    witnesses_eight_mul_add_five k⟩

/-- Every prime not congruent to `1` modulo `24` has a cleared
Erdős–Straus representation; no conjectural prime case is used. -/
theorem hasEgyptian4Cleared_of_prime_mod_ne_one (p : ℕ) (hp : p.Prime)
    (hres : p % 24 ≠ 1) : HasEgyptian4Cleared p := by
  rcases prime_residue_families p hp hres with hfour | hthree | height
  · exact hasEgyptian4Cleared_of_mod_four p hfour
  · exact hasEgyptian4Cleared_of_mod_three p hthree
  · exact hasEgyptian4Cleared_of_mod_eight p height

/-- To prove the Erdős–Straus conjecture for all natural `n ≥ 2`, it suffices
to prove it for primes congruent to `1` modulo `24`. This residual premise
is explicit and is not established here. -/
theorem erdosStraus_residual
    (h : ∀ p : ℕ, p.Prime → p % 24 = 1 → HasEgyptian4Cleared p) :
    ∀ n : ℕ, 2 ≤ n → HasEgyptian4Cleared n := by
  apply erdosStraus_of_prime
  intro p hp _hbound
  by_cases hres : p % 24 = 1
  · exact h p hp hres
  · exact hasEgyptian4Cleared_of_prime_mod_ne_one p hp hres

example : (3 : ℕ) % 4 = 3 ∧ HasEgyptian4Cleared 3 :=
  ⟨by decide, hasEgyptian4Cleared_of_mod_four 3 (by decide)⟩

example : (2 : ℕ) % 3 = 2 ∧ HasEgyptian4Cleared 2 :=
  ⟨by decide, hasEgyptian4Cleared_of_mod_three 2 (by decide)⟩

example : (5 : ℕ) % 8 = 5 ∧ HasEgyptian4Cleared 5 :=
  ⟨by decide, hasEgyptian4Cleared_of_mod_eight 5 (by decide)⟩

example : (13 : ℕ).Prime ∧ 13 % 24 ≠ 1 ∧ HasEgyptian4Cleared 13 :=
  ⟨by decide, by decide,
    hasEgyptian4Cleared_of_prime_mod_ne_one 13 (by decide) (by decide)⟩

example : (73 : ℕ).Prime ∧ 73 % 24 = 1 ∧ HasEgyptian4Cleared 73 := by
  refine ⟨by norm_num, by decide, 20, 292, 730, by decide, by decide, by decide, ?_⟩
  norm_num

end ErdosStraus
