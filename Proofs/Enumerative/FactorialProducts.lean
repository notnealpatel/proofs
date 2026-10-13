import Mathlib

set_option autoImplicit false

namespace FactorialProducts

open Nat

/-- `n!` is a nonempty product of factorials of arguments at least two,
all satisfying McCranie's nontriviality condition `x + 1 < n`. -/
def IsNontrivialFactorialProduct (n : ℕ) : Prop :=
  ∃ L : Multiset ℕ, L ≠ 0 ∧ (∀ x ∈ L, 2 ≤ x) ∧ (∀ x ∈ L, x + 1 < n) ∧
    (L.map Nat.factorial).prod = n !

/-- The three known terms of A003135; completeness remains conjectural. -/
def knownTerms : Finset ℕ := {9, 10, 16}

example : knownTerms = {9, 10, 16} := rfl
example (n : ℕ) : IsNontrivialFactorialProduct n ↔
    ∃ L : Multiset ℕ, L ≠ 0 ∧ (∀ x ∈ L, 2 ≤ x) ∧ (∀ x ∈ L, x + 1 < n) ∧
      (L.map Nat.factorial).prod = n ! := Iff.rfl

/-- A prime divides a product of factorials exactly when it divides one factor. -/
theorem prime_dvd_prod_factorial_iff {p : ℕ} (hp : p.Prime) (L : Multiset ℕ) :
    p ∣ (L.map Nat.factorial).prod ↔ ∃ x ∈ L, p ∣ x ! := by
  induction L using Multiset.induction_on with
  | empty => simp [hp.not_dvd_one]
  | cons a L ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, hp.dvd_mul, ih,
      Multiset.mem_cons, exists_eq_or_imp]

/-- A prime dividing a product of factorials is no larger than some argument. -/
theorem exists_le_of_prime_dvd_prod_factorial {p : ℕ} (hp : p.Prime)
    (L : Multiset ℕ) (h : p ∣ (L.map Nat.factorial).prod) :
    ∃ x ∈ L, p ≤ x := by
  obtain ⟨x, hx, hpx⟩ := (prime_dvd_prod_factorial_iff hp L).mp h
  exact ⟨x, hx, hp.dvd_factorial.mp hpx⟩

/-- Any factorial-product representation of `n!`, for `2 ≤ n`, has an argument
`x` with `n ≤ 2 * x + 2`. No upper bound on the arguments is assumed. -/
theorem largest_factor_lower_bound {n : ℕ} (hn : 2 ≤ n)
    (L : Multiset ℕ) (hL : L ≠ 0) (h2 : ∀ x ∈ L, 2 ≤ x)
    (hprod : (L.map Nat.factorial).prod = n !) :
    ∃ x ∈ L, n ≤ 2 * x + 2 := by
  have hm : n / 2 ≠ 0 := by omega
  obtain ⟨p, hp, hmp, hpm⟩ := Nat.exists_prime_lt_and_le_two_mul (n / 2) hm
  have hpn : p ≤ n := by omega
  have hdvd : p ∣ (L.map Nat.factorial).prod := by
    rw [hprod]
    exact hp.dvd_factorial.mpr hpn
  obtain ⟨x, hx, hpx⟩ := exists_le_of_prime_dvd_prod_factorial hp L hdvd
  exact ⟨x, hx, by omega⟩

/-- Nine is a nontrivial factorial product, with repeated argument three. -/
theorem isNontrivialFactorialProduct_nine : IsNontrivialFactorialProduct 9 :=
  ⟨{7, 3, 3, 2}, by decide, by decide, by decide, by decide⟩

/-- Ten is a nontrivial factorial product with arguments seven and six. -/
theorem isNontrivialFactorialProduct_ten : IsNontrivialFactorialProduct 10 :=
  ⟨{7, 6}, by decide, by decide, by decide, by decide⟩

/-- Sixteen is a nontrivial factorial product with arguments fourteen, five, two. -/
theorem isNontrivialFactorialProduct_sixteen : IsNontrivialFactorialProduct 16 := by
  refine ⟨{14, 5, 2}, by decide, by decide, by decide, ?_⟩
  norm_num [Multiset.map_cons, Multiset.prod_cons, Nat.factorial]

/-- Every known term satisfies the exact nontrivial factorial-product predicate. -/
theorem isNontrivialFactorialProduct_of_mem_knownTerms {n : ℕ}
    (hn : n ∈ knownTerms) : IsNontrivialFactorialProduct n := by
  simp only [knownTerms, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl
  · exact isNontrivialFactorialProduct_nine
  · exact isNontrivialFactorialProduct_ten
  · exact isNontrivialFactorialProduct_sixteen

/-- Six is excluded: prime five divides `6!` but none of the allowed factors. -/
theorem not_isNontrivialFactorialProduct_six : ¬ IsNontrivialFactorialProduct 6 := by
  rintro ⟨L, hL, h2, hsmall, hprod⟩
  have hp : Nat.Prime 5 := by decide
  have hdvd : 5 ∣ (L.map Nat.factorial).prod := by
    rw [hprod]
    exact hp.dvd_factorial.mpr (by decide)
  obtain ⟨x, hx, hpx⟩ := exists_le_of_prime_dvd_prod_factorial hp L hdvd
  have hlt := hsmall x hx
  omega

example : IsNontrivialFactorialProduct 9 := isNontrivialFactorialProduct_nine
example : ∃ L : Multiset ℕ, L ≠ 0 ∧ (∀ x ∈ L, 2 ≤ x) ∧
    (L.map Nat.factorial).prod = (9 : ℕ)! := by
  obtain ⟨L, hL, h2, _, hprod⟩ := isNontrivialFactorialProduct_nine
  exact ⟨L, hL, h2, hprod⟩

end FactorialProducts
