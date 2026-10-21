/-
# A319927 — refutation of Ianakiev's all-powers conjecture

## OEIS source (retrieved 2026-10-21 with `oeis show A319927`; author line
## from the live entry https://oeis.org/A319927)

```
NAME:     Numbers k such that the sum of the squares of the odd non-unitary
          divisors of k divides the sum of the squares of the non-unitary
          divisors of k.
TERMS:    9,18,25,27,45,49,50,54,63,75,81,90,98,99,117,121,125,126,135,147,
          150,153,162,169,171,175,189,198,207,225,234,242,243,245,250,261,
          270,275,279,289,294,297,306,315,325,333,338,342,343,350,351,361,
          363,369,375,378,387,405
AUTHOR:   Ivan N. Ianakiev, Oct 02 2018
COMMENT (the conjecture, unsigned, hence the entry author's, Oct 02 2018):
  Conjecture: For any nonnegative integer power p the sum of the p-th powers
  of the odd non-unitary divisors of a(n) divides the sum of the p-th powers
  of the non-unitary divisors of a(n).
COMMENT (later, not a retraction):
  The start of this sequence, including the 58 terms currently shown in the
  data section, is consistent with a definition "nonsquarefree numbers not
  divisible by 4", but some larger terms are divisible by 4: for example,
  a(1305) = 9216 = 2^10 * 3^2. - _Peter Munn_, Sep 21 2020
  It seems that, for every n and odd prime p, p*a(n) is a term.
  - _Ivan N. Ianakiev_, Sep 11 2022
```

No later comment retracts the conjecture.

## Status

This module **refutes** the conjecture: `k = 9216 = 2^10 * 3^2` is a term
(the sums of squares are `9` and `41243877 = 9 * 4582653`), but for `p = 1`
the only odd non-unitary divisor is `3`, while the sum of all non-unitary
divisors is `16361`, which is not divisible by `3`.  An exhaustive scan
(Python, terms `k ≤ 9216`, `p ≤ 5`) found `9216` to be the smallest
counterexample; it also fails for `p = 3, 4, 5`.

## Definitional fidelity

A divisor `d` of `k` is non-unitary when `gcd(d, k/d) > 1`, as in the
entry's Mathematica and PARI programs.  Both programs exclude `k` whose odd
non-unitary sum vanishes (Mathematica: `x/0` is not an integer; PARI:
`if (suo, ...)`), so membership carries the guard `0 < ONU k 2`; without it
Lean's `0 ∣ 0` would admit every squarefree `k`.

## Corrected form

All 58 listed data terms are not divisible by `4`.  For such `k` the
divisibility holds for every `p` and every `k`, term or not
(`ONU_dvd_NU_of_not_four_dvd`): for odd `k` the two sums coincide, and for
`k = 2m` with `m` odd, doubling is a bijection from the odd to the even
non-unitary divisors, so `NU (2m) p = (1 + 2^p) * ONU (2m) p`.
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace Candidates.A319927Refutation

/-- `NU k p`: the sum of `d ^ p` over the non-unitary divisors `d` of `k`,
i.e. divisors with `gcd(d, k / d) > 1`. -/
def NU (k p : ℕ) : ℕ :=
  ∑ d ∈ k.divisors.filter (fun d => 1 < Nat.gcd d (k / d)), d ^ p

/-- `ONU k p`: the sum of `d ^ p` over the odd non-unitary divisors `d`
of `k`. -/
def ONU (k p : ℕ) : ℕ :=
  ∑ d ∈ (k.divisors.filter (fun d => 1 < Nat.gcd d (k / d))).filter Odd, d ^ p

/-- Membership in A319927: the sum of the squares of the odd non-unitary
divisors of `k` is positive and divides the sum of the squares of the
non-unitary divisors of `k`. -/
def IsTerm (k : ℕ) : Prop :=
  0 < ONU k 2 ∧ ONU k 2 ∣ NU k 2

/-- Membership in A319927 is decidable. -/
instance : DecidablePred IsTerm := fun k =>
  inferInstanceAs (Decidable (0 < ONU k 2 ∧ ONU k 2 ∣ NU k 2))

/-! ## Ground truth -/

/-- `12 = 2^2 * 3` has non-unitary divisors `2, 6`; their squares sum to `40`. -/
example : NU 12 2 = 40 := by decide +kernel

/-- `12` has no odd non-unitary divisor. -/
example : ONU 12 2 = 0 := by decide +kernel

/-- `9` has the single non-unitary divisor `3`. -/
example : NU 9 2 = 9 ∧ ONU 9 2 = 9 := by decide +kernel

/-- The terms of A319927 below `406` are exactly the 58 listed data terms. -/
example : (Finset.range 406).filter IsTerm =
    {9, 18, 25, 27, 45, 49, 50, 54, 63, 75, 81, 90, 98, 99, 117, 121, 125, 126,
      135, 147, 150, 153, 162, 169, 171, 175, 189, 198, 207, 225, 234, 242, 243,
      245, 250, 261, 270, 275, 279, 289, 294, 297, 306, 315, 325, 333, 338, 342,
      343, 350, 351, 361, 363, 369, 375, 378, 387, 405} := by
  decide +kernel

/-! ## The conjecture and its refutation -/

/-- **Ianakiev's conjecture (A319927, Oct 02 2018).** For every term `k` of
A319927 and every `p ≥ 0`, the sum of the `p`-th powers of the odd
non-unitary divisors of `k` divides the sum of the `p`-th powers of the
non-unitary divisors of `k`. -/
def Conjecture : Prop :=
  ∀ k : ℕ, IsTerm k → ∀ p : ℕ, ONU k p ∣ NU k p

/-- `9216 = 2^10 * 3^2` is a term of A319927 (Peter Munn's `a(1305)`). -/
theorem isTerm_9216 : IsTerm 9216 := by
  decide +kernel

/-- For `k = 9216` and `p = 1` the odd non-unitary sum is `3`. -/
theorem ONU_9216_one : ONU 9216 1 = 3 := by
  decide +kernel

/-- For `k = 9216` and `p = 1` the non-unitary sum is `16361`. -/
theorem NU_9216_one : NU 9216 1 = 16361 := by
  decide +kernel

/-- **The conjecture is false.** Counterexample: `k = 9216 = 2^10 * 3^2` is
a term of A319927, but for `p = 1` its odd non-unitary divisor sum `3` does
not divide its non-unitary divisor sum `16361`.  The author probably had in
mind terms not divisible by `4` (all 58 listed data terms are), for which
the divisibility holds for every `p`. -/
theorem conjecture_false : ¬ Conjecture := by
  intro hconj
  have hdvd : ONU 9216 1 ∣ NU 9216 1 := hconj 9216 isTerm_9216 1
  rw [ONU_9216_one, NU_9216_one] at hdvd
  omega

/-! ## Corrected form: terms not divisible by `4` -/

/-- For odd `k` every divisor is odd, so `ONU k p = NU k p`. -/
theorem ONU_eq_NU_of_odd {k : ℕ} (hk : Odd k) (p : ℕ) : ONU k p = NU k p := by
  unfold ONU NU
  rw [Finset.filter_true_of_mem]
  intro d hd
  exact hk.of_dvd_nat (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1)

/-- For odd `m` and an odd divisor `d` of `m`, the non-unitarity gcds of `d`
and of `2d` as divisors of `2m` both equal `gcd(d, m / d)`. -/
theorem gcd_div_eq_of_odd {m d : ℕ} (hm : Odd m) (hd : Odd d) (hdm : d ∣ m) :
    Nat.gcd d (2 * m / d) = Nat.gcd d (m / d) ∧
      Nat.gcd (2 * d) (2 * m / (2 * d)) = Nat.gcd d (m / d) := by
  have hq : Odd (m / d) := hm.of_dvd_nat (Nat.div_dvd_of_dvd hdm)
  have h2d : Nat.Coprime 2 d := Nat.coprime_two_left.mpr hd
  have h2q : Nat.Coprime 2 (m / d) := Nat.coprime_two_left.mpr hq
  refine ⟨?_, ?_⟩
  · rw [Nat.mul_div_assoc 2 hdm]
    exact Nat.Coprime.gcd_mul_left_cancel_right (m / d) h2d
  · rw [Nat.mul_div_mul_left m d two_pos]
    exact Nat.Coprime.gcd_mul_left_cancel d h2q

/-- For odd `m`, the even non-unitary divisors of `2m` are exactly the doubles
of the odd non-unitary divisors of `2m`. -/
theorem evenNonunitary_eq_image {m : ℕ} (hm : Odd m) :
    ((2 * m).divisors.filter (fun d => 1 < Nat.gcd d (2 * m / d))).filter
        (fun d => ¬ Odd d) =
      (((2 * m).divisors.filter (fun d => 1 < Nat.gcd d (2 * m / d))).filter Odd).image
        (fun d => 2 * d) := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact Nat.not_odd_zero hm
  have h2m0 : 2 * m ≠ 0 := by omega
  ext x
  simp only [Finset.mem_filter, Finset.mem_image, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨⟨hx, -⟩, hg⟩, hxe⟩
    obtain ⟨y, rfl⟩ : 2 ∣ x := (Nat.not_odd_iff_even.mp hxe).two_dvd
    have hym : y ∣ m := Nat.dvd_of_mul_dvd_mul_left two_pos hx
    have hy : Odd y := hm.of_dvd_nat hym
    obtain ⟨h1, h2⟩ := gcd_div_eq_of_odd hm hy hym
    refine ⟨y, ⟨⟨⟨Dvd.dvd.mul_left hym 2, h2m0⟩, ?_⟩, hy⟩, rfl⟩
    rw [h1, ← h2]
    exact hg
  · rintro ⟨y, ⟨⟨⟨hy2, -⟩, hg⟩, hy⟩, rfl⟩
    have hym : y ∣ m :=
      Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_two_left.mpr hy).symm hy2
    obtain ⟨h1, h2⟩ := gcd_div_eq_of_odd hm hy hym
    refine ⟨⟨⟨Nat.mul_dvd_mul_left 2 hym, h2m0⟩, ?_⟩, ?_⟩
    · rw [h2, ← h1]
      exact hg
    · rw [Nat.not_odd_iff_even]
      exact even_two_mul y

/-- For odd `m`, `NU (2m) p = (1 + 2^p) * ONU (2m) p`. -/
theorem NU_two_mul_eq_of_odd {m : ℕ} (hm : Odd m) (p : ℕ) :
    NU (2 * m) p = (1 + 2 ^ p) * ONU (2 * m) p := by
  unfold NU ONU
  rw [← Finset.sum_filter_add_sum_filter_not _ Odd, evenNonunitary_eq_image hm,
    Finset.sum_image (fun a _ b _ hab => by omega)]
  simp only [mul_pow, ← Finset.mul_sum]
  ring

/-- **Corrected conjecture.** If `4 ∤ k` (true of all 58 listed data terms of
A319927), then for every `p ≥ 0` the sum of the `p`-th powers of the odd
non-unitary divisors of `k` divides the sum of the `p`-th powers of the
non-unitary divisors of `k`; no membership hypothesis is needed. -/
theorem ONU_dvd_NU_of_not_four_dvd {k : ℕ} (hk : ¬ 4 ∣ k) (p : ℕ) :
    ONU k p ∣ NU k p := by
  rcases Nat.even_or_odd k with ⟨r, hr⟩ | hodd
  · have hr' : Odd r := by
      rcases Nat.even_or_odd r with ⟨s, hs⟩ | hro
      · exact absurd ⟨s, by omega⟩ hk
      · exact hro
    have hk2 : k = 2 * r := by omega
    rw [hk2, NU_two_mul_eq_of_odd hr' p]
    exact Dvd.intro_left _ rfl
  · rw [ONU_eq_NU_of_odd hodd p]

/-- Non-vacuity of the corrected form: `18` is a term of A319927 with `4 ∤ 18`. -/
example : IsTerm 18 ∧ ¬ 4 ∣ 18 := by decide +kernel

end Candidates.A319927Refutation
