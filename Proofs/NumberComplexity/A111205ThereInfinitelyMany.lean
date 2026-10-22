/-
# A111205 — Hilliard: infinitely many nonsquare composites share a factor with `2⌊√k⌋+1`

OEIS A111205, Cino Hilliard: infinitely many nonsquare composites
`k` have `gcd(k, 2⌊√k⌋+1) > 1`.
For `r = 3t+4`, the family `k = r²+2` lies strictly between `r²` and
`(r+1)²`; both `k > 3` and `2r+1` are divisible by `3`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A111205ThereInfinitelyMany

/-! ## Definitions

`IsA111205 k` mirrors the entry's definition (and its Mathematica program):
`k` is composite (`1 < k` and not prime), not a perfect square, and
`gcd(k, 2 * floor(sqrt k) + 1) > 1`, where `2 * floor(sqrt k) + 1 = (r+1)^2 - r^2`
for `r = floor(sqrt k)`.  `Nat.sqrt` is the floor square root. -/

/-- Membership in A111205: `k` is a nonsquare composite number with
`gcd(k, 2 * ⌊√k⌋ + 1) > 1`. -/
def IsA111205 (k : ℕ) : Prop :=
  1 < k ∧ ¬ k.Prime ∧ ¬ IsSquare k ∧ 1 < Nat.gcd k (2 * Nat.sqrt k + 1)

instance : DecidablePred IsA111205 := fun k => by
  unfold IsA111205; infer_instance

/-- Examples: the terms of A111205 up to `290` are exactly the 55 listed
terms of the entry. -/
example : (Finset.range 291).filter IsA111205 =
    {14, 18, 21, 24, 33, 39, 50, 51, 54, 55, 57, 60, 63, 68, 95, 102, 105, 108,
      111, 112, 114, 117, 119, 120, 138, 145, 150, 155, 160, 165, 171, 174, 177,
      180, 183, 186, 189, 192, 195, 203, 248, 258, 261, 264, 267, 270, 273, 275,
      276, 279, 282, 285, 286, 288, 290} := by
  decide +kernel

/-! ## The explicit family -/

/-- The witness family: `a111205Witness t = (3t+4)^2 + 2`. -/
def a111205Witness (t : ℕ) : ℕ := (3 * t + 4) ^ 2 + 2

/-- Examples for the witness family: its first values `18, 51, 102` are
listed terms. -/
example : (a111205Witness 0, a111205Witness 1, a111205Witness 2) = (18, 51, 102) := rfl

/-- The floor square root of `(3t+4)^2 + 2` is `3t+4`. -/
theorem sqrt_a111205Witness (t : ℕ) : Nat.sqrt (a111205Witness t) = 3 * t + 4 := by
  unfold a111205Witness
  rw [sq]
  exact Nat.sqrt_add_eq (3 * t + 4) (by omega)

/-- `(3t+4)^2 + 2` is not a perfect square: it lies strictly between
`(3t+4)^2` and `(3t+5)^2`. -/
theorem not_isSquare_a111205Witness (t : ℕ) : ¬ IsSquare (a111205Witness t) := by
  rintro ⟨m, hm⟩
  have hsqrt : Nat.sqrt (m * m) = m := Nat.sqrt_eq m
  rw [← hm, sqrt_a111205Witness] at hsqrt
  subst hsqrt
  unfold a111205Witness at hm
  nlinarith

/-- `3` divides `(3t+4)^2 + 2`. -/
theorem three_dvd_a111205Witness (t : ℕ) : 3 ∣ a111205Witness t :=
  ⟨3 * t ^ 2 + 8 * t + 6, by unfold a111205Witness; ring⟩

/-- Every witness `(3t+4)^2 + 2` is a term of A111205. -/
theorem isA111205_a111205Witness (t : ℕ) : IsA111205 (a111205Witness t) := by
  have h3 : 3 ∣ a111205Witness t := three_dvd_a111205Witness t
  have hbig : 3 < a111205Witness t := by
    unfold a111205Witness; ring_nf; omega
  refine ⟨by omega, ?_, not_isSquare_a111205Witness t, ?_⟩
  · intro hp
    have h3eq : 3 = a111205Witness t :=
      (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3
    omega
  · have hd : 3 ∣ 2 * Nat.sqrt (a111205Witness t) + 1 := by
      rw [sqrt_a111205Witness]
      exact ⟨2 * t + 3, by ring⟩
    have hg : 3 ∣ Nat.gcd (a111205Witness t) (2 * Nat.sqrt (a111205Witness t) + 1) :=
      Nat.dvd_gcd h3 hd
    have hpos : 0 < Nat.gcd (a111205Witness t) (2 * Nat.sqrt (a111205Witness t) + 1) :=
      Nat.gcd_pos_of_pos_left _ (by omega)
    have hle := Nat.le_of_dvd hpos hg
    omega

/-- The witness family is strictly increasing, hence injective. -/
theorem a111205Witness_strictMono : StrictMono a111205Witness := by
  intro s t hst
  unfold a111205Witness
  have h : 3 * s + 4 < 3 * t + 4 := by omega
  have := Nat.pow_lt_pow_left h (two_ne_zero)
  omega

/-! ## The conjecture -/

/-- **Hilliard's conjecture (A111205, Cino Hilliard, 2005).**

There are infinitely many nonsquare composite `k` with
`gcd(k, 2 * floor(sqrt k) + 1) > 1`.  Proved here by the explicit family
`k = (3t+4)^2 + 2`. -/
theorem a111205_infinite : {k : ℕ | IsA111205 k}.Infinite :=
  Set.infinite_of_injective_forall_mem a111205Witness_strictMono.injective
    isA111205_a111205Witness

end Candidates.A111205ThereInfinitelyMany
