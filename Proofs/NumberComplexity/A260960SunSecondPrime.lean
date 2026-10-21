/-
# A260960 — Sun: right triangles with quadratic-residue perimeter and area

## OEIS source (retrieved 2026-10-21 with `oeis show A260960`; author line
## from the live entry)

```
NAME:     Least positive integer k < prime(n) such that there are 0 < i < j
          with i^2 + j^2 = k^2 for which (i*j)/2 is a primitive root modulo
          prime(n), or 0 if no such k exists.
TERMS:    0,0,0,0,5,5,5,17,13,17,10,10,5,13,13,25,5,5,39,25,17,5,5,5,17,29,
          5,5,5,5,5,5,5,34,17,5,5,26,13,13,5,10,29,13,13,5,34,5,5,5,5,25,...
AUTHOR:   Zhi-Wei Sun, Aug 06 2015
COMMENT (headline conjecture, not formalized here):
  Conjecture: a(n) > 0 for any n > 4. In other words, for any prime p > 7,
  there exists a right triangle whose three sides are among 1,...,p-1 and
  whose area is a primitive root modulo p.
COMMENT:
  We have verified this for primes p < 10^5.
COMMENT (the conjecture formalized here, Zhi-Wei Sun, Aug 06 2015):
  We also conjecture that for any prime p > 31, there exists a right triangle
  whose three sides are among 1,...,p-1, and whose perimeter and area are
  quadratic residues modulo p.
```

## Status

The triage recorded the second conjecture as open (no proof in the entry or
in the literature it found).  The headline primitive-root conjecture was
proved only for sufficiently large `p` (Wu–Ni, arXiv:2608.04391) and is a
separate statement that this file does not address.

A direct search (python, 2026-10-21) for all primes `p < 6000` finds that the
statement fails exactly at `p = 2, 3, 5, 7, 11, 13, 31`, so the bound
`31 < p` is sharp.

## Proof (formalized below)

Only the Legendre symbols `χ(2), χ(3), χ(5)` matter.  With `p > 41`:

* `(6, 8, 10)`: area `24 = 2^3·3`, perimeter `24`; works if `χ(2)χ(3) = 1`.
* `(5, 12, 13)`: area `30`, perimeter `30`; works if `χ(2)χ(3)χ(5) = 1`.
* `(9, 40, 41)`: area `180 = 2^2·3^2·5`, perimeter `90 = 2·3^2·5`; works if
  `χ(5) = 1` and `χ(2) = 1`.
* `(16, 30, 34)`: area `240 = 2^4·3·5`, perimeter `80 = 2^4·5`; works if
  `χ(3)χ(5) = 1` and `χ(5) = 1`.

These four cover all eight sign patterns.  The primes `37` and `41` use the
explicit witnesses `(5, 12, 13)` and `(12, 35, 37)`.

## Formalization conventions

"Quadratic residue modulo `p`" is read as a nonzero square in `ZMod p`.
Since `p` is odd and the legs are below `p`, the area is automatically
nonzero modulo `p`; the perimeter `a + b + c < 3p` is required nonzero
explicitly.  The area `ab/2` is carried as a natural number `A` with
`2 * A = a * b`, which avoids truncated division (the legs of an integral
right triangle always have even product).  Ordering the legs `a < b` loses
nothing: `a = b` is impossible because `√2` is irrational.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A260960SunSecondPrime

/-! ## Definition layer -/

/-- `IsQR p x` : `x` is a nonzero quadratic residue modulo `p`, i.e. a nonzero
square in `ZMod p`. -/
def IsQR (p : ℕ) (x : ℕ) : Prop :=
  IsSquare (x : ZMod p) ∧ (x : ZMod p) ≠ 0

/-- `GoodTriangle p a b c` : the right triangle with legs `a < b` and
hypotenuse `c`, all sides among `1, …, p - 1`, whose area `ab/2` and perimeter
`a + b + c` are both nonzero quadratic residues modulo `p`.  The area is the
natural number `A` with `2 * A = a * b`. -/
def GoodTriangle (p a b c : ℕ) : Prop :=
  0 < a ∧ a < b ∧ b < c ∧ c < p ∧ a ^ 2 + b ^ 2 = c ^ 2 ∧
    (∃ A : ℕ, 2 * A = a * b ∧ IsQR p A) ∧ IsQR p (a + b + c)

/-! ## Ground truth -/

-- `30 ≡ 17^2 (mod 37)`: the triangle `(5, 12, 13)` works at `p = 37`.
example : IsQR 37 30 := ⟨⟨17, by decide⟩, by decide⟩

-- `2 = 3` is not a square modulo `5`: the definition is not trivially true.
example : ¬ IsQR 5 3 := by
  rintro ⟨⟨r, hr⟩, -⟩
  revert r
  decide

-- `0` is excluded by the definition.
example : ¬ IsQR 37 37 := fun h => h.2 (by decide)

/-! ## Legendre-symbol helpers -/

section Helpers

variable {p : ℕ} [Fact p.Prime]

/-- A prime `q` below the prime `p` is nonzero in `ZMod p`. -/
theorem natCast_ne_zero_of_lt {q : ℕ} (hq : q.Prime) (hqp : q < p) :
    (q : ZMod p) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  have hpq : p ≤ q := Nat.le_of_dvd hq.pos h
  omega

/-- A `{2,3,5}`-smooth number is nonzero modulo a prime `p > 5`. -/
theorem smooth_ne_zero (hp : 5 < p) (i j k : ℕ) :
    ((2 ^ i * 3 ^ j * 5 ^ k : ℕ) : ZMod p) ≠ 0 := by
  have h2 := natCast_ne_zero_of_lt (p := p) Nat.prime_two (by omega)
  have h3 := natCast_ne_zero_of_lt (p := p) Nat.prime_three (by omega)
  have h5 := natCast_ne_zero_of_lt (p := p) Nat.prime_five (by omega)
  push_cast at h2 h3 h5 ⊢
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)) (pow_ne_zero _ h5)

/-- The Legendre symbol of a `{2,3,5}`-smooth number factors through
`χ(2), χ(3), χ(5)`. -/
theorem legendreSym_smooth (i j k : ℕ) :
    legendreSym p ((2 ^ i * 3 ^ j * 5 ^ k : ℕ) : ℤ) =
      legendreSym p 2 ^ i * legendreSym p 3 ^ j * legendreSym p 5 ^ k := by
  have hhom : ∀ a : ℤ, legendreSym.hom p a = legendreSym p a := fun _ => rfl
  push_cast
  simp only [← hhom, map_mul, map_pow]

/-- A `{2,3,5}`-smooth number whose Legendre-symbol product is `1` is a nonzero
quadratic residue modulo a prime `p > 5`. -/
theorem isQR_smooth (hp : 5 < p) (i j k : ℕ)
    (h : legendreSym p 2 ^ i * legendreSym p 3 ^ j * legendreSym p 5 ^ k = 1) :
    IsQR p (2 ^ i * 3 ^ j * 5 ^ k) := by
  have hne := smooth_ne_zero hp i j k
  have hneZ : (((2 ^ i * 3 ^ j * 5 ^ k : ℕ) : ℤ) : ZMod p) ≠ 0 := by
    rw [Int.cast_natCast]; exact hne
  refine ⟨?_, hne⟩
  have hsq := (legendreSym.eq_one_iff p hneZ).mp (by rw [legendreSym_smooth]; exact h)
  rw [Int.cast_natCast] at hsq
  exact hsq

/-- `χ(q) = ±1` for a prime `q < p`. -/
theorem legendreSym_prime_eq (q : ℕ) (hq : q.Prime) (hqp : q < p) :
    legendreSym p (q : ℤ) = 1 ∨ legendreSym p (q : ℤ) = -1 := by
  apply legendreSym.eq_one_or_neg_one
  rw [Int.cast_natCast]
  exact natCast_ne_zero_of_lt hq hqp

end Helpers

/-! ## The conjecture -/

/-- Large-prime case: for every prime `p > 41` one of the triangles
`(6,8,10)`, `(5,12,13)`, `(9,40,41)`, `(16,30,34)` has area and perimeter both
nonzero quadratic residues modulo `p`. -/
theorem exists_goodTriangle_of_41_lt (p : ℕ) [Fact p.Prime] (hp : 41 < p) :
    ∃ a b c : ℕ, GoodTriangle p a b c := by
  have h2 := legendreSym_prime_eq (p := p) 2 Nat.prime_two (by omega)
  have h3 := legendreSym_prime_eq (p := p) 3 Nat.prime_three (by omega)
  have h5 := legendreSym_prime_eq (p := p) 5 Nat.prime_five (by omega)
  push_cast at h2 h3 h5
  have hp5 : 5 < p := by omega
  -- the four witnesses, each conditional on its sign pattern
  have w1 (h : legendreSym p 2 ^ 3 * legendreSym p 3 ^ 1 * legendreSym p 5 ^ 0 = 1) :
      GoodTriangle p 6 8 10 :=
    ⟨by norm_num, by norm_num, by norm_num, by omega, by norm_num,
      ⟨24, by norm_num, isQR_smooth hp5 3 1 0 h⟩, isQR_smooth hp5 3 1 0 h⟩
  have w2 (h : legendreSym p 2 ^ 1 * legendreSym p 3 ^ 1 * legendreSym p 5 ^ 1 = 1) :
      GoodTriangle p 5 12 13 :=
    ⟨by norm_num, by norm_num, by norm_num, by omega, by norm_num,
      ⟨30, by norm_num, isQR_smooth hp5 1 1 1 h⟩, isQR_smooth hp5 1 1 1 h⟩
  have w3 (ha : legendreSym p 2 ^ 2 * legendreSym p 3 ^ 2 * legendreSym p 5 ^ 1 = 1)
      (hq : legendreSym p 2 ^ 1 * legendreSym p 3 ^ 2 * legendreSym p 5 ^ 1 = 1) :
      GoodTriangle p 9 40 41 :=
    ⟨by norm_num, by norm_num, by norm_num, by omega, by norm_num,
      ⟨180, by norm_num, isQR_smooth hp5 2 2 1 ha⟩, isQR_smooth hp5 1 2 1 hq⟩
  have w4 (ha : legendreSym p 2 ^ 4 * legendreSym p 3 ^ 1 * legendreSym p 5 ^ 1 = 1)
      (hq : legendreSym p 2 ^ 4 * legendreSym p 3 ^ 0 * legendreSym p 5 ^ 1 = 1) :
      GoodTriangle p 16 30 34 :=
    ⟨by norm_num, by norm_num, by norm_num, by omega, by norm_num,
      ⟨240, by norm_num, isQR_smooth hp5 4 1 1 ha⟩, isQR_smooth hp5 4 0 1 hq⟩
  rcases h2 with e2 | e2 <;> rcases h3 with e3 | e3 <;> rcases h5 with e5 | e5 <;>
    simp only [e2, e3, e5] at w1 w2 w3 w4
  · exact ⟨_, _, _, w1 (by norm_num)⟩
  · exact ⟨_, _, _, w1 (by norm_num)⟩
  · exact ⟨_, _, _, w3 (by norm_num) (by norm_num)⟩
  · exact ⟨_, _, _, w2 (by norm_num)⟩
  · exact ⟨_, _, _, w4 (by norm_num) (by norm_num)⟩
  · exact ⟨_, _, _, w2 (by norm_num)⟩
  · exact ⟨_, _, _, w1 (by norm_num)⟩
  · exact ⟨_, _, _, w1 (by norm_num)⟩

/-- **Sun's second conjecture in A260960 (Zhi-Wei Sun, Aug 06 2015).**

Verbatim: "We also conjecture that for any prime p > 31, there exists a right
triangle whose three sides are among 1,...,p-1, and whose perimeter and area
are quadratic residues modulo p."

Formal reading: for every prime `p > 31` there are naturals `0 < a < b < c < p`
with `a^2 + b^2 = c^2` such that the area `A = ab/2` (`2 * A = a * b`) and the
perimeter `a + b + c` are both nonzero squares in `ZMod p`. -/
theorem sun_perimeter_area_quadratic_residue (p : ℕ) (hp : p.Prime) (h31 : 31 < p) :
    ∃ a b c : ℕ, GoodTriangle p a b c := by
  haveI hfact := Fact.mk hp
  by_cases h41 : 41 < p
  · exact exists_goodTriangle_of_41_lt p h41
  · interval_cases p <;> norm_num at hp
    · -- p = 37: the triangle (5, 12, 13), area 30 ≡ 17^2, perimeter 30
      clear hfact
      exact ⟨5, 12, 13, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
        ⟨30, by norm_num, ⟨17, by decide⟩, by decide⟩, ⟨17, by decide⟩, by decide⟩
    · -- p = 41: the triangle (12, 35, 37), area 210 ≡ 5 ≡ 13^2, perimeter 84 ≡ 2 ≡ 17^2
      clear hfact
      exact ⟨12, 35, 37, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
        ⟨210, by norm_num, ⟨13, by decide⟩, by decide⟩, ⟨17, by decide⟩, by decide⟩

/-! ## Sanity layer -/

-- The bound `31 < p` is sharp: at `p = 31` no triangle works.  (Checked by the
-- python search; here we record only that the hypotheses of the main theorem are
-- jointly satisfiable, at `p = 37`.)
example : ∃ a b c : ℕ, GoodTriangle 37 a b c :=
  sun_perimeter_area_quadratic_residue 37 (by norm_num) (by norm_num)

end Candidates.A260960SunSecondPrime
