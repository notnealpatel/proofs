/-
# A076218 — Lowell: numbers occurring twice in A055524 (refuted as stated)

## OEIS source (retrieved with `oeis show A076218`, `oeis show A055524`, and
## checked against `https://oeis.org/search?q=id:A0...&fmt=text`, 2026-10-21)

```
A076218   NAME:   Numbers n such that 2*n^2 - 3*n + 1 is a square.
          OFFSET: 1,3
          DATA:   0,1,5,145,4901,166465,5654885,192099601,6525731525,...
COMMENT:  Conjecture: a nonzero number occurs twice in A055524 if and only if
          it's in this sequence. - _J. Lowell_, Jul 23 2016
COMMENT:  Equivalently, n=0 or both n-1 and 2*n-1 are perfect squares.
          - _Sture Sjöstedt_, Feb 22 2017

A055524   NAME:   Longest other side of a Pythagorean triangle with n as length
                  of one of the three sides (in fact n is a leg and a(n) the
                  hypotenuse).
          OFFSET: 3,1
          DATA:   5,5,13,10,25,17,41,26,61,37,85,50,113,65,145,82,181,101,...
FORMULA:  a(2k) = k^2+1, a(2k+1) = k^2+(k+1)^2.
```

No later comment in A076218 retracts or amends the conjecture.

## Status

**Refuted as stated** (`conjecture_false`).  The counterexample is `1`:
it is nonzero and a term of A076218 (`2 - 3 + 1 = 0 = 0^2`), but `1` never
occurs in A055524 at all (every value is a hypotenuse `c` with a positive
leg `b < c`, so `c ≥ 2`; see `a055524_ne_one`).  The refutation therefore
does not depend on whether "occurs twice" means "at least twice" or
"exactly twice".

A Python check (`/tmp/claude/a076218.py`, 2026-10-21) confirmed the closed
form of A055524 against a brute-force maximal hypotenuse for `3 ≤ n < 400`,
that no value of A055524 occurs more than twice for `3 ≤ n < 200000`, and
that the doubled values below the complete range are exactly
`5, 145, 4901, 166465, 5654885, 192099601, 6525731525`, i.e. the terms of
A076218 other than `0` and `1`.

The intended statement presumably reads "a number greater than `1`" (the
boundary term `a(2) = 1` of A076218 was overlooked).  That corrected form is
proved here as `occursTwice_iff_mem_of_two_le`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A076218Refutation

/-! ## Definition layer -/

/-- `c` is the hypotenuse of a Pythagorean triangle with leg `n`: there is a
positive other leg `b` with `n^2 + b^2 = c^2`.  The bound `b < c` is automatic
for `0 < n` and only makes the predicate decidable. -/
def IsHypWithLeg (n c : ℕ) : Prop := ∃ b < c, 0 < b ∧ n ^ 2 + b ^ 2 = c ^ 2

/-- Decidability of `IsHypWithLeg` through its bounded existential. -/
instance instDecidableIsHypWithLeg (n c : ℕ) : Decidable (IsHypWithLeg n c) := by
  unfold IsHypWithLeg
  infer_instance

/-- A055524 (offset 3): the longest other side of a Pythagorean triangle with
`n` as one side, which is the largest hypotenuse with leg `n`.  The search bound
`n^2` loses nothing, by `le_sq_of_isHypWithLeg`; see also
`isHypWithLeg_le_a055524`.  Values at `n < 3` are junk (`0`) and are never
used. -/
def a055524 (n : ℕ) : ℕ := Nat.findGreatest (IsHypWithLeg n) (n ^ 2)

/-- A076218 as a set: numbers `n` such that `2n^2 - 3n + 1` is a square.  The
expression is evaluated in `ℤ`, so no truncated subtraction occurs. -/
def a076218 : Set ℕ := {n | IsSquare (2 * (n : ℤ) ^ 2 - 3 * n + 1)}

/-- A number occurs twice in A055524: it is the value at two distinct indices
`i, j ≥ 3` (the offset of A055524).  No value occurs three times
(`occursTwice_iff` gives the shape of the doubled values). -/
def OccursTwice (m : ℕ) : Prop :=
  ∃ i j, 3 ≤ i ∧ 3 ≤ j ∧ i ≠ j ∧ a055524 i = m ∧ a055524 j = m

/-! ## Structure of A055524 -/

/-- A hypotenuse `c` with leg `n` is `c = b + d` with `d ≥ 1` and
`n^2 = d (2b + d)`. -/
theorem exists_of_isHypWithLeg {n c : ℕ} (h : IsHypWithLeg n c) :
    ∃ b d, 0 < b ∧ 1 ≤ d ∧ c = b + d ∧ n ^ 2 = d * (2 * b + d) := by
  obtain ⟨b, hbc, hb, hsq⟩ := h
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hbc
  refine ⟨b, d + 1, hb, by omega, by ring, ?_⟩
  nlinarith

/-- Every hypotenuse with leg `n` is at most `n^2`, so the search bound in
`a055524` is harmless. -/
theorem le_sq_of_isHypWithLeg {n c : ℕ} (h : IsHypWithLeg n c) : c ≤ n ^ 2 := by
  obtain ⟨b, d, hb, hd, rfl, hsq⟩ := exists_of_isHypWithLeg h
  nlinarith

/-- `a055524 n` is an upper bound for every hypotenuse with leg `n`. -/
theorem isHypWithLeg_le_a055524 {n c : ℕ} (h : IsHypWithLeg n c) : c ≤ a055524 n :=
  Nat.le_findGreatest (le_sq_of_isHypWithLeg h) h

/-- Every hypotenuse with leg `n` satisfies `2c ≤ n^2 + 1`. -/
theorem two_mul_le_of_isHypWithLeg {n c : ℕ} (h : IsHypWithLeg n c) :
    2 * c ≤ n ^ 2 + 1 := by
  obtain ⟨b, d, hb, hd, rfl, hsq⟩ := exists_of_isHypWithLeg h
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hd
  nlinarith

/-- Every hypotenuse with even leg `2k` is at most `k^2 + 1`. -/
theorem le_of_isHypWithLeg_two_mul {k c : ℕ} (h : IsHypWithLeg (2 * k) c) :
    c ≤ k ^ 2 + 1 := by
  obtain ⟨b, d, hb, hd, rfl, hsq⟩ := exists_of_isHypWithLeg h
  rcases Nat.even_or_odd d with ⟨e, rfl⟩ | ⟨e, rfl⟩
  · have hk : k ^ 2 = e * (b + e) := by nlinarith
    obtain ⟨f, rfl⟩ := Nat.exists_eq_add_of_le (show 1 ≤ e by omega)
    nlinarith
  · exfalso
    have h1 : (2 * k) ^ 2 = 2 * (2 * k ^ 2) := by ring
    have h2 : (2 * e + 1) * (2 * b + (2 * e + 1)) =
        2 * (2 * e * b + 2 * e ^ 2 + 2 * e + b) + 1 := by ring
    omega

/-- The OEIS formula `a(2k+1) = k^2 + (k+1)^2` for `k ≥ 1`. -/
theorem a055524_two_mul_add_one (k : ℕ) (hk : 1 ≤ k) :
    a055524 (2 * k + 1) = k ^ 2 + (k + 1) ^ 2 := by
  rw [a055524, Nat.findGreatest_eq_iff]
  refine ⟨by nlinarith, fun _ => ⟨2 * k ^ 2 + 2 * k, by nlinarith, by positivity, by ring⟩, ?_⟩
  intro c hc _ hP
  have h2c := two_mul_le_of_isHypWithLeg hP
  nlinarith

/-- The OEIS formula `a(2k) = k^2 + 1` for `k ≥ 2`. -/
theorem a055524_two_mul (k : ℕ) (hk : 2 ≤ k) : a055524 (2 * k) = k ^ 2 + 1 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hsub : (2 + j) ^ 2 - 1 = j ^ 2 + 4 * j + 3 := by
    have hexp : (2 + j) ^ 2 = j ^ 2 + 4 * j + 3 + 1 := by ring
    omega
  rw [a055524, Nat.findGreatest_eq_iff]
  refine ⟨by nlinarith, fun _ => ⟨(2 + j) ^ 2 - 1, ?_, ?_, ?_⟩, ?_⟩
  · rw [hsub]
    nlinarith
  · rw [hsub]
    omega
  · rw [hsub]
    ring
  · intro c hc _ hP
    have hle := le_of_isHypWithLeg_two_mul hP
    omega

/-- No value of A055524 equals `1` (a hypotenuse exceeds a positive leg). -/
theorem a055524_ne_one (n : ℕ) : a055524 n ≠ 1 := by
  intro h
  obtain ⟨-, hP, -⟩ := Nat.findGreatest_eq_iff.mp h
  obtain ⟨b, hb, hb0, -⟩ := hP one_ne_zero
  omega

/-! ## Ground truth -/

-- The first six terms of A055524 (offset 3), by direct evaluation:
-- 5, 5, 13, 10, 25, 17.
example : (List.range 6).map (fun i => a055524 (i + 3)) = [5, 5, 13, 10, 25, 17] := by
  decide

-- The next terms 41, 26, 61, 37 through the proved closed forms.
example : a055524 9 = 41 ∧ a055524 10 = 26 ∧ a055524 11 = 61 ∧ a055524 12 = 37 :=
  ⟨a055524_two_mul_add_one 4 (by norm_num), a055524_two_mul 5 (by norm_num),
    a055524_two_mul_add_one 5 (by norm_num), a055524_two_mul 6 (by norm_num)⟩

-- The first terms of A076218: 0, 1, 5, 145 are members; 2, 3, 4, 6 are not.
example : 0 ∈ a076218 ∧ 1 ∈ a076218 ∧ 5 ∈ a076218 ∧ 145 ∈ a076218 ∧
    2 ∉ a076218 ∧ 3 ∉ a076218 ∧ 4 ∉ a076218 ∧ 6 ∉ a076218 := by
  simp only [a076218, Set.mem_ofPred_eq]
  norm_num

-- `5` occurs twice: `a(3) = a(4) = 5`.
example : OccursTwice 5 := ⟨3, 4, le_rfl, by norm_num, by norm_num, by decide, by decide⟩

/-! ## The conjecture and its refutation -/

/-- **Lowell's conjecture (A076218, J. Lowell, Jul 23 2016).**

Verbatim: "Conjecture: a nonzero number occurs twice in A055524 if and only if
it's in this sequence."

"Occurs twice" is read as "is the value of A055524 at two distinct indices";
since no value occurs three times, this agrees with "exactly twice". -/
def Conjecture : Prop := ∀ m : ℕ, m ≠ 0 → (OccursTwice m ↔ m ∈ a076218)

/-- **Lowell's conjecture is false.**  Counterexample `m = 1`: it is a nonzero
term of A076218 (`2 - 3 + 1 = 0`, a square) but never occurs in A055524
(`a055524_ne_one`).  The author probably intended "a number greater than `1`";
that form is `occursTwice_iff_mem_of_two_le`. -/
theorem conjecture_false : ¬ Conjecture := by
  intro hconj
  have hmem : (1 : ℕ) ∈ a076218 := ⟨0, by norm_num⟩
  obtain ⟨i, -, -, -, -, hi, -⟩ := (hconj 1 one_ne_zero).mpr hmem
  exact a055524_ne_one i hi

/-! ## The corrected statement -/

/-- The doubled values of A055524 are exactly the numbers that are both
`k^2 + 1` (`k ≥ 2`) and `j^2 + (j+1)^2` (`j ≥ 1`). -/
theorem occursTwice_iff (m : ℕ) :
    OccursTwice m ↔ ∃ k j, 2 ≤ k ∧ 1 ≤ j ∧ m = k ^ 2 + 1 ∧ m = j ^ 2 + (j + 1) ^ 2 := by
  constructor
  · rintro ⟨i, j, hi, hj, hij, hai, haj⟩
    have key : ∀ i j, 3 ≤ i → 3 ≤ j → i ≠ j → a055524 i = m → a055524 j = m → Even i →
        ∃ k j, 2 ≤ k ∧ 1 ≤ j ∧ m = k ^ 2 + 1 ∧ m = j ^ 2 + (j + 1) ^ 2 := by
      intro i j hi hj hij hai haj ⟨k, hk⟩
      have hk2 : 2 ≤ k := by omega
      rw [show i = 2 * k by omega, a055524_two_mul k hk2] at hai
      rcases Nat.even_or_odd j with ⟨l, hl⟩ | ⟨l, hl⟩
      · exfalso
        rw [hl, show l + l = 2 * l by ring, a055524_two_mul l (by omega)] at haj
        have hkl : k ^ 2 = l ^ 2 := by omega
        have hkl' : k = l := Nat.pow_left_injective (by norm_num) hkl
        omega
      · rw [hl, a055524_two_mul_add_one l (by omega)] at haj
        exact ⟨k, l, hk2, by omega, hai.symm, haj.symm⟩
    rcases Nat.even_or_odd i with hie | hio
    · exact key i j hi hj hij hai haj hie
    · rcases Nat.even_or_odd j with hje | hjo
      · exact key j i hj hi (Ne.symm hij) haj hai hje
      · exfalso
        obtain ⟨k, rfl⟩ := hio
        obtain ⟨l, rfl⟩ := hjo
        rw [a055524_two_mul_add_one k (by omega)] at hai
        rw [a055524_two_mul_add_one l (by omega)] at haj
        rcases lt_trichotomy k l with hkl | hkl | hkl
        · nlinarith
        · omega
        · nlinarith
  · rintro ⟨k, j, hk, hj, hmk, hmj⟩
    refine ⟨2 * k, 2 * j + 1, by omega, by omega, by omega, ?_, ?_⟩
    · rw [a055524_two_mul k hk, hmk]
    · rw [a055524_two_mul_add_one j hj, hmj]

/-- For `m ≥ 2`, membership in A076218 means `m - 1` and `2m - 1` are both
squares, i.e. `m = k^2 + 1 = j^2 + (j+1)^2` (Sjöstedt's comment), using that
`(2m - 1)(m - 1)` has coprime factors. -/
theorem mem_a076218_iff_of_two_le (m : ℕ) (hm : 2 ≤ m) :
    m ∈ a076218 ↔ ∃ k j, 2 ≤ k ∧ 1 ≤ j ∧ m = k ^ 2 + 1 ∧ m = j ^ 2 + (j + 1) ^ 2 := by
  constructor
  · rintro ⟨r, hr⟩
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hm
    have hnat : (2 * t + 3) * (t + 1) = r.natAbs ^ 2 := by
      have hz : ((2 * t + 3) * (t + 1) : ℕ) = ((r.natAbs ^ 2 : ℕ) : ℤ) := by
        push_cast
        rw [sq_abs, sq, ← hr]
        push_cast
        ring
      exact_mod_cast hz
    have hcop : Nat.Coprime (2 * t + 3) (t + 1) := by
      have hsplit : 2 * t + 3 = 1 + (t + 1) * 2 := by ring
      rw [hsplit, Nat.coprime_add_mul_left_left]
      exact Nat.coprime_one_left _
    obtain ⟨d, hd⟩ := exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr hcop) hnat
    obtain ⟨e, he⟩ := exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr hcop.symm)
      ((mul_comm _ _).trans hnat)
    rcases Nat.even_or_odd d with ⟨q, rfl⟩ | ⟨j, rfl⟩
    · exfalso
      have hq : (q + q) ^ 2 = 2 * (2 * q ^ 2) := by ring
      omega
    · have hj : 1 ≤ j := by
        rcases Nat.eq_zero_or_pos j with h0 | h0
        · subst h0
          omega
        · exact h0
      have hdj : (2 * j + 1) ^ 2 = 4 * j ^ 2 + 4 * j + 1 := by ring
      have hm' : 2 + t = j ^ 2 + (j + 1) ^ 2 := by nlinarith
      refine ⟨e, j, ?_, hj, by omega, hm'⟩
      by_contra hlt
      have he1 : e ≤ 1 := by omega
      have he2 : e ^ 2 ≤ 1 := by nlinarith
      nlinarith
  · rintro ⟨k, j, -, -, hmk, hmj⟩
    refine ⟨(k : ℤ) * (2 * j + 1), ?_⟩
    have hmk' : (m : ℤ) = k ^ 2 + 1 := by exact_mod_cast hmk
    have hmj' : (m : ℤ) = j ^ 2 + (j + 1) ^ 2 := by exact_mod_cast hmj
    linear_combination (2 * (m : ℤ) - 1) * hmk' + 2 * (k : ℤ) ^ 2 * hmj'

/-- **Corrected Lowell statement.**  A number `m ≥ 2` occurs twice in A055524
if and only if it is a term of A076218.  The boundary `2 ≤ m` is sharp: `1` is
a term of A076218 that does not occur (`conjecture_false`), and `0` is a term
that does not occur either. -/
theorem occursTwice_iff_mem_of_two_le (m : ℕ) (hm : 2 ≤ m) :
    OccursTwice m ↔ m ∈ a076218 := by
  rw [occursTwice_iff, mem_a076218_iff_of_two_le m hm]

end Candidates.A076218Refutation
