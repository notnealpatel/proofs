/-
# A160191 — Lodumo_8 of the Lucas numbers: a(n) = 2a(n-6) - a(n-12)

## OEIS source (retrieved with `oeis show A160191`, 2026-10-21)

```
NAME:     Lodumo_8 of Lucas numbers.
TERMS:    2,1,3,4,7,11,10,5,15,12,19,23,18,9,27,20,31,35,26,13,39,28,43,47,34,
          17,51,36,55,59,42,21,63,44,67,71,50,25,75,52,79,83,58,29,87,60,91,95,
          66,33,99,68,103,107,74,37,111,76,115,119,82,41,123,84,127,131,90,45,135
COMMENT:  Numbers congruent to {0,6} mod 8 are missing (see A047451).
FORMULA:  Lodumo_8 transform of A000032 (for definition see Transforms).
FORMULA (the conjecture):
  Conjecture: a(n)= +2*a(n-6) -a(n-12) . - _R. J. Mathar_, Oct 08 2011
FORMULA:  Empirical g.f.: (x^11 +5*x^10 +4*x^9 +9*x^8 +3*x^7 +6*x^6 +11*x^5
          +7*x^4 +4*x^3 +3*x^2 +x +2) / ((x -1)^2*(x +1)^2*(x^2 -x +1)^2
          *(x^2 +x +1)^2). - _Colin Barker_, Oct 04 2014
```

The OEIS Transforms page defines Lodumo_m of a sequence `b`: `a(n)` is the
smallest nonnegative integer not already among `a(0), …, a(n-1)` with
`a(n) ≡ b(n) (mod m)`.  Offset 0, `b = A000032` (Lucas, `L(0) = 2, L(1) = 1`).

## Status

Triage: open (no proof in the entry or the literature as far as the triage
could tell; the g.f. is marked empirical).  Recomputed 2026-10-21: the greedy
transform reproduces all 69 listed terms and the recurrence holds for
`12 ≤ n < 3000`.

## Result

Proved here (`lodumo8_lucas_recurrence`), with no `sorry`.  The argument:
1. For any `m > 0` and any `b`, Lodumo_m has the closed form
   `a(n) = b(n) % m + m * #{i < n : b(i) ≡ b(n) (mod m)}`
   (`lodumo_eq_closedForm`): the values with residue `r` produced before step
   `n` are exactly `r, r + m, …, r + m(c - 1)` (`exists_closedForm_iff`).
2. Lucas numbers mod 8 have period 12, so the residue counts are linear in
   the number of full periods (`cnt_mul_add`).
3. A 12-case kernel `decide` check over one period (`period_table`) finishes.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A160191LodumoTransformLucas

/-! ## Definition layer

`leandoc Nat.lucas` returns `mode:"miss"`: Mathlib has no Lucas numbers, so
they are defined here by the A000032 recurrence.  The Lodumo transform is not
in Mathlib either; it is defined by strong recursion with `Nat.find`, mirroring
the Transforms-page definition verbatim. -/

/-- The Lucas numbers A000032: `L(0) = 2`, `L(1) = 1`, `L(n+2) = L(n) + L(n+1)`. -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => lucas n + lucas (n + 1)

example : (List.range 12).map lucas = [2, 1, 3, 4, 7, 11, 18, 29, 47, 76, 123, 199] := by
  decide

/-- For `m > 0` some residue representative of `r` mod `m` avoids any finite
set `S`; this is the existence proof the Lodumo `Nat.find` consumes. -/
theorem exists_fresh (m : ℕ) [NeZero m] (r : ℕ) (S : Finset ℕ) :
    ∃ x, x % m = r % m ∧ x ∉ S := by
  refine ⟨r % m + m * (S.sup id + 1), ?_, ?_⟩
  · simp [Nat.add_mul_mod_self_left]
  · intro hx
    have hle : r % m + m * (S.sup id + 1) ≤ S.sup id := Finset.le_sup (f := id) hx
    have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
    have hmul : S.sup id + 1 ≤ m * (S.sup id + 1) := Nat.le_mul_of_pos_left _ hm
    omega

/-- The Lodumo_m transform of `b` (OEIS Transforms page): `lodumo m b n` is the
least natural number congruent to `b n` modulo `m` that is not one of
`lodumo m b 0, …, lodumo m b (n - 1)`. -/
def lodumo (m : ℕ) [NeZero m] (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.find (exists_fresh m (b n) (Finset.univ.image fun i : Fin n => lodumo m b i))
termination_by n
decreasing_by all_goals exact i.isLt


/-- `cnt m b r n` is the number of indices `i < n` with `b i % m = r`. -/
def cnt (m : ℕ) (b : ℕ → ℕ) (r n : ℕ) : ℕ :=
  ((Finset.range n).filter fun i => b i % m = r).card

/-- The closed form of the Lodumo transform:
`b n % m + m * #{i < n : b i % m = b n % m}`. -/
def closedForm (m : ℕ) (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  b n % m + m * cnt m b (b n % m) n

/-- No index lies below `0`. -/
theorem cnt_zero (m : ℕ) (b : ℕ → ℕ) (r : ℕ) : cnt m b r 0 = 0 := by
  simp [cnt]

/-- One-step recursion for the residue count. -/
theorem cnt_succ (m : ℕ) (b : ℕ → ℕ) (r n : ℕ) :
    cnt m b r (n + 1) = cnt m b r n + if b n % m = r then 1 else 0 := by
  unfold cnt
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · simp

/-- The closed form has the residue of `b n`. -/
theorem closedForm_mod (m : ℕ) [NeZero m] (b : ℕ → ℕ) (n : ℕ) :
    closedForm m b n % m = b n % m := by
  simp [closedForm, Nat.add_mul_mod_self_left]

/-- The quotient of the closed form by `m` is the earlier count of the residue. -/
theorem closedForm_div (m : ℕ) [NeZero m] (b : ℕ → ℕ) (n : ℕ) :
    closedForm m b n / m = cnt m b (b n % m) n := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  unfold closedForm
  rw [Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt (Nat.mod_lt _ hm), zero_add]

/-- The closed-form values at indices `i < n` are exactly the `x` whose
quotient `x / m` is below the count of `x`'s residue among the first `n`
indices, i.e. `r, r + m, …, r + m (c - 1)` for each residue `r`. -/
theorem exists_closedForm_iff (m : ℕ) [NeZero m] (b : ℕ → ℕ) (n x : ℕ) :
    (∃ i < n, closedForm m b i = x) ↔ x / m < cnt m b (x % m) n := by
  induction n with
  | zero => simp [cnt_zero]
  | succ n ih =>
    have hsplit : (∃ i < n + 1, closedForm m b i = x) ↔
        (∃ i < n, closedForm m b i = x) ∨ closedForm m b n = x := by
      constructor
      · rintro ⟨i, hi, hix⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
        · exact Or.inl ⟨i, hi', hix⟩
        · exact Or.inr hix
      · rintro (⟨i, hi, hix⟩ | h)
        · exact ⟨i, by omega, hix⟩
        · exact ⟨n, by omega, h⟩
    rw [hsplit, ih, cnt_succ]
    have hmod := closedForm_mod m b n
    have hdiv := closedForm_div m b n
    by_cases hr : b n % m = x % m
    · rw [if_pos hr]
      have hiff : closedForm m b n = x ↔ x / m = cnt m b (x % m) n := by
        constructor
        · rintro rfl
          rw [hdiv, hmod]
        · intro h
          rw [← Nat.mod_add_div (closedForm m b n) m, ← Nat.mod_add_div x m, hmod, hdiv, hr, h]
      rw [hiff]
      omega
    · rw [if_neg hr, add_zero]
      have hne : closedForm m b n ≠ x := by
        rintro rfl
        exact hr hmod.symm
      simp [hne]

/-- **Closed form of the Lodumo transform.** For every `m > 0` and every `b`,
`lodumo m b n = b n % m + m * #{i < n : b i ≡ b n (mod m)}`. -/
theorem lodumo_eq_closedForm (m : ℕ) [NeZero m] (b : ℕ → ℕ) (n : ℕ) :
    lodumo m b n = closedForm m b n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hmem : ∀ y, y ∈ (Finset.univ.image fun i : Fin n => lodumo m b i) ↔
        y / m < cnt m b (y % m) n := by
      intro y
      rw [← exists_closedForm_iff]
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨i, i.isLt, (ih i i.isLt).symm⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨⟨i, hi⟩, ih i hi⟩
    rw [lodumo, Nat.find_eq_iff]
    refine ⟨⟨closedForm_mod m b n, ?_⟩, ?_⟩
    · rw [hmem, closedForm_div, closedForm_mod]
      exact lt_irrefl _
    · rintro y hy ⟨hymod, hynot⟩
      apply hynot
      rw [hmem, hymod, ← closedForm_div]
      by_contra hlt
      have hge := not_lt.mp hlt
      have hcf := Nat.mod_add_div (closedForm m b n) m
      have hyd := Nat.mod_add_div y m
      rw [closedForm_mod] at hcf
      rw [hymod] at hyd
      have hmul : m * (closedForm m b n / m) ≤ m * (y / m) := Nat.mul_le_mul_left m hge
      omega

/-- The Lucas numbers have period 12 modulo 8. -/
theorem lucas_add_twelve_mod (n : ℕ) : lucas (n + 12) % 8 = lucas n % 8 := by
  have key : ∀ n, lucas (n + 12) % 8 = lucas n % 8 ∧ lucas (n + 13) % 8 = lucas (n + 1) % 8 := by
    intro n
    induction n with
    | zero => decide
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have e1 : lucas (k + 1 + 13) = lucas (k + 12) + lucas (k + 13) := rfl
      have e2 : lucas (k + 1 + 1) = lucas k + lucas (k + 1) := rfl
      rw [e1, e2, Nat.add_mod, ih.1, ih.2, ← Nat.add_mod]
  exact (key n).1

/-- Iterated period: `L(12 q + j) ≡ L(j) (mod 8)`. -/
theorem lucas_mul_add_mod (q j : ℕ) : lucas (12 * q + j) % 8 = lucas j % 8 := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show 12 * (q + 1) + j = (12 * q + j) + 12 by ring, lucas_add_twelve_mod, ih]

/-- One more full period adds the period count of each residue. -/
theorem cnt_add_twelve (r k : ℕ) : cnt 8 lucas r (k + 12) = cnt 8 lucas r k + cnt 8 lucas r 12 := by
  induction k with
  | zero => simp [cnt_zero]
  | succ k ih =>
    rw [show k + 1 + 12 = (k + 12) + 1 by ring, cnt_succ 8 lucas r (k + 12), ih,
      cnt_succ 8 lucas r k, lucas_add_twelve_mod]
    ring

/-- Residue counts of the Lucas numbers mod 8 are linear in the number of
full periods: `cnt r (12 q + j) = q * cnt r 12 + cnt r j`. -/
theorem cnt_mul_add (r q j : ℕ) :
    cnt 8 lucas r (12 * q + j) = q * cnt 8 lucas r 12 + cnt 8 lucas r j := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show 12 * (q + 1) + j = (12 * q + j) + 12 by ring, cnt_add_twelve, ih]
    ring

/-- The finite period check: for each `j < 12`, the residues at `j` and
`j + 6` occur equally often per period, and the constant terms of the
recurrence agree. -/
theorem period_table : ∀ j < 12,
    cnt 8 lucas (lucas j % 8) 12 = cnt 8 lucas (lucas (j + 6) % 8) 12 ∧
    2 * (lucas j % 8) + 8 * cnt 8 lucas (lucas j % 8) 12 + 16 * cnt 8 lucas (lucas j % 8) j =
      2 * (lucas (j + 6) % 8) + 16 * cnt 8 lucas (lucas (j + 6) % 8) (j + 6) := by
  decide


/-- The recurrence in additive form over `ℕ`: `a(n+12) + a(n) = 2 a(n+6)`. -/
theorem lodumo8_lucas_add (n : ℕ) :
    lodumo 8 lucas (n + 12) + lodumo 8 lucas n = 2 * lodumo 8 lucas (n + 6) := by
  simp only [lodumo_eq_closedForm, closedForm]
  obtain ⟨hC, hlin⟩ := period_table (n % 12) (Nat.mod_lt n (by norm_num))
  have hn : n = 12 * (n / 12) + n % 12 := (Nat.div_add_mod n 12).symm
  set q := n / 12
  set j := n % 12
  have r0 : lucas n % 8 = lucas j % 8 := by rw [hn, lucas_mul_add_mod]
  have r12 : lucas (n + 12) % 8 = lucas j % 8 := by rw [lucas_add_twelve_mod, r0]
  have r6 : lucas (n + 6) % 8 = lucas (j + 6) % 8 := by
    rw [hn, show 12 * q + j + 6 = 12 * q + (j + 6) by ring, lucas_mul_add_mod]
  have c0 : cnt 8 lucas (lucas j % 8) n =
      q * cnt 8 lucas (lucas j % 8) 12 + cnt 8 lucas (lucas j % 8) j := by
    rw [hn, cnt_mul_add]
  have c12 : cnt 8 lucas (lucas j % 8) (n + 12) =
      q * cnt 8 lucas (lucas j % 8) 12 + cnt 8 lucas (lucas j % 8) j +
        cnt 8 lucas (lucas j % 8) 12 := by
    rw [cnt_add_twelve, c0]
  have c6 : cnt 8 lucas (lucas (j + 6) % 8) (n + 6) =
      q * cnt 8 lucas (lucas (j + 6) % 8) 12 + cnt 8 lucas (lucas (j + 6) % 8) (j + 6) := by
    rw [hn, show 12 * q + j + 6 = 12 * q + (j + 6) by ring, cnt_mul_add]
  rw [r0, r12, r6, c0, c12, c6, ← hC]
  linarith

/-- The sequence A160191 itself: the Lodumo_8 transform of the Lucas numbers. -/
def a160191 (n : ℕ) : ℕ := lodumo 8 lucas n

/-- Ground truth: the first 69 terms agree with the OEIS data. -/
example : (List.range 69).map a160191 =
    [2, 1, 3, 4, 7, 11, 10, 5, 15, 12, 19, 23, 18, 9, 27, 20, 31, 35, 26, 13, 39, 28, 43, 47,
      34, 17, 51, 36, 55, 59, 42, 21, 63, 44, 67, 71, 50, 25, 75, 52, 79, 83, 58, 29, 87, 60,
      91, 95, 66, 33, 99, 68, 103, 107, 74, 37, 111, 76, 115, 119, 82, 41, 123, 84, 127, 131,
      90, 45, 135] := by
  have hfun : a160191 = closedForm 8 lucas := funext fun n => lodumo_eq_closedForm 8 lucas n
  rw [hfun]
  decide

/-- **Mathar's conjecture (A160191, R. J. Mathar, Oct 08 2011), proved.**

Verbatim: "Conjecture: a(n)= +2*a(n-6) -a(n-12)", for `a` the Lodumo_8
transform of the Lucas numbers.  Stated with shifted indices
`a(n + 12) = 2 a(n + 6) - a(n)` for every `n`, subtracting in `ℤ`. -/
theorem lodumo8_lucas_recurrence (n : ℕ) :
    (a160191 (n + 12) : ℤ) = 2 * a160191 (n + 6) - a160191 n := by
  have h := lodumo8_lucas_add n
  unfold a160191
  omega

/-- The conjecture in the entry's indexing: `a(n) = 2 a(n-6) - a(n-12)` for
every `n ≥ 12` (the range where all indices are defined), subtracting in `ℤ`. -/
theorem lodumo8_lucas_recurrence_of_le (n : ℕ) (hn : 12 ≤ n) :
    (a160191 n : ℤ) = 2 * a160191 (n - 6) - a160191 (n - 12) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have h := lodumo8_lucas_recurrence k
  rw [show k + 12 - 6 = k + 6 by omega, show k + 12 - 12 = k by omega]
  exact h

end Candidates.A160191LodumoTransformLucas
