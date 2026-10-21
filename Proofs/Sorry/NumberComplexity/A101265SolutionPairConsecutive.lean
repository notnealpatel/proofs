/-
# A101265 — solutions of `a*b ∣ (a+b)(a+b+1)` are consecutive-term pairs

## OEIS source (retrieved with `oeis show A101265` and the oeis.org internal
## format, 2026-10-21)

```
A101265  NAME:   a(1) = 1, a(2) = 2, a(3) = 6;
                 a(n) = 5*a(n-1) - 5*a(n-2) + a(n-3) for n > 3.
         OFFSET: 1,2
         TERMS:  1,2,6,21,77,286,1066,3977,14841,55386,206702,771421,...
         COMMENT (the conjecture):
           Conjecture: consecutive terms of this sequence and consecutive terms
           of A032908 provide all the positive integer solutions of
           (a+b)*(a+b+1) == 0 (mod (a*b)). - _Robert Israel_, Aug 26 2015
         COMMENT: Conjecture is true: see StackExchange link.
           - _Robert Israel_, Sep 06 2015
         LINK:   R. Israel, W. Jagy et al., Diophantine equation
                 (x+y)(x+y+1)-kxy=0, Math StackExchange, Sep 1 2015
                 (question 1417404).
         FORMULA: (a(n) + a(n+1))*(a(n) + a(n+1) + 1) = 6 * a(n) * a(n+1).
A032908  NAME:   One of four 3rd-order recurring sequences for which the first
                 derived sequence and the Galois transformed sequence coincide.
         OFFSET: 0,1
         TERMS:  2,2,3,6,14,35,90,234,611,1598,4182,10947,...
         FORMULA: G.f.: (2 - 6*x + 3*x^2)/((1 - x)*(1 - 3*x + x^2)).
         FORMULA: a(n) = 4*a(n-1) - 4*a(n-2) + a(n-3).
         FORMULA: (a(n) + a(n+1))*(a(n) + a(n+1) + 1) = 5*a(n)*a(n+1).
```

Target statement (triage wording): "Every positive integer solution (a,b) of
a*b | (a+b)(a+b+1) is a pair of consecutive terms of A101265 or of A032908."

## Literature status (triage)

Proved elsewhere: the entry records "Conjecture is true: see StackExchange
link" (R. Israel, Sep 2015); the argument is Vieta jumping.

## Outcome of this module

The literal statement is **false at one boundary point**: `(a, b) = (1, 1)`
solves `1 ∣ 2 * 3`, but with the entry's offsets (A101265 starts
`a(1) = 1, a(2) = 2`; A032908 is `≥ 2`) it is not a pair of consecutive
terms of either sequence.  The pair `(1, 1)` is the extra term `a(0) = 1`
obtained by running the A101265 recurrence backwards, which the entry's
listed data omit.  This module proves

* `literal_conjecture_false`: the kernel-checked refutation at `(1, 1)`;
* `solution_classification`: every positive solution is `(1, 1)` or an
  (unordered) pair of consecutive terms of A101265 or A032908;
* `consecutive_terms_are_solutions`: the converse, so the classification is
  exact.

The proof is Vieta jumping on `a^2 + b^2 + a + b = m*a*b`, the equation
equivalent to `a*b ∣ (a+b)(a+b+1)` with `m = k - 2`.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A101265SolutionPairConsecutive

/-! ## Definition layer -/

/-- OEIS A101265 (offset 1), mirroring the entry's NAME:
`a(1) = 1, a(2) = 2, a(3) = 6`, `a(n) = 5 a(n-1) - 5 a(n-2) + a(n-3)` for
`n > 3`.  Valued in `ℤ` so the recurrence's subtraction is not truncated.
Index `0` lies outside the entry's offset; its value `0` is a placeholder
and every statement below uses only indices `n ≥ 1`. -/
def a101265 : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 6
  | n + 4 => 5 * a101265 (n + 3) - 5 * a101265 (n + 2) + a101265 (n + 1)

/-- OEIS A032908 (offset 0), via the entry's g.f.
`(2 - 6x + 3x^2)/((1 - x)(1 - 3x + x^2))`, i.e. initial terms `2, 2, 3` and
the recurrence `a(n) = 4 a(n-1) - 4 a(n-2) + a(n-3)` from the FORMULA
section.  Valued in `ℤ` so the subtraction is not truncated. -/
def a032908 : ℕ → ℤ
  | 0 => 2
  | 1 => 2
  | 2 => 3
  | n + 3 => 4 * a032908 (n + 2) - 4 * a032908 (n + 1) + a032908 n

-- Ground truth: the first eleven listed terms of A101265 (offset 1).
example : (List.range 11).map (fun n => a101265 (n + 1)) =
    [1, 2, 6, 21, 77, 286, 1066, 3977, 14841, 55386, 206702] := by decide

-- Ground truth: the first twelve listed terms of A032908 (offset 0).
example : (List.range 12).map a032908 =
    [2, 2, 3, 6, 14, 35, 90, 234, 611, 1598, 4182, 10947] := by decide

/-- The Vieta chain with parameter `m` and seed `c`:
`v 0 = v 1 = c`, `v (n+2) = m * v (n+1) - v n - 1`.  Consecutive terms
are exactly the solutions of `x^2 + y^2 + x + y = m x y` reached from the
diagonal solution `(c, c)`. -/
def vieta (m c : ℤ) : ℕ → ℤ
  | 0 => c
  | 1 => c
  | n + 2 => m * vieta m c (n + 1) - vieta m c n - 1

example : (List.range 6).map (vieta 4 1) = [1, 1, 2, 6, 21, 77] := by decide
example : (List.range 6).map (vieta 3 2) = [2, 2, 3, 6, 14, 35] := by decide

/-! ## The Vieta chain -/

/-- The Vieta chain satisfies the third-order recurrence
`v (n+3) = (m+1) v (n+2) - (m+1) v (n+1) + v n`. -/
theorem vieta_add_three (m c : ℤ) (n : ℕ) :
    vieta m c (n + 3) =
      (m + 1) * vieta m c (n + 2) - (m + 1) * vieta m c (n + 1) + vieta m c n := by
  have h3 : vieta m c (n + 3) = m * vieta m c (n + 2) - vieta m c (n + 1) - 1 := rfl
  have h2 : vieta m c (n + 2) = m * vieta m c (n + 1) - vieta m c n - 1 := rfl
  rw [h3]
  linear_combination (-1 : ℤ) * h2

/-- A101265 coincides with the Vieta chain `vieta 4 1` on its offset `n ≥ 1`. -/
theorem a101265_eq_vieta (n : ℕ) : a101265 (n + 1) = vieta 4 1 (n + 1) := by
  suffices h : ∀ n : ℕ, a101265 (n + 1) = vieta 4 1 (n + 1) ∧
      a101265 (n + 2) = vieta 4 1 (n + 2) ∧ a101265 (n + 3) = vieta 4 1 (n + 3) from
    (h n).1
  intro n
  induction n with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ k ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨h2, h3, ?_⟩
    have hrec : a101265 (k + 4) =
        5 * a101265 (k + 3) - 5 * a101265 (k + 2) + a101265 (k + 1) := rfl
    have hv := vieta_add_three 4 1 (k + 1)
    rw [show k + 1 + 3 = k + 4 by ring] at hv
    rw [hrec, h1, h2, h3, hv]
    ring

/-- A032908 coincides with the Vieta chain `vieta 3 2` everywhere. -/
theorem a032908_eq_vieta (n : ℕ) : a032908 n = vieta 3 2 n := by
  suffices h : ∀ n : ℕ, a032908 n = vieta 3 2 n ∧
      a032908 (n + 1) = vieta 3 2 (n + 1) ∧ a032908 (n + 2) = vieta 3 2 (n + 2) from
    (h n).1
  intro n
  induction n with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ k ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨h2, h3, ?_⟩
    have hrec : a032908 (k + 3) =
        4 * a032908 (k + 2) - 4 * a032908 (k + 1) + a032908 k := rfl
    have hv := vieta_add_three 3 2 k
    rw [show k + 1 + 2 = k + 3 by ring, hrec, h1, h2, h3, hv]
    ring

/-- Consecutive terms of a Vieta chain whose seed `(c, c)` solves
`x^2 + y^2 + x + y = m x y` also solve it. -/
theorem vieta_solution (m c : ℤ) (hc : 2 * c ^ 2 + 2 * c = m * c * c) (n : ℕ) :
    vieta m c n ^ 2 + vieta m c (n + 1) ^ 2 + vieta m c n + vieta m c (n + 1) =
      m * vieta m c n * vieta m c (n + 1) := by
  induction n with
  | zero =>
    show c ^ 2 + c ^ 2 + c + c = m * c * c
    linear_combination hc
  | succ k ih =>
    have h2 : vieta m c (k + 2) = m * vieta m c (k + 1) - vieta m c k - 1 := rfl
    rw [h2]
    linear_combination ih

/-- The descent step and induction of Vieta jumping: every solution
`a ≤ b` of `a^2 + b^2 + a + b = m a b` in positive integers is a pair of
consecutive terms of `vieta 4 1` (and `m = 4`) or of `vieta 3 2`
(and `m = 3`). -/
theorem vieta_classify (b : ℕ) : ∀ (a : ℕ) (m : ℤ), 0 < a → a ≤ b →
    (a : ℤ) ^ 2 + (b : ℤ) ^ 2 + a + b = m * a * b →
      (m = 4 ∧ ∃ n, (a : ℤ) = vieta 4 1 n ∧ (b : ℤ) = vieta 4 1 (n + 1)) ∨
      (m = 3 ∧ ∃ n, (a : ℤ) = vieta 3 2 n ∧ (b : ℤ) = vieta 3 2 (n + 1)) := by
  induction b using Nat.strong_induction_on with
  | _ b ih =>
  intro a m ha hab heq
  rcases lt_or_eq_of_le hab with hlt | rfl
  · -- descent: the other root `c = m a - 1 - b = (a^2 + a)/b`
    set c : ℤ := m * a - 1 - b with hc_def
    have hcb : c * b = (a : ℤ) ^ 2 + a := by
      rw [hc_def]; linear_combination -heq
    have hbpos : (0 : ℤ) < b := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le a) hlt)
    have hapos : (0 : ℤ) < a := by exact_mod_cast ha
    have hcpos : 0 < c := by
      have hcb_pos : 0 < c * b := by rw [hcb]; positivity
      exact pos_of_mul_pos_left hcb_pos hbpos.le
    have hca : c ≤ a := by
      have hab1 : (a : ℤ) + 1 ≤ b := by exact_mod_cast hlt
      have hcb_le : c * b ≤ a * b := by
        rw [hcb]; nlinarith
      exact le_of_mul_le_mul_right hcb_le hbpos
    have hceq : c ^ 2 + (a : ℤ) ^ 2 + c + a = m * c * a := by
      linear_combination c * hc_def - hcb
    have hcnat : ((c.toNat : ℕ) : ℤ) = c := Int.toNat_of_nonneg hcpos.le
    have hcnat_pos : 0 < c.toNat := by omega
    have hcnat_le : c.toNat ≤ a := by omega
    have hb_eq : (b : ℤ) = m * a - c - 1 := by rw [hc_def]; ring
    rcases ih a hlt c.toNat m hcnat_pos hcnat_le (by rw [hcnat]; linear_combination hceq)
      with ⟨hm, n, hcn, han⟩ | ⟨hm, n, hcn, han⟩
    · refine Or.inl ⟨hm, n + 1, han, ?_⟩
      have hv : vieta 4 1 (n + 2) = 4 * vieta 4 1 (n + 1) - vieta 4 1 n - 1 := rfl
      rw [hv, hb_eq, hm, ← han, ← hcn, hcnat]
    · refine Or.inr ⟨hm, n + 1, han, ?_⟩
      have hv : vieta 3 2 (n + 2) = 3 * vieta 3 2 (n + 1) - vieta 3 2 n - 1 := rfl
      rw [hv, hb_eq, hm, ← han, ← hcn, hcnat]
  · -- diagonal: `2 a^2 + 2 a = m a^2` forces `a ∣ 2`
    have hapos : (0 : ℤ) < a := by exact_mod_cast ha
    have h2 : (2 : ℤ) = (m - 2) * a := by
      have hfac : (a : ℤ) * (2 * a + 2) = (a : ℤ) * (m * a) := by linear_combination heq
      have hcancel := mul_left_cancel₀ hapos.ne' hfac
      linear_combination hcancel
    have hdvd : a ∣ 2 := by
      have hdvdz : (a : ℤ) ∣ 2 := ⟨m - 2, by linear_combination h2⟩
      exact_mod_cast hdvdz
    have hale : a ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases a
    · left
      refine ⟨by push_cast at h2; linarith, 0, rfl, rfl⟩
    · right
      refine ⟨by push_cast at h2; linarith, 0, rfl, rfl⟩

/-- For `3 ≤ m` and `1 ≤ c` the Vieta chain is bounded below by `c` and
monotone. -/
theorem vieta_ge_and_le_succ (m c : ℤ) (hm : 3 ≤ m) (hc : 1 ≤ c) (n : ℕ) :
    c ≤ vieta m c n ∧ vieta m c n ≤ vieta m c (n + 1) := by
  induction n with
  | zero => exact ⟨le_refl c, le_refl c⟩
  | succ k ih =>
    obtain ⟨hck, hkk⟩ := ih
    have h2 : vieta m c (k + 2) = m * vieta m c (k + 1) - vieta m c k - 1 := rfl
    refine ⟨hck.trans hkk, ?_⟩
    rw [h2]
    nlinarith

/-- Terms of A101265 from index `2` on are at least `2`. -/
theorem two_le_a101265 (n : ℕ) (hn : 2 ≤ n) : 2 ≤ a101265 n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [a101265_eq_vieta]
  have hmono : Monotone (vieta 4 1) :=
    monotone_nat_of_le_succ fun j => (vieta_ge_and_le_succ 4 1 (by norm_num) le_rfl j).2
  calc (2 : ℤ) = vieta 4 1 2 := rfl
    _ ≤ vieta 4 1 (k + 1) := hmono (by omega)

/-- Every term of A032908 is at least `2`. -/
theorem two_le_a032908 (n : ℕ) : 2 ≤ a032908 n := by
  rw [a032908_eq_vieta]
  exact (vieta_ge_and_le_succ 3 2 (by norm_num) (by norm_num) n).1

/-! ## From divisibility to the Vieta equation -/

/-- For positive `a, b`, `a * b ∣ (a + b) * (a + b + 1)` yields an integer
`m` with `a^2 + b^2 + a + b = m a b`. -/
theorem exists_vieta_eq_of_dvd (a b : ℕ) (h : a * b ∣ (a + b) * (a + b + 1)) :
    ∃ m : ℤ, (a : ℤ) ^ 2 + (b : ℤ) ^ 2 + a + b = m * a * b := by
  obtain ⟨k, hk⟩ := h
  have hkz : ((a : ℤ) + b) * ((a : ℤ) + b + 1) = (a : ℤ) * b * k := by exact_mod_cast hk
  exact ⟨(k : ℤ) - 2, by linear_combination hkz⟩

/-- The ordered classification: a positive solution with `a ≤ b` is
`(1, 1)`, or `(a(n), a(n+1))` for A101265 with `n ≥ 1`, or
`(a(n), a(n+1))` for A032908. -/
theorem solution_classification_of_le (a b : ℕ) (ha : 0 < a) (hab : a ≤ b)
    (h : a * b ∣ (a + b) * (a + b + 1)) :
    (a = 1 ∧ b = 1) ∨
      (∃ n : ℕ, 1 ≤ n ∧ (a : ℤ) = a101265 n ∧ (b : ℤ) = a101265 (n + 1)) ∨
      (∃ n : ℕ, (a : ℤ) = a032908 n ∧ (b : ℤ) = a032908 (n + 1)) := by
  obtain ⟨m, hm⟩ := exists_vieta_eq_of_dvd a b h
  rcases vieta_classify b a m ha hab hm with ⟨-, n, han, hbn⟩ | ⟨-, n, han, hbn⟩
  · rcases n with _ | k
    · left
      have ha1 : (a : ℤ) = 1 := han
      have hb1 : (b : ℤ) = 1 := hbn
      exact ⟨by exact_mod_cast ha1, by exact_mod_cast hb1⟩
    · right; left
      refine ⟨k + 1, by omega, ?_, ?_⟩
      · rw [han, a101265_eq_vieta]
      · rw [hbn, a101265_eq_vieta]
  · right; right
    exact ⟨n, by rw [han, a032908_eq_vieta], by rw [hbn, a032908_eq_vieta]⟩

/-! ## Main results -/

/-- **Classification of the solutions (corrected form of R. Israel's
conjecture, A101265/A032908, Aug 26 2015; proved on Math StackExchange
1417404).**  Every pair of positive integers `(a, b)` with
`a * b ∣ (a + b)(a + b + 1)` is either `(1, 1)` or, in some order, a pair of
consecutive terms `a(n), a(n+1)` of A101265 (offset `1`, so `n ≥ 1`) or of
A032908 (offset `0`).  The exceptional pair `(1, 1)` is the backward
extension `a(0) = 1` of A101265 that the entry's data omit. -/
theorem solution_classification (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (h : a * b ∣ (a + b) * (a + b + 1)) :
    (a = 1 ∧ b = 1) ∨
      (∃ n : ℕ, 1 ≤ n ∧
        (((a : ℤ) = a101265 n ∧ (b : ℤ) = a101265 (n + 1)) ∨
          ((b : ℤ) = a101265 n ∧ (a : ℤ) = a101265 (n + 1)))) ∨
      (∃ n : ℕ,
        ((a : ℤ) = a032908 n ∧ (b : ℤ) = a032908 (n + 1)) ∨
          ((b : ℤ) = a032908 n ∧ (a : ℤ) = a032908 (n + 1))) := by
  rcases le_total a b with hab | hba
  · rcases solution_classification_of_le a b ha hab h with h11 | ⟨n, hn, h1, h2⟩ | ⟨n, h1, h2⟩
    · exact Or.inl h11
    · exact Or.inr (Or.inl ⟨n, hn, Or.inl ⟨h1, h2⟩⟩)
    · exact Or.inr (Or.inr ⟨n, Or.inl ⟨h1, h2⟩⟩)
  · have h' : b * a ∣ (b + a) * (b + a + 1) := by
      rw [mul_comm b a, add_comm b a]; exact h
    rcases solution_classification_of_le b a hb hba h' with ⟨h1, h2⟩ | ⟨n, hn, h1, h2⟩ |
        ⟨n, h1, h2⟩
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr (Or.inl ⟨n, hn, Or.inr ⟨h1, h2⟩⟩)
    · exact Or.inr (Or.inr ⟨n, Or.inr ⟨h1, h2⟩⟩)

/-- **Converse.**  Consecutive terms of A101265 (`n ≥ 1`) are positive and
solve `a * b ∣ (a + b)(a + b + 1)`; indeed
`(a(n) + a(n+1))(a(n) + a(n+1) + 1) = 6 a(n) a(n+1)` (entry FORMULA). -/
theorem a101265_consecutive_solution (n : ℕ) (hn : 1 ≤ n) :
    0 < a101265 n ∧ 0 < a101265 (n + 1) ∧
      (a101265 n + a101265 (n + 1)) * (a101265 n + a101265 (n + 1) + 1) =
        6 * (a101265 n * a101265 (n + 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [a101265_eq_vieta, a101265_eq_vieta]
  have hpos := vieta_ge_and_le_succ 4 1 (by norm_num) le_rfl
  have hsol := vieta_solution 4 1 (by norm_num) (k + 1)
  refine ⟨by linarith [(hpos (k + 1)).1], by linarith [(hpos (k + 2)).1], ?_⟩
  linear_combination hsol

/-- **Converse.**  Consecutive terms of A032908 are positive and solve
`a * b ∣ (a + b)(a + b + 1)`; indeed
`(a(n) + a(n+1))(a(n) + a(n+1) + 1) = 5 a(n) a(n+1)` (entry FORMULA). -/
theorem a032908_consecutive_solution (n : ℕ) :
    0 < a032908 n ∧ 0 < a032908 (n + 1) ∧
      (a032908 n + a032908 (n + 1)) * (a032908 n + a032908 (n + 1) + 1) =
        5 * (a032908 n * a032908 (n + 1)) := by
  rw [a032908_eq_vieta, a032908_eq_vieta]
  have hsol := vieta_solution 3 2 (by norm_num) n
  refine ⟨by linarith [two_le_a032908 n, a032908_eq_vieta n],
    by linarith [two_le_a032908 (n + 1), a032908_eq_vieta (n + 1)], ?_⟩
  linear_combination hsol

/-- R. Israel's conjecture (A101265 and A032908, Aug 26 2015), read literally
with the entries' offsets: every positive solution `(a, b)` of
`a * b ∣ (a + b)(a + b + 1)` is, in some order, a pair of consecutive terms
of A101265 (indices `n, n+1` with `n ≥ 1`) or of A032908 (indices `n, n+1`
with `n ≥ 0`). -/
def LiteralConjecture : Prop :=
  ∀ a b : ℕ, 0 < a → 0 < b → a * b ∣ (a + b) * (a + b + 1) →
    (∃ n : ℕ, 1 ≤ n ∧
      (((a : ℤ) = a101265 n ∧ (b : ℤ) = a101265 (n + 1)) ∨
        ((b : ℤ) = a101265 n ∧ (a : ℤ) = a101265 (n + 1)))) ∨
    (∃ n : ℕ,
      ((a : ℤ) = a032908 n ∧ (b : ℤ) = a032908 (n + 1)) ∨
        ((b : ℤ) = a032908 n ∧ (a : ℤ) = a032908 (n + 1)))

/-- **Refutation of the literal statement at `(1, 1)`.**  The pair `(1, 1)`
solves `1 ∣ 2 * 3`, but every A101265 term with index `≥ 2` and every A032908
term is at least `2`, so `(1, 1)` is not a pair of consecutive terms of
either sequence with the entries' offsets. -/
theorem literal_conjecture_false : ¬ LiteralConjecture := by
  intro hconj
  rcases hconj 1 1 one_pos one_pos (by norm_num) with ⟨n, hn, h | h⟩ | ⟨n, h | h⟩
  · have h2 := two_le_a101265 (n + 1) (by omega); push_cast at h; linarith [h.2]
  · have h2 := two_le_a101265 (n + 1) (by omega); push_cast at h; linarith [h.2]
  · have h2 := two_le_a032908 n; push_cast at h; linarith [h.1]
  · have h2 := two_le_a032908 n; push_cast at h; linarith [h.1]

/-- Every listed consecutive pair is a genuine solution and the exceptional
pair `(1, 1)` is one too: the classification's hypotheses are satisfiable
and each of its three branches occurs. -/
example : (1 * 1 ∣ (1 + 1) * (1 + 1 + 1)) ∧ (1 * 2 ∣ (1 + 2) * (1 + 2 + 1)) ∧
    (2 * 3 ∣ (2 + 3) * (2 + 3 + 1)) := by decide

end Candidates.A101265SolutionPairConsecutive
