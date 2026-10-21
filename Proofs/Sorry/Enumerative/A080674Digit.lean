/-
# A080674 — Wajnberg: a(n) counts integers below 10^n with no digit in {0,...,5}

## OEIS source (retrieved with `oeis show A080674`, 2026-10-21)

```
NAME:     a(n) = (4/3)*(4^n - 1).
TERMS:    0,4,20,84,340,1364,5460,21844,87380,349524,1398100,...
COMMENT (the conjecture):
  Conjectured to be the number of integers from 0 to (10^n)-1 that lack 0, 1,
  2, 3, 4 and 5 as a digit. - _Alexandre Wajnberg_, Apr 25 2005
FORMULA:
  a(n) = Sum_{i = 1..n} 4^i.
  a(n) = 4*a(n-1) + 4. - _Alexandre Wajnberg_, Apr 25 2005
```

## Status

Triage status: open (no proof recorded in the entry).  The argument is
elementary: an admissible number with exactly `i` decimal digits has every
digit in `{6,7,8,9}`, giving `4^i` of them for `1 ≤ i ≤ n`; the integer `0`
is excluded because its decimal numeral is `0`.

## Convention

`Nat.digits 10 0 = []`, whereas the decimal numeral of `0` is the single
digit `0`.  The definition `decimalDigits` below restores the numeral `0` for
the integer `0`, so that `0` is (correctly) not counted.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A080674Digit

/-- The decimal digits of `x` (least significant first), with the numeral of
`0` taken to be the single digit `0` (unlike `Nat.digits 10 0 = []`). -/
def decimalDigits (x : ℕ) : List ℕ :=
  if x = 0 then [0] else Nat.digits 10 x

/-- `x` has no decimal digit in `{0,...,5}`. -/
def NoDigitBelowSix (x : ℕ) : Prop :=
  ∀ d ∈ decimalDigits x, 6 ≤ d

instance : DecidablePred NoDigitBelowSix := fun x => by
  unfold NoDigitBelowSix
  infer_instance

/-- The number of integers in `[0, 10^n - 1]` with no decimal digit in
`{0,...,5}`. -/
def count (n : ℕ) : ℕ :=
  ((Finset.range (10 ^ n)).filter NoDigitBelowSix).card

/-- The OEIS sequence A080674: `a(n) = (4/3)(4^n - 1)`, in `ℚ`. -/
def a (n : ℕ) : ℚ := 4 / 3 * (4 ^ n - 1)

example : decimalDigits 0 = [0] := rfl
example : decimalDigits 697 = [7, 9, 6] := by decide
example : NoDigitBelowSix 6798 := by decide
example : ¬ NoDigitBelowSix 0 := by decide
example : ¬ NoDigitBelowSix 650 := by decide
example : count 0 = 0 := by decide
example : count 1 = 4 := by decide
example : count 2 = 20 := by decide
example : a 0 = 0 := by norm_num [a]
example : a 1 = 4 := by norm_num [a]
example : a 2 = 20 := by norm_num [a]
example : a 3 = 84 := by norm_num [a]

/-- `x` has no digit below six iff `x` is positive and every `Nat.digits`
digit is at least six. -/
theorem noDigitBelowSix_iff (x : ℕ) :
    NoDigitBelowSix x ↔ 0 < x ∧ ∀ d ∈ Nat.digits 10 x, 6 ≤ d := by
  unfold NoDigitBelowSix decimalDigits
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · simp [hx, Nat.pos_iff_ne_zero.mp hx]

/-- Appending a last digit `r` to `q`: `r + 10 q` has no digit below six iff
`6 ≤ r` and `q` is either `0` or itself has no digit below six. -/
theorem noDigitBelowSix_add_ten_mul {q r : ℕ} (hr : r < 10) :
    NoDigitBelowSix (r + 10 * q) ↔ 6 ≤ r ∧ (q = 0 ∨ NoDigitBelowSix q) := by
  rw [noDigitBelowSix_iff]
  by_cases h0 : r = 0 ∧ q = 0
  · obtain ⟨rfl, rfl⟩ := h0
    simp
  · have hxy : r ≠ 0 ∨ q ≠ 0 := by tauto
    rw [Nat.digits_add 10 (by norm_num) r q hr hxy, noDigitBelowSix_iff]
    have hpos : 0 < r + 10 * q := by omega
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · simp only [mul_zero, add_zero, Nat.digits_zero, List.mem_cons, List.not_mem_nil,
        or_false, forall_eq, lt_self_iff_false, IsEmpty.forall_iff, implies_true, and_true,
        and_iff_right_iff_imp]
      omega
    · simp [hpos, hq, Nat.pos_iff_ne_zero.mp hq]

/-- The admissible numbers below `10^(n+1)` are exactly `r + 10 q` with
`r ∈ {6,...,9}` and `q < 10^n` either `0` or admissible. -/
theorem filter_range_succ_eq_image (n : ℕ) :
    (Finset.range (10 ^ (n + 1))).filter NoDigitBelowSix =
      (((Finset.range (10 ^ n)).filter (fun q => q = 0 ∨ NoDigitBelowSix q)) ×ˢ
        Finset.Icc 6 9).image (fun p => p.2 + 10 * p.1) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, Finset.mem_product,
    Finset.mem_Icc, Prod.exists]
  have hpow : 10 ^ (n + 1) = 10 * 10 ^ n := by ring
  constructor
  · rintro ⟨hx, hP⟩
    have hdecomp : x % 10 + 10 * (x / 10) = x := Nat.mod_add_div x 10
    rw [← hdecomp, noDigitBelowSix_add_ten_mul (Nat.mod_lt x (by norm_num))] at hP
    refine ⟨x / 10, x % 10, ⟨⟨?_, hP.2⟩, hP.1, ?_⟩, hdecomp⟩
    · omega
    · omega
  · rintro ⟨q, r, ⟨⟨hq, hQ⟩, hr6, hr9⟩, rfl⟩
    refine ⟨by omega, ?_⟩
    rw [noDigitBelowSix_add_ten_mul (by omega)]
    exact ⟨hr6, hQ⟩

/-- Recurrence: `count (n+1) = 4 (count n + 1)`. -/
theorem count_succ (n : ℕ) : count (n + 1) = 4 * (count n + 1) := by
  unfold count
  rw [filter_range_succ_eq_image]
  have hinj : Set.InjOn (fun p : ℕ × ℕ => p.2 + 10 * p.1)
      ↑(((Finset.range (10 ^ n)).filter (fun q => q = 0 ∨ NoDigitBelowSix q)) ×ˢ
        Finset.Icc 6 9) := by
    rintro ⟨q₁, r₁⟩ h₁ ⟨q₂, r₂⟩ h₂ heq
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_Icc] at h₁ h₂
    simp only at heq
    ext <;> simp only <;> omega
  rw [Finset.card_image_of_injOn hinj, Finset.card_product]
  have hins : (Finset.range (10 ^ n)).filter (fun q => q = 0 ∨ NoDigitBelowSix q) =
      insert 0 ((Finset.range (10 ^ n)).filter NoDigitBelowSix) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
    constructor
    · rintro ⟨hq, rfl | hQ⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hq, hQ⟩
    · rintro (rfl | ⟨hq, hQ⟩)
      · exact ⟨pow_pos (by norm_num) n, Or.inl rfl⟩
      · exact ⟨hq, Or.inr hQ⟩
  have h0 : (0 : ℕ) ∉ (Finset.range (10 ^ n)).filter NoDigitBelowSix := by
    simp [noDigitBelowSix_iff]
  rw [hins, Finset.card_insert_of_notMem h0]
  simp only [Nat.card_Icc, Nat.reduceAdd, Nat.reduceSub]
  ring

/-- Cast-free closed form: `3 * count n + 4 = 4^(n+1)`. -/
theorem three_mul_count_add_four (n : ℕ) : 3 * count n + 4 = 4 ^ (n + 1) := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [count_succ, pow_succ]
    omega

/-- **Wajnberg's conjecture (A080674, Alexandre Wajnberg, Apr 25 2005).**
Verbatim: "Conjectured to be the number of integers from 0 to (10^n)-1 that
lack 0, 1, 2, 3, 4 and 5 as a digit."  That is, for every `n`, the number of
integers in `[0, 10^n - 1]` with no decimal digit in `{0,...,5}` equals
`a(n) = (4/3)(4^n - 1)`. -/
theorem count_eq_a (n : ℕ) : (count n : ℚ) = a n := by
  have h := three_mul_count_add_four n
  have hq : (3 * count n + 4 : ℚ) = 4 ^ (n + 1) := by exact_mod_cast h
  unfold a
  rw [pow_succ] at hq
  linarith

end Candidates.A080674Digit
