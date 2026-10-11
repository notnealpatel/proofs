import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# Integer symmetric-function coefficients and the Blomberg diagonal

`weight i m` is the Boolean elementary-symmetric value at Hamming weight `m`.
`coefficient i k` is its independent integer binomial inversion, not an integer
recovery from characteristic-p data. Van Heesch (2014), printed pp. 3–5,
uses the corresponding triangular weight equations; Table 3 on p. 8 supplies
the offset-three diagonal. Casting the integer equations gives the equations
in any commutative ring, and triangular uniqueness identifies their residues.
No bound on the characteristic recovers the integer lifts from those residues.

The diagonal is indexed by ambient `n`, starting at `n = 4`; the OEIS A250109
index is `n - 3`. The step-four recurrence therefore starts at ambient `n = 16`.
The cubic formulas are multiplied by six to avoid integer division. These are
coefficient identities, not assertions about multiplicative complexity or
minimum AND-gate counts. The original circuit-complexity obligation is separate.
-/

set_option autoImplicit false

open Finset

namespace Blomberg

/-- The Boolean elementary symmetric function at weight `m`, interpreted in the integers. -/
def weight (i m : ℕ) : ℤ := (m.choose i % 2 : ℕ)

/-- Integer binomial inversion coefficients, defined independently of any characteristic. -/
def coefficient (i k : ℕ) : ℤ :=
  ∑ m ∈ Icc i k, (-1 : ℤ) ^ (k - m) * (k.choose m : ℤ) * weight i m

/-- The offset-three diagonal, with all claims below guarded by `4 ≤ n`. -/
def diagonal (n : ℕ) : ℤ := coefficient (n - 3) n

example : weight 1 4 = 0 := rfl
example : coefficient 1 4 = -8 := by decide
example : diagonal 4 = -8 := by decide
example : diagonal 5 = 0 := by decide
example : diagonal 6 = -20 := by decide
example : diagonal 7 = -20 := by decide
example : diagonal 8 = -64 := by decide
example : 4 ≤ (4 : ℕ) ∧ 16 ≤ (16 : ℕ) := by decide
example : (range (0 + 1)).Nonempty := ⟨0, by simp⟩

/-- Lucas's theorem specializes to the parity of the second binomial coefficient. -/
theorem choose_two_mod_two (t : ℕ) : t.choose 2 % 2 = (t / 2) % 2 := by
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := t) (k := 2) (p := 2)
  simpa [Nat.ModEq, Nat.choose_one_right] using h

/-- Lucas's theorem specializes to the parity of the third binomial coefficient. -/
theorem choose_three_mod_two (t : ℕ) :
    t.choose 3 % 2 = (t % 2) * ((t / 2) % 2) := by
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := t) (k := 3) (p := 2)
  have ht : t % 2 < 2 := Nat.mod_lt _ (by decide)
  interval_cases hr : t % 2 <;> simpa [Nat.ModEq, hr, Nat.choose_one_right] using h

/-- At offset three the inversion sum has exactly four terms. -/
theorem coefficient_offset_three (i : ℕ) :
    coefficient i (i + 3) =
      -( (i + 3).choose 3 : ℤ) + ((i + 1) % 2 : ℕ) * ((i + 3).choose 2 : ℤ)
        - ((i + 2).choose 2 % 2 : ℕ) * (i + 3 : ℕ) + ((i + 3).choose 3 % 2 : ℕ) := by
  unfold coefficient
  rw [show i + 3 = (i + 2) + 1 by omega, sum_Icc_succ_top (by omega)]
  rw [show i + 2 = (i + 1) + 1 by omega, sum_Icc_succ_top (by omega)]
  rw [sum_Icc_succ_top (by omega)]
  simp only [Finset.Icc_self, Finset.sum_singleton]
  have h1 : (i + 1).choose i = i + 1 := by
    have hs := Nat.choose_symm (n := i + 1) (k := 1) (by omega)
    simp_all
  have h2 : (i + 2).choose i = (i + 2).choose 2 := by
    rw [← Nat.choose_symm (show 2 ≤ i + 2 by omega)]
    congr 1
  have h3 : (i + 3).choose i = (i + 3).choose 3 := by
    rw [← Nat.choose_symm (show 3 ≤ i + 3 by omega)]
    congr 1
  have h4 : (i + 3).choose (i + 1) = (i + 3).choose 2 := by
    rw [← Nat.choose_symm (show 2 ≤ i + 3 by omega)]
    congr 1
  have h5 : (i + 3).choose (i + 2) = i + 3 := by
    have hs := Nat.choose_symm (n := i + 3) (k := 1) (by omega)
    simp_all
  simp only [weight, Nat.choose_self, h1, h2, h3, h4, h5]
  norm_num [show i + 1 + 1 + 1 - i = 3 by omega,
    show i + 1 + 1 + 1 - (i + 1) = 2 by omega,
    show i + 1 + 1 + 1 - (i + 1 + 1) = 1 by omega]
  ring

/-- The guarded diagonal equals the explicit four-term integer formula. -/
theorem diagonal_four_terms (n : ℕ) (hn : 4 ≤ n) :
    diagonal n = -(n.choose 3 : ℤ) + ((n - 2) % 2 : ℕ) * (n.choose 2 : ℤ)
      - ((n - 1).choose 2 % 2 : ℕ) * (n : ℤ) + (n.choose 3 % 2 : ℕ) := by
  have he : n - 3 + 3 = n := by omega
  have h := coefficient_offset_three (n - 3)
  simpa only [he, show n - 3 + 1 = n - 2 by omega,
    show n - 3 + 2 = n - 1 by omega, diagonal] using h

/-- Twice the second binomial coefficient is a signed polynomial without division. -/
theorem two_mul_choose_two (n : ℕ) (hn : 2 ≤ n) :
    2 * (n.choose 2 : ℤ) = (n : ℤ) * ((n : ℤ) - 1) := by
  have hd := Nat.descFactorial_eq_factorial_mul_choose n 2
  have hcast := congrArg (fun a : ℕ => (a : ℤ)) hd
  simpa [Nat.descFactorial_succ, Nat.cast_sub (show 1 ≤ n by omega), mul_comm] using hcast.symm

/-- Six times the third binomial coefficient is a signed polynomial without division. -/
theorem six_mul_choose_three (n : ℕ) (hn : 3 ≤ n) :
    6 * (n.choose 3 : ℤ) = (n : ℤ) * ((n : ℤ) - 1) * ((n : ℤ) - 2) := by
  have hd := Nat.descFactorial_eq_factorial_mul_choose n 3
  have hcast := congrArg (fun a : ℕ => (a : ℤ)) hd
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero, mul_one,
    Nat.cast_mul, Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_sub (show 2 ≤ n by omega)] at hcast
  norm_num at hcast
  nlinarith [hcast]

/-- The four residue-class cubics, stated after multiplication by six in the integers. -/
theorem diagonal_cubic (n : ℕ) (hn : 4 ≤ n) :
    6 * diagonal n =
      if n % 4 = 0 then -(n : ℤ) * ((n : ℤ)^2 - 3 * (n : ℤ) + 8)
      else if n % 4 = 1 then -(n : ℤ) * ((n : ℤ) - 1) * ((n : ℤ) - 5)
      else if n % 4 = 2 then -(n : ℤ) * ((n : ℤ) - 1) * ((n : ℤ) - 2)
      else -((n : ℤ) - 1) * ((n : ℤ) - 2) * ((n : ℤ) - 3) := by
  rw [diagonal_four_terms n hn, choose_two_mod_two, choose_three_mod_two]
  have h2 := two_mul_choose_two n (by omega)
  have h3 := six_mul_choose_three n (by omega)
  have hr : n % 4 < 4 := Nat.mod_lt _ (by decide)
  interval_cases hres : n % 4
  all_goals
    have hp : (n - 2) % 2 = n % 2 := by omega
    have hq : (n - 1) / 2 % 2 = (if n % 4 = 0 ∨ n % 4 = 3 then 1 else 0) := by
      simp only [hres]
      norm_num
      omega
    have hs : n / 2 % 2 = (if n % 4 = 2 ∨ n % 4 = 3 then 1 else 0) := by
      simp only [hres]
      norm_num
      omega
    have ht : n % 2 = (if n % 4 = 1 ∨ n % 4 = 3 then 1 else 0) := by
      simp only [hres]
      norm_num
      omega
    simp only [hp, hq, hs, ht, hres] at *
    norm_num at *
    nlinarith [h2, h3]

/-- The corrected integer coefficient diagonal has step-four third difference `-64`. -/
theorem diagonal_recurrence (n : ℕ) (hn : 16 ≤ n) :
    diagonal n = 3 * diagonal (n - 4) - 3 * diagonal (n - 8) + diagonal (n - 12) - 64 := by
  have h0 := diagonal_cubic n (by omega)
  have h4 := diagonal_cubic (n - 4) (by omega)
  have h8 := diagonal_cubic (n - 8) (by omega)
  have h12 := diagonal_cubic (n - 12) (by omega)
  have hm4 : (n - 4) % 4 = n % 4 := by omega
  have hm8 : (n - 8) % 4 = n % 4 := by omega
  have hm12 : (n - 12) % 4 = n % 4 := by omega
  have hc4 : ((n - 4 : ℕ) : ℤ) = (n : ℤ) - 4 := by
    exact Nat.cast_sub (by omega)
  have hc8 : ((n - 8 : ℕ) : ℤ) = (n : ℤ) - 8 := by
    exact Nat.cast_sub (by omega)
  have hc12 : ((n - 12 : ℕ) : ℤ) = (n : ℤ) - 12 := by
    exact Nat.cast_sub (by omega)
  rw [hm4, hc4] at h4
  rw [hm8, hc8] at h8
  rw [hm12, hc12] at h12
  have hr : n % 4 < 4 := Nat.mod_lt _ (by decide)
  suffices heq : 6 * diagonal n =
      6 * (3 * diagonal (n - 4) - 3 * diagonal (n - 8) + diagonal (n - 12) - 64) by omega
  interval_cases hres : n % 4 <;>
    norm_num at h0 h4 h8 h12 <;>
    linear_combination h0 - 3 * h4 + 3 * h8 - h12

/-- Extending the inversion sum to all weights adds only zero terms below `i`. -/
theorem coefficient_eq_sum_range (i k : ℕ) :
    coefficient i k = ∑ m ∈ range (k + 1),
      (-1 : ℤ) ^ (k - m) * (k.choose m : ℤ) * weight i m := by
  unfold coefficient
  apply sum_subset
  · intro m hm
    simp only [mem_Icc, mem_range] at *
    omega
  · intro m hm hnot
    have hmi : m < i := by
      simp only [mem_Icc, mem_range] at *
      omega
    simp [weight, Nat.choose_eq_zero_of_lt hmi]

/-- The product of the binomial matrix and its signed inverse is the identity. -/
theorem binomial_kernel (w m : ℕ) (hm : m ≤ w) :
    (∑ j ∈ Ico m (w + 1), (w.choose j : ℤ) * (-1 : ℤ) ^ (j - m) * (j.choose m : ℤ)) =
      if m = w then 1 else 0 := by
  have hprod : ∀ j ∈ Ico m (w + 1),
      (w.choose j : ℤ) * (-1 : ℤ) ^ (j - m) * (j.choose m : ℤ) =
        (w.choose m : ℤ) * ((-1 : ℤ) ^ (j - m) * ((w - m).choose (j - m) : ℤ)) := by
    intro j hj
    have hjm : m ≤ j := (mem_Ico.mp hj).1
    have h := congrArg (fun a : ℕ => (a : ℤ)) (Nat.choose_mul (n := w) hjm)
    push_cast at h
    calc
      _ = (-1 : ℤ) ^ (j - m) * ((w.choose j : ℤ) * (j.choose m : ℤ)) := by ring
      _ = _ := by rw [h]; ring
  rw [sum_congr rfl hprod, ← mul_sum, sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left]
  rw [show w + 1 - m = (w - m) + 1 by omega, Int.alternating_sum_range_choose]
  by_cases he : m = w
  · subst m
    simp
  · have hne : w - m ≠ 0 := by omega
    simp [he, hne]

/-- Binomial inversion reconstructs each integer Boolean weight. -/
theorem weight_eq_sum_range (i w : ℕ) :
    weight i w = ∑ j ∈ range (w + 1), (w.choose j : ℤ) * coefficient i j := by
  symm
  simp_rw [coefficient_eq_sum_range, mul_sum]
  rw [show (∑ j ∈ range (w + 1), ∑ m ∈ range (j + 1),
    (w.choose j : ℤ) * ((-1 : ℤ) ^ (j - m) * (j.choose m : ℤ) * weight i m)) =
    ∑ m ∈ range (w + 1), ∑ j ∈ Ico m (w + 1),
    (w.choose j : ℤ) * ((-1 : ℤ) ^ (j - m) * (j.choose m : ℤ) * weight i m) by
      simpa only [Nat.Ico_zero_eq_range] using
        (sum_Ico_Ico_comm 0 (w + 1) (fun m j =>
          (w.choose j : ℤ) * ((-1 : ℤ) ^ (j - m) * (j.choose m : ℤ) * weight i m))).symm]
  have hinner : ∀ m ∈ range (w + 1),
      (∑ j ∈ Ico m (w + 1), (w.choose j : ℤ) *
        ((-1 : ℤ) ^ (j - m) * (j.choose m : ℤ) * weight i m)) =
          (if m = w then 1 else 0) * weight i m := by
    intro m hm
    rw [← binomial_kernel w m (by simpa using hm), sum_mul]
    apply sum_congr rfl
    intro j hj
    ring
  rw [sum_congr rfl hinner]
  simp

/-- A binomial triangular system has at most one solution over any commutative ring. -/
theorem triangular_unique {R : Type*} [CommRing R] (a b : ℕ → R)
    (h : ∀ w, (∑ j ∈ range (w + 1), (w.choose j : R) * a j) =
      ∑ j ∈ range (w + 1), (w.choose j : R) * b j) : a = b := by
  funext w
  induction w using Nat.strong_induction_on with
  | h w ih =>
    have hs : (∑ j ∈ range w, (w.choose j : R) * a j) =
        ∑ j ∈ range w, (w.choose j : R) * b j := by
      apply sum_congr rfl
      intro j hj
      rw [ih j (mem_range.mp hj)]
    have hw := h w
    rw [sum_range_succ, sum_range_succ, hs] at hw
    simpa using hw

/-- Casting the independently defined integer coefficients preserves the weight equations. -/
theorem weight_eq_sum_range_cast {R : Type*} [CommRing R] (i w : ℕ) :
    (weight i w : R) = ∑ j ∈ range (w + 1), (w.choose j : R) * (coefficient i j : R) := by
  have hc := congrArg (fun z : ℤ => (z : R)) (weight_eq_sum_range i w)
  simpa only [Int.cast_sum, Int.cast_mul, Int.cast_natCast] using hc

/-- The integer inversion coefficients are the unique solution of the integer weight system. -/
theorem coefficient_unique (i : ℕ) (a : ℕ → ℤ)
    (h : ∀ w, weight i w = ∑ j ∈ range (w + 1), (w.choose j : ℤ) * a j) :
    a = coefficient i := by
  apply triangular_unique
  intro w
  rw [← h w, weight_eq_sum_range]

/-- Reduction modulo any modulus preserves the triangular identity; it does not recover lifts. -/
theorem weight_eq_sum_range_zmod (p i w : ℕ) :
    (weight i w : ZMod p) = ∑ j ∈ range (w + 1),
      (w.choose j : ZMod p) * (coefficient i j : ZMod p) :=
  weight_eq_sum_range_cast i w

/-- Coefficients below the elementary-symmetric degree are zero. -/
theorem coefficient_eq_zero_of_lt (i k : ℕ) (hk : k < i) : coefficient i k = 0 := by
  simp [coefficient, Finset.Icc_eq_empty_of_lt hk]

/-- The source's degree-restricted triangular weight identity holds over the integers. -/
theorem weight_eq_sum_Icc (i w : ℕ) :
    weight i w = ∑ j ∈ Icc i w, (w.choose j : ℤ) * coefficient i j := by
  rw [weight_eq_sum_range]
  symm
  apply sum_subset
  · intro j hj
    simp only [mem_Icc, mem_range] at *
    omega
  · intro j hj hnot
    have hji : j < i := by
      simp only [mem_Icc, mem_range] at *
      omega
    rw [coefficient_eq_zero_of_lt i j hji, mul_zero]

/-- Even a finite triangular system determines all coefficients in its range. -/
theorem triangular_unique_upto {R : Type*} [CommRing R] (n : ℕ) (a b : ℕ → R)
    (h : ∀ w, w ≤ n → (∑ j ∈ range (w + 1), (w.choose j : R) * a j) =
      ∑ j ∈ range (w + 1), (w.choose j : R) * b j) :
    ∀ j, j ≤ n → a j = b j := by
  intro w
  induction w using Nat.strong_induction_on with
  | h w ih =>
    intro hw
    have hs : (∑ j ∈ range w, (w.choose j : R) * a j) =
        ∑ j ∈ range w, (w.choose j : R) * b j := by
      apply sum_congr rfl
      intro j hj
      have hjw := mem_range.mp hj
      rw [ih j hjw (by omega)]
    have heq := h w hw
    rw [sum_range_succ, sum_range_succ, hs] at heq
    simpa using heq

example : 0 ≤ (0 : ℕ) := by decide
example : weight 0 0 = 1 := rfl
example : coefficient 0 0 = 1 := by decide
example : ∀ w, weight 1 w = ∑ j ∈ range (w + 1),
    (w.choose j : ℤ) * coefficient 1 j := weight_eq_sum_range 1
example : ∀ w, w ≤ 4 →
    (∑ j ∈ range (w + 1), (w.choose j : ℤ) * coefficient 1 j) =
      ∑ j ∈ range (w + 1), (w.choose j : ℤ) * coefficient 1 j := by
  intro w hw
  rfl

end Blomberg
