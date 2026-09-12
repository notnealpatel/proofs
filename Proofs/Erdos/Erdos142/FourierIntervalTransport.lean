import Erdos.Erdos142.FourierAP
import Erdos.Erdos142.CyclicAPCount
import Erdos.Erdos142.CorrelationIncrement

set_option autoImplicit false

open Finset
open scoped BigOperators ComplexConjugate ZMod

namespace Erdos142

/-- Reduction modulo `p` preserves the cardinality of a finite set whose
members are all strictly below `p`. -/
theorem card_natCyclicImage_eq_card_of_lt (p : ℕ) (A : Finset ℕ)
    (hA : ∀ a ∈ A, a < p) :
    (natCyclicImage p A).card = A.card := by
  rw [natCyclicImage]
  apply card_image_of_injOn
  intro a ha b hb hab
  have hval := congrArg ZMod.val hab
  rw [ZMod.val_natCast_of_lt (hA a ha),
    ZMod.val_natCast_of_lt (hA b hb)] at hval
  exact hval

/-- Casting a subset of `range N` into `ZMod p` preserves its cardinality
when `N ≤ p`. -/
theorem card_natCyclicImage_eq_card (p N : ℕ) (A : Finset ℕ)
    (hA : A ⊆ Finset.range N) (hN : N ≤ p) :
    (natCyclicImage p A).card = A.card := by
  apply card_natCyclicImage_eq_card_of_lt p A
  intro a ha
  exact (Finset.mem_range.mp (hA ha)).trans_le hN

/-- The negative standard additive character at a cast natural number has
the explicit phase dictated by Mathlib's negative-sign DFT convention. -/
theorem stdAddChar_neg_natCast_mul_eq_exp (p n : ℕ) [NeZero p]
    (r : ZMod p) :
    ZMod.stdAddChar (-((n : ZMod p) * r)) =
      Complex.exp (2 * Real.pi * Complex.I *
        (-((r.val : ℝ) / (p : ℝ))) * (n : ℝ)) := by
  have hcast : -((n : ZMod p) * r) =
      ((-(n : ℤ) * (r.val : ℤ) : ℤ) : ZMod p) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val r]
    push_cast
    ring
  rw [hcast, ZMod.stdAddChar_coe]
  push_cast
  congr 1
  field_simp

/-- The cyclic DFT of the zero-extended balanced indicator on a no-wrap
natural interval is exactly its finite exponential sum on that interval. -/
theorem unnormalizedDFT_balanced_natCyclicImage_eq_interval_sum
    (p N : ℕ) [NeZero p] (A : Finset ℕ) (hA : A ⊆ Finset.range N)
    (_hNpos : 0 < N) (hN : N < p) (r : ZMod p) :
    unnormalizedDFT p (fun x =>
      (if x ∈ natCyclicImage p A then (1 : ℂ) else 0) -
        (((A.card : ℝ) / (N : ℝ) : ℝ) : ℂ) *
          (if x ∈ natCyclicImage p (Finset.range N) then (1 : ℂ) else 0)) r =
      ∑ n ∈ Finset.range N, (balancedIndicator (Finset.range N) A n : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I *
          (-((r.val : ℝ) / (p : ℝ))) * (n : ℝ)) := by
  have hAp : ∀ a ∈ A, a < p := by
    intro a ha
    exact (Finset.mem_range.mp (hA ha)).trans hN
  have hRangeP : ∀ n ∈ Finset.range N, n < p := by
    intro n hn
    exact (Finset.mem_range.mp hn).trans hN
  have hImage : natCyclicImage p A ⊆
      natCyclicImage p (Finset.range N) := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := Finset.mem_image.mp hx
    apply Finset.mem_image.mpr
    exact ⟨a, hA ha, hax⟩
  have hmemA (n : ℕ) (hn : n ∈ Finset.range N) :
      (n : ZMod p) ∈ natCyclicImage p A ↔ n ∈ A := by
    rw [mem_natCyclicImage_iff_val_mem hAp,
      ZMod.val_natCast_of_lt (hRangeP n hn)]
  have hmemRange (n : ℕ) (hn : n ∈ Finset.range N) :
      (n : ZMod p) ∈ natCyclicImage p (Finset.range N) := by
    rw [mem_natCyclicImage_iff_val_mem hRangeP,
      ZMod.val_natCast_of_lt (hRangeP n hn)]
    exact hn
  rw [unnormalizedDFT_apply]
  calc
    (∑ x : ZMod p, ZMod.stdAddChar (-(x * r)) *
        ((if x ∈ natCyclicImage p A then (1 : ℂ) else 0) -
          (((A.card : ℝ) / (N : ℝ) : ℝ) : ℂ) *
            (if x ∈ natCyclicImage p (Finset.range N) then (1 : ℂ) else 0))) =
        ∑ x ∈ natCyclicImage p (Finset.range N),
          ZMod.stdAddChar (-(x * r)) *
            ((if x ∈ natCyclicImage p A then (1 : ℂ) else 0) -
              (((A.card : ℝ) / (N : ℝ) : ℝ) : ℂ) *
                (if x ∈ natCyclicImage p (Finset.range N) then (1 : ℂ) else 0)) := by
      symm
      apply Finset.sum_subset (by simp)
      intro x hxuniv hxoutside
      have hxA : x ∉ natCyclicImage p A := fun hx => hxoutside (hImage hx)
      simp only [hxA, hxoutside, if_false, mul_zero, sub_zero]
    _ = ∑ n ∈ Finset.range N,
          ZMod.stdAddChar (-((n : ZMod p) * r)) *
            ((if (n : ZMod p) ∈ natCyclicImage p A then (1 : ℂ) else 0) -
              (((A.card : ℝ) / (N : ℝ) : ℝ) : ℂ) *
                (if (n : ZMod p) ∈ natCyclicImage p (Finset.range N)
                  then (1 : ℂ) else 0)) := by
      rw [natCyclicImage, Finset.sum_image]
      intro a ha b hb hab
      have hval := congrArg ZMod.val hab
      rw [ZMod.val_natCast_of_lt (hRangeP a ha),
        ZMod.val_natCast_of_lt (hRangeP b hb)] at hval
      exact hval
    _ = ∑ n ∈ Finset.range N, (balancedIndicator (Finset.range N) A n : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I *
          (-((r.val : ℝ) / (p : ℝ))) * (n : ℝ)) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [stdAddChar_neg_natCast_mul_eq_exp, if_pos (hmemRange n hn)]
      simp only [balancedIndicator, Finset.card_range]
      simp only [hmemA n hn]
      by_cases hnA : n ∈ A
      · simp only [hnA, if_true]
        push_cast
        ring
      · simp only [hnA, if_false]
        push_cast
        ring

/-- Joint ground truth for modulus `19`, interval length `8`, and frequency
`1`; this instantiates every hypothesis of the transport theorem. -/
example :
    unnormalizedDFT 19 (fun x =>
      (if x ∈ natCyclicImage 19 ({0, 2, 5} : Finset ℕ) then (1 : ℂ) else 0) -
        (((({0, 2, 5} : Finset ℕ).card : ℝ) / (8 : ℝ) : ℝ) : ℂ) *
          (if x ∈ natCyclicImage 19 (Finset.range 8) then (1 : ℂ) else 0))
        (1 : ZMod 19) =
      ∑ n ∈ Finset.range 8,
        (balancedIndicator (Finset.range 8) ({0, 2, 5} : Finset ℕ) n : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I *
            (-((((1 : ZMod 19).val : ℝ)) / (19 : ℝ))) * (n : ℝ)) := by
  exact unnormalizedDFT_balanced_natCyclicImage_eq_interval_sum
    19 8 ({0, 2, 5} : Finset ℕ) (by decide) (by norm_num) (by norm_num)
      (1 : ZMod 19)

#check @card_natCyclicImage_eq_card_of_lt
#check @card_natCyclicImage_eq_card
#check @stdAddChar_neg_natCast_mul_eq_exp
#check @unnormalizedDFT_balanced_natCyclicImage_eq_interval_sum

#print axioms card_natCyclicImage_eq_card_of_lt
#print axioms card_natCyclicImage_eq_card
#print axioms stdAddChar_neg_natCast_mul_eq_exp
#print axioms unnormalizedDFT_balanced_natCyclicImage_eq_interval_sum

end Erdos142
