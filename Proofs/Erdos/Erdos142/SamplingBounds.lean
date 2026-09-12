/-
  Erdős Problem #142 — polynomial consequences of fixed-size sampling.

  The exact binomial supersaturation inequality in `Sampling` is converted
  here into a falling-factorial inequality.  Taking a sample of size twice
  the ambient additive Roth number and comparing the exact inclusion
  probability with the corresponding cube gives the cubic sparsening bound
  used in the proof of Lemma 2.3 of Balogh--Liu--Sharifzadeh.

  These are bounded finite corollaries.  They do not prove the asymptotic
  assertion in Erdős Problem #142.
-/

import Erdos.Erdos142.Sampling

set_option autoImplicit false

open Finset

namespace Erdos142

private theorem six_mul_choose_three (n : ℕ) :
    6 * Nat.choose n 3 = n * (n - 1) * (n - 2) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose n 3
  simpa [Nat.descFactorial, Nat.factorial, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc] using h.symm

/-- Multiplying a binomial coefficient by the third falling factorial of its
lower argument transfers that falling factorial to the upper argument. -/
theorem choose_mul_fallingFactorial_three (m t : ℕ) (ht : 3 ≤ t) :
    Nat.choose m t * (t * (t - 1) * (t - 2)) =
      (m * (m - 1) * (m - 2)) * Nat.choose (m - 3) (t - 3) := by
  have hchoose := Nat.choose_mul (n := m) (k := t) (s := 3) ht
  calc
    Nat.choose m t * (t * (t - 1) * (t - 2)) =
        Nat.choose m t * (6 * Nat.choose t 3) := by
      rw [six_mul_choose_three]
    _ = 6 * (Nat.choose m t * Nat.choose t 3) := by ring
    _ = 6 * (Nat.choose m 3 * Nat.choose (m - 3) (t - 3)) := by
      rw [hchoose]
    _ = (6 * Nat.choose m 3) * Nat.choose (m - 3) (t - 3) := by ring
    _ = (m * (m - 1) * (m - 2)) * Nat.choose (m - 3) (t - 3) := by
      rw [six_mul_choose_three]

/-- Falling-factorial form of fixed-size sampling supersaturation.  For a
sample size `t` between three and `A.card`, the excess over the ambient
additive Roth number, times the third falling factorial of `A.card`, is at
most the progression count times the third falling factorial of `t`. -/
theorem sub_mul_card_fallingFactorial_le_threeAPCount_mul_fallingFactorial
    {A U : Finset ℕ} (hAU : A ⊆ U) (t : ℕ) (ht : 3 ≤ t)
    (htA : t ≤ A.card) :
    (t - addRothNumber U) * A.card * (A.card - 1) * (A.card - 2) ≤
      threeAPCount A * t * (t - 1) * (t - 2) := by
  let C := Nat.choose (A.card - 3) (t - 3)
  have hC : 0 < C := by
    apply Nat.choose_pos
    omega
  have hkernel := sub_mul_choose_le_threeAPCount_mul_choose hAU t ht htA
  have hscaled :=
    Nat.mul_le_mul_right (t * (t - 1) * (t - 2)) hkernel
  have hid := choose_mul_fallingFactorial_three A.card t ht
  apply Nat.le_of_mul_le_mul_right (c := C) _ hC
  dsimp only [C] at hC ⊢
  calc
    (t - addRothNumber U) * A.card * (A.card - 1) * (A.card - 2) *
        Nat.choose (A.card - 3) (t - 3) =
        (t - addRothNumber U) *
          (Nat.choose A.card t * (t * (t - 1) * (t - 2))) := by
      rw [hid]
      ring
    _ ≤ threeAPCount A * Nat.choose (A.card - 3) (t - 3) *
        (t * (t - 1) * (t - 2)) := by
      simpa only [Nat.mul_assoc] using hscaled
    _ = threeAPCount A * t * (t - 1) * (t - 2) *
        Nat.choose (A.card - 3) (t - 3) := by ring

private theorem card_cube_mul_falling_le_sample_cube_mul_falling
    (t m : ℕ) (ht : 2 ≤ t) (htm : t ≤ m) :
    m * m * m * (t * (t - 1) * (t - 2)) ≤
      t * t * t * (m * (m - 1) * (m - 2)) := by
  have ht1 : t - 1 + 1 = t := Nat.sub_add_cancel (by omega)
  have ht2 : t - 2 + 2 = t := Nat.sub_add_cancel ht
  have hm1 : m - 1 + 1 = m := Nat.sub_add_cancel (by omega)
  have hm2 : m - 2 + 2 = m := Nat.sub_add_cancel (by omega)
  have hfactor1 : m * (t - 1) ≤ t * (m - 1) := by
    nlinarith
  have hfactor2 : m * (t - 2) ≤ t * (m - 2) := by
    nlinarith
  calc
    m * m * m * (t * (t - 1) * (t - 2)) =
        (m * t) * (m * (t - 1)) * (m * (t - 2)) := by ring
    _ ≤ (m * t) * (t * (m - 1)) * (t * (m - 2)) := by
      simpa only [Nat.mul_assoc] using
        Nat.mul_le_mul_left (m * t) (Nat.mul_le_mul hfactor1 hfactor2)
    _ = t * t * t * (m * (m - 1) * (m - 2)) := by ring

/-- Every finite set of naturals with at least two elements has additive Roth
number at least two.  This rules out the apparent `r = 1` boundary in the
cubic sampling argument whenever a set of size at least `2 * r` is present. -/
theorem two_le_addRothNumber_of_two_le_card (U : Finset ℕ)
    (hU : 2 ≤ U.card) :
    2 ≤ addRothNumber U := by
  obtain ⟨B, hBU, hBcard⟩ := Finset.exists_subset_card_eq hU
  have hfree : ThreeAPFree (B : Set ℕ) := by
    rw [threeAPFree_iff_eq_right]
    intro a ha b hb c hc habc
    by_contra hac
    have hab : a ≠ b := by
      rintro rfl
      omega
    have hbc : b ≠ c := by
      rintro rfl
      omega
    have hsub : ({a, b, c} : Finset ℕ) ⊆ B := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact ha
      · exact hb
      · exact hc
    have hcard3 : ({a, b, c} : Finset ℕ).card = 3 := by
      simp [hab, hac, hbc]
    have hcard : ({a, b, c} : Finset ℕ).card ≤ B.card :=
      Finset.card_le_card hsub
    omega
  simpa only [hBcard] using hfree.le_addRothNumber hBU

/-- Cubic BLS sparsening bound for canonical three-term progressions.  If
`A ⊆ U`, the size of `A` is at least twice the positive additive Roth number
of `U`, and `T = threeAPCount A`, then `A.card ^ 3 ≤ 8 * r ^ 2 * T`.
The proof derives `2 ≤ r`, so the otherwise delicate `r = 1` case is included
rather than excluded by an extra hypothesis. -/
theorem card_cube_le_eight_mul_addRothNumber_sq_mul_threeAPCount
    {A U : Finset ℕ} (hAU : A ⊆ U)
    (hdouble : 2 * addRothNumber U ≤ A.card)
    (hpos : 0 < addRothNumber U) :
    A.card ^ 3 ≤ 8 * addRothNumber U ^ 2 * threeAPCount A := by
  let r := addRothNumber U
  let m := A.card
  let T := threeAPCount A
  have hm2 : 2 ≤ m := by
    dsimp only [m, r] at hdouble ⊢
    omega
  have hU2 : 2 ≤ U.card := by
    exact hm2.trans (Finset.card_le_card hAU)
  have hr2 : 2 ≤ r := by
    exact two_le_addRothNumber_of_two_le_card U hU2
  have ht3 : 3 ≤ 2 * r := by omega
  have htm : 2 * r ≤ m := hdouble
  have hfall0 :=
    sub_mul_card_fallingFactorial_le_threeAPCount_mul_fallingFactorial
      hAU (2 * r) ht3 htm
  have hfall :
      r * m * (m - 1) * (m - 2) ≤
        T * (2 * r) * (2 * r - 1) * (2 * r - 2) := by
    dsimp only [r, m, T] at hfall0 ⊢
    simpa only [Nat.two_mul, Nat.add_sub_cancel_left] using hfall0
  have hratio := card_cube_mul_falling_le_sample_cube_mul_falling
    (2 * r) m (by omega) htm
  have hm1 : 0 < m - 1 := by omega
  have hm2' : 0 < m - 2 := by omega
  have hfm : 0 < m * (m - 1) * (m - 2) :=
    Nat.mul_pos (Nat.mul_pos (by omega) hm1) hm2'
  have hcombined :
      r * (m * m * m) * (m * (m - 1) * (m - 2)) ≤
        (T * ((2 * r) * (2 * r) * (2 * r))) *
          (m * (m - 1) * (m - 2)) := by
    calc
      r * (m * m * m) * (m * (m - 1) * (m - 2)) =
          (m * m * m) * (r * m * (m - 1) * (m - 2)) := by ring
      _ ≤ (m * m * m) *
          (T * (2 * r) * (2 * r - 1) * (2 * r - 2)) :=
        Nat.mul_le_mul_left (m * m * m) hfall
      _ = T * (m * m * m *
          ((2 * r) * (2 * r - 1) * (2 * r - 2))) := by ring
      _ ≤ T * ((2 * r) * (2 * r) * (2 * r) *
          (m * (m - 1) * (m - 2))) :=
        Nat.mul_le_mul_left T hratio
      _ = (T * ((2 * r) * (2 * r) * (2 * r))) *
          (m * (m - 1) * (m - 2)) := by ring
  have hcanceled :
      r * (m * m * m) ≤ T * ((2 * r) * (2 * r) * (2 * r)) :=
    Nat.le_of_mul_le_mul_right hcombined hfm
  apply Nat.le_of_mul_le_mul_left (c := r) _ hpos
  dsimp only [r, m, T] at hpos ⊢
  dsimp only [r, m, T] at hcanceled
  convert hcanceled using 1 <;> ring

/-- Threshold contrapositive of the cubic sparsening bound: if allowing `q`
progressions makes its cubic upper bound too small, then `A` has more than
`q` canonical three-term progressions. -/
theorem lt_threeAPCount_of_eight_mul_addRothNumber_sq_mul_lt_card_cube
    {A U : Finset ℕ} (q : ℕ) (hAU : A ⊆ U)
    (hdouble : 2 * addRothNumber U ≤ A.card)
    (hpos : 0 < addRothNumber U)
    (hlarge : 8 * addRothNumber U ^ 2 * q < A.card ^ 3) :
    q < threeAPCount A := by
  by_contra hnot
  have hcount : threeAPCount A ≤ q := Nat.le_of_not_gt hnot
  have hcubic := card_cube_le_eight_mul_addRothNumber_sq_mul_threeAPCount
    hAU hdouble hpos
  have hupper :
      A.card ^ 3 ≤ 8 * addRothNumber U ^ 2 * q := by
    exact hcubic.trans (Nat.mul_le_mul_left _ hcount)
  exact (not_lt_of_ge hupper) hlarge

set_option maxRecDepth 2048 in
/-- Joint satisfiability check for the sampling and cubic hypotheses.  The
interval `range 8` has additive Roth number four, so sampling all eight
points realizes the boundary `2 * r = A.card`. -/
example :
    let U := Finset.range 8
    let A := Finset.range 8
    A ⊆ U ∧
      3 ≤ A.card ∧
      2 * addRothNumber U ≤ A.card ∧
      0 < addRothNumber U ∧
      A.card ^ 3 ≤ 8 * addRothNumber U ^ 2 * threeAPCount A ∧
      1 < threeAPCount A := by
  dsimp only
  have hAU : Finset.range 8 ⊆ Finset.range 8 := Finset.Subset.rfl
  have hdouble : 2 * addRothNumber (Finset.range 8) ≤ (Finset.range 8).card := by
    decide
  have hpos : 0 < addRothNumber (Finset.range 8) := by decide
  refine ⟨hAU, by decide, hdouble, hpos, ?_, ?_⟩
  · exact card_cube_le_eight_mul_addRothNumber_sq_mul_threeAPCount
      hAU hdouble hpos
  · apply lt_threeAPCount_of_eight_mul_addRothNumber_sq_mul_lt_card_cube
      1 hAU hdouble hpos
    decide

#check @choose_mul_fallingFactorial_three
#check @sub_mul_card_fallingFactorial_le_threeAPCount_mul_fallingFactorial
#check @two_le_addRothNumber_of_two_le_card
#check @card_cube_le_eight_mul_addRothNumber_sq_mul_threeAPCount
#check @lt_threeAPCount_of_eight_mul_addRothNumber_sq_mul_lt_card_cube

#print axioms choose_mul_fallingFactorial_three
#print axioms sub_mul_card_fallingFactorial_le_threeAPCount_mul_fallingFactorial
#print axioms two_le_addRothNumber_of_two_le_card
#print axioms card_cube_le_eight_mul_addRothNumber_sq_mul_threeAPCount
#print axioms lt_threeAPCount_of_eight_mul_addRothNumber_sq_mul_lt_card_cube

end Erdos142
