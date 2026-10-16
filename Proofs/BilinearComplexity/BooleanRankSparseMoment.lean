import BilinearComplexity.BooleanRankProbability
import Mathlib.Tactic.Ring

set_option autoImplicit false

open scoped BigOperators
namespace BilinearComplexity.BooleanRankSparseMoment
open BilinearComplexity.BooleanRankProbability

/-- The power recording the number of ones is the product of the individual marks. -/
theorem pow_card_ones {n : ℕ} (x : Fin n → BoolSemiring) (z : ℝ) :
    z ^ (Finset.univ.filter fun i => x i = 1).card =
      ∏ i, if x i = 1 then z else 1 := by
  rw [Finset.prod_ite]
  simp

/-- The support-contained generating mass factors into the outside zero mass
and the Bernoulli generating polynomial on the target support. -/
theorem contained_generating_mass {n : ℕ} (p z : ℝ) (S : Finset (Fin n)) :
    (∑ x : Fin n → BoolSemiring,
      if ∀ i, x i = 1 → i ∈ S then
        (∏ i, entryWeight p (x i)) * z ^ (Finset.univ.filter fun i => x i = 1).card
      else 0) =
      (1 - p) ^ (n - S.card) * ((1 - p) + p * z) ^ S.card := by
  simp_rw [pow_card_ones, ← Finset.prod_mul_distrib]
  have hfactor : (∑ x : Fin n → BoolSemiring,
      if ∀ i, x i = 1 → i ∈ S then
        ∏ i, entryWeight p (x i) * (if x i = 1 then z else 1) else 0) =
      ∏ i : Fin n, ∑ b : BoolSemiring, if b = 1 → i ∈ S then
        entryWeight p b * (if b = 1 then z else 1) else 0 := by
    convert cylinder_factor
      (fun (_ : Fin n) b => entryWeight p b * (if b = 1 then z else 1))
      (fun i b => b = 1 → i ∈ S) using 1
    apply Finset.sum_congr rfl
    intro x hx
    split_ifs <;> rfl
  rw [hfactor]
  have hentry (i : Fin n) :
      (∑ b : BoolSemiring, if b = 1 → i ∈ S then
        entryWeight p b * (if b = 1 then z else 1) else 0) =
        if i ∈ S then (1 - p) + p * z else 1 - p := by
    by_cases hi : i ∈ S
    · change (∑ b : Bool, if b = true → i ∈ S then
        (if b = true then p else 1 - p) * (if b = true then z else 1) else 0) = _
      simp [hi, add_comm]
    · change (∑ b : Bool, if b = true → i ∈ S then
        (if b = true then p else 1 - p) * (if b = true then z else 1) else 0) = _
      simp [hi]
  simp_rw [hentry]
  rw [Finset.prod_ite]
  have hfilter : (Finset.univ.filter fun i : Fin n => i ∈ S) = S := by ext; simp
  have hcompl : (Finset.univ.filter fun i : Fin n => i ∉ S) = Finset.univ \ S := by
    ext; simp
  rw [hfilter, hcompl]
  simp [Finset.card_sdiff, mul_comm]

/-- The exact support-conditioned row moment identity, as a real polynomial
identity with no restrictions on either parameter. Outside support containment
the exponent is zero, not the row's original number of ones. -/
theorem support_conditioned_moment {n : ℕ} (p z : ℝ) (S : Finset (Fin n)) :
    (∑ x : Fin n → BoolSemiring,
      (∏ i, entryWeight p (x i)) *
        z ^ (if ∀ i, x i = 1 → i ∈ S then
          (Finset.univ.filter fun i => x i = 1).card else 0)) =
      1 - (1 - p) ^ (n - S.card) +
        (1 - p) ^ (n - S.card) * ((1 - p) + p * z) ^ S.card := by
  have hsplit (x : Fin n → BoolSemiring) :
      (∏ i, entryWeight p (x i)) *
          z ^ (if ∀ i, x i = 1 → i ∈ S then
            (Finset.univ.filter fun i => x i = 1).card else 0) =
        (∏ i, entryWeight p (x i)) -
          (if ∀ i, x i = 1 → i ∈ S then ∏ i, entryWeight p (x i) else 0) +
          (if ∀ i, x i = 1 → i ∈ S then
            (∏ i, entryWeight p (x i)) *
              z ^ (Finset.univ.filter fun i => x i = 1).card else 0) := by
    split_ifs <;> simp
  have htotal : (∑ x : Fin n → BoolSemiring, ∏ i, entryWeight p (x i)) = 1 := by
    rw [← Fintype.prod_sum]
    simp [sum_entryWeight]
  have hcontained : (∑ x : Fin n → BoolSemiring,
      if ∀ i, x i = 1 → i ∈ S then ∏ i, entryWeight p (x i) else 0) =
        (1 - p) ^ (n - S.card) := by
    simpa using contained_generating_mass p 1 S
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, htotal, hcontained,
    contained_generating_mass]

example (p z : ℝ) :
    (∑ x : Fin 0 → BoolSemiring, (∏ i, entryWeight p (x i)) *
      z ^ (if ∀ i, x i = 1 → i ∈ (∅ : Finset (Fin 0)) then
        (Finset.univ.filter fun i => x i = 1).card else 0)) = 1 := by
  simpa using support_conditioned_moment p z (∅ : Finset (Fin 0))

example {n : ℕ} (p z : ℝ) :
    (∑ x : Fin n → BoolSemiring, (∏ i, entryWeight p (x i)) *
      z ^ (if ∀ i, x i = 1 → i ∈ (∅ : Finset (Fin n)) then
        (Finset.univ.filter fun i => x i = 1).card else 0)) = 1 := by
  simpa using support_conditioned_moment p z (∅ : Finset (Fin n))

example {n : ℕ} (p z : ℝ) :
    (∑ x : Fin n → BoolSemiring, (∏ i, entryWeight p (x i)) *
      z ^ (Finset.univ.filter fun i => x i = 1).card) = ((1 - p) + p * z) ^ n := by
  simpa using support_conditioned_moment p z (Finset.univ : Finset (Fin n))

example {n : ℕ} (p : ℝ) (S : Finset (Fin n)) :
    (∑ x : Fin n → BoolSemiring, (∏ i, entryWeight p (x i)) *
      (1 : ℝ) ^ (if ∀ i, x i = 1 → i ∈ S then
        (Finset.univ.filter fun i => x i = 1).card else 0)) = 1 := by
  simpa using support_conditioned_moment p 1 S

example : Nonempty (Fin 0 → BoolSemiring) ∧ Nonempty (Fin 2 → BoolSemiring) :=
  ⟨⟨fun _ => 0⟩, ⟨fun _ => 0⟩⟩

end BilinearComplexity.BooleanRankSparseMoment
