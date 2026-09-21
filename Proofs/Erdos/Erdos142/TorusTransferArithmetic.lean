/-
  Erdős Problem #142 — arithmetic/adapter kernel for the finite-torus transfer.

  This module is the arithmetic glue between the three now-accepted kernels:

  * `Erdos.Erdos142.SignedShortResidue` supplies the signed short residues
    `shortSignedSet R q`, the coordinate box `shortBox R q (2*k)`, and its
    cardinality bound `card_shortBox_two_k_le`;
  * `Erdos.Erdos142.ShortMultipleAvoidance` supplies the structure
    `ShortMultipleBox q k R` together with the existence theorems
    `ShortMultipleBox.exists_avoiding` and
    `ShortMultipleBox.exists_avoiding_and_injOn`;
  * `Erdos.Erdos142.TorusGrid` supplies the canonical lift `cyclicLift q a`
    together with the product-slice separation output
    `torusF_product_slice_separation_sq`.

  Three capabilities are packaged here:

  1. `signedShortBox q k R hR` presents the concrete signed box
     `shortBox R q (2*k)` as a `ShortMultipleBox q k R`, consuming only `1 ≤ R`;
  2. `sub_mem_shortSignedSet_of_lift_dist_lt` (and its square form
     `sub_mem_shortSignedSet_of_lift_sq_lt`) turn a lift-distance bound
     `|cyclicLift q X - cyclicLift q Z| < R / q` — respectively the square bound
     with `2 * (R^2 / (2 * q^2))`, matching `torusF_product_slice_separation_sq`
     at `Δ = R^2 / (2 * q^2)` — into membership `X - Z ∈ shortSignedSet R q`;
  3. `signedShortBox_exists_avoiding` and
     `signedShortBox_exists_avoiding_and_injOn` are the concrete-box
     read-offs of the avoidance theorems under the scale hypothesis
     `N * (2*R - 1)^(2*k) < q^(2*k)`.

  Only the arithmetic adapter is proved here; the full product-space transfer is
  deliberately out of scope.
-/

import Erdos.Erdos142.SignedShortResidue
import Erdos.Erdos142.ShortMultipleAvoidance
import Erdos.Erdos142.TorusGrid

set_option autoImplicit false

namespace Erdos142

/-- The **concrete signed short-multiple box**: the coordinate box
`shortBox R q (2*k)` of short vectors in the `2k`-dimensional residue grid,
presented as a `ShortMultipleBox q k R`.  Only `1 ≤ R` is needed: the origin and
negation stability come from `zero_mem_shortBox` / `neg_mem_shortBox`, and the
size bound from `card_shortBox_two_k_le`. -/
noncomputable def signedShortBox (q k R : ℕ) (hR : 1 ≤ R) : ShortMultipleBox q k R where
  carrier := shortBox R q (2 * k)
  zero_mem := zero_mem_shortBox hR
  neg_mem := fun _ hb => neg_mem_shortBox hb
  card_le := card_shortBox_two_k_le hR

/-- The carrier of the concrete signed box is exactly `shortBox R q (2*k)`. -/
@[simp]
theorem signedShortBox_carrier (q k R : ℕ) (hR : 1 ≤ R) :
    (signedShortBox q k R hR).carrier = shortBox R q (2 * k) := rfl

/-- **Lift-distance to residue membership.**  If `q > 0`, `1 ≤ R`, and the
canonical lifts of `X Z : ZMod q` differ by less than `R / q` in absolute
value, then the residue difference `X - Z` (this orientation) is a signed short
residue: `X - Z ∈ shortSignedSet R q`.

The witness is the integer difference of least nonnegative representatives
`(X.val : ℤ) - Z.val`; closeness of the lifts is exactly
`|(X.val : ℤ) - Z.val| < R`, and an integral value of absolute value below `R`
lies in `[-(R-1), R-1]`. -/
theorem sub_mem_shortSignedSet_of_lift_dist_lt {q : ℕ} (hq : 0 < q) {R : ℕ}
    (hR : 1 ≤ R) {X Z : ZMod q}
    (h : |cyclicLift q X - cyclicLift q Z| < (R : ℝ) / q) :
    X - Z ∈ shortSignedSet R q := by
  haveI : NeZero q := ⟨hq.ne'⟩
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hdiff : cyclicLift q X - cyclicLift q Z =
      ((X.val : ℝ) - (Z.val : ℝ)) / (q : ℝ) := by
    simp only [cyclicLift]
    ring
  have hreal : |(X.val : ℝ) - (Z.val : ℝ)| < (R : ℝ) := by
    rw [hdiff, abs_div, abs_of_pos hqR] at h
    rwa [div_lt_div_iff_of_pos_right hqR] at h
  have hInt : |((X.val : ℤ) - (Z.val : ℤ))| < (R : ℤ) := by
    have hcast : ((|((X.val : ℤ) - (Z.val : ℤ))| : ℤ) : ℝ) < (R : ℝ) := by
      rw [Int.cast_abs, Int.cast_sub, Int.cast_natCast, Int.cast_natCast]
      exact hreal
    exact_mod_cast hcast
  have hRcast : ((R - 1 : ℕ) : ℤ) = (R : ℤ) - 1 := by
    rw [Nat.cast_sub hR]
    norm_num
  have hbound : |((X.val : ℤ) - (Z.val : ℤ))| ≤ ((R - 1 : ℕ) : ℤ) := by
    rw [hRcast]
    exact Int.le_sub_one_of_lt hInt
  rw [mem_shortSignedSet]
  refine ⟨(X.val : ℤ) - (Z.val : ℤ), ?_, ?_, ?_⟩
  · rw [← hRcast]
    exact (abs_le.mp hbound).1
  · rw [← hRcast]
    exact (abs_le.mp hbound).2
  · push_cast
    rw [ZMod.natCast_zmod_val X, ZMod.natCast_zmod_val Z]

/-- **Symmetric orientation of the lift-distance bridge.**  The same hypothesis
`|cyclicLift q X - cyclicLift q Z| < R / q` also yields `Z - X ∈ shortSignedSet R q`,
by negation stability of the signed short residues.  This removes orientation
friction for downstream consumers that need the difference in the other order. -/
theorem sub_comm_mem_shortSignedSet_of_lift_dist_lt {q : ℕ} (hq : 0 < q) {R : ℕ}
    (hR : 1 ≤ R) {X Z : ZMod q}
    (h : |cyclicLift q X - cyclicLift q Z| < (R : ℝ) / q) :
    Z - X ∈ shortSignedSet R q := by
  have hmem := sub_mem_shortSignedSet_of_lift_dist_lt hq hR h
  simpa only [neg_sub] using neg_mem_shortSignedSet hmem

/-- **Square-form lift bridge.**  The square bound
`(cyclicLift q X - cyclicLift q Z)^2 < 2 * (R^2 / (2 * q^2))` — with
`2 * (R^2 / (2 * q^2)) = (R / q)^2` — implies `X - Z ∈ shortSignedSet R q`.
This is the `sqrt`-free form matching `torusF_product_slice_separation_sq`
at slice width `Δ = R^2 / (2 * q^2)`. -/
theorem sub_mem_shortSignedSet_of_lift_sq_lt {q : ℕ} (hq : 0 < q) {R : ℕ}
    (hR : 1 ≤ R) {X Z : ZMod q}
    (h : (cyclicLift q X - cyclicLift q Z) ^ 2 <
      2 * ((R : ℝ) ^ 2 / (2 * (q : ℝ) ^ 2))) :
    X - Z ∈ shortSignedSet R q := by
  refine sub_mem_shortSignedSet_of_lift_dist_lt hq hR ?_
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hRR : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR
  have hc : (0 : ℝ) < (R : ℝ) / q := div_pos hRR hqR
  have heq : 2 * ((R : ℝ) ^ 2 / (2 * (q : ℝ) ^ 2)) = ((R : ℝ) / q) ^ 2 := by
    rw [div_pow]
    field_simp
  rw [heq] at h
  have h' : |cyclicLift q X - cyclicLift q Z| < |(R : ℝ) / q| := sq_lt_sq.mp h
  rwa [abs_of_pos hc] at h'

/-- **Direct concrete-box avoidance.**  For prime `q`, `1 ≤ N ≤ q`, and the
scale hypothesis `N * (2*R - 1)^(2*k) < q^(2*k)`, the packed signed box
`signedShortBox q k R hR` admits a dilation vector `b` avoiding every
short-multiple preimage of `shortBox R q (2*k)`. -/
theorem signedShortBox_exists_avoiding {q k R N : ℕ} [Fact q.Prime] (hR : 1 ≤ R)
    (hN1 : 1 ≤ N) (hNq : N ≤ q)
    (hscale : N * (2 * R - 1) ^ (2 * k) < q ^ (2 * k)) :
    ∃ b : Fin (2 * k) → ZMod q,
      ∀ t : ℕ, 1 ≤ t → t < N → t • b ∉ shortBox R q (2 * k) :=
  (signedShortBox q k R hR).exists_avoiding hN1 hNq hscale

/-- **Direct concrete-box avoidance with injectivity.**  Combining
`signedShortBox_exists_avoiding` with the injectivity theorem for the translated
progression, for any base point `a` there is a dilation `b` avoiding every
short-multiple preimage of `shortBox R q (2*k)` and for which
`x ↦ a + x • b` is injective on `{0, 1, …, N-1}`. -/
theorem signedShortBox_exists_avoiding_and_injOn {q k R N : ℕ} [Fact q.Prime]
    (hR : 1 ≤ R) (hN1 : 1 ≤ N) (hNq : N ≤ q)
    (hscale : N * (2 * R - 1) ^ (2 * k) < q ^ (2 * k))
    (a : Fin (2 * k) → ZMod q) :
    ∃ b : Fin (2 * k) → ZMod q,
      (∀ t : ℕ, 1 ≤ t → t < N → t • b ∉ shortBox R q (2 * k)) ∧
        Set.InjOn (fun x : ℕ => a + x • b) (↑(Finset.range N) : Set ℕ) :=
  (signedShortBox q k R hR).exists_avoiding_and_injOn hN1 hNq hscale a

/-- **Cardinality form of the concrete-box progression.**  Under the same
hypotheses, the translated progression `{a + x • b | x < N}` is a set of exactly
`N` distinct grid vectors. -/
theorem signedShortBox_translate_card {q k R N : ℕ} [Fact q.Prime] (hR : 1 ≤ R)
    (hN1 : 1 ≤ N) (hNq : N ≤ q)
    (hscale : N * (2 * R - 1) ^ (2 * k) < q ^ (2 * k))
    (a : Fin (2 * k) → ZMod q) :
    ∃ b : Fin (2 * k) → ZMod q,
      (∀ t : ℕ, 1 ≤ t → t < N → t • b ∉ shortBox R q (2 * k)) ∧
        ((Finset.range N).image fun x : ℕ => a + x • b).card = N := by
  obtain ⟨b, hb⟩ := signedShortBox_exists_avoiding hR hN1 hNq hscale
  exact ⟨b, hb, card_image_range_translate_of_avoiding (zero_mem_shortBox hR) hb⟩

-- Ground-truth checks protecting the orientation and boundary of the bridges.

/-- Orientation check: `X = 1`, `Z = 0` in `ZMod 5` with `R = 2` have lift
distance `1/5 < 2/5`, and `1 - 0 = 1` is a signed short residue. -/
example : ((1 : ZMod 5) - (0 : ZMod 5)) ∈ shortSignedSet 2 5 := by
  apply sub_mem_shortSignedSet_of_lift_dist_lt (by norm_num) (by norm_num)
  have h1 : ((1 : ZMod 5)).val = 1 := ZMod.val_natCast_of_lt (by norm_num)
  have h0 : ((0 : ZMod 5)).val = 0 := ZMod.val_natCast_of_lt (by norm_num)
  rw [cyclicLift, cyclicLift, h1, h0]
  norm_num

/-- Boundary check: the strict lift-distance bound matters.  With `X = 2`,
`Z = 0` in `ZMod 5` and `R = 2` the lift distance equals `2/5`, and `2` is not a
signed short residue (the signed short representatives are `-1, 0, 1`). -/
example : (2 : ZMod 5) ∉ shortSignedSet 2 5 := by
  rw [mem_shortSignedSet]
  rintro ⟨m, h1, h2, h3⟩
  have hm : m = -1 ∨ m = 0 ∨ m = 1 := by omega
  rcases hm with rfl | rfl | rfl <;> exact absurd h3 (by decide)

/-- Square-form check: the square bound at `R = 2`, `q = 5` holds for the
`1/5` separation and delivers the oriented residue difference. -/
example : ((1 : ZMod 5) - (0 : ZMod 5)) ∈ shortSignedSet 2 5 := by
  apply sub_mem_shortSignedSet_of_lift_sq_lt (by norm_num) (by norm_num)
  have h1 : ((1 : ZMod 5)).val = 1 := ZMod.val_natCast_of_lt (by norm_num)
  have h0 : ((0 : ZMod 5)).val = 0 := ZMod.val_natCast_of_lt (by norm_num)
  rw [cyclicLift, cyclicLift, h1, h0]
  norm_num

#print axioms sub_mem_shortSignedSet_of_lift_dist_lt
#print axioms sub_comm_mem_shortSignedSet_of_lift_dist_lt
#print axioms sub_mem_shortSignedSet_of_lift_sq_lt
#print axioms signedShortBox_exists_avoiding
#print axioms signedShortBox_exists_avoiding_and_injOn
#print axioms signedShortBox_translate_card

end Erdos142