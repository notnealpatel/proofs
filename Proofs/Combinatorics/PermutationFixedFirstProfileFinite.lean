import Combinatorics.PermutationFixedFirstLimit
import Combinatorics.PermutationEndpointProfile

set_option autoImplicit false

namespace PermutationFixedFirstProfile

open PermutationOrderCounting PermutationEndpointCounting PermutationFixedFirstLimit
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Output-label transposition identifies any two second-label fibers while fixing the first label. -/
theorem card_fixedTwo_eq {n : ℕ} (p q m b c : Fin n)
    (hmb : m ≠ b) (hmc : m ≠ c) :
    Nat.card (FixedTwo p q m b) = Nat.card (FixedTwo p q m c) := by
  classical
  let e : FixedTwo p q m b ≃ FixedTwo p q m c :=
    { toFun := fun π => ⟨π.val.trans (Equiv.swap b c), by
        constructor
        · change Equiv.swap b c (π.val p) = m
          rw [π.property.1]
          exact Equiv.swap_apply_of_ne_of_ne hmb hmc
        · change Equiv.swap b c (π.val q) = c
          rw [π.property.2]
          exact Equiv.swap_apply_left b c⟩
      invFun := fun π => ⟨π.val.trans (Equiv.swap b c), by
        constructor
        · change Equiv.swap b c (π.val p) = m
          rw [π.property.1]
          exact Equiv.swap_apply_of_ne_of_ne hmb hmc
        · change Equiv.swap b c (π.val q) = b
          rw [π.property.2]
          exact Equiv.swap_apply_right b c⟩
      left_inv := by
        intro π
        apply Subtype.ext
        ext i
        exact congrArg Fin.val (Equiv.swap_apply_self b c (π.val i))
      right_inv := by
        intro π
        apply Subtype.ext
        ext i
        exact congrArg Fin.val (Equiv.swap_apply_self b c (π.val i)) }
  exact Nat.card_congr e

example : Nat.card (FixedTwo (0 : Fin 3) 1 0 1) =
    Nat.card (FixedTwo (0 : Fin 3) 1 0 2) :=
  card_fixedTwo_eq 0 1 0 1 2 (by decide) (by decide)

/-- Partition a first-label event by its second-position label, excluding the impossible repeated label. -/
theorem card_first_event_partition {n : ℕ} (p q m : Fin n) (hpq : p ≠ q)
    (E : Equiv.Perm (Fin n) → Prop) :
    Nat.card {π : FixedFirst p m // E π.val} =
      ∑ b : {b : Fin n // b ≠ m}, Nat.card {π : FixedTwo p q m b.val // E π.val} := by
  classical
  let e : {π : FixedFirst p m // E π.val} ≃
      (Σ b : {b : Fin n // b ≠ m}, {π : FixedTwo p q m b.val // E π.val}) :=
    { toFun := fun π =>
        ⟨⟨π.val.val q, by
          intro he
          exact hpq (π.val.val.injective (π.val.property.trans he.symm))⟩,
          ⟨⟨π.val.val, π.val.property, rfl⟩, π.property⟩⟩
      invFun := fun π => ⟨⟨π.2.val.val, π.2.val.property.1⟩, π.2.property⟩
      left_inv := by intro π; rfl
      right_inv := by
        rintro ⟨b, ⟨⟨π, hπ⟩, hE⟩⟩
        rcases hπ with ⟨hp, hq⟩
        cases b with
        | mk b hb =>
          dsimp at hq
          subst b
          rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [Nat.card_eq_fintype_card]

example : Nat.card {π : FixedFirst (0 : Fin 2) 0 // FullAvoid π.val} =
    ∑ b : {b : Fin 2 // b ≠ 0},
      Nat.card {π : FixedTwo (0 : Fin 2) 1 0 b.val // FullAvoid π.val} :=
  card_first_event_partition 0 1 0 (by decide) FullAvoid

/-- The actual first-only fraction is the unweighted average over all valid distinct second labels. -/
theorem A_eq_row {n : ℕ} (hn : 2 ≤ n) (m : Fin n) :
    A n m.val =
      (∑ b : {b : Fin n // b ≠ m}, PermutationSameEdgeLimit.F n m.val b.val.val) /
        ((n : ℝ) - 1) := by
  classical
  letI : NeZero n := ⟨by omega⟩
  letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  let p : Fin n := 0
  let q : Fin n := ⟨n - 1, by omega⟩
  have hpq : p ≠ q := by intro h; have hv := congrArg Fin.val h; dsimp [p, q] at hv; omega
  let B := {b : Fin n // b ≠ m}
  obtain ⟨c, hc⟩ := exists_ne m
  let D : ℝ := Nat.card (FixedTwo p q m c)
  have hDpos : 0 < D := by
    have hnon := fixedTwo_nonempty p q m c hpq hc.symm
    dsimp [D]
    exact_mod_cast (Nat.card_pos_iff.mpr ⟨hnon, inferInstance⟩ :
      0 < Nat.card (FixedTwo p q m c))
  have hden (b : B) : (Nat.card (FixedTwo p q m b.val) : ℝ) = D := by
    dsimp [D]
    exact_mod_cast card_fixedTwo_eq p q m b.val c b.property.symm hc.symm
  have hB : Fintype.card B = n - 1 := by
    simpa only [B, Fintype.card_fin, Fintype.card_subtype_eq] using
      (Fintype.card_subtype_compl (fun b : Fin n => b = m))
  have htotal : (Nat.card (FixedFirst p m) : ℝ) = ((n : ℝ) - 1) * D := by
    have hpart := card_first_event_partition p q m hpq (fun _ => True)
    simp only [Nat.card_subtype_true] at hpart
    have hr : (Nat.card (FixedFirst p m) : ℝ) =
        ∑ b : B, (Nat.card (FixedTwo p q m b.val) : ℝ) := by exact_mod_cast hpart
    rw [hr]
    simp only [hden, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hB]
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have hnum (b : B) :
      (Nat.card {π : FixedTwo p q m b.val // FullAvoid π.val} : ℝ) / D =
        PermutationSameEdgeLimit.F n m.val b.val.val := by
    rw [PermutationSameEdgeLimit.F_eq_actual hn m.isLt b.val.isLt
      (fun he => b.property (Fin.ext he.symm))]
    let e : {π : FixedTwo p q m b.val // FullAvoid π.val} ≃
        PermutationMixedEndpointBound.AvoidTwo q m b.val :=
      { toFun := fun π => ⟨π.val.val, π.val.property, π.property⟩
        invFun := fun π => ⟨⟨π.val, π.property.1⟩, π.property.2⟩
        left_inv := by intro π; rfl
        right_inv := by intro π; rfl }
    have hcard := Nat.card_congr e
    rw [← hden b]
    simp only [Nat.card_eq_fintype_card] at hcard ⊢
    rw [hcard]
  have hpart := card_first_event_partition p q m hpq FullAvoid
  have hpartR : (Nat.card {π : FixedFirst p m // FullAvoid π.val} : ℝ) =
      ∑ b : B, (Nat.card {π : FixedTwo p q m b.val // FullAvoid π.val} : ℝ) := by
    exact_mod_cast hpart
  rw [A, dif_pos (show 1 ≤ n ∧ m.val < n from ⟨by omega, m.isLt⟩)]
  change (Nat.card {π : FixedFirst p m // FullAvoid π.val} : ℝ) /
    Nat.card (FixedFirst p m) = _
  rw [hpartR, htotal]
  simp_rw [← hnum]
  rw [← Finset.sum_div]
  field_simp
  rfl

example : A 2 0 =
    (∑ b : {b : Fin 2 // b ≠ 0}, PermutationSameEdgeLimit.F 2 0 b.val.val) /
      ((2 : ℝ) - 1) := A_eq_row (by decide) (0 : Fin 2)

/-- Uniform errors on valid distinct fibers pass unchanged to their row average. -/
theorem row_error {n : ℕ} (hn : 2 ≤ n) (m : Fin n)
    (P : ℝ × ℝ → ℝ) (e : ℝ)
    (he : ∀ b : {b : Fin n // b ≠ m},
      |PermutationSameEdgeLimit.F n m.val b.val.val -
        P ((m.val : ℝ) / n, (b.val.val : ℝ) / n)| ≤ e) :
    |A n m.val -
      (∑ b : {b : Fin n // b ≠ m}, P ((m.val : ℝ) / n, (b.val.val : ℝ) / n)) /
        ((n : ℝ) - 1)| ≤ e := by
  classical
  have hnR : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hB : Fintype.card {b : Fin n // b ≠ m} = n - 1 := by
    simpa only [Fintype.card_fin, Fintype.card_subtype_eq] using
      (Fintype.card_subtype_compl (fun b : Fin n => b = m))
  rw [A_eq_row hn m, ← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hnR]
  apply (div_le_iff₀ hnR).mpr
  calc
    |∑ b : {b : Fin n // b ≠ m},
      (PermutationSameEdgeLimit.F n m.val b.val.val -
        P ((m.val : ℝ) / n, (b.val.val : ℝ) / n))| ≤
        ∑ b : {b : Fin n // b ≠ m},
          |PermutationSameEdgeLimit.F n m.val b.val.val -
            P ((m.val : ℝ) / n, (b.val.val : ℝ) / n)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _b : {b : Fin n // b ≠ m}, e := Finset.sum_le_sum (fun b _ => he b)
    _ = e * ((n : ℝ) - 1) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hB,
        Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
      ring

/-- The residual-bearing profile controls each entire actual row, not only individual fibers. -/
theorem actual_row_error (P : ℝ × ℝ → ℝ)
    (hP : ∀ K z, z ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 →
      0 ≤ PermutationEndpointProfile.profileApprox K z - P z ∧
      PermutationEndpointProfile.profileApprox K z - P z ≤ 6 / ((K + 3) / 3).factorial)
    (K n : ℕ) (hn : 3 ≤ n) (m : Fin n)
    (hsize : 2 * (K + 3) - 2 ≤ n)
    (hlarge : (2 * (K + 3) - 2 - 2) * (2 * (K + 3) - 2 - 2 + 3) ≤ n) :
    |A n m.val -
      (∑ b : {b : Fin n // b ≠ m}, P ((m.val : ℝ) / n, (b.val.val : ℝ) / n)) /
        ((n : ℝ) - 1)| ≤
      ((2 * (K + 3) - 2).factorial : ℝ) *
        (2 * (2 * (K + 3) - 2 - 2 : ℕ) * ((2 * (K + 3) - 2 - 2 : ℕ) + 2) / n) +
          6 / ((K + 3) / 3).factorial := by
  apply row_error (by omega) m P
  intro b
  exact PermutationEndpointProfile.actual_profile_error P hP K n m.val b.val.val hn
    m.isLt b.val.isLt (fun he => b.property (Fin.ext he.symm)) hsize hlarge

end PermutationFixedFirstProfile
