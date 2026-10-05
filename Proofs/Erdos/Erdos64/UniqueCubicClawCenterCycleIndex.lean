import Mathlib

set_option autoImplicit false

namespace Erdos64.UniqueCubicClawCenter.CycleIndex

/-- Addition by one is injective on cyclic indices, including the singleton case. -/
theorem succ_injective (m : ℕ) :
    Function.Injective (fun i : Fin (m + 1) => i + 1) := by
  intro i j h
  exact add_right_cancel h

/-- A cyclic successor has no fixed point when there are at least two indices. -/
theorem succ_ne (m : ℕ) (h : 2 ≤ m + 1) (i : Fin (m + 1)) : i + 1 ≠ i := by
  intro he
  have hz : (1 : Fin (m + 1)) = 0 :=
    add_left_cancel (show i + 1 = i + 0 by simpa using he)
  have hv := congrArg Fin.val hz
  norm_num [Fin.val_one, Nat.mod_eq_of_lt (show 1 < m + 1 by omega)] at hv

/-- Two cyclic successor steps do not return when there are at least three indices. -/
theorem succ_succ_ne (m : ℕ) (h : 3 ≤ m + 1) (i : Fin (m + 1)) :
    (i + 1) + 1 ≠ i := by
  intro he
  have hz : (1 : Fin (m + 1)) + 1 = 0 :=
    add_left_cancel (show i + (1 + 1) = i + 0 by simpa only [add_assoc, add_zero] using he)
  have hv := congrArg Fin.val hz
  norm_num [Fin.val_add, Fin.val_one,
    Nat.mod_eq_of_lt (show 1 < m + 1 by omega),
    Nat.mod_eq_of_lt (show 2 < m + 1 by omega)] at hv

/-- Unordered consecutive pairs distinguish cyclic edge indices for cycles of length at least three. -/
theorem pair_injective (m : ℕ) (h : 3 ≤ m + 1) :
    Function.Injective (fun i : Fin (m + 1) => ({i, i + 1} : Finset (Fin (m + 1)))) := by
  intro i j he
  change ({i, i + 1} : Finset (Fin (m + 1))) = {j, j + 1} at he
  have hi : i = j ∨ i = j + 1 := by
    have hm : i ∈ ({j, j + 1} : Finset (Fin (m + 1))) := by
      rw [← he]
      simp
    simpa using hm
  rcases hi with hij | hij
  · exact hij
  · have hs : i + 1 = j ∨ i + 1 = j + 1 := by
      have hm : i + 1 ∈ ({j, j + 1} : Finset (Fin (m + 1))) := by
        rw [← he]
        simp
      simpa using hm
    rcases hs with hs | hs
    · exact False.elim (succ_succ_ne m h j (by simpa only [hij] using hs))
    · exact succ_injective m hs

/-- Injective labels preserve the distinction between unordered consecutive index pairs. -/
theorem image_pair_injective {A : Type*} [DecidableEq A] (m : ℕ)
    (h : 3 ≤ m + 1) (c : Fin (m + 1) → A) (hc : Function.Injective c) :
    Function.Injective (fun i : Fin (m + 1) => ({c i, c (i + 1)} : Finset A)) := by
  intro i j he
  change ({c i, c (i + 1)} : Finset A) = {c j, c (j + 1)} at he
  apply pair_injective m h
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  have hx : c x = c i ∨ c x = c (i + 1) ↔ c x = c j ∨ c x = c (j + 1) := by
    have hm : c x ∈ ({c i, c (i + 1)} : Finset A) ↔
        c x ∈ ({c j, c (j + 1)} : Finset A) := by rw [he]
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  simpa only [hc.eq_iff] using hx

/-- Removing any one index from the universe of `Fin (m + 1)` leaves exactly `m` indices. -/
theorem card_erase (m : ℕ) (z : Fin (m + 1)) :
    (Finset.univ.erase z : Finset (Fin (m + 1))).card = m := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ z)]
  simp

/-- A dyadic cycle with exponent at least two has at least four indices. -/
theorem four_le_of_dyadic (m k : ℕ) (h : m + 1 = 2 ^ k) (hk : 2 ≤ k) :
    4 ≤ m + 1 := by
  have hp : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
  rw [h]
  norm_num at hp ⊢
  exact hp

/-- Removing one index from an even-sized index universe leaves an odd number of indices. -/
theorem odd_card_erase_of_even (m : ℕ) (z : Fin (m + 1)) (h : Even (m + 1)) :
    Odd (Finset.univ.erase z : Finset (Fin (m + 1))).card := by
  rw [card_erase]
  rcases h with ⟨t, ht⟩
  use t - 1
  omega

/-- Removing one index from a dyadic cycle of exponent at least two leaves odd cardinality. -/
theorem odd_card_erase_of_dyadic (m k : ℕ) (z : Fin (m + 1))
    (h : m + 1 = 2 ^ k) (hk : 2 ≤ k) :
    Odd (Finset.univ.erase z : Finset (Fin (m + 1))).card := by
  apply odd_card_erase_of_even
  rw [h]
  exact Nat.even_pow.mpr ⟨by decide, by omega⟩

end Erdos64.UniqueCubicClawCenter.CycleIndex
