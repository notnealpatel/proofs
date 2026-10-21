/-
# Commuting probability is monotone under passage to subgroups

## Classical source (recorded 2026-10-21)

* P. X. Gallagher, "The number of conjugacy classes in a finite group",
  Math. Z. 118 (1970) 175–179: `k(G) ≤ [G : H] · k(H)` for `H ≤ G`.
* W. H. Gustafson, "What is the probability that two group elements
  commute?", Amer. Math. Monthly 80 (1973) 1031–1034: `Pr(H) ≥ Pr(G)`.
* R. K. Nath and A. K. Das, arXiv:1009.5526, Theorem 2.1.

## Informal statement (verbatim from the target spec)

For a finite group G and any subgroup H, commProb G <= commProb H;
equivalently k(G) <= [G:H]·k(H).

## Mathlib adjacency

Mathlib's `commProb` (`Mathlib/GroupTheory/CommutingProbability.lean`) is the
definition used here; nothing is re-defined.  Mathlib proves only the opposite
direction `Subgroup.commProb_subgroup_le : commProb H ≤ commProb G * H.index ^ 2`
and the quotient bound `Subgroup.commProb_quotient_le`.

## Proof

For `x : G`, `|C_G(x)| ≤ [G : H] · |H ∩ C_G(x)|` because the relative index
`[C_G(x) : H ∩ C_G(x)]` is at most `[G : H]`.  Summing over `x : G` and then
swapping the order of summation of the commuting pairs in `G × H`,
`#comm(G) ≤ [G:H] · Σ_{h ∈ H} |C_G(h)| ≤ [G:H]^2 · #comm(H)`, and dividing by
`|G|^2 = [G:H]^2 |H|^2` gives the claim.
-/
import Mathlib.GroupTheory.CommutingProbability

set_option autoImplicit false

namespace GroupTPP.CommutingProbabilitySubgroup

open Finset Subgroup

variable {G : Type*} [Group G]

/-- For subgroups `H, K` of a finite group `G`, `|K| ≤ [G : H] · |H ⊓ K|`,
since the relative index of `H` in `K` is at most the index of `H` in `G`. -/
theorem card_le_index_mul_card_inf [Finite G] (H K : Subgroup G) :
    Nat.card K ≤ H.index * Nat.card (H ⊓ K : Subgroup G) := by
  have hcard : Nat.card (H ⊓ K : Subgroup G) * H.relIndex K = Nat.card K := by
    rw [← inf_relIndex_right, ← relIndex_bot_left, ← relIndex_bot_left,
      relIndex_mul_relIndex _ _ _ bot_le inf_le_right]
  have hrel : H.relIndex K ≤ H.index := by
    rw [← relIndex_top_right]
    exact relIndex_le_of_le_right le_top (by rw [relIndex_top_right]; exact index_ne_zero_of_finite)
  calc Nat.card K = Nat.card (H ⊓ K : Subgroup G) * H.relIndex K := hcard.symm
    _ ≤ Nat.card (H ⊓ K : Subgroup G) * H.index := Nat.mul_le_mul_left _ hrel
    _ = H.index * Nat.card (H ⊓ K : Subgroup G) := Nat.mul_comm _ _

open scoped Classical in
/-- The centralizer of `x` has as many elements as there are `y : G` commuting with `x`. -/
theorem card_centralizer_eq_sum [Fintype G] (x : G) :
    Nat.card (centralizer {x} : Subgroup G) = ∑ y : G, if Commute x y then 1 else 0 := by
  rw [← Finset.card_filter, Nat.card_eq_fintype_card, ← Fintype.card_subtype]
  refine Fintype.card_congr (Equiv.subtypeEquivRight fun y => ?_)
  rw [mem_centralizer_singleton_iff]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

open scoped Classical in
/-- `H ⊓ C_G(x)` has as many elements as there are `h : H` commuting with `x`. -/
theorem card_inf_centralizer_eq_sum [Fintype G] (H : Subgroup G) (x : G) :
    Nat.card (H ⊓ centralizer {x} : Subgroup G) =
      ∑ h : H, if Commute x (h : G) then 1 else 0 := by
  rw [← Finset.card_filter, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr
    { toFun := fun z => ⟨⟨z.1, z.2.1⟩, (mem_centralizer_singleton_iff.mp z.2.2).symm⟩
      invFun := fun w => ⟨w.1.1, w.1.2, mem_centralizer_singleton_iff.mpr w.2.symm⟩
      left_inv := fun z => rfl
      right_inv := fun w => rfl }

open scoped Classical in
/-- The number of commuting pairs of a finite magma `M` is the double sum of the
commuting indicator. -/
theorem card_commuting_pairs_eq_sum (M : Type*) [Mul M] [Fintype M] :
    Nat.card { p : M × M // Commute p.1 p.2 } =
      ∑ x : M, ∑ y : M, if Commute x y then 1 else 0 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter,
    Fintype.sum_prod_type]

/-- Counting form of Gallagher's inequality: `#comm(G) ≤ [G : H]^2 · #comm(H)`. -/
theorem card_commuting_pairs_le [Finite G] (H : Subgroup G) :
    Nat.card { p : G × G // Commute p.1 p.2 } ≤
      H.index ^ 2 * Nat.card { p : H × H // Commute p.1 p.2 } := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  set n := H.index with hn
  have hcoe : ∀ a b : H, Commute a b ↔ Commute (a : G) (b : G) := fun a b => by
    simp only [Commute, SemiconjBy, Subtype.ext_iff, Subgroup.coe_mul]
  have hstep : ∀ x : G, (∑ y : G, if Commute x y then 1 else 0) ≤
      n * ∑ h : H, if Commute x (h : G) then 1 else 0 := fun x => by
    rw [← card_centralizer_eq_sum, ← card_inf_centralizer_eq_sum]
    exact card_le_index_mul_card_inf H _
  calc Nat.card { p : G × G // Commute p.1 p.2 }
        = ∑ x : G, ∑ y : G, if Commute x y then 1 else 0 := card_commuting_pairs_eq_sum G
    _ ≤ ∑ x : G, n * ∑ h : H, if Commute x (h : G) then 1 else 0 :=
        Finset.sum_le_sum fun x _ => hstep x
    _ = n * ∑ h : H, ∑ x : G, if Commute (h : G) x then 1 else 0 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp only [Commute.symm_iff]
    _ ≤ n * ∑ h : H, n * ∑ h' : H, if Commute (h : G) (h' : G) then 1 else 0 :=
        Nat.mul_le_mul_left _ (Finset.sum_le_sum fun h _ => hstep h)
    _ = n ^ 2 * ∑ h : H, ∑ h' : H, if Commute h h' then 1 else 0 := by
        simp only [← Finset.mul_sum, hcoe, sq, Nat.mul_assoc]
    _ = n ^ 2 * Nat.card { p : H × H // Commute p.1 p.2 } := by
        rw [card_commuting_pairs_eq_sum]

/-- **Gallagher (1970), Gustafson (1973).**  For a finite group `G` and any subgroup
`H ≤ G`, the commuting probability of `G` is at most that of `H`:
`commProb G ≤ commProb H`. -/
theorem commProb_le_commProb_subgroup [Finite G] (H : Subgroup G) :
    commProb G ≤ commProb H := by
  have hcount := card_commuting_pairs_le H
  have hG : (0 : ℚ) < Nat.card G := Nat.cast_pos.mpr Finite.card_pos
  have hH : (0 : ℚ) < Nat.card H := Nat.cast_pos.mpr Finite.card_pos
  have hcardG : (Nat.card G : ℚ) = Nat.card H * H.index := by
    rw [← Nat.cast_mul, H.card_mul_index]
  rw [commProb_def, commProb_def, div_le_div_iff₀ (pow_pos hG 2) (pow_pos hH 2), hcardG]
  have hcountQ : (Nat.card { p : G × G // Commute p.1 p.2 } : ℚ) ≤
      (H.index : ℚ) ^ 2 * Nat.card { p : H × H // Commute p.1 p.2 } := by
    exact_mod_cast hcount
  calc (Nat.card { p : G × G // Commute p.1 p.2 } : ℚ) * (Nat.card H : ℚ) ^ 2
      ≤ (H.index : ℚ) ^ 2 * Nat.card { p : H × H // Commute p.1 p.2 } * (Nat.card H : ℚ) ^ 2 :=
        mul_le_mul_of_nonneg_right hcountQ (sq_nonneg _)
    _ = Nat.card { p : H × H // Commute p.1 p.2 } * ((Nat.card H : ℚ) * H.index) ^ 2 := by
        ring

/-! ## Non-vacuity: the hypotheses are met by a concrete nonabelian group -/

/-- Instantiation at `S₃` and its trivial subgroup. -/
example : commProb (Equiv.Perm (Fin 3)) ≤ commProb (⊥ : Subgroup (Equiv.Perm (Fin 3))) :=
  commProb_le_commProb_subgroup _

/-- Instantiation at the dihedral group `D₃` (order 6) and its rotation subgroup. -/
example : commProb (DihedralGroup 3) ≤
    commProb (Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup 3)) :=
  commProb_le_commProb_subgroup _

end GroupTPP.CommutingProbabilitySubgroup
