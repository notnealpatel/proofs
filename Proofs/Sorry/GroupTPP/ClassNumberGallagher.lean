/-
# Gallagher's inequality `k(G) ≤ k(N) · k(G/N)`

## Source (recorded 2026-10-21)

P. X. Gallagher, "The number of conjugacy classes in a finite group",
Math. Z. 118 (1970) 175-179 (the lemma on normal subgroups); see also
W. H. Gustafson, "What is the probability that two group elements commute?",
Amer. Math. Monthly 80 (1973).

## Informal statement (verbatim from the target spec)

For a finite group G and normal subgroup N, the number of conjugacy classes
satisfies k(G) <= k(N) * k(G/N); equivalently commProb G <= commProb N *
commProb (G/N). Corollaries: commProb G <= commProb (G/N) and
commProb G <= commProb N.

## Mathlib adjacency

Mathlib's `Mathlib/GroupTheory/CommutingProbability.lean` has only the reverse
direction `Subgroup.commProb_quotient_le` and `commProb_subgroup_le`; no
Gallagher-type upper bound was found (leandoc, 2026-10-21).

## Proof

Count commuting pairs (`card_comm_eq_card_conjClasses_mul_card`). Commuting
pairs of `G` map to commuting pairs of `G ⧸ N`; each fibre over `(a, b)` has at
most `#comm(N)` elements: for `x ∈ a`, the `y ∈ b` commuting with `x` form a
coset slice of `C_G(x)` of size `≤ |C_G(x) ∩ N|`; summing over `x ∈ a` and
swapping the sum gives `∑_{n ∈ N} |C_G(n) ∩ a| ≤ ∑_{n ∈ N} |C_N(n)| = #comm(N)`.
No new definitions: `ConjClasses`, `Nat.card`, `commProb` are Mathlib's.
-/
import Mathlib

set_option autoImplicit false

namespace GroupTPP.ClassNumberGallagher

open Finset

variable {G : Type*} [Group G]

open Classical in
/-- **Coset slice of a subgroup.** For subgroups `H, N ≤ G` and any coset `a ∈ G ⧸ N`,
the part of `H` lying in the left coset `a` has at most as many elements as
`H ∩ N`: it is empty or a left translate of `H ∩ N`. -/
theorem card_filter_mem_coset_le [Fintype G] (H N : Subgroup G) (a : G ⧸ N) :
    #{y | y ∈ H ∧ (y : G ⧸ N) = a} ≤ #{y | y ∈ H ∧ y ∈ N} := by
  rcases Finset.eq_empty_or_nonempty
      (({y | y ∈ H ∧ (y : G ⧸ N) = a} : Finset G)) with hempty | ⟨y₀, hy₀⟩
  · rw [hempty, card_empty]
    exact Nat.zero_le _
  · simp only [mem_filter, mem_univ, true_and] at hy₀
    refine card_le_card_of_injOn (fun y => y₀⁻¹ * y) ?_ ?_
    · intro y hy
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hy ⊢
      refine ⟨H.mul_mem (H.inv_mem hy₀.1) hy.1, ?_⟩
      exact QuotientGroup.eq.mp (hy₀.2.trans hy.2.symm)
    · intro y₁ _ y₂ _ h
      exact mul_left_cancel h


open Classical in
/-- Elements commuting with `x` form the centralizer of `{x}`. -/
theorem mem_centralizer_singleton_iff_commute (x y : G) :
    y ∈ Subgroup.centralizer {x} ↔ Commute x y := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact eq_comm

/-- A guarded count is a double indicator sum: `[P] · #{y | Q y} = ∑ y, [P ∧ Q y]`. -/
theorem ite_card_filter_eq_sum {α : Type*} [Fintype α] (P : Prop) [Decidable P]
    (Q : α → Prop) [DecidablePred Q] :
    (if P then #{y | Q y} else 0) = ∑ y : α, if P ∧ Q y then 1 else 0 := by
  by_cases hP : P
  · simp only [hP, if_true, true_and, card_filter]
  · simp only [hP, if_false, false_and, sum_const_zero]

open Classical in
/-- **Fibre bound.** Over a fixed pair `(a, b)` of cosets of a normal subgroup
`N`, the number of commuting pairs `(x, y)` of `G` with `xN = a`, `yN = b` is at
most the number of commuting pairs of `N`. -/
theorem card_commute_fiber_le [Fintype G] (N : Subgroup G) [N.Normal] (a b : G ⧸ N) :
    #{p : G × G | Commute p.1 p.2 ∧ ((p.1 : G ⧸ N), (p.2 : G ⧸ N)) = (a, b)} ≤
      #{p : N × N | Commute p.1 p.2} := by
  have step1 : #{p : G × G | Commute p.1 p.2 ∧ ((p.1 : G ⧸ N), (p.2 : G ⧸ N)) = (a, b)} =
      ∑ x : G, if (x : G ⧸ N) = a then
        #{y | y ∈ Subgroup.centralizer {x} ∧ (y : G ⧸ N) = b} else 0 := by
    rw [card_filter, Fintype.sum_prod_type]
    refine sum_congr rfl fun x _ => ?_
    split_ifs with hx
    · rw [card_filter]
      refine sum_congr rfl fun y _ => ?_
      simp [Prod.ext_iff, hx, mem_centralizer_singleton_iff_commute]
    · refine sum_eq_zero fun y _ => ?_
      simp [Prod.ext_iff, hx]
  have step2 : (∑ x : G, if (x : G ⧸ N) = a then
        #{y | y ∈ Subgroup.centralizer {x} ∧ (y : G ⧸ N) = b} else 0) ≤
      ∑ x : G, if (x : G ⧸ N) = a then
        #{y | y ∈ Subgroup.centralizer {x} ∧ y ∈ N} else 0 := by
    refine sum_le_sum fun x _ => ?_
    split_ifs
    · exact card_filter_mem_coset_le _ N b
    · exact le_rfl
  have step3 : (∑ x : G, if (x : G ⧸ N) = a then
        #{y | y ∈ Subgroup.centralizer {x} ∧ y ∈ N} else 0) =
      ∑ y : G, if y ∈ N then
        #{x | x ∈ Subgroup.centralizer {y} ∧ (x : G ⧸ N) = a} else 0 := by
    simp only [ite_card_filter_eq_sum]
    rw [sum_comm]
    refine sum_congr rfl fun y _ => sum_congr rfl fun x _ => ?_
    simp only [mem_centralizer_singleton_iff_commute]
    exact if_congr ⟨fun h => ⟨h.2.2, h.2.1.symm, h.1⟩, fun h => ⟨h.2.2, h.2.1.symm, h.1⟩⟩
      rfl rfl
  have step4 : (∑ y : G, if y ∈ N then
        #{x | x ∈ Subgroup.centralizer {y} ∧ (x : G ⧸ N) = a} else 0) ≤
      ∑ y : G, if y ∈ N then
        #{x | x ∈ Subgroup.centralizer {y} ∧ x ∈ N} else 0 := by
    refine sum_le_sum fun y _ => ?_
    split_ifs
    · exact card_filter_mem_coset_le _ N a
    · exact le_rfl
  have step5 : (∑ y : G, if y ∈ N then
        #{x | x ∈ Subgroup.centralizer {y} ∧ x ∈ N} else 0) =
      #{p : N × N | Commute p.1 p.2} := by
    have hG : (∑ y : G, if y ∈ N then
          #{x | x ∈ Subgroup.centralizer {y} ∧ x ∈ N} else 0) =
        #{p : G × G | p.1 ∈ N ∧ p.2 ∈ N ∧ Commute p.1 p.2} := by
      simp only [ite_card_filter_eq_sum]
      rw [card_filter, Fintype.sum_prod_type, sum_comm]
      refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
      simp only [mem_centralizer_singleton_iff_commute]
      exact if_congr ⟨fun h => ⟨h.2.2, h.1, h.2.1.symm⟩, fun h => ⟨h.2.1, h.2.2.symm, h.1⟩⟩
        rfl rfl
    rw [hG]
    symm
    refine card_nbij (fun p => ((p.1 : G), (p.2 : G))) ?_ ?_ ?_
    · intro p hp
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hp ⊢
      exact ⟨p.1.2, p.2.2, hp.map N.subtype⟩
    · intro p _ q _ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)
    · intro p hp
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hp
      refine ⟨(⟨p.1, hp.1⟩, ⟨p.2, hp.2.1⟩), ?_, rfl⟩
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
      exact Subtype.ext hp.2.2
  calc _ = _ := step1
    _ ≤ _ := step2
    _ = _ := step3
    _ ≤ _ := step4
    _ = _ := step5

/-- **Commuting pairs are submultiplicative along `1 → N → G → G/N → 1`.** For a
finite group `G` and normal subgroup `N`, the number of commuting pairs of `G` is at
most the number of commuting pairs of `N` times that of `G ⧸ N`. -/
theorem card_commute_le_mul_quotient [Finite G] (N : Subgroup G) [N.Normal] :
    Nat.card {p : G × G // Commute p.1 p.2} ≤
      Nat.card {p : N × N // Commute p.1 p.2} *
        Nat.card {q : (G ⧸ N) × (G ⧸ N) // Commute q.1 q.2} := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  let _ : Fintype (G ⧸ N) := Fintype.ofFinite (G ⧸ N)
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  refine card_le_mul_card_image_of_maps_to
    (f := fun p : G × G => ((p.1 : G ⧸ N), (p.2 : G ⧸ N))) ?_ _ ?_
  · intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp ⊢
    exact hp.map (QuotientGroup.mk' N)
  · intro q _
    rw [filter_filter]
    exact card_commute_fiber_le N q.1 q.2

/-- **Gallagher's inequality** (Gallagher 1970). For a finite group `G` and a normal
subgroup `N`, the number of conjugacy classes satisfies `k(G) ≤ k(N) · k(G/N)`. -/
theorem card_conjClasses_le_mul_quotient [Finite G] (N : Subgroup G) [N.Normal] :
    Nat.card (ConjClasses G) ≤ Nat.card (ConjClasses N) * Nat.card (ConjClasses (G ⧸ N)) := by
  have hpairs := card_commute_le_mul_quotient N
  rw [card_comm_eq_card_conjClasses_mul_card, card_comm_eq_card_conjClasses_mul_card,
    card_comm_eq_card_conjClasses_mul_card] at hpairs
  have hG : Nat.card G = Nat.card (G ⧸ N) * Nat.card N :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have hpos : 0 < Nat.card G := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc Nat.card (ConjClasses G) * Nat.card G
      ≤ Nat.card (ConjClasses N) * Nat.card N *
          (Nat.card (ConjClasses (G ⧸ N)) * Nat.card (G ⧸ N)) := hpairs
    _ = Nat.card (ConjClasses N) * Nat.card (ConjClasses (G ⧸ N)) * Nat.card G := by
      rw [hG]; ring

/-- **Gallagher's inequality, commuting-probability form.** For a finite group `G`
and a normal subgroup `N`, `commProb G ≤ commProb N · commProb (G ⧸ N)`. -/
theorem commProb_le_mul_quotient [Finite G] (N : Subgroup G) [N.Normal] :
    commProb G ≤ commProb N * commProb (G ⧸ N) := by
  have hpairs := card_commute_le_mul_quotient N
  have hG : Nat.card G = Nat.card (G ⧸ N) * Nat.card N :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup N
  rw [commProb_def, commProb_def, commProb_def, hG, div_mul_div_comm]
  have hcast : (Nat.card {p : G × G // Commute p.1 p.2} : ℚ) ≤
      (Nat.card {p : N × N // Commute p.1 p.2} : ℚ) *
        Nat.card {q : (G ⧸ N) × (G ⧸ N) // Commute q.1 q.2} := by
    exact_mod_cast hpairs
  calc (Nat.card {p : G × G // Commute p.1 p.2} : ℚ) / ((Nat.card (G ⧸ N) * Nat.card N : ℕ) : ℚ) ^ 2
      ≤ (Nat.card {p : N × N // Commute p.1 p.2} : ℚ) *
          Nat.card {q : (G ⧸ N) × (G ⧸ N) // Commute q.1 q.2} /
            ((Nat.card (G ⧸ N) * Nat.card N : ℕ) : ℚ) ^ 2 :=
        div_le_div_of_nonneg_right hcast (by positivity)
    _ = _ := by
      push_cast
      ring

/-- **Corollary.** For a finite group `G` and normal subgroup `N`,
`commProb G ≤ commProb (G ⧸ N)`. -/
theorem commProb_le_commProb_quotient [Finite G] (N : Subgroup G) [N.Normal] :
    commProb G ≤ commProb (G ⧸ N) :=
  (commProb_le_mul_quotient N).trans
    (mul_le_of_le_one_left (commProb_pos _).le (commProb_le_one _))

/-- **Corollary.** For a finite group `G` and normal subgroup `N`,
`commProb G ≤ commProb N`. -/
theorem commProb_le_commProb_subgroup [Finite G] (N : Subgroup G) [N.Normal] :
    commProb G ≤ commProb N :=
  (commProb_le_mul_quotient N).trans
    (mul_le_of_le_one_right (commProb_pos _).le (commProb_le_one _))

/-- Non-vacuity: the hypotheses are met by `S₃` with its alternating subgroup. -/
example : Nat.card (ConjClasses (Equiv.Perm (Fin 3))) ≤
    Nat.card (ConjClasses (alternatingGroup (Fin 3))) *
      Nat.card (ConjClasses (Equiv.Perm (Fin 3) ⧸ alternatingGroup (Fin 3))) :=
  card_conjClasses_le_mul_quotient _

end GroupTPP.ClassNumberGallagher
