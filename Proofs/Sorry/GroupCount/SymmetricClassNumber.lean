/-
# k(S_n) = p(n): conjugacy classes of the symmetric group are counted by partitions

## Classical source

Cauchy (cycle decomposition and conjugacy in the symmetric group); stated e.g. as
Sagan, *The Symmetric Group* (2nd ed., 2001), Prop. 1.1.1 and the remark following it,
and James–Kerber, *The Representation Theory of the Symmetric Group* (1981), 1.2.

Informal statement (verbatim from the target spec):

  Nat.card (ConjClasses (Equiv.Perm (Fin n))) = Fintype.card (Nat.Partition n);
  consequently commProb (Equiv.Perm (Fin n)) = p(n)/n! and the number of commuting
  pairs in S_n is n!·p(n).

Date: 2026-10-21.

## Mathlib adjacency

Mathlib has `Equiv.Perm.partition`, `Equiv.Perm.partition_eq_of_isConj`,
`Equiv.Perm.filter_parts_partition_eq_cycleType` and
`Equiv.Perm.exists_with_cycleType_iff`, but no bijection
`ConjClasses (Perm α) ≃ (Fintype.card α).Partition` and no class-number count.
-/
import Mathlib

set_option autoImplicit false

namespace GroupCount.SymmetricClassNumber

open Equiv

/-- A partition of `n` is determined by its multiset of parts that are at least `2`:
the remaining parts are all `1`, and their number is forced by the sum. -/
theorem partition_eq_of_filter_two_le_eq {n : ℕ} {p q : n.Partition}
    (h : p.parts.filter (2 ≤ ·) = q.parts.filter (2 ≤ ·)) : p = q := by
  -- the parts below `2` are all equal to `1`
  have hones : ∀ r : n.Partition,
      r.parts.filter (fun a => ¬ 2 ≤ a) =
        Multiset.replicate (r.parts.filter (fun a => ¬ 2 ≤ a)).card 1 := by
    intro r
    rw [Multiset.eq_replicate]
    refine ⟨rfl, fun b hb => ?_⟩
    rw [Multiset.mem_filter] at hb
    have hpos := r.parts_pos hb.1
    omega
  -- the sum splits along the filter
  have hsum : ∀ r : n.Partition,
      (r.parts.filter (2 ≤ ·)).sum + (r.parts.filter (fun a => ¬ 2 ≤ a)).card = n := by
    intro r
    conv_rhs => rw [← r.parts_sum, ← Multiset.filter_add_not (2 ≤ ·) r.parts]
    rw [Multiset.sum_add, hones r, Multiset.sum_replicate, smul_eq_mul, mul_one,
      Multiset.card_replicate]
  have hcard : (p.parts.filter (fun a => ¬ 2 ≤ a)).card =
      (q.parts.filter (fun a => ¬ 2 ≤ a)).card := by
    have hp := hsum p
    have hq := hsum q
    rw [h] at hp
    omega
  rw [Nat.Partition.ext_iff, ← Multiset.filter_add_not (2 ≤ ·) p.parts,
    ← Multiset.filter_add_not (2 ≤ ·) q.parts, h, hones p, hones q, hcard]

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Every partition of `Fintype.card α` is the cycle partition of some permutation of `α`. -/
theorem partition_surjective :
    Function.Surjective (Perm.partition : Perm α → (Fintype.card α).Partition) := by
  intro p
  have hle : (p.parts.filter (2 ≤ ·)).sum ≤ Fintype.card α := by
    conv_rhs => rw [← p.parts_sum, ← Multiset.filter_add_not (2 ≤ ·) p.parts, Multiset.sum_add]
    exact Nat.le_add_right _ _
  obtain ⟨g, hg⟩ := (Perm.exists_with_cycleType_iff (α := α)).2
    ⟨hle, fun a ha => (Multiset.mem_filter.1 ha).2⟩
  refine ⟨g, partition_eq_of_filter_two_le_eq ?_⟩
  rw [Perm.filter_parts_partition_eq_cycleType, hg]

/-- Conjugacy classes of `Perm α` correspond bijectively to partitions of `Fintype.card α`,
via the cycle type (with fixed points recorded as parts equal to `1`). -/
noncomputable def conjClassesEquivPartition :
    ConjClasses (Perm α) ≃ (Fintype.card α).Partition :=
  Equiv.ofBijective
    (Quotient.lift Perm.partition fun _ _ h => Perm.partition_eq_of_isConj.1 h)
    ⟨by
      rintro ⟨σ⟩ ⟨τ⟩ h
      exact ConjClasses.mk_eq_mk_iff_isConj.2 (Perm.partition_eq_of_isConj.2 h),
    by
      intro p
      obtain ⟨g, hg⟩ := partition_surjective (α := α) p
      exact ⟨ConjClasses.mk g, hg⟩⟩

/-- The conjugacy class of `σ` is sent to the cycle partition of `σ`. -/
theorem conjClassesEquivPartition_mk (σ : Perm α) :
    conjClassesEquivPartition (ConjClasses.mk σ) = σ.partition :=
  rfl

/-- **k(S_n) = p(n).** The number of conjugacy classes of the symmetric group on `n`
letters equals the number of partitions of `n`. -/
theorem card_conjClasses_perm_fin (n : ℕ) :
    Nat.card (ConjClasses (Perm (Fin n))) = Fintype.card (Nat.Partition n) := by
  rw [Nat.card_congr conjClassesEquivPartition, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- The commuting probability of `S_n` is `p(n) / n!`. -/
theorem commProb_perm_fin (n : ℕ) :
    commProb (Perm (Fin n)) = (Fintype.card (Nat.Partition n) : ℚ) / n.factorial := by
  rw [commProb_def', card_conjClasses_perm_fin, Nat.card_perm, Nat.card_fin]

/-- The number of ordered commuting pairs in `S_n` is `n! · p(n)`. -/
theorem card_commute_perm_fin (n : ℕ) :
    Nat.card {p : Perm (Fin n) × Perm (Fin n) // Commute p.1 p.2} =
      n.factorial * Fintype.card (Nat.Partition n) := by
  rw [card_comm_eq_card_conjClasses_mul_card, card_conjClasses_perm_fin, Nat.card_perm,
    Nat.card_fin, mul_comm]

/-! Ground truth.  Mathlib's `Fintype (Nat.Partition n)` instance is built by
`Fintype.ofSurjective` from compositions and does not kernel-reduce for `n ≥ 2`
(`decide` gets stuck), so the numeric checks use `n ≤ 1`, where `Nat.Partition n` is
`Unique`; the `S_3` check below tests the bijection itself on a transposition. -/

/-- Ground truth: `S_1` (trivial group) has one conjugacy class, `p(1) = 1`. -/
example : Nat.card (ConjClasses (Perm (Fin 1))) = 1 := by
  rw [card_conjClasses_perm_fin, Fintype.card_unique]

/-- Ground truth: `S_0` (trivial group) has one conjugacy class, `p(0) = 1`. -/
example : Nat.card (ConjClasses (Perm (Fin 0))) = 1 := by
  rw [card_conjClasses_perm_fin, Fintype.card_unique]

/-- Ground truth: the transposition `(0 1)` in `S_3` lands on the partition `2 + 1` of `3`. -/
example : (conjClassesEquivPartition (ConjClasses.mk (Equiv.swap (0 : Fin 3) 1))).parts =
    {2, 1} := by
  rw [conjClassesEquivPartition_mk, Perm.parts_partition, Perm.card_support_swap (by decide),
    (Perm.isSwap_iff_cycleType).1 ⟨0, 1, by decide, rfl⟩]
  decide

/-- Ground truth: `S_1` has `1! · p(1) = 1` ordered commuting pair. -/
example : Nat.card {p : Perm (Fin 1) × Perm (Fin 1) // Commute p.1 p.2} = 1 := by
  rw [card_commute_perm_fin, Fintype.card_unique, Nat.factorial_one]

end GroupCount.SymmetricClassNumber
