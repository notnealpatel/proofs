/-
# Ordered set partitions counted by A007052

Sources: Gus Wiseman's OEIS A007052 comment (Mar 05 2020) and A332872.
For blocks `B_i, B_j` with `i+2 ≤ j`, the condition means every element of
`B_i` is smaller than every element of `B_j`, for all such pairs of blocks.
The number of these ordered partitions of `Fin (n+1)` equals the recurrence
`A007052 0 = 1`, `A007052 1 = 3`, `A007052 (n+2) = 4 A007052 (n+1)-2 A007052 n`.

Encoding blocks by an admissible surjection and deleting the smallest
element gives coupled recurrences for total counts and counts with the
first two blocks separated.
-/
import Mathlib

set_option autoImplicit false

open Finset

namespace Candidates.A007052WisemanOrderedPartitions

/-! ## Definitions -/

/-- OEIS A007052, by its recurrence: `a 0 = 1`, `a 1 = 3`, `a (n+2) = 4 a (n+1) - 2 a n`
(valued in `ℤ` so the subtraction is not truncated). -/
def A007052 : ℕ → ℤ
  | 0 => 1
  | 1 => 3
  | (n+2) => 4 * A007052 (n+1) - 2 * A007052 n

/-- The first thirteen listed terms of A007052. -/
example : (List.range 13).map A007052 =
    [1, 3, 10, 34, 116, 396, 1352, 4616, 15760, 53808, 183712, 627232, 2141504] := by
  decide

/-- `B : Fin k → Finset (Fin m)` is an ordered set partition of `Fin m` with `k` blocks: the
blocks are nonempty, cover `Fin m`, and are pairwise disjoint. -/
def IsOrderedSetPartition {m k : ℕ} (B : Fin k → Finset (Fin m)) : Prop :=
  (∀ i, (B i).Nonempty) ∧ (∀ x, ∃ i, x ∈ B i) ∧ ∀ i j x, x ∈ B i → x ∈ B j → i = j

/-- Wiseman's condition: no element of a block is greater than any element of a later,
non-adjacent block, i.e. `x < y` whenever `x ∈ B i`, `y ∈ B j` and `i + 2 ≤ j`. -/
def NonAdjacentBlocksOrdered {m k : ℕ} (B : Fin k → Finset (Fin m)) : Prop :=
  ∀ i j : Fin k, (i : ℕ) + 2 ≤ j → ∀ x ∈ B i, ∀ y ∈ B j, x < y

/-- `IsOrderedSetPartition` is decidable (finite quantification). -/
instance {m k : ℕ} (B : Fin k → Finset (Fin m)) : Decidable (IsOrderedSetPartition B) := by
  unfold IsOrderedSetPartition; infer_instance

/-- `NonAdjacentBlocksOrdered` is decidable (finite quantification). -/
instance {m k : ℕ} (B : Fin k → Finset (Fin m)) : Decidable (NonAdjacentBlocksOrdered B) := by
  unfold NonAdjacentBlocksOrdered; infer_instance

/-- `{1,2,3}` (here `Fin 3`) has 13 ordered set partitions in all
(the Fubini number), so the condition is not vacuous ... -/
example : (∑ k ∈ range 4, (univ.filter fun B : Fin k → Finset (Fin 3) =>
    IsOrderedSetPartition B).card) = 13 := by
  decide

/-- ... and exactly 10 of them satisfy Wiseman's condition, matching `A007052 2 = 10`
and Wiseman's listed examples. -/
example : (∑ k ∈ range 4, (univ.filter fun B : Fin k → Finset (Fin 3) =>
    IsOrderedSetPartition B ∧ NonAdjacentBlocksOrdered B).card) = 10 := by
  decide

/-! ## Block-index encoding -/

/-- Block-index form of Wiseman's condition: reading `β x` as the index of the block containing
`x`, every element of block `i` is smaller than every element of block `j` whenever `i + 2 ≤ j`. -/
def BlockIndexAdmissible {m k : ℕ} (β : Fin m → Fin k) : Prop :=
  ∀ x y : Fin m, (β x : ℕ) + 2 ≤ β y → x < y

/-- Auxiliary condition: every element of block `0` is smaller than every element of block `1`. -/
def FirstBlocksSeparated {m k : ℕ} (β : Fin m → Fin k) : Prop :=
  ∀ x y : Fin m, (β x : ℕ) = 0 → (β y : ℕ) = 1 → x < y

/-- `BlockIndexAdmissible` is decidable (finite quantification). -/
instance {m k : ℕ} (β : Fin m → Fin k) : Decidable (BlockIndexAdmissible β) := by
  unfold BlockIndexAdmissible; infer_instance

/-- `FirstBlocksSeparated` is decidable (finite quantification). -/
instance {m k : ℕ} (β : Fin m → Fin k) : Decidable (FirstBlocksSeparated β) := by
  unfold FirstBlocksSeparated; infer_instance

/-- Number of admissible surjections `Fin m → Fin k`, i.e. of ordered set partitions of
`Fin m` into `k` blocks satisfying Wiseman's condition (see
`card_orderedSetPartitions_eq_admCount`). -/
def admCount (m k : ℕ) : ℕ :=
  (univ.filter fun β : Fin m → Fin k => Function.Surjective β ∧ BlockIndexAdmissible β).card

/-- Number of admissible surjections `Fin m → Fin k` whose first two blocks are separated. -/
def sepCount (m k : ℕ) : ℕ :=
  (univ.filter fun β : Fin m → Fin k =>
    Function.Surjective β ∧ BlockIndexAdmissible β ∧ FirstBlocksSeparated β).card

/-- The encoding: the first four totals are `1, 3, 10, 34`. -/
example : (∑ k ∈ range 2, admCount 1 k, ∑ k ∈ range 3, admCount 2 k,
    ∑ k ∈ range 4, admCount 3 k, ∑ k ∈ range 5, admCount 4 k) = (1, 3, 10, 34) := by
  decide

/-- Bridge: ordered set partitions of `Fin m` into `k` blocks satisfying Wiseman's condition are
in bijection with admissible surjections `Fin m → Fin k` (block-index encoding). -/
theorem card_orderedSetPartitions_eq_admCount (m k : ℕ) :
    (univ.filter fun B : Fin k → Finset (Fin m) =>
      IsOrderedSetPartition B ∧ NonAdjacentBlocksOrdered B).card = admCount m k := by
  symm
  refine Finset.card_bij' (fun β _ => fun i => univ.filter (fun x => β x = i))
    (fun B hB => fun x => ((mem_filter.1 hB).2.1.2.1 x).choose)
    ?_ ?_ ?_ ?_
  · intro β hβ
    simp only [mem_filter, mem_univ, true_and] at hβ ⊢
    obtain ⟨hs, hadm⟩ := hβ
    refine ⟨⟨fun i => ?_, fun x => ⟨β x, by simp⟩, fun i j x hi hj => ?_⟩, ?_⟩
    · obtain ⟨x, hx⟩ := hs i
      exact ⟨x, by simp [hx]⟩
    · simp only [mem_filter, mem_univ, true_and] at hi hj
      rw [← hi, ← hj]
    · intro i j hij x hx y hy
      simp only [mem_filter, mem_univ, true_and] at hx hy
      exact hadm x y (by rw [hx, hy]; exact hij)
  · intro B hB
    have hB' := hB
    simp only [mem_filter, mem_univ, true_and] at hB' ⊢
    obtain ⟨⟨hne, hcov, hdisj⟩, hna⟩ := hB'
    refine ⟨fun i => ?_, fun x y hxy => ?_⟩
    · obtain ⟨x, hx⟩ := hne i
      exact ⟨x, hdisj _ _ x (hcov x).choose_spec hx⟩
    · exact hna _ _ hxy x (hcov x).choose_spec y (hcov y).choose_spec
  · intro β _
    funext x
    generalize_proofs hmem
    exact (Finset.mem_filter.1 hmem.choose_spec).2.symm
  · intro B hB
    have hB' := hB
    simp only [mem_filter, mem_univ, true_and] at hB'
    funext i
    ext x
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro rfl
      exact (hB'.1.2.1 x).choose_spec
    · intro hx
      exact hB'.1.2.2 _ _ x (hB'.1.2.1 x).choose_spec hx

/-! ## Removing the smallest element -/

/-- Counting maps on `Fin (m+1)` by their value at `0` and their tail. -/
theorem card_cons {m k : ℕ} (P : (Fin (m+1) → Fin k) → Prop) [DecidablePred P] :
    (univ.filter P).card =
      ∑ a : Fin k, (univ.filter (fun γ : Fin m → Fin k => P (Fin.cons a γ))).card := by
  rw [← Finset.card_sigma]
  refine Finset.card_bij' (fun β _ => ⟨β 0, Fin.tail β⟩) (fun p _ => Fin.cons p.1 p.2)
    ?_ ?_ ?_ ?_
  · intro β hβ
    simpa [Fin.cons_self_tail] using hβ
  · rintro ⟨a, γ⟩ h
    simpa using h
  · intro β _
    simp
  · rintro ⟨a, γ⟩ _
    simp

/-- `Fin.cons a γ` is surjective iff `γ` hits every value other than `a`. -/
theorem surjective_cons_iff {m k : ℕ} (a : Fin k) (γ : Fin m → Fin k) :
    Function.Surjective (Fin.cons a γ : Fin (m+1) → Fin k) ↔ ∀ v, v ≠ a → ∃ x, γ x = v := by
  constructor
  · intro h v hv
    obtain ⟨i, hi⟩ := h v
    induction i using Fin.cases with
    | zero => exact absurd hi.symm (by simpa using hv)
    | succ i => exact ⟨i, by simpa using hi⟩
  · intro h v
    by_cases hv : v = a
    · exact ⟨0, by simp [hv]⟩
    · obtain ⟨x, hx⟩ := h v hv
      exact ⟨x.succ, by simp [hx]⟩

/-- Admissibility of `Fin.cons a γ`: `γ` is admissible and `a` is at most one more than every
value of `γ`. -/
theorem blockIndexAdmissible_cons_iff {m k : ℕ} (a : Fin k) (γ : Fin m → Fin k) :
    BlockIndexAdmissible (Fin.cons a γ : Fin (m+1) → Fin k) ↔ BlockIndexAdmissible γ ∧ ∀ x, (a : ℕ) ≤ γ x + 1 := by
  constructor
  · intro h
    refine ⟨fun x y hxy => ?_, fun x => ?_⟩
    · have := h x.succ y.succ (by simpa using hxy)
      simpa using this
    · by_contra hlt
      have := h x.succ 0 (by simp only [Fin.cons_succ, Fin.cons_zero]; omega)
      exact absurd this (by simp)
  · rintro ⟨h, ha⟩ x y hxy
    induction x using Fin.cases with
    | zero =>
      induction y using Fin.cases with
      | zero => simp at hxy
      | succ y => exact Fin.succ_pos y
    | succ x =>
      induction y using Fin.cases with
      | zero => simp only [Fin.cons_succ, Fin.cons_zero] at hxy; have := ha x; omega
      | succ y => simpa using h x y (by simpa using hxy)

/-- Separation of the first two blocks for `Fin.cons a γ`. -/
theorem firstBlocksSeparated_cons_iff {m k : ℕ} (a : Fin k) (γ : Fin m → Fin k) :
    FirstBlocksSeparated (Fin.cons a γ : Fin (m+1) → Fin k) ↔ FirstBlocksSeparated γ ∧ ((a : ℕ) = 1 → ∀ x, (γ x : ℕ) ≠ 0) := by
  constructor
  · intro h
    refine ⟨fun x y hx hy => ?_, fun ha x hx => ?_⟩
    · simpa using h x.succ y.succ (by simpa using hx) (by simpa using hy)
    · have := h x.succ 0 (by simpa using hx) (by simpa using ha)
      exact absurd this (by simp)
  · rintro ⟨h, ha⟩ x y hx hy
    induction x using Fin.cases with
    | zero =>
      induction y using Fin.cases with
      | zero => simp only [Fin.cons_zero] at hx hy; omega
      | succ y => exact Fin.succ_pos y
    | succ x =>
      induction y using Fin.cases with
      | zero => simp only [Fin.cons_succ, Fin.cons_zero] at hx hy; exact absurd hx (ha hy x)
      | succ y => simpa using h x y (by simpa using hx) (by simpa using hy)

/-- Splitting the maps hitting every value other than `a` by whether they hit `a` as well. -/
theorem card_split {m k : ℕ} (a : Fin k) (Q : (Fin m → Fin k) → Prop) [DecidablePred Q] :
    (univ.filter (fun γ : Fin m → Fin k => (∀ v, v ≠ a → ∃ x, γ x = v) ∧ Q γ)).card =
      (univ.filter (fun γ : Fin m → Fin k => Function.Surjective γ ∧ Q γ)).card +
      (univ.filter (fun γ : Fin m → Fin k =>
        ((∀ v, v ≠ a → ∃ x, γ x = v) ∧ ∀ x, γ x ≠ a) ∧ Q γ)).card := by
  rw [← Finset.card_filter_add_card_filter_not (fun γ : Fin m → Fin k => ∃ x, γ x = a),
    Finset.filter_filter, Finset.filter_filter]
  congr 2
  · ext γ
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨⟨hs, hQ⟩, ha⟩
      refine ⟨fun v => ?_, hQ⟩
      by_cases hv : v = a
      · subst hv; exact ha
      · exact hs v hv
    · rintro ⟨hs, hQ⟩
      exact ⟨⟨fun v _ => hs v, hQ⟩, hs a⟩
  · ext γ
    simp only [mem_filter, mem_univ, true_and, not_exists]
    tauto

/-- Maps whose range is exactly `univ \ {p}` correspond to surjections onto `Fin j`, via
post-composition with `p.succAbove`. -/
theorem card_missing_only {m j : ℕ} (p : Fin (j+1)) (Q : (Fin m → Fin (j+1)) → Prop)
    [DecidablePred Q] :
    (univ.filter (fun γ : Fin m → Fin (j+1) =>
        ((∀ v, v ≠ p → ∃ x, γ x = v) ∧ ∀ x, γ x ≠ p) ∧ Q γ)).card =
      (univ.filter (fun γ' : Fin m → Fin j =>
        Function.Surjective γ' ∧ Q (p.succAbove ∘ γ'))).card := by
  symm
  refine Finset.card_bij (fun γ' _ => p.succAbove ∘ γ') ?_ ?_ ?_
  · intro γ' hγ'
    simp only [mem_filter, mem_univ, true_and] at hγ' ⊢
    refine ⟨⟨fun v hv => ?_, fun x => Fin.succAbove_ne p (γ' x)⟩, hγ'.2⟩
    obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq hv
    obtain ⟨x, hx⟩ := hγ'.1 z
    exact ⟨x, by simp [hx, hz]⟩
  · intro γ₁ _ γ₂ _ h
    funext x
    exact Fin.succAbove_right_injective (congrFun h x)
  · intro γ hγ
    simp only [mem_filter, mem_univ, true_and] at hγ
    obtain ⟨⟨hsurj, hmiss⟩, hQ⟩ := hγ
    choose γ' hγ' using fun x => Fin.exists_succAbove_eq (hmiss x)
    have hcomp : p.succAbove ∘ γ' = γ := funext hγ'
    refine ⟨γ', ?_, hcomp⟩
    simp only [mem_filter, mem_univ, true_and]
    refine ⟨fun z => ?_, by rw [hcomp]; exact hQ⟩
    obtain ⟨x, hx⟩ := hsurj (p.succAbove z) (Fin.succAbove_ne p z)
    exact ⟨x, Fin.succAbove_right_injective ((hγ' x).trans hx)⟩

/-- Value of `(1 : Fin (j+2)).succAbove v`: it fixes `0` and shifts every other value up by one. -/
theorem val_succAbove_one {j : ℕ} (v : Fin (j+1)) :
    (((1 : Fin (j+2)).succAbove v : Fin (j+2)) : ℕ) = if (v : ℕ) = 0 then 0 else (v : ℕ) + 1 := by
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_one]
  split_ifs <;> simp_all

/-- Shifting all block indices up by one preserves admissibility. -/
theorem blockIndexAdmissible_succ_comp_iff {m j : ℕ} (γ : Fin m → Fin j) :
    BlockIndexAdmissible (Fin.succ ∘ γ) ↔ BlockIndexAdmissible γ := by
  simp [BlockIndexAdmissible]

/-- Opening a gap at block index `1` is admissible iff the original map is admissible and its
blocks `0` and `1` are separated. -/
theorem blockIndexAdmissible_succAbove_one_iff {m j : ℕ} (γ : Fin m → Fin (j+1)) :
    BlockIndexAdmissible ((1 : Fin (j+2)).succAbove ∘ γ) ↔ BlockIndexAdmissible γ ∧ FirstBlocksSeparated γ := by
  simp only [BlockIndexAdmissible, FirstBlocksSeparated, Function.comp, val_succAbove_one]
  constructor
  · intro h
    refine ⟨fun x y hxy => h x y ?_, fun x y hx hy => h x y ?_⟩
    · split_ifs <;> omega
    · simp [hx, hy]
  · rintro ⟨h1, h2⟩ x y hxy
    split_ifs at hxy with hx hy hy
    · omega
    · rcases Nat.lt_or_ge (γ y : ℕ) 2 with hlt | hge
      · exact h2 x y hx (by omega)
      · exact h1 x y (by omega)
    · omega
    · exact h1 x y (by omega)

/-- Admissible surjections on `Fin (m+1)` sending `0` to block `0`. -/
theorem card_cons_zero (m j : ℕ) :
    (univ.filter fun γ : Fin m → Fin (j+1) =>
      Function.Surjective (Fin.cons 0 γ : Fin (m+1) → Fin (j+1)) ∧
        BlockIndexAdmissible (Fin.cons 0 γ : Fin (m+1) → Fin (j+1))).card = admCount m (j+1) + admCount m j := by
  have hfil : (univ.filter fun γ : Fin m → Fin (j+1) =>
      Function.Surjective (Fin.cons 0 γ : Fin (m+1) → Fin (j+1)) ∧
        BlockIndexAdmissible (Fin.cons 0 γ : Fin (m+1) → Fin (j+1))) =
      univ.filter fun γ : Fin m → Fin (j+1) => (∀ v, v ≠ 0 → ∃ x, γ x = v) ∧ BlockIndexAdmissible γ := by
    refine Finset.filter_congr fun γ _ => ?_
    rw [surjective_cons_iff, blockIndexAdmissible_cons_iff]
    simp
  rw [hfil, card_split, card_missing_only]
  simp only [Fin.succAbove_zero, blockIndexAdmissible_succ_comp_iff]
  rfl

/-- Admissible surjections on `Fin (m+1)` sending `0` to block `1`. -/
theorem card_cons_one (m j : ℕ) :
    (univ.filter fun γ : Fin m → Fin (j+2) =>
      Function.Surjective (Fin.cons 1 γ : Fin (m+1) → Fin (j+2)) ∧
        BlockIndexAdmissible (Fin.cons 1 γ : Fin (m+1) → Fin (j+2))).card = admCount m (j+2) + sepCount m (j+1) := by
  have hfil : (univ.filter fun γ : Fin m → Fin (j+2) =>
      Function.Surjective (Fin.cons 1 γ : Fin (m+1) → Fin (j+2)) ∧
        BlockIndexAdmissible (Fin.cons 1 γ : Fin (m+1) → Fin (j+2))) =
      univ.filter fun γ : Fin m → Fin (j+2) => (∀ v, v ≠ 1 → ∃ x, γ x = v) ∧ BlockIndexAdmissible γ := by
    refine Finset.filter_congr fun γ _ => ?_
    rw [surjective_cons_iff, blockIndexAdmissible_cons_iff]
    simp
  rw [hfil, card_split, card_missing_only]
  simp only [blockIndexAdmissible_succAbove_one_iff]
  rfl

/-- The element `0` never lies in a block of index at least `2`. -/
theorem card_cons_of_two_le {m k : ℕ} (a : Fin k) (ha : 2 ≤ (a : ℕ)) :
    (univ.filter fun γ : Fin m → Fin k =>
      Function.Surjective (Fin.cons a γ : Fin (m+1) → Fin k) ∧
        BlockIndexAdmissible (Fin.cons a γ : Fin (m+1) → Fin k)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro γ _ ⟨hs, hadm⟩
  rw [surjective_cons_iff] at hs
  rw [blockIndexAdmissible_cons_iff] at hadm
  have hk : 0 < k := by omega
  obtain ⟨x, hx⟩ := hs ⟨0, hk⟩ (by intro h; rw [← h] at ha; simp at ha)
  have := hadm.2 x
  rw [hx] at this
  simp only [zero_add] at this
  omega

/-- Separated admissible surjections on `Fin (m+1)` sending `0` to block `0`. -/
theorem card_cons_sep_zero (m j : ℕ) :
    (univ.filter fun γ : Fin m → Fin (j+1) =>
      Function.Surjective (Fin.cons 0 γ : Fin (m+1) → Fin (j+1)) ∧
        BlockIndexAdmissible (Fin.cons 0 γ : Fin (m+1) → Fin (j+1)) ∧
        FirstBlocksSeparated (Fin.cons 0 γ : Fin (m+1) → Fin (j+1))).card = sepCount m (j+1) + admCount m j := by
  have hfil : (univ.filter fun γ : Fin m → Fin (j+1) =>
      Function.Surjective (Fin.cons 0 γ : Fin (m+1) → Fin (j+1)) ∧
        BlockIndexAdmissible (Fin.cons 0 γ : Fin (m+1) → Fin (j+1)) ∧
        FirstBlocksSeparated (Fin.cons 0 γ : Fin (m+1) → Fin (j+1))) =
      univ.filter fun γ : Fin m → Fin (j+1) =>
        (∀ v, v ≠ 0 → ∃ x, γ x = v) ∧ (BlockIndexAdmissible γ ∧ FirstBlocksSeparated γ) := by
    refine Finset.filter_congr fun γ _ => ?_
    rw [surjective_cons_iff, blockIndexAdmissible_cons_iff, firstBlocksSeparated_cons_iff]
    simp
  rw [hfil, card_split, card_missing_only]
  simp only [Fin.succAbove_zero, blockIndexAdmissible_succ_comp_iff]
  have hsep : ∀ γ' : Fin m → Fin j, FirstBlocksSeparated (Fin.succ ∘ γ') := by
    intro γ' x y hx
    simp at hx
  simp only [hsep, and_true]
  rfl

/-- In a separated admissible surjection, the element `0` lies in block `0`. -/
theorem card_cons_sep_of_ne_zero {m k : ℕ} (a : Fin k) (ha : (a : ℕ) ≠ 0) :
    (univ.filter fun γ : Fin m → Fin k =>
      Function.Surjective (Fin.cons a γ : Fin (m+1) → Fin k) ∧
        BlockIndexAdmissible (Fin.cons a γ : Fin (m+1) → Fin k) ∧
        FirstBlocksSeparated (Fin.cons a γ : Fin (m+1) → Fin k)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro γ _ ⟨hs, hadm, hsep⟩
  rw [surjective_cons_iff] at hs
  rw [blockIndexAdmissible_cons_iff] at hadm
  rw [firstBlocksSeparated_cons_iff] at hsep
  have hk : 0 < k := by omega
  obtain ⟨x, hx⟩ := hs ⟨0, hk⟩ (by intro h; rw [← h] at ha; simp at ha)
  have h1 := hadm.2 x
  rw [hx] at h1
  simp only [zero_add] at h1
  have h2 := hsep.2 (by omega) x
  rw [hx] at h2
  simp at h2

/-! ## Recurrences for the counts -/

/-- Recurrence `admCount (m+1) (j+2) = 2 admCount m (j+2) + admCount m (j+1) + sepCount m (j+1)`. -/
theorem admCount_succ_add_two (m j : ℕ) :
    admCount (m+1) (j+2) = 2 * admCount m (j+2) + admCount m (j+1) + sepCount m (j+1) := by
  rw [admCount, card_cons, Fin.sum_univ_succ, Fin.sum_univ_succ]
  have hrest : ∑ i : Fin j, (univ.filter fun γ : Fin m → Fin (j+2) =>
      Function.Surjective (Fin.cons i.succ.succ γ : Fin (m+1) → Fin (j+2)) ∧
        BlockIndexAdmissible (Fin.cons i.succ.succ γ : Fin (m+1) → Fin (j+2))).card = 0 := by
    refine Finset.sum_eq_zero fun i _ => card_cons_of_two_le _ (by simp)
  rw [hrest, Fin.succ_zero_eq_one, card_cons_zero, card_cons_one]
  ring

/-- Recurrence for one block. -/
theorem admCount_succ_one (m : ℕ) : admCount (m+1) 1 = admCount m 1 + admCount m 0 := by
  rw [admCount, card_cons, Fin.sum_univ_one, card_cons_zero]

/-- Recurrence `sepCount (m+1) (j+1) = sepCount m (j+1) + admCount m j`. -/
theorem sepCount_succ_add_one (m j : ℕ) : sepCount (m+1) (j+1) = sepCount m (j+1) + admCount m j := by
  rw [sepCount, card_cons, Fin.sum_univ_succ]
  have hrest : ∑ i : Fin j, (univ.filter fun γ : Fin m → Fin (j+1) =>
      Function.Surjective (Fin.cons i.succ γ : Fin (m+1) → Fin (j+1)) ∧
        BlockIndexAdmissible (Fin.cons i.succ γ : Fin (m+1) → Fin (j+1)) ∧
        FirstBlocksSeparated (Fin.cons i.succ γ : Fin (m+1) → Fin (j+1))).card = 0 := by
    refine Finset.sum_eq_zero fun i _ => card_cons_sep_of_ne_zero _ (by simp)
  rw [hrest, card_cons_sep_zero, add_zero]

/-- No map from a nonempty set into zero blocks. -/
theorem admCount_succ_zero (m : ℕ) : admCount (m+1) 0 = 0 := by
  simp [admCount]

/-- No map from a nonempty set into zero blocks. -/
theorem sepCount_succ_zero (m : ℕ) : sepCount (m+1) 0 = 0 := by
  simp [sepCount]

/-- The empty ordered set partition of the empty set. -/
theorem admCount_zero_zero : admCount 0 0 = 1 := by decide

/-- The empty ordered set partition of the empty set. -/
theorem sepCount_zero_zero : sepCount 0 0 = 1 := by decide

/-- The empty set has no ordered set partition with a positive number of blocks. -/
theorem admCount_zero_succ (k : ℕ) : admCount 0 (k+1) = 0 := by
  rw [admCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro β _ ⟨hs, _⟩
  obtain ⟨x, _⟩ := hs 0
  exact x.elim0

/-- The empty set has no ordered set partition with a positive number of blocks. -/
theorem sepCount_zero_succ (k : ℕ) : sepCount 0 (k+1) = 0 := by
  rw [sepCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro β _ ⟨hs, _⟩
  obtain ⟨x, _⟩ := hs 0
  exact x.elim0

/-- There are no surjections `Fin m → Fin k` when `m < k`. -/
theorem admCount_eq_zero_of_lt {m k : ℕ} (h : m < k) : admCount m k = 0 := by
  rw [admCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro β _ ⟨hs, _⟩
  have := Fintype.card_le_of_surjective β hs
  simp only [Fintype.card_fin] at this
  omega

/-- There are no surjections `Fin m → Fin k` when `m < k`. -/
theorem sepCount_eq_zero_of_lt {m k : ℕ} (h : m < k) : sepCount m k = 0 := by
  rw [sepCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro β _ ⟨hs, _⟩
  have := Fintype.card_le_of_surjective β hs
  simp only [Fintype.card_fin] at this
  omega

/-- A nonempty set has exactly one admissible one-block partition. -/
theorem admCount_succ_one_eq_one (m : ℕ) : admCount (m+1) 1 = 1 := by
  induction m with
  | zero => rw [admCount_succ_one, admCount_zero_succ, admCount_zero_zero]
  | succ m ih => rw [admCount_succ_one, ih, admCount_succ_zero]

/-! ## Totals over the number of blocks -/

/-- Total number of admissible surjections from `Fin m`, over all block counts `k ≤ m`. -/
def admTotal (m : ℕ) : ℤ := ∑ k ∈ range (m+1), (admCount m k : ℤ)

/-- Total number of separated admissible surjections from `Fin m`, over all `k ≤ m`. -/
def sepTotal (m : ℕ) : ℤ := ∑ k ∈ range (m+1), (sepCount m k : ℤ)

/-- Summing `admCount m k` over any range `k < N` with `m + 1 ≤ N` gives `admTotal m`. -/
theorem sum_admCount_eq_admTotal (m N : ℕ) (h : m + 1 ≤ N) :
    ∑ k ∈ range N, (admCount m k : ℤ) = admTotal m := by
  induction N, h using Nat.le_induction with
  | base => rfl
  | succ N hN ih => rw [sum_range_succ, ih, admCount_eq_zero_of_lt (by omega)]; simp

/-- Summing `sepCount m k` over any range `k < N` with `m + 1 ≤ N` gives `sepTotal m`. -/
theorem sum_sepCount_eq_sepTotal (m N : ℕ) (h : m + 1 ≤ N) :
    ∑ k ∈ range N, (sepCount m k : ℤ) = sepTotal m := by
  induction N, h using Nat.le_induction with
  | base => rfl
  | succ N hN ih => rw [sum_range_succ, ih, sepCount_eq_zero_of_lt (by omega)]; simp

/-- Recurrence `admTotal (m+2) = 3 admTotal (m+1) + sepTotal (m+1) - 1`. -/
theorem admTotal_succ_succ (m : ℕ) : admTotal (m+2) = 3 * admTotal (m+1) + sepTotal (m+1) - 1 := by
  have hL : admTotal (m+2) = ∑ j ∈ range (m+1), (admCount (m+2) (j+2) : ℤ) + admCount (m+2) 1 + admCount (m+2) 0 := by
    rw [admTotal, sum_range_succ', sum_range_succ']
  have hA : admTotal (m+1) = ∑ j ∈ range (m+1), (admCount (m+1) (j+2) : ℤ) + admCount (m+1) 1 + admCount (m+1) 0 := by
    rw [← sum_admCount_eq_admTotal (m+1) (m+3) (by omega), sum_range_succ', sum_range_succ']
  have hB : admTotal (m+1) = ∑ j ∈ range (m+1), (admCount (m+1) (j+1) : ℤ) + admCount (m+1) 0 := by
    rw [admTotal, sum_range_succ']
  have hC : sepTotal (m+1) = ∑ j ∈ range (m+1), (sepCount (m+1) (j+1) : ℤ) + sepCount (m+1) 0 := by
    rw [sepTotal, sum_range_succ']
  have hrec : ∑ j ∈ range (m+1), (admCount (m+2) (j+2) : ℤ) =
      2 * ∑ j ∈ range (m+1), (admCount (m+1) (j+2) : ℤ) + ∑ j ∈ range (m+1), (admCount (m+1) (j+1) : ℤ) +
        ∑ j ∈ range (m+1), (sepCount (m+1) (j+1) : ℤ) := by
    rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    rw [admCount_succ_add_two]
    push_cast
    ring
  have h0 := admCount_succ_zero (m+1)
  have h0' := admCount_succ_zero m
  have hg0 := sepCount_succ_zero m
  have h1 := admCount_succ_one_eq_one (m+1)
  have h1' := admCount_succ_one_eq_one m
  rw [hL, hrec, h0, h1]
  simp only [h0', h1'] at hA hB
  rw [hg0] at hC
  push_cast at hA hB hC ⊢
  linear_combination (-2) * hA - hB - hC

/-- Recurrence `sepTotal (m+2) = sepTotal (m+1) + admTotal (m+1)`. -/
theorem sepTotal_succ_succ (m : ℕ) : sepTotal (m+2) = sepTotal (m+1) + admTotal (m+1) := by
  have hL : sepTotal (m+2) = ∑ j ∈ range (m+2), (sepCount (m+2) (j+1) : ℤ) + sepCount (m+2) 0 := by
    rw [sepTotal, sum_range_succ']
  have hA : sepTotal (m+1) = ∑ j ∈ range (m+2), (sepCount (m+1) (j+1) : ℤ) + sepCount (m+1) 0 := by
    rw [← sum_sepCount_eq_sepTotal (m+1) (m+3) (by omega), sum_range_succ']
  have hB : admTotal (m+1) = ∑ j ∈ range (m+2), (admCount (m+1) j : ℤ) := rfl
  have hrec : ∑ j ∈ range (m+2), (sepCount (m+2) (j+1) : ℤ) =
      ∑ j ∈ range (m+2), (sepCount (m+1) (j+1) : ℤ) + ∑ j ∈ range (m+2), (admCount (m+1) j : ℤ) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    rw [sepCount_succ_add_one]
    push_cast
    ring
  rw [hL, hrec, sepCount_succ_zero, hA, hB, sepCount_succ_zero]
  push_cast
  ring

/-- Base value `admTotal 1 = 1`. -/
theorem admTotal_one : admTotal 1 = 1 := by
  simp [admTotal, sum_range_succ, admCount_succ_zero, admCount_succ_one_eq_one]

/-- Base value `sepTotal 1 = 1`. -/
theorem sepTotal_one : sepTotal 1 = 1 := by
  simp [sepTotal, sum_range_succ, sepCount_succ_zero, sepCount_succ_add_one, sepCount_zero_succ, admCount_zero_zero]

/-- Closed values: `admTotal (n+1) = A007052 n` and
`sepTotal (n+1) = A007052 (n+1) - 3 A007052 n + 1`. -/
theorem admTotal_sepTotal_eq (n : ℕ) : admTotal (n+1) = A007052 n ∧ sepTotal (n+1) = A007052 (n+1) - 3 * A007052 n + 1 := by
  induction n with
  | zero => simp [admTotal_one, sepTotal_one, A007052]
  | succ n ih =>
    obtain ⟨hT, hU⟩ := ih
    constructor
    · rw [admTotal_succ_succ, hT, hU]; ring
    · rw [sepTotal_succ_succ, hT, hU, A007052]; ring

/-! ## The conjecture -/

/-- No ordered set partition of `Fin m` has more than `m` blocks, so the range `k < n + 2`
in `a007052_wiseman` covers every possible number of blocks of `Fin (n+1)`. -/
theorem card_orderedSetPartitions_eq_zero_of_lt {m k : ℕ} (h : m < k) :
    (univ.filter fun B : Fin k → Finset (Fin m) =>
      IsOrderedSetPartition B ∧ NonAdjacentBlocksOrdered B).card = 0 := by
  rw [card_orderedSetPartitions_eq_admCount, admCount_eq_zero_of_lt h]

/-- Wiseman's count: ordered partitions of `Fin (n+1)` with every earlier
block entirely below each non-adjacent later block are counted by A007052.
Block counts at least `n+2` contribute zero. -/
theorem a007052_wiseman (n : ℕ) :
    ((∑ k ∈ range (n + 2), (univ.filter fun B : Fin k → Finset (Fin (n + 1)) =>
      IsOrderedSetPartition B ∧ NonAdjacentBlocksOrdered B).card : ℕ) : ℤ) = A007052 n := by
  simp only [card_orderedSetPartitions_eq_admCount]
  rw [← (admTotal_sepTotal_eq n).1, admTotal]
  push_cast
  rfl

end Candidates.A007052WisemanOrderedPartitions
