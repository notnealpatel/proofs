/-
# Conjugation of integer partitions

G. E. Andrews, *The Theory of Partitions* (1976; Cambridge, 1998), Chapter 1,
Theorem 1.4; R. P. Stanley, *Enumerative Combinatorics*, Vol. 1, §1.8.
Conjugation of `Nat.Partition n` is an involution exchanging the number of
parts and the largest part. It equates counts with at most k parts and
counts with all parts at most k, as well as their exact versions.
Column lengths are `partsGT s j = #{parts > j}` for `j < max part`.
The empty partition has largest part 0, so the statements include `n=k=0`.
-/
import Mathlib

set_option autoImplicit false

namespace PartitionConjugation

/-! ## Conjugation on multisets of parts -/

/-- `partsGT s j` is the number of parts of `s` (counted with multiplicity) exceeding `j`; for
a partition this is the length of column `j` of its Ferrers diagram. -/
def partsGT (s : Multiset ℕ) (j : ℕ) : ℕ := (s.filter (j < ·)).card

/-- The conjugate parts of `s`: the column lengths `partsGT s j` for `0 ≤ j < max s` of the
Ferrers diagram of `s`. -/
def conjParts (s : Multiset ℕ) : Multiset ℕ := (Multiset.range s.sup).map (partsGT s)

/-- The conjugate of `3 + 1` is `2 + 1 + 1`. -/
example : conjParts {3, 1} = {2, 1, 1} := by decide

/-- The conjugate of `4 + 2 + 1` is `3 + 2 + 1 + 1`. -/
example : conjParts {4, 2, 1} = {3, 2, 1, 1} := by decide

/-- The conjugate of `5` is `1 + 1 + 1 + 1 + 1`. -/
example : conjParts {5} = {1, 1, 1, 1, 1} := by decide

/-- The conjugate of the empty partition is empty. -/
example : conjParts 0 = 0 := by decide

/-- `partsGT {3, 1, 1} 0 = 3` and `partsGT {3, 1, 1} 1 = 1`. -/
example : partsGT {3, 1, 1} 0 = 3 ∧ partsGT {3, 1, 1} 1 = 1 := by decide

/-- Counting a parts-exceed predicate as a sum of indicators. -/
lemma card_filter_lt_eq_sum (s : Multiset ℕ) (j : ℕ) :
    (s.filter (j < ·)).card = (s.map fun a => if j < a then 1 else 0).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons b s ih =>
    by_cases h : j < b
    · simp [Multiset.filter_cons_of_pos _ h, h, ih, add_comm]
    · simp [Multiset.filter_cons_of_neg _ h, h, ih]

/-- `#{j < M : j < a} = min M a`. -/
lemma sum_range_ite_lt (M a : ℕ) :
    ((Multiset.range M).map fun j => if j < a then 1 else 0).sum = min M a := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Multiset.range_succ, Multiset.map_cons, Multiset.sum_cons, ih]
    split_ifs with h <;> omega

/-- Conjugation preserves the total: counting the cells of the Ferrers diagram by columns
equals counting them by rows. -/
lemma sum_conjParts (s : Multiset ℕ) : (conjParts s).sum = s.sum := by
  have hcols : (conjParts s).sum =
      ((Multiset.range s.sup).map fun j => (s.map fun a => if j < a then 1 else 0).sum).sum := by
    unfold conjParts partsGT
    simp_rw [card_filter_lt_eq_sum]
  rw [hcols, Multiset.sum_map_sum_map]
  simp_rw [sum_range_ite_lt]
  conv_rhs => rw [← Multiset.map_id s]
  congr 1
  exact Multiset.map_congr rfl fun a ha => min_eq_right (Multiset.le_sup ha)

/-- Every conjugate part is positive. -/
lemma pos_of_mem_conjParts {s : Multiset ℕ} {a : ℕ} (ha : a ∈ conjParts s) : 0 < a := by
  obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.1 ha
  rw [Multiset.mem_range] at hj
  unfold partsGT
  rw [Multiset.card_pos_iff_exists_mem]
  by_contra h
  push Not at h
  have hle : s.sup ≤ j := Multiset.sup_le.2 fun b hb => by
    by_contra hb'
    exact h b (Multiset.mem_filter.2 ⟨hb, by omega⟩)
  omega

/-- No part exceeds any `j` at or above the largest part. -/
lemma partsGT_eq_zero {s : Multiset ℕ} {j : ℕ} (hj : s.sup ≤ j) : partsGT s j = 0 := by
  unfold partsGT
  rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
  intro a ha
  have hle : a ≤ s.sup := Multiset.le_sup ha
  omega

/-- If some part exceeds `j`, then `j` is below the largest part. -/
lemma lt_sup_of_partsGT_pos {s : Multiset ℕ} {j : ℕ} (hj : 0 < partsGT s j) : j < s.sup := by
  by_contra h
  rw [partsGT_eq_zero (not_lt.1 h)] at hj
  exact lt_irrefl 0 hj

/-- Column lengths of a Ferrers diagram are weakly decreasing. -/
lemma partsGT_antitone (s : Multiset ℕ) : Antitone (partsGT s) := by
  intro i j hij
  unfold partsGT
  exact Multiset.card_le_card (Multiset.monotone_filter_right s fun a h => by omega)

/-- Column `i` of the conjugate counts the columns `j` of `s` of length exceeding `i`. -/
lemma partsGT_conjParts (s : Multiset ℕ) (i : ℕ) :
    partsGT (conjParts s) i = ((Finset.range s.sup).filter fun j => i < partsGT s j).card := by
  unfold conjParts
  rw [partsGT, Multiset.filter_map, Multiset.card_map]
  rfl

/-- Galois-type duality: cell `(l, i)` lies in the diagram of `s` exactly when cell `(i, l)`
lies in the diagram of its conjugate. -/
lemma lt_partsGT_iff (s : Multiset ℕ) (i l : ℕ) :
    i < partsGT s l ↔ l < partsGT (conjParts s) i := by
  rw [partsGT_conjParts]
  constructor
  · intro h
    have hsub : Finset.range (l + 1) ⊆ (Finset.range s.sup).filter fun j => i < partsGT s j := by
      intro j hj
      rw [Finset.mem_range] at hj
      have hjl : partsGT s l ≤ partsGT s j := partsGT_antitone s (by omega)
      have hpos : 0 < partsGT s j := by omega
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (lt_sup_of_partsGT_pos hpos), by omega⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_range] at hcard
    omega
  · intro h
    by_contra hle
    have hsub : ((Finset.range s.sup).filter fun j => i < partsGT s j) ⊆ Finset.range l := by
      intro j hj
      rw [Finset.mem_filter] at hj
      rw [Finset.mem_range]
      by_contra hjl
      have hanti := partsGT_antitone s (not_lt.1 hjl)
      omega
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_range] at hcard
    omega

/-- Every column length of `s` is at most the largest conjugate part. -/
lemma partsGT_le_sup_conjParts (s : Multiset ℕ) (i : ℕ) :
    partsGT s i ≤ (conjParts s).sup := by
  rcases Nat.eq_zero_or_pos (partsGT s i) with h | h
  · rw [h]; exact Nat.zero_le _
  · have hM : 0 < s.sup := lt_of_le_of_lt (Nat.zero_le i) (lt_sup_of_partsGT_pos h)
    have hmem : partsGT s 0 ∈ conjParts s :=
      Multiset.mem_map.2 ⟨0, Multiset.mem_range.2 hM, rfl⟩
    exact (partsGT_antitone s (Nat.zero_le i)).trans (Multiset.le_sup hmem)

/-- The double conjugate has the same column lengths as `s`. -/
lemma partsGT_conjParts_conjParts (s : Multiset ℕ) :
    partsGT (conjParts (conjParts s)) = partsGT s := by
  funext i
  rw [partsGT_conjParts]
  have hfilt : ((Finset.range (conjParts s).sup).filter
      fun j => i < partsGT (conjParts s) j) = Finset.range (partsGT s i) := by
    ext j
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_range, ← lt_partsGT_iff]
    have hbound := partsGT_le_sup_conjParts s i
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨by omega, h⟩
  rw [hfilt, Finset.card_range]

/-- `#{parts > b} = #{parts = b + 1} + #{parts > b + 1}`. -/
lemma card_filter_lt_succ (s : Multiset ℕ) (b : ℕ) :
    (s.filter (b < ·)).card = s.count (b + 1) + (s.filter (b + 1 < ·)).card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    rcases lt_trichotomy x (b + 1) with h | h | h
    · have h1 : ¬ b < x := by omega
      have h2 : ¬ b + 1 < x := by omega
      have h3 : b + 1 ≠ x := by omega
      simp [Multiset.filter_cons_of_neg _ h1, Multiset.filter_cons_of_neg _ h2,
        Multiset.count_cons_of_ne h3, ih]
    · subst h
      rw [Multiset.filter_cons_of_pos _ (Nat.lt_succ_self b),
        Multiset.filter_cons_of_neg (p := fun y => b + 1 < y) _ (lt_irrefl (b + 1)),
        Multiset.card_cons, Multiset.count_cons_self, ih]
      omega
    · have h1 : b < x := by omega
      have h3 : b + 1 ≠ x := by omega
      rw [Multiset.filter_cons_of_pos _ h1,
        Multiset.filter_cons_of_pos (p := fun y => b + 1 < y) _ h, Multiset.card_cons,
        Multiset.card_cons, Multiset.count_cons_of_ne h3, ih]
      omega

/-- A multiset of positive integers is determined by its column-length function `partsGT`. -/
lemma eq_of_partsGT_eq {s t : Multiset ℕ} (hs : ∀ a ∈ s, 0 < a) (ht : ∀ a ∈ t, 0 < a)
    (h : partsGT s = partsGT t) : s = t := by
  ext a
  rcases a with _ | b
  · rw [Multiset.count_eq_zero.2 fun h0 => lt_irrefl 0 (hs 0 h0),
      Multiset.count_eq_zero.2 fun h0 => lt_irrefl 0 (ht 0 h0)]
  · have hs' := card_filter_lt_succ s b
    have ht' := card_filter_lt_succ t b
    have e1 := congrFun h b
    have e2 := congrFun h (b + 1)
    unfold partsGT at e1 e2
    omega
/-- Conjugating twice returns the original multiset of positive parts. -/
lemma conjParts_conjParts {s : Multiset ℕ} (hs : ∀ a ∈ s, 0 < a) :
    conjParts (conjParts s) = s :=
  eq_of_partsGT_eq (fun _ ha => pos_of_mem_conjParts ha) hs (partsGT_conjParts_conjParts s)

/-! ## Conjugation of `Nat.Partition` -/

/-- The conjugate partition (transpose of the Ferrers diagram) of a partition of `n`. -/
def conj {n : ℕ} (p : n.Partition) : n.Partition where
  parts := conjParts p.parts
  parts_pos ha := pos_of_mem_conjParts ha
  parts_sum := (sum_conjParts p.parts).trans p.parts_sum

/-- Conjugation of partitions is an involution. -/
theorem conj_conj {n : ℕ} (p : n.Partition) : conj (conj p) = p :=
  Nat.Partition.ext (conjParts_conjParts fun _ ha => p.parts_pos ha)

/-- The number of parts of the conjugate equals the largest part. -/
theorem card_parts_conj {n : ℕ} (p : n.Partition) :
    Multiset.card (conj p).parts = p.parts.sup := by
  simp [conj, conjParts]

/-- The largest part of the conjugate equals the number of parts. -/
theorem sup_parts_conj {n : ℕ} (p : n.Partition) :
    (conj p).parts.sup = Multiset.card p.parts := by
  rw [← card_parts_conj (conj p), conj_conj]

/-! ## The counting identities -/

/-- **Andrews, Theorem 1.4.** The number of partitions of `n` into at most `k` parts equals the
number of partitions of `n` all of whose parts are at most `k`. -/
theorem card_card_parts_le_eq_card_parts_le (n k : ℕ) :
    (Finset.univ.filter fun p : n.Partition => Multiset.card p.parts ≤ k).card =
      (Finset.univ.filter fun p : n.Partition => ∀ a ∈ p.parts, a ≤ k).card := by
  refine Finset.card_nbij' conj conj ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp ⊢
    rw [← Multiset.sup_le, sup_parts_conj]
    exact hp
  · intro p hp
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp ⊢
    rw [card_parts_conj]
    exact Multiset.sup_le.2 hp
  · intro p _
    exact conj_conj p
  · intro p _
    exact conj_conj p

/-- **Exact version.** The number of partitions of `n` with exactly `k` parts equals the number
of partitions of `n` whose largest part is `k` (largest part `p.parts.sup`, which is `0` for the
empty partition of `0`). -/
theorem card_card_parts_eq_eq_card_sup_parts_eq (n k : ℕ) :
    (Finset.univ.filter fun p : n.Partition => Multiset.card p.parts = k).card =
      (Finset.univ.filter fun p : n.Partition => p.parts.sup = k).card := by
  refine Finset.card_nbij' conj conj ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp ⊢
    rw [sup_parts_conj]
    exact hp
  · intro p hp
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp ⊢
    rw [card_parts_conj]
    exact hp
  · intro p _
    exact conj_conj p
  · intro p _
    exact conj_conj p

/-- `conj`: the partition `3 + 1` of `4` conjugates to `2 + 1 + 1`, so the
partition with `2` parts goes to a partition with largest part `2`. -/
example : (conj (⟨{3, 1}, by decide, by decide⟩ : (4 : ℕ).Partition)).parts = {2, 1, 1} := by
  decide

end PartitionConjugation
