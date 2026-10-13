import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.Fintype.Card
import Enumerative.PartitionPerfectPower

set_option autoImplicit false

namespace A000041

/-- Partitions of `n` with every part at most `k`, retaining multiset multiplicities. -/
def B (n k : ℕ) := {q : Nat.Partition n // ∀ a ∈ q.parts, a ≤ k}

instance (n k : ℕ) : Fintype (B n k) := inferInstanceAs (Fintype {q : Nat.Partition n // ∀ a ∈ q.parts, a ≤ k})

/-- The number of canonical multiset partitions of `n` with parts at most `k`. -/
def P (n k : ℕ) : ℕ := Fintype.card (B n k)

example (n k : ℕ) : B n k = {q : Nat.Partition n // ∀ a ∈ q.parts, a ≤ k} := rfl
example (n k : ℕ) : P n k = Fintype.card (B n k) := rfl

/-- Erasing exactly one occurrence of `k` identifies bounded partitions containing `k`
with bounded partitions of `n - k`. The guards ensure genuine natural subtraction. -/
def boundedEraseEquiv {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    {q : B n k // k ∈ q.val.parts} ≃ B (n - k) k where
  toFun q := ⟨Nat.Partition.partitionWithPartEquiv hk hkn ⟨q.val.val, q.property⟩, by
    intro a ha
    rw [Nat.Partition.partitionWithPartEquiv_apply_parts] at ha
    exact q.val.property a (q.val.val.parts.erase_subset k ha)⟩
  invFun q := ⟨⟨((Nat.Partition.partitionWithPartEquiv hk hkn).symm q.val).val, by
    intro a ha
    rw [Nat.Partition.partitionWithPartEquiv_symm_apply_parts] at ha
    rcases Multiset.mem_cons.mp ha with heq | hmem
    · exact heq ▸ le_refl k
    · exact q.property a hmem⟩,
    ((Nat.Partition.partitionWithPartEquiv hk hkn).symm q.val).property⟩
  left_inv q := by
    have h := (Nat.Partition.partitionWithPartEquiv hk hkn).symm_apply_apply
      ⟨q.val.val, q.property⟩
    have hval := congrArg (fun r : {p : Nat.Partition n // k ∈ p.parts} => r.val) h
    exact Subtype.ext (Subtype.ext hval)
  right_inv q := by
    apply Subtype.ext
    exact (Nat.Partition.partitionWithPartEquiv hk hkn).apply_symm_apply q.val

/-- The restricted forward map removes one occurrence, not the entire support of `k`. -/
theorem boundedEraseEquiv_parts {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (q : {q : B n k // k ∈ q.val.parts}) :
    (boundedEraseEquiv hk hkn q).val.parts = q.val.val.parts.erase k :=
  Nat.Partition.partitionWithPartEquiv_apply_parts hk hkn ⟨q.val.val, q.property⟩

/-- The restricted inverse adds one occurrence of `k`. -/
theorem boundedEraseEquiv_symm_parts {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (q : B (n - k) k) :
    ((boundedEraseEquiv hk hkn).symm q).val.val.parts = k ::ₘ q.val.parts :=
  Nat.Partition.partitionWithPartEquiv_symm_apply_parts hk hkn q.val

/-- Bounded partitions lacking `k` are exactly those with parts at most `k - 1`.
The positivity guard keeps the lowered bound off truncated subtraction. -/
def boundedWithoutEquiv {n k : ℕ} (hk : 1 ≤ k) :
    {q : B n k // k ∉ q.val.parts} ≃ B n (k - 1) where
  toFun q := ⟨q.val.val, by
    intro a ha
    have hle : a ≤ k := q.val.property a ha
    have hne : a ≠ k := fun heq => q.property (heq ▸ ha)
    omega⟩
  invFun q := ⟨⟨q.val, by
    intro a ha
    exact (q.property a ha).trans (Nat.sub_le k 1)⟩, by
    intro hmem
    have hle : k ≤ k - 1 := q.property k hmem
    omega⟩
  left_inv q := rfl
  right_inv q := rfl

/-- Lowering the bound preserves the underlying multiset. -/
theorem boundedWithoutEquiv_parts {n k : ℕ} (hk : 1 ≤ k)
    (q : {q : B n k // k ∉ q.val.parts}) :
    (boundedWithoutEquiv hk q).val.parts = q.val.val.parts := rfl

/-- When `n ≤ k`, the part bound is automatic for every canonical partition of `n`. -/
def boundedForgetEquiv {n k : ℕ} (hnk : n ≤ k) : B n k ≃ Nat.Partition n where
  toFun q := q.val
  invFun q := ⟨q, fun _ ha => (Nat.Partition.le_of_mem_parts ha).trans hnk⟩
  left_inv _q := rfl
  right_inv _q := rfl

/-- Forgetting an automatic bound preserves the canonical partition itself. -/
theorem boundedForgetEquiv_apply {n k : ℕ} (hnk : n ≤ k) (q : B n k) :
    boundedForgetEquiv hnk q = q.val := rfl

/-- The only partition of zero is the empty multiset, whatever the upper bound. -/
theorem bounded_partition_zero (k : ℕ) : P 0 k = 1 := by
  unfold P
  rw [Fintype.card_congr (boundedForgetEquiv (Nat.zero_le k))]
  exact Fintype.card_unique

/-- A positive integer has no partition with all positive parts at most zero. -/
theorem bounded_partition_bound_zero {n : ℕ} (hn : 0 < n) : P n 0 = 0 := by
  have hempty : IsEmpty (B n 0) := ⟨by
    intro q
    have hparts : q.val.parts = 0 := Multiset.eq_zero_of_forall_notMem (by
      intro a ha
      have hpos : 0 < a := q.val.parts_pos ha
      have hle : a ≤ 0 := q.property a ha
      omega)
    have hsum : n = 0 := by simpa [hparts] using q.val.parts_sum.symm
    omega⟩
  exact Fintype.card_eq_zero_iff.mpr hempty

/-- At the diagonal bound `n`, the bounded count is the canonical partition number. -/
theorem partitionNumber_eq_bounded (n : ℕ) : partitionNumber n = P n n :=
  (Fintype.card_congr (boundedForgetEquiv (le_refl n))).symm

/-- Splitting on occurrence of `k` gives the bounded partition recurrence.
The deletion branch removes exactly one copy of `k`, preserving multiplicities. -/
theorem bounded_partition_recurrence {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    P n k = P n (k - 1) + P (n - k) k := by
  classical
  have hsplit := Fintype.card_congr
    (Equiv.sumCompl (fun q : B n k => k ∈ q.val.parts))
  rw [Fintype.card_sum] at hsplit
  have hwith := Fintype.card_congr (boundedEraseEquiv hk hkn)
  have hwithout := Fintype.card_congr (boundedWithoutEquiv (n := n) hk)
  calc
    P n k = Fintype.card {q : B n k // k ∈ q.val.parts} +
        Fintype.card {q : B n k // k ∉ q.val.parts} := hsplit.symm
    _ = P (n - k) k + P n (k - 1) := congrArg₂ (· + ·) hwith hwithout
    _ = P n (k - 1) + P (n - k) k := Nat.add_comm _ _

/-- If `n < k`, no part can be `k`, so lowering the bound leaves the count unchanged. -/
theorem bounded_partition_skip {n k : ℕ} (hnk : n < k) : P n k = P n (k - 1) := by
  have hle : n ≤ k := Nat.le_of_lt hnk
  have hpred : n ≤ k - 1 := by omega
  calc
    P n k = Fintype.card (Nat.Partition n) :=
      Fintype.card_congr (boundedForgetEquiv hle)
    _ = P n (k - 1) := (Fintype.card_congr (boundedForgetEquiv hpred)).symm

/-- A concrete repeated-part model satisfies the deletion branch's guards and membership. -/
example : ∃ q : B 2 1, 1 ≤ (1 : ℕ) ∧ (1 : ℕ) ≤ 2 ∧ 1 ∈ q.val.parts := by
  let q : Nat.Partition 2 := Nat.Partition.ofSums 2 (1 ::ₘ 1 ::ₘ 0) (by decide)
  refine ⟨⟨q, ?_⟩, by decide, by decide, ?_⟩
  · simp [q, Nat.Partition.ofSums]
  · simp [q, Nat.Partition.ofSums]

/-- A concrete partition lacking `2` witnesses the complementary branch. -/
example : ∃ q : B 2 2, 1 ≤ (2 : ℕ) ∧ 2 ∉ q.val.parts := by
  let q : Nat.Partition 2 := Nat.Partition.ofSums 2 (1 ::ₘ 1 ::ₘ 0) (by decide)
  refine ⟨⟨q, ?_⟩, by decide, ?_⟩
  · simp [q, Nat.Partition.ofSums]
  · simp [q, Nat.Partition.ofSums]

/-- The lower boundary of the deletion branch has a nonempty source and empty target parts. -/
example : ∃ q : B 1 1, 1 ∈ q.val.parts ∧
    (boundedEraseEquiv (by decide) (by decide) ⟨q, by simp [Nat.Partition.partition_one_parts]⟩).val.parts = 0 := by
  refine ⟨⟨Nat.Partition.indiscrete 1, ?_⟩, ?_, ?_⟩
  · simp
  · simp
  · exact Nat.Partition.partition_zero_parts _

/-- The skip branch and the positive zero-bound branch both have satisfiable guards. -/
example : (0 : ℕ) < 1 ∧ (0 : ℕ) < 2 ∧ P 0 1 = 1 ∧ P 2 0 = 0 :=
  ⟨by decide, by decide, bounded_partition_zero 1, bounded_partition_bound_zero (by decide)⟩

/-- A structurally recursive bounded partition counter. Zero fuel is only a fallback;
`boundedCountCore_eq_P` certifies the result whenever `n + k ≤ fuel`. -/
def boundedCountCore : ℕ → ℕ → ℕ → ℕ
  | 0, n, _ => if n = 0 then 1 else 0
  | fuel + 1, n, k =>
      if n = 0 then 1
      else if k = 0 then 0
      else if k ≤ n then
        boundedCountCore fuel n (k - 1) + boundedCountCore fuel (n - k) k
      else boundedCountCore fuel n (k - 1)

example : boundedCountCore 0 0 0 = 1 := rfl
example : boundedCountCore 0 1 1 = 0 := rfl
example : boundedCountCore 4 2 2 = 2 := by decide
example : boundedCountCore 5 2 3 = 2 := by decide
example : boundedCountCore 3 3 0 = 0 := by decide

/-- Sufficient fuel makes the structural recurrence count canonical bounded partitions. -/
theorem boundedCountCore_eq_P (fuel n k : ℕ) (hfuel : n + k ≤ fuel) :
    boundedCountCore fuel n k = P n k := by
  induction fuel generalizing n k with
  | zero =>
    have hn : n = 0 := by omega
    subst n
    rw [boundedCountCore, if_pos rfl]
    exact (bounded_partition_zero k).symm
  | succ fuel ih =>
    by_cases hn : n = 0
    · subst n
      rw [boundedCountCore, if_pos rfl]
      exact (bounded_partition_zero k).symm
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      by_cases hk : k = 0
      · subst k
        rw [boundedCountCore, if_neg hn, if_pos rfl]
        exact (bounded_partition_bound_zero hnpos).symm
      · have hkpos : 1 ≤ k := by omega
        have hlow : n + (k - 1) ≤ fuel := by omega
        by_cases hkn : k ≤ n
        · have hdel : (n - k) + k ≤ fuel := by omega
          rw [boundedCountCore, if_neg hn, if_neg hk, if_pos hkn,
            ih n (k - 1) hlow, ih (n - k) k hdel]
          exact (bounded_partition_recurrence hkpos hkn).symm
        · have hnk : n < k := Nat.lt_of_not_ge hkn
          rw [boundedCountCore, if_neg hn, if_neg hk, if_neg hkn,
            ih n (k - 1) hlow]
          exact (bounded_partition_skip hnk).symm

/-- A computable canonical partition count, using enough fuel at the diagonal bound. -/
def computablePartitionNumber (n : ℕ) : ℕ := boundedCountCore (n + n) n n

example : computablePartitionNumber 0 = 1 := rfl
example : computablePartitionNumber 1 = 1 := by decide
example : computablePartitionNumber 2 = 2 := by decide

/-- The fuelled diagonal counter equals the canonical `Fintype.card` partition number. -/
theorem computablePartitionNumber_eq_partitionNumber (n : ℕ) :
    computablePartitionNumber n = partitionNumber n := by
  calc
    computablePartitionNumber n = P n n := boundedCountCore_eq_P (n + n) n n (le_refl _)
    _ = partitionNumber n := (partitionNumber_eq_bounded n).symm

/-- Sufficient fuel has a concrete jointly satisfiable instance with two partitions. -/
example : (2 : ℕ) + 2 ≤ 4 ∧ boundedCountCore 4 2 2 = P 2 2 :=
  ⟨by decide, boundedCountCore_eq_P 4 2 2 (by decide)⟩

/-- Kernel-checked values of the fuelled partition counter from zero through sixteen. -/
theorem computablePartitionNumber_range_seventeen :
    (List.range 17).map computablePartitionNumber =
      [1, 1, 2, 3, 5, 7, 11, 15, 22, 30, 42, 56, 77, 101, 135, 176, 231] := by
  decide +kernel

/-- Canonical partition numbers from zero through sixteen, transported from the
proved computable counter rather than enumerating canonical partition subtypes. -/
theorem partitionNumber_range_seventeen :
    (List.range 17).map partitionNumber =
      [1, 1, 2, 3, 5, 7, 11, 15, 22, 30, 42, 56, 77, 101, 135, 176, 231] := by
  have hmap : (List.range 17).map partitionNumber =
      (List.range 17).map computablePartitionNumber :=
    List.map_congr_left (fun n _ => (computablePartitionNumber_eq_partitionNumber n).symm)
  exact hmap.trans computablePartitionNumber_range_seventeen

end A000041
