import Enumerative.GreedyQuasiBarrycadeRowFive

set_option autoImplicit false

namespace GreedyQuasiBarrycade

/-- The 29 exceptional entries of the sixth row, in zero-based order. -/
def sixthPrefix : List ℕ :=
  [30,3,4,5,6,2,1,8,10,11,7,12,13,9,17,16,14,15,18,19,20,21,22,23,24,25,26,27,28]

example : sixthPrefix.length = 29 := rfl
example : sixthPrefix.sum = 436 := by decide

/-- An explicit six-row table extending the accepted first five rows. -/
def sixTable (r n : ℕ) : ℕ :=
  if r = 5 then if n < 29 then sixthPrefix.getD n 0 else n + 2
  else explicitTable r n

example : sixTable 5 0 = 30 := rfl
example : sixTable 5 28 = 28 := rfl
example : sixTable 5 29 = 31 := rfl
example : sixTable 4 0 = 17 := rfl

/-- Rows before the sixth are unchanged. -/
theorem sixTable_earlier (i : ℕ) (hi : i < 5) : sixTable i = explicitTable i := by
  funext n
  simp [sixTable, show i ≠ 5 by omega]

/-- The explicit sixth row is linear from index 29. -/
theorem explicit_sixth_tail (n : ℕ) (hn : 29 ≤ n) : sixTable 5 n = n + 2 := by
  simp [sixTable, Nat.not_lt.mpr hn]

/-- The tail sum is triangular with shift 29, expressed without subtraction. -/
theorem sixth_shifted_sum (n : ℕ) (hn : 29 ≤ n) :
    partialSum (sixTable 5) n + 29 = triangular (n + 1) := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    rw [sum_succ, explicit_sixth_tail n hn, triangular_succ (n + 1)]
    omega

private theorem sixth_used_base :
    (Finset.range 29).image (sixTable 5) =
      (Finset.range 31).filter (fun a => 0 < a ∧ a ≠ 29) := by decide

/-- After index 29 the used values are exactly the positive values through
`n+1`, with 29 omitted. -/
theorem sixth_used (n a : ℕ) (hn : 29 ≤ n) :
    (∃ m, m < n ∧ sixTable 5 m = a) ↔ 0 < a ∧ a ≤ n + 1 ∧ a ≠ 29 := by
  have hbase : (∃ m, m < 29 ∧ sixTable 5 m = a) ↔
      0 < a ∧ a ≤ 30 ∧ a ≠ 29 := by
    have hmem := congrArg (fun s : Finset ℕ => a ∈ s) sixth_used_base
    simpa [Finset.mem_image, Finset.mem_range, Finset.mem_filter,
      Nat.lt_succ_iff, and_assoc, and_left_comm, and_comm] using hmem
  induction n, hn using Nat.le_induction with
  | base => exact hbase
  | succ n hn ih =>
    have hstep : (∃ m, m < n + 1 ∧ sixTable 5 m = a) ↔
        (∃ m, m < n ∧ sixTable 5 m = a) ∨ sixTable 5 n = a := by
      constructor
      · rintro ⟨m, hm, heq⟩
        by_cases hmn : m < n
        · exact Or.inl ⟨m, hmn, heq⟩
        · have he : m = n := by omega
          exact Or.inr (he ▸ heq)
      · rintro (⟨m, hm, heq⟩ | heq)
        · exact ⟨m, by omega, heq⟩
        · exact ⟨n, by omega, heq⟩
    simp only [hstep, ih, explicit_sixth_tail n hn]
    omega

/-- A finite sixth-row certificate: complete-tail triangular gaps and explicit
positive-length witnesses for all smaller unused positive candidates. -/
def SixthCertificate (n : ℕ) : Prop :=
  let a := sixTable 5 n
  let x := partialSum (sixTable 5) n + a
  0 < a ∧
  (∀ m ∈ Finset.range n, sixTable 5 m ≠ a) ∧
  (∀ i ∈ Finset.range 5,
    (∀ k ∈ Finset.range (rowPrefix i).length, 0 < k →
      partialSum (explicitTable i) k ≠ x) ∧
    (x + rowShift i < triangular ((rowPrefix i).length + 1) ∨
    ∃ j ∈ Finset.range 32,
      triangular j < x + rowShift i ∧ x + rowShift i < triangular (j + 1))) ∧
  ∀ b ∈ Finset.range a, 0 < b →
    (∃ m ∈ Finset.range n, sixTable 5 m = b) ∨
    (∃ i ∈ Finset.range 5, ∃ k ∈ Finset.range 40,
      0 < k ∧ partialSum (explicitTable i) k = partialSum (sixTable 5) n + b)

instance (n : ℕ) : Decidable (SixthCertificate n) := by
  unfold SixthCertificate
  infer_instance

example : SixthCertificate 0 := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- Kernel-checked certificates for all 29 exceptional entries. The finite
bounds search for witnesses; they do not truncate the earlier infinite rows. -/
theorem sixth_certificates : ∀ n ∈ Finset.range 29, SixthCertificate n := by decide

/-- Every exceptional earlier-row sum is at most 137. -/
theorem sixth_earlier_sum_bound :
    ∀ i ∈ Finset.range 5, ∀ k ∈ Finset.range (rowPrefix i).length,
      partialSum (explicitTable i) k ≤ 137 := by decide

end GreedyQuasiBarrycade
