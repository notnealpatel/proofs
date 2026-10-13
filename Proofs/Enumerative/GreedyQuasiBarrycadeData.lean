import Enumerative.GreedyQuasiBarrycade
import Mathlib.Tactic

/-!
# The fifth row of the greedy infinite quasi-barrycade

Primary source: arXiv:2609.18476, greedy rule and Algorithm `alvarrho`.
The paper displays and asserts the first four rows. The reviewed certificate
`row5-proof.txt` supplies the finite checks and infinite-tail argument used here
for all five rows, including the fifth row's unique omission of 16.
No literature novelty or all-rows conjecture is claimed.

Entry indices are zero-based: index 16 is the paper's seventeenth entry.
-/

set_option autoImplicit false

namespace GreedyQuasiBarrycade

/-- The triangular number `T n`, defined as `1 + ⋯ + n`. -/
def triangular (n : ℕ) : ℕ := partialSum (fun m => m + 1) n

example : triangular 0 = 0 := rfl
example : triangular 17 = 153 := by decide

/-- Triangular numbers satisfy `T(n+1) = T(n) + n+1`. -/
theorem triangular_succ (n : ℕ) :
    triangular (n + 1) = triangular n + (n + 1) := by
  simp [triangular, partialSum, Finset.sum_range_succ]

/-- Triangular numbers are monotone in their natural-number index. -/
theorem triangular_monotone : Monotone triangular := by
  apply monotone_nat_of_le_succ
  intro n
  rw [triangular_succ]
  omega

/-- The sum definition of triangular numbers agrees with the usual
formula, expressed without division. -/
theorem two_mul_triangular (n : ℕ) :
    2 * triangular n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [triangular_succ]
    nlinarith [ih]

/-- The exceptional finite entry prefixes of rows with indices 0 through 4.
Rows 0 and 1 need no exceptions to their respective linear tails. -/
def rowPrefix (r : ℕ) : List ℕ :=
  match r with
  | 2 => [4, 3, 1]
  | 3 => [11, 1, 4, 2, 5, 6, 3, 7, 8, 9]
  | 4 => [17, 5, 2, 1, 6, 7, 3, 8, 9, 4, 10, 11, 13, 12, 14, 15]
  | _ => []

example : rowPrefix 0 = [] := rfl
example : rowPrefix 1 = [] := rfl
example : rowPrefix 2 = [4, 3, 1] := rfl
example : rowPrefix 3 = [11, 1, 4, 2, 5, 6, 3, 7, 8, 9] := rfl
example : rowPrefix 4 = [17, 5, 2, 1, 6, 7, 3, 8, 9, 4, 10, 11, 13, 12, 14, 15] := rfl
example : rowPrefix 5 = [] := rfl

/-- The explicit first five infinite rows; rows beyond index 4 are arbitrary
and have no role in the five-row greedy certificate. -/
def explicitTable (r n : ℕ) : ℕ :=
  if r = 0 then n + 1
  else if n < (rowPrefix r).length then (rowPrefix r).getD n 0
  else n + 2

example : explicitTable 0 0 = 1 := rfl
example : explicitTable 1 0 = 2 := rfl
example : explicitTable 2 0 = 4 := rfl
example : explicitTable 3 0 = 11 := rfl
example : explicitTable 4 0 = 17 := rfl
example : explicitTable 4 15 = 15 := rfl
example : explicitTable 4 16 = 18 := rfl
example : explicitTable 5 0 = 2 := rfl

/-- The missing value and corresponding triangular-sum shift in each row. -/
def rowShift (r : ℕ) : ℕ :=
  match r with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 10
  | 4 => 16
  | _ => 0

example : (rowShift 0, rowShift 1, rowShift 2, rowShift 3, rowShift 4) =
    (0, 1, 2, 10, 16) := rfl
example : rowShift 5 = 0 := rfl

/-- After an exceptional prefix, each nonzero-index explicit row has entry `n+2`. -/
theorem explicit_tail (r n : ℕ) (hr : r ≠ 0)
    (hn : (rowPrefix r).length ≤ n) : explicitTable r n = n + 2 := by
  simp [explicitTable, hr, Nat.not_lt.mpr hn]

/-- Extending a prefix by one entry adds that entry to its partial sum. -/
theorem sum_succ (row : Row) (n : ℕ) :
    partialSum row (n + 1) = partialSum row n + row n := by
  simp [partialSum, Finset.sum_range_succ]

private theorem shifted_sum_from_base (r d : ℕ) (hr : r ≠ 0)
    (hbase : partialSum (explicitTable r) (rowPrefix r).length + d =
      triangular ((rowPrefix r).length + 1)) :
    ∀ n, (rowPrefix r).length ≤ n →
      partialSum (explicitTable r) n + d = triangular (n + 1) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact hbase
  | succ n hn ih =>
    rw [sum_succ, explicit_tail r n hr hn, triangular_succ (n + 1)]
    omega

/-- Exact shifted triangular sum formula for rows 1 through 4 (zero-based)
after their exceptional prefixes. The shift is added, avoiding truncated subtraction. -/
theorem explicit_shifted_sum (r n : ℕ) (hr : r < 5) (hr0 : r ≠ 0)
    (hn : (rowPrefix r).length ≤ n) :
    partialSum (explicitTable r) n + rowShift r = triangular (n + 1) := by
  apply shifted_sum_from_base r (rowShift r) hr0 _ n hn
  interval_cases r <;> first | contradiction | decide

/-- The first row's sums are precisely triangular numbers, including the empty sum. -/
theorem explicit_first_sum (n : ℕ) :
    partialSum (explicitTable 0) n = triangular n := rfl

private theorem triangular_ne_of_gap (j y : ℕ)
    (hlo : triangular j < y) (hhi : y < triangular (j + 1)) :
    ∀ l, triangular l ≠ y := by
  intro l heq
  by_cases hl : l ≤ j
  · have hmono := triangular_monotone hl
    omega
  · have hmono := triangular_monotone (show j + 1 ≤ l by omega)
    omega

/-- A finite certificate excluding the infinite triangular tail of row `i`:
the shifted candidate is below its starting index or lies in a triangular gap. -/
def TailAvoid (i x : ℕ) : Prop :=
  x + rowShift i < triangular ((rowPrefix i).length + 1) ∨
  ∃ j ∈ Finset.range 20,
    triangular j < x + rowShift i ∧ x + rowShift i < triangular (j + 1)

instance (i x : ℕ) : Decidable (TailAvoid i x) := by
  unfold TailAvoid
  infer_instance

example : TailAvoid 3 17 := by decide
example : TailAvoid 0 17 := by decide

/-- A finite triangular-gap certificate excludes every positive-length sum
in the specified earlier row's infinite tail. -/
theorem tailAvoid_ne (i x k : ℕ) (hi : i < 5) (hk : 0 < k)
    (hcut : (rowPrefix i).length ≤ k) (havoid : TailAvoid i x) :
    partialSum (explicitTable i) k ≠ x := by
  intro heq
  let l := if i = 0 then k else k + 1
  have hsum : partialSum (explicitTable i) k + rowShift i = triangular l := by
    by_cases hi0 : i = 0
    · subst i
      simpa [l, rowShift] using explicit_first_sum k
    · simpa [l, hi0] using explicit_shifted_sum i k hi hi0 hcut
  have hl : (rowPrefix i).length + 1 ≤ l := by
    by_cases hi0 : i = 0
    · subst i
      simp only [l, rowPrefix, if_pos rfl, List.length_nil]
      omega
    · simp only [l, if_neg hi0]
      omega
  rcases havoid with hbelow | ⟨j, hj, hlo, hhi⟩
  · have hmono := triangular_monotone hl
    omega
  · exact triangular_ne_of_gap j (x + rowShift i) hlo hhi l (by omega)

private theorem used_succ_iff (row : Row) (n a : ℕ) :
    (∃ m, m < n + 1 ∧ row m = a) ↔
      (∃ m, m < n ∧ row m = a) ∨ row n = a := by
  constructor
  · rintro ⟨m, hm, heq⟩
    by_cases hmn : m < n
    · exact Or.inl ⟨m, hmn, heq⟩
    · have hmn' : m = n := by omega
      exact Or.inr (hmn' ▸ heq)
  · rintro (⟨m, hm, heq⟩ | heq)
    · exact ⟨m, by omega, heq⟩
    · exact ⟨n, by omega, heq⟩

private theorem used_base (r : ℕ) (hr : r < 5) (hr0 : r ≠ 0) :
    (Finset.range (rowPrefix r).length).image (explicitTable r) =
      (Finset.range ((rowPrefix r).length + 2)).filter
        (fun a => 0 < a ∧ a ≠ rowShift r) := by
  interval_cases r <;> first | contradiction | decide

/-- After its finite prefix, each explicit row with index 1 through 4 has
used exactly the positive values at most `n+1`, except its indicated omission. -/
theorem explicit_used (r n a : ℕ) (hr : r < 5) (hr0 : r ≠ 0)
    (hn : (rowPrefix r).length ≤ n) :
    (∃ m, m < n ∧ explicitTable r m = a) ↔
      0 < a ∧ a ≤ n + 1 ∧ a ≠ rowShift r := by
  have hbase : (∃ m, m < (rowPrefix r).length ∧ explicitTable r m = a) ↔
      0 < a ∧ a ≤ (rowPrefix r).length + 1 ∧ a ≠ rowShift r := by
    have hmem := congrArg (fun s : Finset ℕ => a ∈ s) (used_base r hr hr0)
    simpa [Finset.mem_image, Finset.mem_range, Finset.mem_filter,
      Nat.lt_succ_iff, and_assoc, and_left_comm, and_comm] using hmem
  have hd : rowShift r ≤ (rowPrefix r).length + 1 := by
    interval_cases r <;> first | contradiction | decide
  induction n, hn using Nat.le_induction with
  | base => exact hbase
  | succ n hn ih =>
    simp only [used_succ_iff, ih, explicit_tail r n hr0 hn]
    omega

end GreedyQuasiBarrycade
