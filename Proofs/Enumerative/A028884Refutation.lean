/-
# A028884 — Purath: `(n+3)^2 - 8 = A079896(A265284(n-1))` (refuted as stated)

## OEIS source (retrieved with `oeis show A028884` and checked against
## `https://oeis.org/A028884/internal`, 2026-10-21)

```
A028884   NAME:   a(n) = (n + 3)^2 - 8.
          OFFSET: 0,2
          DATA:   1,8,17,28,41,56,73,92,113,136,161,188,217,248,281,316,353,392,...
COMMENT (block "From _Klaus Purath_, Jan 04 2023: (Start)" ... "(End)"):
  For n > 0, this is a proper subsequence of A079896.
  Conjecture: a(n) = A079896(A265284(n-1)). -
```

Referenced entries (same retrieval date):

```
A079896   NAME:   Discriminants of indefinite binary quadratic forms.
          OFFSET: 1,1
          DATA:   5,8,12,13,17,20,21,24,28,29,32,33,37,40,41,44,45,48,52,53,...
          COMMENT: Numbers n such that n == 0 (mod 4) or n == 1 (mod 4), but n
                   is not a square.
          COMMENT: [I changed the offset to 1, since this is an important list.
                   ... - _N. J. A. Sloane_, Mar 14 2023]
A265284   NAME:   Total number of ON (black) cells after n iterations of the
                  "Rule 94" elementary cellular automaton starting with a single
                  ON (black) cell.
          OFFSET: 0,2
          DATA:   1,4,8,14,20,28,36,46,56,68,80,94,108,124,140,158,176,196,...
```

No later comment in A028884 retracts or amends the conjecture.

## Status

**Refuted as currently stated.**  With the current offsets
(A028884 offset 0, A079896 offset 1, A265284 offset 0), at `n = 1`:
`a(1) = 8`, `A265284(0) = 1`, `A079896(1) = 5`, and `8 ≠ 5`.
A Python check (`/tmp/claude/a028884.py`, 2026-10-21) found that the
stated identity fails for every `1 ≤ n ≤ 299`.

The conjecture is dated Jan 04 2023, before Sloane changed the offset of
A079896 from 0 to 1 on Mar 14 2023.  Under the old offset the conjecture
reads `a(n) = A079896(A265284(n-1) + 1)` in current indexing.  The same
Python check confirmed that form for every `1 ≤ n ≤ 299`.  This module
kernel-checks the shifted form only for `1 ≤ n ≤ 8`
(`shifted_conjecture_of_le_eight`).  A general proof would need a closed
form for the Rule 94 counts.  Barker's closed form in A265284 is only
conjectural.

This module **refutes** the conjecture as stated (`conjecture_false`).
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A028884Refutation

/-! ## Definition layer -/

/-- A028884: `a(n) = (n + 3)^2 - 8` (offset 0).  The natural-number
subtraction is never truncated, because `9 ≤ (n + 3)^2`; see
`cast_a028884`. -/
def a028884 (n : ℕ) : ℕ := (n + 3) ^ 2 - 8

/-- The natural-number definition agrees with the integer formula
`(n + 3)^2 - 8`, so the truncated subtraction never hits its junk value. -/
theorem cast_a028884 (n : ℕ) : (a028884 n : ℤ) = ((n : ℤ) + 3) ^ 2 - 8 := by
  have h8 : 8 ≤ (n + 3) ^ 2 :=
    calc 8 ≤ 3 ^ 2 := by norm_num
      _ ≤ (n + 3) ^ 2 := Nat.pow_le_pow_left (Nat.le_add_left 3 n) 2
  rw [a028884, Nat.cast_sub h8]
  push_cast
  ring

/-- Membership predicate of A079896: `d ≡ 0` or `1 (mod 4)` and `d` is not a
perfect square (the first comment of A079896).  Since `0` and `1` are squares,
every member is positive. -/
def IsIndefDisc (d : ℕ) : Prop := (d % 4 = 0 ∨ d % 4 = 1) ∧ ¬ IsSquare d

/-- A079896 with its current offset 1: `a079896 k` is the `k`-th member
(`k = 1, 2, …`) of `IsIndefDisc` in increasing order.  The value at `k = 0`
is a junk value; the conjecture below only evaluates it at
`A265284(n-1) ≥ 1` (`a265284_pos`). -/
noncomputable def a079896 (k : ℕ) : ℕ := Nat.nth IsIndefDisc (k - 1)

/-- The elementary cellular automaton Rule 94: the new state of a cell is bit
`4l + 2c + r` of `94 = 0b01011110`, where `l`, `c`, `r` are the old states of
its left neighbour, itself, and its right neighbour. -/
def rule94 (l c r : Bool) : Bool :=
  Nat.testBit 94 (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- Generation `n` of Rule 94 on `ℤ`, started from a single ON cell at `0`. -/
def rule94Gen : ℕ → ℤ → Bool
  | 0 => fun x => decide (x = 0)
  | n + 1 => fun x => rule94 (rule94Gen n (x - 1)) (rule94Gen n x) (rule94Gen n (x + 1))

/-- Number of ON cells in generation `n`.  Rule 94 maps `000` to `0`, so every
ON cell of generation `n` lies in `[-n, n]`.  The window is indexed by
`i ∈ [0, 2n]`, the cell being `i - n`. -/
def rule94OnCount (n : ℕ) : ℕ :=
  ((Finset.range (2 * n + 1)).filter
    (fun i : ℕ => rule94Gen n ((i : ℤ) - n) = true)).card

/-- A265284 (offset 0): total number of ON cells after `n` iterations of
Rule 94 from a single ON cell, i.e. the ON cells of generations `0, …, n`
added together. -/
def a265284 (n : ℕ) : ℕ := ∑ i ∈ Finset.range (n + 1), rule94OnCount i

/-- A265284 is positive, so `a079896 (a265284 m)` never reaches the junk
index `0`. -/
theorem a265284_pos (n : ℕ) : 0 < a265284 n := by
  have h0 : rule94OnCount 0 = 1 := by decide
  have hle : rule94OnCount 0 ≤ a265284 n :=
    Finset.single_le_sum (f := rule94OnCount) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.succ_pos n))
  omega

/-! ## Decidability of the A079896 predicate (proof infrastructure) -/

/-- A perfect square `d` has a square root at most `d`. -/
theorem isSquare_iff_exists_mem_range (d : ℕ) :
    IsSquare d ↔ ∃ m ∈ Finset.range (d + 1), m * m = d := by
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r, Finset.mem_range.mpr ?_, hr.symm⟩
    rcases Nat.eq_zero_or_pos r with h0 | hpos
    · omega
    · have hrr : r ≤ r * r := Nat.le_mul_of_pos_left r hpos
      omega
  · rintro ⟨m, -, hm⟩
    exact ⟨m, hm.symm⟩

/-- `IsIndefDisc` with the square test replaced by a bounded search. -/
theorem isIndefDisc_iff (d : ℕ) :
    IsIndefDisc d ↔ (d % 4 = 0 ∨ d % 4 = 1) ∧ ¬ ∃ m ∈ Finset.range (d + 1), m * m = d := by
  rw [IsIndefDisc, isSquare_iff_exists_mem_range]

/-- Kernel-reducible decision procedure for `IsIndefDisc` (Mathlib's
`IsSquare` instance on `ℕ` goes through `Nat.sqrt`, which `decide` cannot
reduce). -/
instance instDecidableIsIndefDisc (d : ℕ) : Decidable (IsIndefDisc d) :=
  decidable_of_iff _ (isIndefDisc_iff d).symm

/-- Evaluation rule for A079896: if `d` is a member and exactly `k - 1`
members lie below `d`, then `d` is the `k`-th member. -/
theorem a079896_eq_of_count {k d : ℕ} (hd : IsIndefDisc d)
    (hc : Nat.count IsIndefDisc d = k - 1) : a079896 k = d := by
  rw [a079896, ← hc]
  exact Nat.nth_count hd

/-- The pairs `(k, A079896(k))` of the first 14 listed terms of A079896, in
the form needed by `a079896_eq_of_count`. -/
theorem a079896_data_certificate :
    ∀ p ∈ [(1, 5), (2, 8), (3, 12), (4, 13), (5, 17), (6, 20), (7, 21),
        (8, 24), (9, 28), (10, 29), (11, 32), (12, 33), (13, 37), (14, 40)],
      IsIndefDisc p.2 ∧
        ((Finset.range p.2).filter IsIndefDisc).card = p.1 - 1 := by
  decide

/-- A079896 agrees with the first 14 listed OEIS terms
`5, 8, 12, 13, 17, 20, 21, 24, 28, 29, 32, 33, 37, 40`. -/
theorem a079896_data :
    ∀ p ∈ [(1, 5), (2, 8), (3, 12), (4, 13), (5, 17), (6, 20), (7, 21),
        (8, 24), (9, 28), (10, 29), (11, 32), (12, 33), (13, 37), (14, 40)],
      a079896 p.1 = p.2 := by
  intro p hp
  obtain ⟨hd, hc⟩ := a079896_data_certificate p hp
  exact a079896_eq_of_count hd (by rw [Nat.count_eq_card_filter_range]; exact hc)

/-! ## Ground truth -/

-- A028884 against its DATA line.
example : (List.range 18).map a028884 =
    [1, 8, 17, 28, 41, 56, 73, 92, 113, 136, 161, 188, 217, 248, 281, 316, 353, 392] := by
  decide

-- A265284 against its DATA line (the unmemoised `rule94Gen` costs `3^n`
-- per cell, so the check stops at index 8).
example : (List.range 9).map a265284 = [1, 4, 8, 14, 20, 28, 36, 46, 56] := by
  decide +kernel

-- A079896: the first term is `5` (index 1) and the second is `8` (index 2).
example : a079896 1 = 5 ∧ a079896 2 = 8 :=
  ⟨a079896_data (1, 5) (by simp), a079896_data (2, 8) (by simp)⟩

/-! ## The conjecture and its refutation -/

/-- **Purath's conjecture (A028884, Klaus Purath, Jan 04 2023).**

Verbatim: "Conjecture: a(n) = A079896(A265284(n-1))."

The guard `1 ≤ n` comes from the source: A265284 has offset 0, so `n - 1`
must be a valid index, and the preceding comment reads "For n > 0, this is
a proper subsequence of A079896".  The current offsets are used: A079896 has
offset 1 (`a079896`), and A265284 and A028884 have offset 0. -/
def Conjecture : Prop :=
  ∀ n : ℕ, 1 ≤ n → a028884 n = a079896 (a265284 (n - 1))

/-- **The conjecture is false as stated.**  Counterexample `n = 1`:
`a(1) = 8`, `A265284(0) = 1`, and `A079896(1) = 5`.

The author probably meant A079896 with the offset 0 it had before
Mar 14 2023.  In current indexing that reads
`a(n) = A079896(A265284(n-1) + 1)`; see `shifted_conjecture_of_le_eight`. -/
theorem conjecture_false : ¬ Conjecture := by
  intro hconj
  have h1 : a028884 1 = a079896 (a265284 0) := hconj 1 le_rfl
  have hlhs : a028884 1 = 8 := by decide
  have hidx : a265284 0 = 1 := by decide
  have hrhs : a079896 1 = 5 := a079896_data (1, 5) (by simp)
  rw [hlhs, hidx, hrhs] at h1
  omega

/-- The offset-corrected form `a(n) = A079896(A265284(n-1) + 1)` holds for
`1 ≤ n ≤ 8` (finite kernel check).  This is not a proof of the general
corrected form.  That proof would need a closed form for the Rule 94
counts A265284. -/
theorem shifted_conjecture_of_le_eight (n : ℕ) (hn1 : 1 ≤ n) (hn8 : n ≤ 8) :
    a028884 n = a079896 (a265284 (n - 1) + 1) := by
  have hcert : ∀ m ∈ Finset.range 8,
      IsIndefDisc (a028884 (m + 1)) ∧
        ((Finset.range (a028884 (m + 1))).filter IsIndefDisc).card = a265284 m := by
    decide +kernel
  obtain ⟨hd, hc⟩ := hcert (n - 1) (Finset.mem_range.mpr (by omega))
  have hn : n - 1 + 1 = n := Nat.sub_add_cancel hn1
  rw [hn] at hd hc
  refine (a079896_eq_of_count hd ?_).symm
  rw [Nat.count_eq_card_filter_range, hc]
  omega

end Candidates.A028884Refutation
