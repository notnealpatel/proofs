/-
# A126364 — Forgues: `a(n) = 3 a(n-1) - A025565(n)` (refuted)

## OEIS source (retrieved with `oeis show A126364` and checked against
## `https://oeis.org/search?q=id:A126364&fmt=text`, 2026-10-21)

```
A126364   NAME:   Number of base 10 n-digit numbers with adjacent digits
                  differing by one or less.
          OFFSET: 1,1
          DATA:   10,28,80,230,664,1922,5574,16188,47064,136946,398746,1161634,
                  3385486,9869934,28781908,83948652,244894048,714493794,...
COMMENT:  [Empirical] a(base,n)=a(base-1,n)+3^(n-1) for base>=n;
          a(base,n)=a(base-1,n)+3^(n-1)-2 when base=n-1.
FORMULA:  G.f.: x*(10 - 32*x + 12*x^2 + 20*x^3 - 4*x^4)/(1 - 6*x + 10*x^2
          - x^3 - 6*x^4 + x^5). - _Alexander R. Povolotsky_, Aug 18 2011
FORMULA:  Conjecture: a(n) = 3*a(n-1) - A025565(n), n >= 2.
          - _Daniel Forgues_, Aug 23 2011
```

Referenced entries (same retrieval date):

```
A025565   NAME:   a(n) = T(n,n-1), where T is array defined in A025564.
          OFFSET: 1,2
          DATA:   1,2,4,10,26,70,192,534,1500,4246,12092,34606,99442,286730,...
          FORMULA: G.f.: x*sqrt((1+x)/(1-3*x)).
A025564   NAME:   Triangular array, read by rows: pairwise sums of trinomial
                  array A027907.
          OFFSET: 0,3
          DATA:   1,1,2,1,1,3,4,3,1,1,4,8,10,8,4,1,1,5,13,22,26,22,13,5,1,...
          FORMULA: T(n, k) = T(n-1, k-2) + T(n-1, k-1) + T(n-1, k), starting
                   with [1], [1, 2, 1], [1, 3, 4, 3, 1].
```

No later comment in A126364 retracts or amends the conjecture.

## Status

**Refuted.**  The identity holds for `2 ≤ n ≤ 11` and first fails at
`n = 12`: `3 * a(11) - A025565(12) = 3 * 398746 - 34606 = 1161632`, but
`a(12) = 1161634`.  A Python check (`/tmp/claude/a126364.py`, 2026-10-21)
recomputed `a(n)` by brute force for `n ≤ 5` and by the digit transfer
recursion for `n ≤ 15`; it matched the DATA line and found the failures
`n = 12, 13, 14`.  A second check (`/tmp/claude/a126364b.py`) shows that
in base `b` (`2 ≤ b ≤ 14`) the identity holds exactly for `2 ≤ n ≤ b + 1`
and `n ≤ 18`: it is a large-base phenomenon, broken once the digit walk
can feel both ends of the digit range (compare the entry's own
[Empirical] comment).  The failure is also forced in general, since the
g.f. of A126364 is rational and that of A025565 is not.

This module **refutes** the conjecture (`conjecture_false`) and
kernel-checks that `n = 12` is the least counterexample
(`conjecture_of_le_eleven`).
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A126364Refutation

/-! ## Definition layer -/

/-- Two decimal digits differ by at most one. -/
def DigitAdj (a b : Fin 10) : Prop := (a : ℕ) ≤ b + 1 ∧ (b : ℕ) ≤ a + 1

/-- `DigitAdj` is decidable (a conjunction of `ℕ` inequalities). -/
instance (a b : Fin 10) : Decidable (DigitAdj a b) := by
  unfold DigitAdj; infer_instance

/-- A string of `n` decimal digits (leading digit first) whose adjacent digits
differ by at most one. -/
def IsAdjBounded {n : ℕ} (s : Fin n → Fin 10) : Prop :=
  ∀ i j : Fin n, (i : ℕ) + 1 = j → DigitAdj (s i) (s j)

/-- `IsAdjBounded` is decidable (bounded quantifiers over `Fin n`). -/
instance {n : ℕ} (s : Fin n → Fin 10) : Decidable (IsAdjBounded s) := by
  unfold IsAdjBounded; infer_instance

/-- A126364 (offset 1): the number of base-10 strings of `n` digits whose
adjacent digits differ by at most one.

**Fidelity note.**  The DATA line counts digit strings *with* leading zeros
(equivalently, the numbers `0 ≤ m < 10^n` written with exactly `n` digits):
`a(1) = 10` includes `0`, and `a(2) = 28` includes `00, 01`.  Excluding a
leading zero would give `9, 26, 75, …`, which does not match.  The value
`a126364 0 = 1` (the empty string) is outside the offset and is never used. -/
def a126364 (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun s : Fin n → Fin 10 => IsAdjBounded s)).card

-- Brute-force ground truth straight from the definition.
example : a126364 1 = 10 := by decide
example : a126364 2 = 28 := by decide

/-! ## Transfer recursion (proof infrastructure) -/

/-- For a string of length `m + 1`, adjacency only has to be checked at the
`m` consecutive pairs `(i.castSucc, i.succ)`. -/
theorem isAdjBounded_succ_iff {m : ℕ} (s : Fin (m + 1) → Fin 10) :
    IsAdjBounded s ↔ ∀ i : Fin m, DigitAdj (s i.castSucc) (s i.succ) := by
  constructor
  · intro h i
    exact h _ _ (by simp)
  · intro h i j hij
    have hi : (i : ℕ) < m := by omega
    have hk := h ⟨i, hi⟩
    have hj : (⟨i, hi⟩ : Fin m).succ = j := Fin.ext (by simp only [Fin.val_succ]; omega)
    have hi' : (⟨i, hi⟩ : Fin m).castSucc = i := Fin.ext rfl
    rwa [hj, hi'] at hk

/-- The admissible strings of length `m + 1` with leading digit `d`. -/
def startSet (m : ℕ) (d : Fin 10) : Finset (Fin (m + 1) → Fin 10) :=
  Finset.univ.filter (fun s => IsAdjBounded s ∧ s 0 = d)

/-- Prepending a digit `d` keeps a string admissible iff `d` is adjacent to
the old leading digit. -/
theorem isAdjBounded_cons {m : ℕ} (d : Fin 10) (t : Fin (m + 1) → Fin 10) :
    IsAdjBounded (Fin.cons d t : Fin (m + 2) → Fin 10) ↔
      DigitAdj d (t 0) ∧ IsAdjBounded t := by
  rw [isAdjBounded_succ_iff, isAdjBounded_succ_iff, Fin.forall_fin_succ]
  simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.succ_zero_eq_one]
  rfl

/-- Transfer recursion: an admissible string of length `m + 2` with leading
digit `d` is `d` followed by an admissible string of length `m + 1` whose
leading digit is adjacent to `d`. -/
theorem card_startSet_succ (m : ℕ) (d : Fin 10) :
    (startSet (m + 1) d).card =
      ∑ e : Fin 10, if DigitAdj d e then (startSet m e).card else 0 := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun s => s 1) (t := Finset.univ)
    (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs with hde
  · refine Finset.card_nbij' Fin.tail
      (fun t : Fin (m + 1) → Fin 10 => (Fin.cons d t : Fin (m + 2) → Fin 10)) ?_ ?_ ?_ ?_
    · intro s hs
      simp only [startSet, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
        true_and] at hs ⊢
      obtain ⟨⟨hsv, hs0⟩, hs1⟩ := hs
      rw [← Fin.cons_self_tail s, isAdjBounded_cons] at hsv
      exact ⟨hsv.2, hs1⟩
    · intro t ht
      simp only [startSet, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
        true_and] at ht ⊢
      obtain ⟨htv, ht0⟩ := ht
      refine ⟨⟨(isAdjBounded_cons d t).mpr ⟨ht0 ▸ hde, htv⟩, Fin.cons_zero _ _⟩, ?_⟩
      exact ht0
    · intro s hs
      simp only [startSet, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
        true_and] at hs
      obtain ⟨⟨-, hs0⟩, -⟩ := hs
      rw [← hs0]
      exact Fin.cons_self_tail s
    · intro t _
      exact Fin.tail_cons _ _
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro s hs hs1
    simp only [startSet, Finset.mem_filter, Finset.mem_univ, true_and] at hs
    obtain ⟨hsv, hs0⟩ := hs
    rw [← Fin.cons_self_tail s, isAdjBounded_cons] at hsv
    apply hde
    have h := hsv.1
    rw [hs0] at h
    rw [← hs1]
    exact h


/-- One transfer step on count vectors indexed by the leading digit. -/
def stepList (v : List ℕ) : List ℕ :=
  (List.finRange 10).map fun d => ∑ e : Fin 10, if DigitAdj d e then v.getD e 0 else 0

/-- `startVec m` lists, for `d = 0, …, 9`, the number of admissible strings of
length `m + 1` with leading digit `d` (see `card_startSet_eq`). -/
def startVec : ℕ → List ℕ
  | 0 => List.replicate 10 1
  | m + 1 => stepList (startVec m)

/-- Entry `d` of `stepList v` is the sum of the entries of `v` at the digits
adjacent to `d`. -/
theorem getD_stepList (v : List ℕ) (d : Fin 10) :
    (stepList v).getD d 0 = ∑ e : Fin 10, if DigitAdj d e then v.getD e 0 else 0 := by
  simp [stepList]

/-- There is exactly one string of length one with a given digit. -/
theorem card_startSet_zero : ∀ d : Fin 10, (startSet 0 d).card = 1 := by decide

/-- The list computation `startVec` counts the admissible strings by leading
digit. -/
theorem card_startSet_eq (m : ℕ) (d : Fin 10) : (startSet m d).card = (startVec m).getD d 0 := by
  induction m generalizing d with
  | zero =>
    rw [card_startSet_zero]
    revert d
    decide
  | succ m ih =>
    rw [card_startSet_succ, startVec, getD_stepList]
    simp only [ih]

/-- Splitting the admissible strings of length `m + 1` by their leading digit. -/
theorem a126364_succ (m : ℕ) : a126364 (m + 1) = ∑ d : Fin 10, (startSet m d).card := by
  rw [a126364, Finset.card_eq_sum_card_fiberwise (f := fun s => s 0) (t := Finset.univ)
    (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [startSet, Finset.filter_filter]

/-- A126364 is computed by the transfer recursion: `a(m + 1)` is the sum of the
entries of `startVec m`. -/
theorem a126364_succ_eq (m : ℕ) : a126364 (m + 1) = ∑ d : Fin 10, (startVec m).getD d 0 := by
  rw [a126364_succ]
  simp only [card_startSet_eq]

/-- The total of the count vector `startVec m`, equal to `a126364 (m + 1)`. -/
def totalCount (m : ℕ) : ℕ := ∑ d : Fin 10, (startVec m).getD d 0

/-- `a126364 (m + 1) = totalCount m`. -/
theorem a126364_succ_eq_totalCount (m : ℕ) : a126364 (m + 1) = totalCount m :=
  a126364_succ_eq m

/-- A126364 agrees with the first 27 listed OEIS terms (all of the local DATA
line). -/
theorem a126364_data :
    (List.range 27).map (fun m => a126364 (m + 1)) =
      [10, 28, 80, 230, 664, 1922, 5574, 16188, 47064, 136946, 398746, 1161634,
        3385486, 9869934, 28781908, 83948652, 244894048, 714493794, 2084792450,
        6083620812, 17753709802, 51812911858, 151218254846, 441351052720,
        1288175317718, 3759883395300, 10974394864558] := by
  simp only [a126364_succ_eq_totalCount]
  decide

/-! ## A025564 and A025565 -/

/-- Row `n` of the triangle A025564 (offset 0, top row `[1]`), built by the
entry's recurrence `T(n, k) = T(n-1, k-2) + T(n-1, k-1) + T(n-1, k)` from the
starting rows `[1]` and `[1, 2, 1]`.  Row `n` has `2n + 1` entries. -/
def a025564Row : ℕ → List ℕ
  | 0 => [1]
  | 1 => [1, 2, 1]
  | n + 2 =>
    let p := a025564Row (n + 1)
    List.zipWith3 (fun x y z => x + y + z) (p ++ [0, 0]) (0 :: p ++ [0]) (0 :: 0 :: p)

/-- A025564: `T(n, k)`, entry `k` (from `0`) of row `n`; `0` outside the row. -/
def a025564 (n k : ℕ) : ℕ := (a025564Row n).getD k 0

/-- A025565 (offset 1): the middle entry of the A025564 triangle in row
`n - 1`.

**Index-convention note.**  The entry's NAME reads `T(n,n-1)`; with the
A025564 numbering (top row = row 0, first column = column 0) the listed
terms `1, 2, 4, 10, 26, 70, …` are the middle entries `T(n-1, n-1)` (the
NAME counts rows from `1`).  The DATA line fixes the convention; see
`a025565_data`.  `a025565 0` is outside the offset and is never used. -/
def a025565 (n : ℕ) : ℕ := a025564 (n - 1) (n - 1)

/-- A025564 agrees with the first 36 listed OEIS terms (rows 0 to 5). -/
theorem a025564_data :
    (List.range 6).flatMap a025564Row =
      [1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 4, 8, 10, 8, 4, 1, 1, 5, 13, 22, 26, 22,
        13, 5, 1, 1, 6, 19, 40, 61, 70, 61, 40, 19, 6, 1] := by
  decide

/-- A025565 agrees with the first 15 listed OEIS terms. -/
theorem a025565_data :
    (List.range 15).map (fun m => a025565 (m + 1)) =
      [1, 2, 4, 10, 26, 70, 192, 534, 1500, 4246, 12092, 34606, 99442, 286730,
        829168] := by
  decide

/-! ## The conjecture and its refutation -/

/-- **Forgues' conjecture (A126364, Daniel Forgues, Aug 23 2011).**

Verbatim: "Conjecture: a(n) = 3*a(n-1) - A025565(n), n >= 2."

The identity is stated in `ℤ`, so the subtraction is not truncated; the
guard `2 ≤ n` is from the source and keeps `n - 1` at an index `≥ 1` inside
the offset of A126364. -/
def Conjecture : Prop :=
  ∀ n : ℕ, 2 ≤ n → (a126364 n : ℤ) = 3 * (a126364 (n - 1) : ℤ) - (a025565 n : ℤ)

/-- **The conjecture is false.**  Counterexample `n = 12`:
`a(12) = 1161634`, but `3 * a(11) - A025565(12) = 3 * 398746 - 34606 =
1161632`.

The author probably extrapolated from the large-base regime: in base `b`
the identity holds exactly for `2 ≤ n ≤ b + 1` (numerically, `b ≤ 14`,
`n ≤ 18`), so in base 10 it holds for `n ≤ 11`
(`conjecture_of_le_eleven`) and breaks once a length-`n` digit walk can
reach both ends of the digit range `0..9`. -/
theorem conjecture_false : ¬ Conjecture := by
  intro hconj
  have h12 := hconj 12 (by norm_num)
  have ha12 : a126364 12 = 1161634 := by
    rw [a126364_succ_eq_totalCount]
    decide
  have ha11 : a126364 11 = 398746 := by
    rw [a126364_succ_eq_totalCount]
    decide
  have hb12 : a025565 12 = 34606 := by decide
  rw [show (12 : ℕ) - 1 = 11 from rfl, ha12, ha11, hb12] at h12
  norm_num at h12

/-- The conjectured identity holds for `2 ≤ n ≤ 11` (finite kernel check), so
`n = 12` is the least counterexample. -/
theorem conjecture_of_le_eleven (n : ℕ) (hn2 : 2 ≤ n) (hn11 : n ≤ 11) :
    (a126364 n : ℤ) = 3 * (a126364 (n - 1) : ℤ) - (a025565 n : ℤ) := by
  have hcert : ∀ m ∈ Finset.range 10,
      (totalCount (m + 1) : ℤ) = 3 * (totalCount m : ℤ) - (a025565 (m + 2) : ℤ) := by
    decide
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hm : m + 2 - 1 = m + 1 := rfl
  rw [hm, a126364_succ_eq_totalCount, a126364_succ_eq_totalCount]
  exact hcert m (Finset.mem_range.mpr (by omega))

end Candidates.A126364Refutation
