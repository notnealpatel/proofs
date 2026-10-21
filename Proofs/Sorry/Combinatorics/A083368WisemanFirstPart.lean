/-
# A083368 — Wiseman: the first part of row `j` of A385817 is A083368(j)

## OEIS source (retrieved with `oeis show A083368` and the live entry, 2026-10-21)

```
NAME:     a(n) is the position of the highest one in A003754(n).
OFFSET:   1
TERMS:    1,2,1,3,2,1,4,1,3,2,1,5,2,1,4,1,3,2,1,6,1,3,2,1,5,2,1,4,1,3,2,1,7,...
KEYWORDS: nonn,base,nice,easy
COMMENT:  Previous name was: A Fibbinary system represents a number as a sum
          of distinct Fibonacci numbers (instead of distinct powers of two).
          Using representations without adjacent zeros, a(n) = the highest
          bit-position which changes going from n-1 to n.
COMMENT:  A003754(n), when written in binary, is the representation of n.
EXAMPLE:  27 is represented 110111, 28 is 111010; the fourth position
          changes, so a(28)=4.
COMMENT (the conjecture):
  From _Gus Wiseman_, Jul 24 2025: (Start)
  Conjecture: To obtain this sequence, start with A245563 (maximal run
  lengths of binary indices), then remove empty and duplicate rows (giving
  A385817), then take the first term of each remaining row. ...
  (End)
```

A385817: "Irregular triangle read by rows listing the lengths of maximal runs
(sequences of consecutive elements increasing by 1) of binary indices,
duplicate rows removed."  Mathematica: `DeleteDuplicates[Table[Length/@Split[
Join@@Position[Reverse[IntegerDigits[n,2]],1],#2==#1+1&],{n,0,100}]]`.

## Definitions used here

* `runLengths n` is row `n` of A245563, literally the Mathematica program:
  `Nat.bitIndices n` (Mathlib's increasing list of binary indices) split by
  `List.splitBy (fun a b => b == a + 1)` (Mathematica `Split[_, #2==#1+1&]`),
  then `List.length` of each run.
* `IsFirstRow n`: the row of `n` is nonempty and differs from every earlier
  row; `a385817Row j := runLengths (Nat.nth IsFirstRow (j - 1))` is the
  `j`-th row (offset 1) after removing empty and duplicate rows.
* `NoAdjZero n`: the binary expansion `Nat.digits 2 n` has no two adjacent
  zeros; `a003754 j := Nat.nth NoAdjZero (j - 1)` (offset 1, `A003754(1) = 0`).
* `a083368 j := (a003754 j ^^^ a003754 (j + 1)).size`: the 1-based highest
  bit position that changes going from the Fibbinary representation of
  `j - 1` (namely `A003754(j)`) to that of `j` (namely `A003754(j + 1)`).
  This is the entry's previous name, and matches its EXAMPLE
  (`55 ^^^ 58 = 13`, size `4`, so `a(28) = 4`).  The current NAME
  ("position of the highest one in A003754(n)") does not literally fit the
  DATA (`A003754(3) = 2` but `a(3) = 1`), so the previous name is used.
  Python check (2026-10-21): this definition reproduces all 102 listed terms.

## Literature status (triage)

Open: no proof in the entry or the literature as far as the triage could
tell.  Triage evidence: holds for the first 28656 rows.  Re-validated here
(Python, 2026-10-21): holds for all 46367 rows whose first appearance is
below `2^22`, and every first appearance there equals `2 * A003754(j) + 1`.

## Result of this module

The conjecture is proved for every `j ≥ 1`, with no remaining `sorry`.  The
proof shows that the first appearances of rows are exactly the odd numbers
with no two adjacent binary zeros (`isFirstRow_iff`), so the `j`-th one is
`2 * A003754(j) + 1` (`nth_isFirstRow`); its first run is one more than the
number of trailing ones of `A003754(j)`, and the highest bit changing between
consecutive no-`00` numbers is at the same position
(`size_xor_of_consecutive`).
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A083368WisemanFirstPart

/-! ## Definition layer -/

/-- Row `n` of A245563: the lengths of the maximal runs of consecutive binary
indices of `n` (least significant first), mirroring the Mathematica program
`Length/@Split[binaryIndices, #2==#1+1&]`. -/
def runLengths (n : ℕ) : List ℕ :=
  ((Nat.bitIndices n).splitBy (fun a b => b == a + 1)).map List.length

/-- `n` is the first appearance of its row of A245563, and that row is
nonempty: these `n` index the rows kept in A385817. -/
def IsFirstRow (n : ℕ) : Prop := runLengths n ≠ [] ∧ ∀ m < n, runLengths m ≠ runLengths n

/-- Row `j` (offset 1) of A385817: the `j`-th distinct nonempty row of A245563
in order of first appearance. -/
noncomputable def a385817Row (j : ℕ) : List ℕ := runLengths (Nat.nth IsFirstRow (j - 1))

/-- The binary expansion of `n` contains no two adjacent zeros (A003754). -/
def NoAdjZero (n : ℕ) : Prop := ¬ [0, 0] <:+: Nat.digits 2 n

/-- Decidability of `NoAdjZero`, used for ground-truth checks and counting. -/
instance : DecidablePred NoAdjZero := fun n => by unfold NoAdjZero; infer_instance

/-- Decidability of `IsFirstRow`, used for ground-truth checks and counting. -/
instance : DecidablePred IsFirstRow := fun n => by unfold IsFirstRow; infer_instance

/-- A003754 (offset 1): the `j`-th number with no two adjacent zeros in binary,
`0, 1, 2, 3, 5, 6, 7, 10, 11, …`. -/
noncomputable def a003754 (j : ℕ) : ℕ := Nat.nth NoAdjZero (j - 1)

/-- A083368 (offset 1): the 1-based highest bit position that changes going
from the Fibbinary representation of `j - 1` (`A003754(j)`) to that of `j`
(`A003754(j + 1)`). -/
noncomputable def a083368 (j : ℕ) : ℕ := (a003754 j ^^^ a003754 (j + 1)).size

/-- Ground-truth helper: `nth p k = n` follows from `p n` and `count p n = k`. -/
theorem nth_eq_of_count {p : ℕ → Prop} [DecidablePred p] {n k : ℕ} (hp : p n)
    (hc : Nat.count p n = k) : Nat.nth p k = n :=
  hc ▸ Nat.nth_count hp

/-! ## Ground truth -/

example : Nat.bitIndices 13 = [0, 2, 3] := by decide
example : runLengths 0 = [] := by decide
example : runLengths 13 = [1, 2] := by decide
example : runLengths 27 = [2, 2] := by decide
example : NoAdjZero 0 ∧ NoAdjZero 5 ∧ ¬ NoAdjZero 4 ∧ ¬ NoAdjZero 9 := by decide

-- A003754: 0, 1, 2, 3, 5, 6, 7, 10, 11.
example : a003754 1 = 0 := nth_eq_of_count (by decide) (by decide)
example : a003754 5 = 5 := nth_eq_of_count (by decide) (by decide)
example : a003754 9 = 11 := nth_eq_of_count (by decide) (by decide)

-- A083368: 1, 2, 1, 3, 2, 1, 4, 1.
example : a083368 1 = 1 := by
  have h1 : a003754 1 = 0 := nth_eq_of_count (by decide) (by decide)
  have h2 : a003754 2 = 1 := nth_eq_of_count (by decide) (by decide)
  rw [a083368, h1, h2]
  decide
example : a083368 4 = 3 := by
  have h4 : a003754 4 = 3 := nth_eq_of_count (by decide) (by decide)
  have h5 : a003754 5 = 5 := nth_eq_of_count (by decide) (by decide)
  rw [a083368, h4, h5]
  decide
example : a083368 7 = 4 := by
  have h7 : a003754 7 = 7 := nth_eq_of_count (by decide) (by decide)
  have h8 : a003754 8 = 10 := nth_eq_of_count (by decide) (by decide)
  rw [a083368, h7, h8]
  decide
example : a083368 8 = 1 := by
  have h8 : a003754 8 = 10 := nth_eq_of_count (by decide) (by decide)
  have h9 : a003754 9 = 11 := nth_eq_of_count (by decide) (by decide)
  rw [a083368, h8, h9]
  decide

-- A385817 rows: [1], [2], [1, 1], [3], [2, 1], [1, 2], [4].
example : a385817Row 1 = [1] := by
  rw [a385817Row, nth_eq_of_count (n := 1) (by decide) (by decide)]
  decide
example : a385817Row 3 = [1, 1] := by
  rw [a385817Row, nth_eq_of_count (n := 5) (by decide) (by decide)]
  decide
example : a385817Row 5 = [2, 1] := by
  rw [a385817Row, nth_eq_of_count (n := 11) (by decide) (by decide)]
  decide
example : a385817Row 6 = [1, 2] := by
  rw [a385817Row, nth_eq_of_count (n := 13) (by decide) (by decide)]
  decide
example : a385817Row 7 = [4] := by
  rw [a385817Row, nth_eq_of_count (n := 15) (by decide) (by decide)]
  decide

/-! ## `List.splitBy` helpers -/

/-- Splitting commutes with mapping by `f` when `f` transports the relation. -/
theorem splitBy_map {α β : Type*} {f : α → β} {r : β → β → Bool} {r' : α → α → Bool}
    (hf : ∀ a b, r (f a) (f b) = r' a b) (l : List α) :
    (l.map f).splitBy r = (l.splitBy r').map (List.map f) := by
  rw [List.splitBy_eq_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← List.map_flatten, List.flatten_splitBy]
  · simp
  · intro m hm
    obtain ⟨m', hm', rfl⟩ := List.mem_map.1 hm
    rw [List.isChain_map]
    exact (List.isChain_of_mem_splitBy hm').imp (fun a b h => by rw [hf]; exact h)
  · rw [List.isChain_map]
    refine (List.isChain_getLast_head_splitBy r' l).imp ?_
    rintro a b ⟨ha, hb, h⟩
    refine ⟨by simpa using ha, by simpa using hb, ?_⟩
    rw [List.getLast_map, List.head_map, hf]
    exact h

/-- Consing an element unrelated to the head of `l` starts a new singleton run. -/
theorem splitBy_cons_of_false {α : Type*} {r : α → α → Bool} {a : α} {l : List α}
    (hr : ∀ x ∈ l.head?, r a x = false) :
    (a :: l).splitBy r = [a] :: l.splitBy r := by
  cases l with
  | nil => rfl
  | cons b m =>
    have h := List.splitBy_append_cons (l := [a]) (a := b) (r := r) m (by simpa using hr)
    exact h

/-- Consing an element related to the head of the first run extends that run. -/
theorem splitBy_cons_of_true {α : Type*} {r : α → α → Bool} {a : α} {l : List α}
    {g : List α} {gs : List (List α)} (h : l.splitBy r = g :: gs)
    (hg : g ≠ []) (hr : r a (g.head hg) = true) :
    (a :: l).splitBy r = (a :: g) :: gs := by
  obtain ⟨hflat, hnil, hchain, hc'⟩ := List.splitBy_eq_iff.1 h
  rw [List.splitBy_eq_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [hflat]
  · simp only [List.mem_cons, not_or] at hnil ⊢
    exact ⟨(List.cons_ne_nil a g).symm, hnil.2⟩
  · intro m hm
    rcases List.mem_cons.1 hm with rfl | hm
    · rw [List.isChain_cons]
      refine ⟨?_, hchain g List.mem_cons_self⟩
      intro y hy
      cases g with
      | nil => exact absurd rfl hg
      | cons c g' =>
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
        subst hy
        exact hr
    · exact hchain m (List.mem_cons_of_mem g hm)
  · cases gs with
    | nil => exact List.isChain_singleton _
    | cons g2 gs' =>
      rw [List.isChain_cons_cons] at hc' ⊢
      refine ⟨?_, hc'.2⟩
      obtain ⟨ha, hb, h2⟩ := hc'.1
      refine ⟨List.cons_ne_nil a g, hb, ?_⟩
      rw [List.getLast_cons hg]
      exact h2

/-! ## Run-length recursion -/

/-- The consecutive-run relation is invariant under the shift `(· + 1)`. -/
theorem succRel (a b : ℕ) :
    ((fun a b : ℕ => b == a + 1) (a + 1) (b + 1)) = (fun a b : ℕ => b == a + 1) a b := by
  simp

/-- Splitting into consecutive runs commutes with shifting every index by one. -/
theorem splitBy_map_succ (l : List ℕ) :
    (l.map (· + 1)).splitBy (fun a b => b == a + 1) =
      (l.splitBy (fun a b => b == a + 1)).map (List.map (· + 1)) :=
  splitBy_map (fun a b => by simp) l

/-- The row of `0` is empty. -/
theorem runLengths_zero : runLengths 0 = [] := by
  simp [runLengths]

/-- Doubling shifts all binary indices and leaves the run lengths unchanged. -/
theorem runLengths_two_mul (n : ℕ) : runLengths (2 * n) = runLengths n := by
  rw [runLengths, Nat.bitIndices_two_mul, splitBy_map succRel, List.map_map]
  simp only [runLengths, Function.comp_def, List.length_map]

/-- For even `n`, the new bit `0` of `2n+1` forms its own run of length one. -/
theorem runLengths_two_mul_add_one_of_even {n : ℕ} (hn : n % 2 = 0) :
    runLengths (2 * n + 1) = 1 :: runLengths n := by
  rw [runLengths, Nat.bitIndices_two_mul_add_one, splitBy_cons_of_false, splitBy_map succRel]
  · simp only [List.map_cons, List.length_singleton, List.map_map, runLengths,
      Function.comp_def, List.length_map]
  · intro x hx
    rw [List.head?_map, Option.mem_def, Option.map_eq_some_iff] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hy0 : y ≠ 0 := by
      rintro rfl
      have hmem : 0 ∈ n.bitIndices := List.mem_of_mem_head? hy
      rw [Nat.mem_bitIndices, Nat.testBit_zero] at hmem
      simp [hn] at hmem
    simpa using hy0

/-- For odd `n`, the new bit `0` of `2n+1` extends the first run of `n` by one. -/
theorem runLengths_two_mul_add_one_of_odd {n h : ℕ} {t : List ℕ} (hn : n % 2 = 1)
    (hrl : runLengths n = h :: t) :
    runLengths (2 * n + 1) = (h + 1) :: t := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
  have hne : (Nat.bitIndices (2 * m + 1)).splitBy (fun a b => b == a + 1) ≠ [] := by
    rw [Ne, List.splitBy_eq_nil, Nat.bitIndices_two_mul_add_one]
    exact List.cons_ne_nil _ _
  obtain ⟨g, gs, hs⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨hflat, hnil, -, -⟩ := List.splitBy_eq_iff.1 hs
  cases g with
  | nil => exact absurd List.mem_cons_self hnil
  | cons c g' =>
    have hc : c = 0 := by
      rw [Nat.bitIndices_two_mul_add_one] at hflat
      simp only [List.flatten_cons, List.cons_append, List.cons.injEq] at hflat
      exact hflat.1.symm
    subst hc
    rw [runLengths, hs] at hrl
    simp only [List.map_cons, List.length_cons, List.cons.injEq] at hrl
    obtain ⟨rfl, rfl⟩ := hrl
    have hmap := splitBy_map_succ (2 * m + 1).bitIndices
    rw [hs, List.map_cons] at hmap
    rw [runLengths, Nat.bitIndices_two_mul_add_one (2 * m + 1),
      splitBy_cons_of_true hmap (List.cons_ne_nil _ _) (by simp)]
    simp

/-- The row of `n` is empty exactly when `n = 0`. -/
theorem runLengths_eq_nil_iff {n : ℕ} : runLengths n = [] ↔ n = 0 := by
  constructor
  · intro h
    rw [runLengths, List.map_eq_nil_iff, List.splitBy_eq_nil] at h
    rw [← Nat.sum_map_two_pow_bitIndices n, h]
    rfl
  · rintro rfl
    exact runLengths_zero

/-! ## Trailing ones and the first run -/

/-- The number of trailing one bits of `n`. -/
def trailingOnes (n : ℕ) : ℕ :=
  if h : n % 2 = 1 then trailingOnes (n / 2) + 1 else 0
decreasing_by omega

/-- Appending a one bit adds a trailing one. -/
theorem trailingOnes_two_mul_add_one (m : ℕ) : trailingOnes (2 * m + 1) = trailingOnes m + 1 := by
  rw [trailingOnes, dif_pos (by omega)]
  congr 2
  omega

/-- An even number has no trailing ones. -/
theorem trailingOnes_of_even {m : ℕ} (hm : m % 2 = 0) : trailingOnes m = 0 := by
  rw [trailingOnes, dif_neg (by omega)]

/-- The first run of `2m+1` has length one more than the trailing ones of `m`. -/
theorem runLengths_two_mul_add_one_head (m : ℕ) :
    ∃ t, runLengths (2 * m + 1) = (trailingOnes m + 1) :: t := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.mod_two_eq_zero_or_one m with hm | hm
    · exact ⟨runLengths m, by rw [runLengths_two_mul_add_one_of_even hm, trailingOnes_of_even hm]⟩
    · obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k + 1 := ⟨m / 2, by omega⟩
      obtain ⟨t, ht⟩ := ih k (by omega)
      exact ⟨t, by rw [runLengths_two_mul_add_one_of_odd hm ht, trailingOnes_two_mul_add_one]⟩

/-! ## No two adjacent zeros -/

/-- `0` (binary expansion empty) has no two adjacent zeros. -/
theorem noAdjZero_zero : NoAdjZero 0 := by
  simp [NoAdjZero]

/-- Appending a one bit preserves and reflects the no-`00` property. -/
theorem noAdjZero_two_mul_add_one {n : ℕ} : NoAdjZero (2 * n + 1) ↔ NoAdjZero n := by
  rw [NoAdjZero, NoAdjZero, Nat.digits_def' (by norm_num) (by omega), List.infix_cons_iff]
  have h1 : (2 * n + 1) % 2 = 1 := by omega
  have h2 : (2 * n + 1) / 2 = n := by omega
  rw [h1, h2]
  simp

/-- For `n > 0`, appending a zero bit keeps no `00` iff `n` is odd and has no `00`. -/
theorem noAdjZero_two_mul {n : ℕ} (hn : 0 < n) :
    NoAdjZero (2 * n) ↔ n % 2 = 1 ∧ NoAdjZero n := by
  rw [NoAdjZero, NoAdjZero, Nat.digits_def' (by norm_num) (by omega), List.infix_cons_iff]
  have h1 : (2 * n) % 2 = 0 := by omega
  have h2 : (2 * n) / 2 = n := by omega
  rw [h1, h2, Nat.digits_def' (by norm_num) hn, List.infix_cons_iff (l₂ := Nat.digits 2 (n / 2))]
  rcases Nat.mod_two_eq_zero_or_one n with hm | hm <;> simp [hm]

/-- Dropping the last bit preserves the no-`00` property. -/
theorem noAdjZero_half {n : ℕ} (h : NoAdjZero n) : NoAdjZero (n / 2) := by
  rcases Nat.mod_two_eq_zero_or_one n with hm | hm
  · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
    rw [show 2 * k / 2 = k by omega]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact noAdjZero_zero
    · exact ((noAdjZero_two_mul hk).1 h).2
  · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
    rw [show (2 * k + 1) / 2 = k by omega]
    exact noAdjZero_two_mul_add_one.1 h

/-! ## First appearances are the odd no-`00` numbers -/

/-- Every positive `n` has an odd no-`00` number `m ≤ n` with the same run lengths
(runs separated by single zeros, starting at bit `0`). -/
theorem exists_canonical_le (n : ℕ) (hn : 0 < n) :
    ∃ m ≤ n, m % 2 = 1 ∧ NoAdjZero m ∧ runLengths m = runLengths n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.mod_two_eq_zero_or_one n with hpar | hpar
    · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
      obtain ⟨m, hmk, hm1, hm2, hm3⟩ := ih k (by omega) (by omega)
      exact ⟨m, by omega, hm1, hm2, by rw [hm3, runLengths_two_mul]⟩
    · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · exact ⟨1, le_rfl, rfl, noAdjZero_two_mul_add_one.2 noAdjZero_zero, rfl⟩
      rcases Nat.mod_two_eq_zero_or_one k with hk2 | hk2
      · obtain ⟨k', rfl⟩ : ∃ k', k = 2 * k' := ⟨k / 2, by omega⟩
        obtain ⟨m, hmk, hm1, hm2, hm3⟩ := ih k' (by omega) (by omega)
        refine ⟨2 * (2 * m) + 1, by omega, by omega, ?_, ?_⟩
        · exact noAdjZero_two_mul_add_one.2 ((noAdjZero_two_mul (by omega)).2 ⟨hm1, hm2⟩)
        · rw [runLengths_two_mul_add_one_of_even (by omega),
            runLengths_two_mul_add_one_of_even hk2, runLengths_two_mul, runLengths_two_mul, hm3]
      · obtain ⟨m, hmk, hm1, hm2, hm3⟩ := ih k (by omega) hk
        obtain ⟨t, ht⟩ := runLengths_two_mul_add_one_head (k / 2)
        rw [show 2 * (k / 2) + 1 = k by omega] at ht
        refine ⟨2 * m + 1, by omega, by omega, noAdjZero_two_mul_add_one.2 hm2, ?_⟩
        rw [runLengths_two_mul_add_one_of_odd hm1 (hm3.trans ht),
          runLengths_two_mul_add_one_of_odd hk2 ht]

/-- For odd `p`, the first run of `p` has length `trailingOnes (p / 2) + 1`. -/
theorem runLengths_odd_head {p : ℕ} (hp : p % 2 = 1) :
    ∃ t, runLengths p = (trailingOnes (p / 2) + 1) :: t := by
  have h := runLengths_two_mul_add_one_head (p / 2)
  rwa [show 2 * (p / 2) + 1 = p by omega] at h

/-- Odd no-`00` numbers are determined by their run lengths. -/
theorem canonical_injective (a : ℕ) : ∀ b : ℕ, a % 2 = 1 → NoAdjZero a → b % 2 = 1 →
    NoAdjZero b → runLengths a = runLengths b → a = b := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro b ha1 ha2 hb1 hb2 hab
    obtain ⟨p, rfl⟩ : ∃ p, a = 2 * p + 1 := ⟨a / 2, by omega⟩
    obtain ⟨q, rfl⟩ : ∃ q, b = 2 * q + 1 := ⟨b / 2, by omega⟩
    have hp := noAdjZero_two_mul_add_one.1 ha2
    have hq := noAdjZero_two_mul_add_one.1 hb2
    rcases Nat.mod_two_eq_zero_or_one p with hp2 | hp2 <;>
      rcases Nat.mod_two_eq_zero_or_one q with hq2 | hq2
    · rw [runLengths_two_mul_add_one_of_even hp2, runLengths_two_mul_add_one_of_even hq2,
        List.cons.injEq] at hab
      have hpq := hab.2
      rcases Nat.eq_zero_or_pos p with rfl | hp0
      · rw [runLengths_zero, eq_comm, runLengths_eq_nil_iff] at hpq
        omega
      have hq0 : 0 < q := by
        rcases Nat.eq_zero_or_pos q with rfl | hq0
        · rw [runLengths_zero, runLengths_eq_nil_iff] at hpq
          omega
        · exact hq0
      obtain ⟨p', rfl⟩ : ∃ p', p = 2 * p' := ⟨p / 2, by omega⟩
      obtain ⟨q', rfl⟩ : ∃ q', q = 2 * q' := ⟨q / 2, by omega⟩
      obtain ⟨hp'1, hp'2⟩ := (noAdjZero_two_mul (by omega)).1 hp
      obtain ⟨hq'1, hq'2⟩ := (noAdjZero_two_mul (by omega)).1 hq
      rw [runLengths_two_mul, runLengths_two_mul] at hpq
      have := ih p' (by omega) q' hp'1 hp'2 hq'1 hq'2 hpq
      omega
    · obtain ⟨t, ht⟩ := runLengths_odd_head hq2
      rw [runLengths_two_mul_add_one_of_even hp2, runLengths_two_mul_add_one_of_odd hq2 ht,
        List.cons.injEq] at hab
      omega
    · obtain ⟨t, ht⟩ := runLengths_odd_head hp2
      rw [runLengths_two_mul_add_one_of_even hq2, runLengths_two_mul_add_one_of_odd hp2 ht,
        List.cons.injEq] at hab
      omega
    · obtain ⟨tp, htp⟩ := runLengths_odd_head hp2
      obtain ⟨tq, htq⟩ := runLengths_odd_head hq2
      have hab' := hab
      rw [runLengths_two_mul_add_one_of_odd hp2 htp, runLengths_two_mul_add_one_of_odd hq2 htq,
        List.cons.injEq] at hab'
      have hpq : runLengths p = runLengths q := by
        rw [htp, htq, hab'.2, show trailingOnes (p / 2) = trailingOnes (q / 2) by omega]
      have := ih p (by omega) q hp2 hp hq2 hq hpq
      omega

/-- **First appearances.** `n` is the first appearance of a nonempty row of A245563
exactly when `n` is odd and has no two adjacent zeros in binary. -/
theorem isFirstRow_iff {n : ℕ} : IsFirstRow n ↔ n % 2 = 1 ∧ NoAdjZero n := by
  constructor
  · rintro ⟨hne, hfirst⟩
    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exact absurd runLengths_zero hne
      · exact hn
    obtain ⟨m, hmn, hm1, hm2, hm3⟩ := exists_canonical_le n hn
    rcases hmn.lt_or_eq with hlt | rfl
    · exact absurd hm3 (hfirst m hlt)
    · exact ⟨hm1, hm2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun h => by rw [runLengths_eq_nil_iff] at h; omega, fun m hm heq => ?_⟩
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · rw [runLengths_zero, eq_comm, runLengths_eq_nil_iff] at heq
        omega
      · exact hm0
    obtain ⟨m', hm'm, hm'1, hm'2, hm'3⟩ := exists_canonical_le m hm0
    have := canonical_injective m' n hm'1 hm'2 h1 h2 (hm'3.trans heq)
    omega

/-! ## Indexing first appearances -/

/-- There are infinitely many numbers with no two adjacent binary zeros. -/
theorem noAdjZero_infinite : (Set.ofPred NoAdjZero).Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  induction a with
  | zero => exact ⟨1, noAdjZero_two_mul_add_one.2 noAdjZero_zero, Nat.zero_lt_one⟩
  | succ a ih =>
    obtain ⟨b, hb, hab⟩ := ih
    exact ⟨2 * b + 1, noAdjZero_two_mul_add_one.2 hb, by omega⟩

/-- First appearances below `2x+1` correspond to no-`00` numbers below `x`. -/
theorem count_isFirstRow (x : ℕ) : Nat.count IsFirstRow (2 * x + 1) = Nat.count NoAdjZero x := by
  induction x with
  | zero =>
    rw [Nat.count_succ, Nat.count_zero, Nat.count_zero, if_neg]
    rw [isFirstRow_iff]
    omega
  | succ x ih =>
    have h2 : ¬ IsFirstRow (2 * x + 1 + 1) := by
      rw [isFirstRow_iff]
      omega
    have hiff : IsFirstRow (2 * x + 1) ↔ NoAdjZero x := by
      rw [isFirstRow_iff, noAdjZero_two_mul_add_one]
      exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
    rw [show 2 * (x + 1) + 1 = 2 * x + 1 + 1 + 1 by omega, Nat.count_succ, Nat.count_succ, ih,
      Nat.count_succ (p := NoAdjZero), if_neg h2]
    by_cases hx : NoAdjZero x
    · rw [if_pos (hiff.2 hx), if_pos hx]
    · rw [if_neg (fun h => hx (hiff.1 h)), if_neg hx]

/-- The `k`-th (0-based) first appearance is `2 * A003754(k + 1) + 1`. -/
theorem nth_isFirstRow (k : ℕ) :
    Nat.nth IsFirstRow k = 2 * Nat.nth NoAdjZero k + 1 := by
  have hx := Nat.nth_mem_of_infinite noAdjZero_infinite k
  have hc := Nat.count_nth_of_infinite noAdjZero_infinite k
  have hfirst : IsFirstRow (2 * Nat.nth NoAdjZero k + 1) := by
    rw [isFirstRow_iff, noAdjZero_two_mul_add_one]
    exact ⟨by omega, hx⟩
  have h := Nat.nth_count hfirst
  rwa [count_isFirstRow, hc] at h

/-! ## The changing bit between consecutive no-`00` numbers -/

/-- **Successor bit.** If `x < y` are consecutive no-`00` numbers, the highest
bit where they differ is at 1-based position `trailingOnes x + 1`. -/
theorem size_xor_of_consecutive (x : ℕ) : ∀ y : ℕ, NoAdjZero x → NoAdjZero y → x < y →
    (∀ z, x < z → z < y → ¬ NoAdjZero z) → (x ^^^ y).size = trailingOnes x + 1 := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro y hx hy hxy hbetween
    rcases Nat.mod_two_eq_zero_or_one x with hx2 | hx2
    · obtain ⟨m, rfl⟩ : ∃ m, x = 2 * m := ⟨x / 2, by omega⟩
      have hm : NoAdjZero m := by
        have := noAdjZero_half hx
        rwa [show 2 * m / 2 = m by omega] at this
      have hsucc : NoAdjZero (2 * m + 1) := noAdjZero_two_mul_add_one.2 hm
      have hy' : y = 2 * m + 1 := by
        by_contra hne
        exact hbetween (2 * m + 1) (by omega) (by omega) hsucc
      subst hy'
      have e1 : 2 * m + 1 = Nat.bit true m := by simp [Nat.bit_val]
      have e0 : 2 * m = Nat.bit false m := by simp [Nat.bit_val]
      rw [trailingOnes_of_even hx2, e1, e0, Nat.xor_bit, Nat.xor_self]
      decide
    · obtain ⟨m, rfl⟩ : ∃ m, x = 2 * m + 1 := ⟨x / 2, by omega⟩
      have hm : NoAdjZero m := noAdjZero_two_mul_add_one.1 hx
      obtain ⟨b, k, hyk⟩ : ∃ b : Bool, ∃ k, y = Nat.bit b k :=
        by
          rcases Nat.mod_two_eq_zero_or_one y with h | h
          · exact ⟨false, y / 2, by rw [Nat.bit_val, Bool.toNat_false]; omega⟩
          · exact ⟨true, y / 2, by rw [Nat.bit_val, Bool.toNat_true]; omega⟩
      subst hyk
      have hbval := Nat.bit_val b k
      have hb1 := Bool.toNat_le b
      have hk : NoAdjZero k := by
        have := noAdjZero_half hy
        rwa [Nat.bit_div_two] at this
      have hmk : m < k := by omega
      have hbetween' : ∀ z, m < z → z < k → ¬ NoAdjZero z := by
        intro z hz1 hz2 hz
        exact hbetween (2 * z + 1) (by omega) (by omega) (noAdjZero_two_mul_add_one.2 hz)
      have hih := ih m (by omega) k hm hk hmk hbetween'
      have hne : m ^^^ k ≠ 0 := fun h => by
        have := Nat.eq_of_xor_eq_zero h
        omega
      have e1 : 2 * m + 1 = Nat.bit true m := by simp [Nat.bit_val]
      rw [e1, Nat.xor_bit, Nat.size_bit (Nat.bit_ne_zero _ hne), hih, ← e1,
        trailingOnes_two_mul_add_one]

/-! ## The conjecture -/

/-- **Wiseman's conjecture (A083368, Gus Wiseman, Jul 24 2025).**

Verbatim: "Conjecture: To obtain this sequence, start with A245563 (maximal
run lengths of binary indices), then remove empty and duplicate rows (giving
A385817), then take the first term of each remaining row."

For every `j ≥ 1`, the first entry of row `j` of A385817 equals A083368(j).
The guard `1 ≤ j` is the offset of both sequences. -/
theorem a385817Row_head_eq_a083368 (j : ℕ) (hj : 1 ≤ j) :
    (a385817Row j).head? = some (a083368 j) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hinf := noAdjZero_infinite
  set x := Nat.nth NoAdjZero i with hxdef
  have hx : NoAdjZero x := Nat.nth_mem_of_infinite hinf i
  have hy : NoAdjZero (Nat.nth NoAdjZero (i + 1)) := Nat.nth_mem_of_infinite hinf (i + 1)
  have hxy : x < Nat.nth NoAdjZero (i + 1) := Nat.nth_strictMono hinf (Nat.lt_succ_self i)
  have hbetween : ∀ z, x < z → z < Nat.nth NoAdjZero (i + 1) → ¬ NoAdjZero z := by
    intro z hz1 hz2 hz
    have hzc := Nat.nth_count hz
    rw [← hzc] at hz1 hz2
    have h1 := (Nat.nth_strictMono hinf).lt_iff_lt.1 hz1
    have h2 := (Nat.nth_strictMono hinf).lt_iff_lt.1 hz2
    omega
  have hsize := size_xor_of_consecutive x _ hx hy hxy hbetween
  have hrow : a385817Row (i + 1) = runLengths (2 * x + 1) := by
    rw [a385817Row, Nat.add_sub_cancel, nth_isFirstRow]
  obtain ⟨t, ht⟩ := runLengths_two_mul_add_one_head x
  have ha : a083368 (i + 1) = (x ^^^ Nat.nth NoAdjZero (i + 1)).size := by
    rw [a083368, a003754, a003754, Nat.add_sub_cancel, Nat.add_sub_cancel]
  rw [hrow, ht, ha, hsize]
  rfl

/-- Satisfiability of the hypothesis at `j = 1`: row 1 of A385817 is `[1]`
and `A083368(1) = 1`. -/
example : 1 ≤ 1 ∧ (a385817Row 1).head? = some 1 :=
  ⟨le_rfl, by rw [a385817Row, nth_eq_of_count (n := 1) (by decide) (by decide)]; decide⟩

end Candidates.A083368WisemanFirstPart
