/-
# A387737 — partitions with a large part and smallest part ≥ number of parts

## OEIS source (retrieved 2026-10-21 with `oeis show A387737`, `oeis show A387736`,
## and the live entries `https://oeis.org/A387737`, `https://oeis.org/A387736`)

```
A387737
NAME:     Number of partitions of n such that the largest part is >= n/2 and if
          the partition has k parts then the smallest part is >= k.
OFFSET:   1
TERMS:    1,1,1,2,2,3,3,4,4,5,5,7,7,9,9,12,12,15,15,19,19,23,23,29,29,35,35,43,...
EXAMPLE:  a(6)=3 because of the partitions 6, 4+2, and 3+3.
FORMULA (the conjecture, in the entry by its author _Sean A. Irvine_, Sep 07 2025):
          Conjecture: a(n) = A387736(n) + 1, n>=4.

A387736
NAME:     Number of partitions of n such that the largest part is >= n/2,
          adjacent parts differ by at least 2, and the smallest part >= 2.
OFFSET:   0
TERMS:    0,0,1,1,1,1,2,2,3,3,4,4,6,6,8,8,11,11,14,14,18,18,22,22,28,28,34,34,...
EXAMPLE:  a(6)=2 because of the partitions 6 and 4+2.
```

## Status

Triage: open (no proof in the entry or the literature as far as the triage
could tell).  Computation (this campaign): the identity holds for every
`4 ≤ n ≤ 70`, the brute-force counts agreeing with both data lines; for
`n = 1, 2, 3` the differences are `1, 0, 0`, so the guard `4 ≤ n` is needed.

This file proves the conjecture for all `n ≥ 4`
(`a387737_eq_a387736_add_one`), with no `sorry`.

## Proof idea

Write a partition in nonincreasing order as `a :: μ` with `a` the largest part
and `j = |μ|`.  For A387737, `μ` has all parts `≥ j + 1`; for A387736, `μ` has
gaps `≥ 2` and parts `≥ 2`.  The size-preserving bijection
`ν_i = μ_i + j + 1 - 2 i` (implemented index-free as "subtract `j + 1`, then add
the staircase `2j, …, 4, 2`") maps one tail class onto the other and fixes the
largest part.  The largest-part condition carries over, and the gap between `a`
and `ν_1` is automatic except when `j = 1` and `a - μ_1 ≤ 1`.  That leaves
exactly one partition, `(⌈n/2⌉, ⌊n/2⌋)`, which is counted by A387737 and not by
A387736.
-/
import Mathlib

set_option autoImplicit false

namespace Candidates.A387737CountsPartitionsLargest

open Finset

/-! ## Definition layer -/

/-- "The largest part is `≥ n/2`": some part `a` satisfies `n ≤ 2 * a` (real
division cleared; a part with this property exists iff the largest part has it). -/
def HasLargePart {n : ℕ} (p : Nat.Partition n) : Prop := ∃ a ∈ p.parts, n ≤ 2 * a

/-- Decidability of `HasLargePart` via bounded existence over the multiset of parts. -/
instance {n : ℕ} : DecidablePred (@HasLargePart n) := fun _ => Multiset.decidableExistsMultiset

/-- The parts of `p` listed in nonincreasing order. -/
def decParts {n : ℕ} (p : Nat.Partition n) : List ℕ := p.parts.sort (· ≥ ·)

/-- A387737 condition: largest part `≥ n/2`, and every part (equivalently the
smallest part) is at least the number of parts. -/
def IsA387737 {n : ℕ} (p : Nat.Partition n) : Prop :=
  HasLargePart p ∧ ∀ a ∈ p.parts, Multiset.card p.parts ≤ a

/-- A387736 condition: largest part `≥ n/2`, adjacent parts (in nonincreasing
order) differ by at least `2`, and every part (equivalently the smallest part)
is at least `2`. -/
def IsA387736 {n : ℕ} (p : Nat.Partition n) : Prop :=
  HasLargePart p ∧ (decParts p).IsChain (fun a b => b + 2 ≤ a) ∧ ∀ a ∈ p.parts, 2 ≤ a

/-- Decidability of the A387737 condition. -/
instance {n : ℕ} : DecidablePred (@IsA387737 n) := fun _ => by
  unfold IsA387737; infer_instance

/-- Decidability of the A387736 condition. -/
instance {n : ℕ} : DecidablePred (@IsA387736 n) := fun _ => by
  unfold IsA387736; infer_instance

/-- `A387737(n)`: the number of partitions of `n` with largest part `≥ n/2` and
smallest part `≥` the number of parts. -/
def a387737 (n : ℕ) : ℕ := #{p : Nat.Partition n | IsA387737 p}

/-- `A387736(n)`: the number of partitions of `n` with largest part `≥ n/2`,
adjacent parts differing by at least `2`, and smallest part `≥ 2`. -/
def a387736 (n : ℕ) : ℕ := #{p : Nat.Partition n | IsA387736 p}

/-- Build a partition of `n` from a list of positive parts summing to `n`. -/
def ofList {n : ℕ} (L : List ℕ) (hpos : ∀ x ∈ L, 0 < x) (hs : L.sum = n) : Nat.Partition n :=
  ⟨↑L, fun hx => hpos _ hx, by rw [Multiset.sum_coe, hs]⟩

/-- Sorting the parts of a partition built from a nonincreasing list returns that list. -/
theorem decParts_ofList {n : ℕ} (L : List ℕ) (hpos : ∀ x ∈ L, 0 < x) (hs : L.sum = n)
    (hd : L.IsChain (fun a b => b ≤ a)) : decParts (ofList L hpos hs) = L := by
  rw [decParts, ofList, Multiset.coe_sort]
  exact List.mergeSort_eq_self _ (List.isChain_iff_pairwise.1 hd)

/-! ## Ground truth -/

/-- `A387737(1) = 1` (first data term): the only partition `(1)` qualifies. -/
example : a387737 1 = 1 := by
  rw [a387737, Finset.univ_unique, Finset.filter_singleton, if_pos (by decide)]
  rfl

/-- `A387736(1) = 0` (data term at offset 1): the only partition `(1)` has a part `< 2`. -/
example : a387736 1 = 0 := by
  rw [a387736, Finset.univ_unique, Finset.filter_singleton, if_neg]
  · rfl
  · rintro ⟨-, -, h⟩
    exact absurd (h 1 (by decide)) (by decide)

/-- A387737 example, `a(6) = 3`: `6`, `4+2`, `3+3` are counted. -/
example : IsA387737 (ofList [6] (by decide) (by decide) : Nat.Partition 6) ∧
    IsA387737 (ofList [4, 2] (by decide) (by decide) : Nat.Partition 6) ∧
    IsA387737 (ofList [3, 3] (by decide) (by decide) : Nat.Partition 6) := by
  decide

/-- The other partitions of `6` are not counted by A387737. -/
example : ¬ IsA387737 (ofList [5, 1] (by decide) (by decide) : Nat.Partition 6) ∧
    ¬ IsA387737 (ofList [4, 1, 1] (by decide) (by decide) : Nat.Partition 6) ∧
    ¬ IsA387737 (ofList [3, 2, 1] (by decide) (by decide) : Nat.Partition 6) ∧
    ¬ IsA387737 (ofList [2, 2, 2] (by decide) (by decide) : Nat.Partition 6) := by
  decide

/-- A387736 example, `a(6) = 2`: `6` and `4+2` are counted, `3+3` is not. -/
example : IsA387736 (ofList [6] (by decide) (by decide) : Nat.Partition 6) ∧
    IsA387736 (ofList [4, 2] (by decide) (by decide) : Nat.Partition 6) ∧
    ¬ IsA387736 (ofList [3, 3] (by decide) (by decide) : Nat.Partition 6) := by
  simp only [IsA387736, decParts_ofList _ _ _ (by decide : List.IsChain _ [6]),
    decParts_ofList _ _ _ (by decide : List.IsChain _ [4, 2]),
    decParts_ofList _ _ _ (by decide : List.IsChain (fun a b => b ≤ a) [3, 3])]
  decide

/-! ## List layer: the staircase bijection on tails -/

/-- Add the staircase `2m, …, 4, 2` to a list of length `m` (the entry with `k` entries after it
gains `2 (k + 1)`). -/
def stair : List ℕ → List ℕ
  | [] => []
  | x :: xs => (x + 2 * (xs.length + 1)) :: stair xs

/-- Subtract the staircase `2m, …, 4, 2` from a list of length `m` (truncated subtraction). -/
def unstair : List ℕ → List ℕ
  | [] => []
  | y :: ys => (y - 2 * (ys.length + 1)) :: unstair ys

/-- `stair` preserves length. -/
theorem length_stair (l : List ℕ) : (stair l).length = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [stair, ih]

/-- `unstair` preserves length. -/
theorem length_unstair (l : List ℕ) : (unstair l).length = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [unstair, ih]

/-- `stair` adds `m (m + 1)` to the sum of a list of length `m`. -/
theorem sum_stair (l : List ℕ) : (stair l).sum = l.sum + l.length * (l.length + 1) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [stair, List.sum_cons, ih, List.length_cons]
    ring

/-- `unstair` is a left inverse of `stair`. -/
theorem unstair_stair (l : List ℕ) : unstair (stair l) = l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [stair, unstair, ih, length_stair]

/-- Every entry of `stair l` is at least `2`. -/
theorem two_le_of_mem_stair (l : List ℕ) : ∀ z ∈ stair l, 2 ≤ z := by
  induction l with
  | nil => simp [stair]
  | cons x xs ih =>
    intro z hz
    simp only [stair, List.mem_cons] at hz
    rcases hz with rfl | hz
    · omega
    · exact ih z hz

/-- In a chain with consecutive gaps `≥ 2` and all entries `≥ 2`, the head is at least twice the
length. -/
theorem head_big (ys : List ℕ) : ∀ y : ℕ, (y :: ys).IsChain (fun a b => b + 2 ≤ a) →
    (∀ x ∈ y :: ys, 2 ≤ x) → 2 * (ys.length + 1) ≤ y := by
  induction ys with
  | nil => intro y _ h; simpa using h y (by simp)
  | cons w ws ih =>
    intro y hc h2
    rw [List.isChain_cons_cons] at hc
    have := ih w hc.2 (fun x hx => h2 x (List.mem_cons_of_mem _ hx))
    simp only [List.length_cons]
    omega

/-- On chains with gaps `≥ 2` and entries `≥ 2`, `stair` is a left inverse of `unstair`. -/
theorem stair_unstair (ν : List ℕ) (hc : ν.IsChain (fun a b => b + 2 ≤ a))
    (h2 : ∀ x ∈ ν, 2 ≤ x) : stair (unstair ν) = ν := by
  induction ν with
  | nil => rfl
  | cons y ys ih =>
    have hy := head_big ys y hc h2
    simp only [unstair, stair, length_unstair]
    rw [ih hc.tail (fun x hx => h2 x (List.mem_cons_of_mem _ hx))]
    congr 1
    omega

/-- `stair` turns a nonincreasing list into one with consecutive gaps `≥ 2`. -/
theorem isChain_stair (l : List ℕ) (hl : l.IsChain (fun a b => b ≤ a)) :
    (stair l).IsChain (fun a b => b + 2 ≤ a) := by
  induction l with
  | nil => exact List.isChain_nil
  | cons x xs ih =>
    cases xs with
    | nil => exact List.isChain_singleton _
    | cons w ws =>
      rw [List.isChain_cons_cons] at hl
      simp only [stair, List.length_cons] at ih ⊢
      rw [List.isChain_cons_cons]
      exact ⟨by omega, ih hl.2⟩

/-- `unstair` turns a list with gaps `≥ 2` and entries `≥ 2` into a nonincreasing list. -/
theorem isChain_unstair (ν : List ℕ) (hc : ν.IsChain (fun a b => b + 2 ≤ a))
    (h2 : ∀ x ∈ ν, 2 ≤ x) : (unstair ν).IsChain (fun a b => b ≤ a) := by
  induction ν with
  | nil => exact List.isChain_nil
  | cons y ys ih =>
    cases ys with
    | nil => exact List.isChain_singleton _
    | cons w ws =>
      have hy := head_big (w :: ws) y hc h2
      have hw := head_big ws w hc.tail (fun x hx => h2 x (List.mem_cons_of_mem _ hx))
      have hc' := hc
      rw [List.isChain_cons_cons] at hc'
      simp only [unstair, List.length_cons] at ih hy ⊢
      rw [List.isChain_cons_cons]
      exact ⟨by omega, ih hc'.2 (fun x hx => h2 x (List.mem_cons_of_mem _ hx))⟩

/-- Subtracting `c` from every entry (all `≥ c`) lowers the sum by `length * c`. -/
theorem sum_map_sub_add (c : ℕ) (l : List ℕ) (h : ∀ x ∈ l, c ≤ x) :
    (l.map (· - c)).sum + l.length * c = l.sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.map_cons, List.sum_cons, List.length_cons, add_one_mul]
    omega

/-- `unstair` lowers the sum by `m (m + 1)` on gap-`2` chains with entries `≥ 2`. -/
theorem sum_unstair (ν : List ℕ) (hc : ν.IsChain (fun a b => b + 2 ≤ a))
    (h2 : ∀ x ∈ ν, 2 ≤ x) : (unstair ν).sum + ν.length * (ν.length + 1) = ν.sum := by
  conv_rhs => rw [← stair_unstair ν hc h2]
  rw [sum_stair, length_unstair]

/-- Tail map for A387737 → A387736: subtract `j + 1` from each of the `j` parts, then add the
staircase. -/
def tailF (μ : List ℕ) : List ℕ := stair (μ.map (· - (μ.length + 1)))

/-- Tail map for A387736 → A387737: remove the staircase, then add `j + 1` to each of the `j`
parts. -/
def tailG (ν : List ℕ) : List ℕ := (unstair ν).map (· + (ν.length + 1))

/-- Map on nonincreasing part lists: keep the largest part, transform the tail by `tailF`. -/
def F : List ℕ → List ℕ
  | [] => []
  | a :: μ => a :: tailF μ

/-- Inverse map on part lists: keep the largest part, transform the tail by `tailG`. -/
def G : List ℕ → List ℕ
  | [] => []
  | a :: ν => a :: tailG ν

/-- `tailF` preserves length. -/
theorem length_tailF (μ : List ℕ) : (tailF μ).length = μ.length := by
  simp [tailF, length_stair]

/-- `tailG` undoes `tailF` on tails whose entries are all `≥ length + 1`. -/
theorem tailG_tailF (μ : List ℕ) (h : ∀ x ∈ μ, μ.length + 1 ≤ x) : tailG (tailF μ) = μ := by
  rw [tailG, length_tailF, tailF, unstair_stair, List.map_map]
  conv_rhs => rw [← List.map_id μ]
  refine List.map_congr_left (fun x hx => ?_)
  have := h x hx
  simp only [Function.comp_apply, id_eq]
  omega

/-- `tailF` undoes `tailG` on gap-`2` chains with entries `≥ 2`. -/
theorem tailF_tailG (ν : List ℕ) (hc : ν.IsChain (fun a b => b + 2 ≤ a))
    (h2 : ∀ x ∈ ν, 2 ≤ x) : tailF (tailG ν) = ν := by
  have hlen : (tailG ν).length = ν.length := by simp [tailG, length_unstair]
  rw [tailF, hlen, tailG, List.map_map]
  have : (fun x => x - (ν.length + 1)) ∘ (fun x => x + (ν.length + 1)) = id := by
    funext x; simp
  rw [this, List.map_id, stair_unstair ν hc h2]

/-- `tailF` preserves the sum on tails whose entries are all `≥ length + 1`. -/
theorem sum_tailF (μ : List ℕ) (h : ∀ x ∈ μ, μ.length + 1 ≤ x) : (tailF μ).sum = μ.sum := by
  rw [tailF, sum_stair, List.length_map, ← sum_map_sub_add (μ.length + 1) μ h]

/-- `tailG` preserves the sum on gap-`2` chains with entries `≥ 2`. -/
theorem sum_tailG (ν : List ℕ) (hc : ν.IsChain (fun a b => b + 2 ≤ a))
    (h2 : ∀ x ∈ ν, 2 ≤ x) : (tailG ν).sum = ν.sum := by
  rw [← sum_unstair ν hc h2, tailG, ← length_unstair ν]
  have := sum_map_sub_add (ν.length + 1) ((unstair ν).map (· + (ν.length + 1)))
    (fun x hx => by obtain ⟨u, -, rfl⟩ := List.mem_map.1 hx; omega)
  rw [List.map_map] at this
  have hid : (fun x => x - (ν.length + 1)) ∘ (fun x => x + (ν.length + 1)) = id := by
    funext x; simp
  rw [hid, List.map_id, List.length_map] at this
  rw [length_unstair] at this ⊢
  omega

/-- The exceptional part list `(⌈n/2⌉, ⌊n/2⌋)`, counted by A387737 but not by A387736. -/
def eL (n : ℕ) : List ℕ := [n - n / 2, n / 2]

/-- List form of the A387737 condition: some part `a` has `n ≤ 2a`, and every part is `≥` the
number of parts. -/
def Q1 (n : ℕ) (L : List ℕ) : Prop := (∃ a ∈ L, n ≤ 2 * a) ∧ ∀ x ∈ L, L.length ≤ x

/-- List form of the A387736 condition: some part `a` has `n ≤ 2a`, consecutive gaps `≥ 2`, all
parts `≥ 2`. -/
def Q2 (n : ℕ) (L : List ℕ) : Prop :=
  (∃ a ∈ L, n ≤ 2 * a) ∧ L.IsChain (fun a b => b + 2 ≤ a) ∧ ∀ x ∈ L, 2 ≤ x

/-- In a nonincreasing list the head is the maximum. -/
theorem le_head_of_isChain (a : ℕ) (μ : List ℕ) (h : (a :: μ).IsChain (fun a b => b ≤ a)) :
    ∀ x ∈ a :: μ, x ≤ a := by
  have hp := (List.isChain_iff_pairwise.1 h)
  intro x hx
  rcases List.mem_cons.1 hx with rfl | hx
  · exact le_rfl
  · exact List.rel_of_pairwise_cons hp hx

/-- A list with consecutive gaps `≥ 2` is nonincreasing. -/
theorem isChain_le_of_gap {L : List ℕ} (h : L.IsChain (fun a b => b + 2 ≤ a)) :
    L.IsChain (fun a b => b ≤ a) := h.imp (fun a b hab => by omega)

/-- If every entry is `≥ c` then `length * c ≤ sum`. -/
theorem le_sum_of_forall_le (c : ℕ) (l : List ℕ) (h : ∀ x ∈ l, c ≤ x) :
    l.length * c ≤ l.sum := by
  have := sum_map_sub_add c l h
  omega

/-- Subtracting a constant preserves being nonincreasing. -/
theorem isChain_map_sub (c : ℕ) (l : List ℕ) (h : l.IsChain (fun a b => b ≤ a)) :
    (l.map (· - c)).IsChain (fun a b => b ≤ a) :=
  List.isChain_map_of_isChain (R := fun a b : ℕ => b ≤ a) (S := fun a b : ℕ => b ≤ a) _
    (fun _ _ hxy => Nat.sub_le_sub_right hxy c) h

/-- Adding a constant preserves being nonincreasing. -/
theorem isChain_map_add (c : ℕ) (l : List ℕ) (h : l.IsChain (fun a b => b ≤ a)) :
    (l.map (· + c)).IsChain (fun a b => b ≤ a) :=
  List.isChain_map_of_isChain (R := fun a b : ℕ => b ≤ a) (S := fun a b : ℕ => b ≤ a) _
    (fun _ _ hxy => Nat.add_le_add_right hxy c) h

/-- Forward direction on lists: for `n ≥ 4`, `F` sends a nonincreasing A387737 list of sum `n`
to a list of sum `n` that is either the exceptional list or an A387736 list. -/
theorem F_spec (n : ℕ) (hn : 4 ≤ n) (L : List ℕ) (hd : L.IsChain (fun a b => b ≤ a))
    (hs : L.sum = n) (hq : Q1 n L) :
    (F L).sum = n ∧ (F L = eL n ∨ Q2 n (F L)) := by
  obtain ⟨⟨b, hbL, hb⟩, hall⟩ := hq
  cases L with
  | nil => simp at hbL
  | cons a μ =>
    have hmax := le_head_of_isChain a μ hd
    have ha : n ≤ 2 * a := hb.trans (by have := hmax b hbL; omega)
    have hμ : ∀ x ∈ μ, μ.length + 1 ≤ x := fun x hx => by
      simpa using hall x (List.mem_cons_of_mem _ hx)
    have hsum : (F (a :: μ)).sum = n := by
      rw [F, List.sum_cons, sum_tailF μ hμ, ← hs, List.sum_cons]
    refine ⟨hsum, ?_⟩
    rw [List.sum_cons] at hs
    cases μ with
    | nil =>
      right
      simp only [F, tailF, List.map_nil, stair, List.sum_nil] at hs ⊢
      refine ⟨⟨a, List.mem_singleton_self a, by omega⟩, List.isChain_singleton _,
        fun x hx => by rw [List.mem_singleton] at hx; omega⟩
    | cons m rest =>
      have hm := hμ m (by simp)
      have hrest : ∀ x ∈ rest, rest.length + 2 ≤ x := fun x hx => by
        have := hμ x (List.mem_cons_of_mem _ hx)
        simp only [List.length_cons] at this
        omega
      have hsr := le_sum_of_forall_le _ rest hrest
      have hma : m ≤ a := hmax m (by simp)
      have hFt : tailF (m :: rest) =
          (m + rest.length) :: stair (rest.map (· - (rest.length + 2))) := by
        simp only [tailF, List.length_cons, List.map_cons, stair, List.length_map]
        congr 1
        simp only [List.length_cons] at hm
        omega
      have htail : (tailF (m :: rest)).IsChain (fun a b => b + 2 ≤ a) :=
        isChain_stair _ (isChain_map_sub _ _ hd.tail)
      have h2tail : ∀ x ∈ tailF (m :: rest), 2 ≤ x := two_le_of_mem_stair _
      by_cases hgap : m + rest.length + 2 ≤ a
      · right
        refine ⟨⟨a, List.mem_cons_self, ha⟩, ?_, ?_⟩
        · rw [F, List.isChain_cons]
          refine ⟨?_, htail⟩
          rw [hFt]
          intro y hy
          rw [List.head?_cons, Option.mem_some_iff] at hy
          omega
        · intro x hx
          rcases List.mem_cons.1 hx with rfl | hx
          · omega
          · exact h2tail x hx
      · left
        have hr : rest = [] := by
          rcases rest with _ | ⟨w, ws⟩
          · rfl
          · exfalso
            simp only [List.length_cons, List.sum_cons] at hsr hgap hs
            nlinarith
        subst hr
        simp only [List.sum_cons, List.sum_nil] at hs
        rw [F, hFt]
        simp only [eL, List.length_nil, List.map_nil, stair, add_zero, List.cons.injEq, and_true]
        simp only [List.length_nil, List.length_singleton] at hgap hm
        omega


/-- `G` fixes the exceptional list when `n ≥ 4`. -/
theorem G_eL (n : ℕ) (hn : 4 ≤ n) : G (eL n) = eL n := by
  simp only [eL, G, tailG, unstair, List.length_nil, List.length_singleton, List.map_cons,
    List.map_nil, List.cons.injEq, and_true, true_and]
  omega

/-- `F` fixes the exceptional list when `n ≥ 4`. -/
theorem F_eL (n : ℕ) (hn : 4 ≤ n) : F (eL n) = eL n := by
  simp only [eL, F, tailF, stair, List.length_nil, List.length_singleton, List.map_cons,
    List.map_nil, List.cons.injEq, and_true, true_and]
  omega

/-- For `n ≥ 4` the exceptional list is nonincreasing, sums to `n`, and satisfies the A387737
condition. -/
theorem eL_spec (n : ℕ) (hn : 4 ≤ n) :
    (eL n).IsChain (fun a b => b ≤ a) ∧ (eL n).sum = n ∧ Q1 n (eL n) := by
  refine ⟨?_, ?_, ⟨n - n / 2, by simp [eL], by omega⟩, ?_⟩
  · simp only [eL, List.isChain_cons_cons]
    exact ⟨by omega, List.isChain_singleton _⟩
  · simp only [eL, List.sum_cons, List.sum_nil]
    omega
  · intro x hx
    simp only [eL, List.mem_cons, List.not_mem_nil, or_false] at hx
    simp only [eL, List.length_cons, List.length_nil]
    omega

/-- The exceptional list violates the gap-`2` condition, so it is not an A387736 list. -/
theorem not_Q2_eL (n : ℕ) : ¬ Q2 n (eL n) := by
  rintro ⟨-, hc, -⟩
  simp only [eL, List.isChain_cons_cons] at hc
  omega

/-- Backward direction on lists: for `n ≥ 4`, `G` sends an A387736 list of sum `n` to a
nonincreasing A387737 list of sum `n`. -/
theorem G_spec (n : ℕ) (hn : 4 ≤ n) (N : List ℕ) (hs : N.sum = n) (hq : Q2 n N) :
    (G N).IsChain (fun a b => b ≤ a) ∧ (G N).sum = n ∧ Q1 n (G N) := by
  obtain ⟨⟨b, hbN, hb⟩, hc, h2⟩ := hq
  cases N with
  | nil => simp at hbN
  | cons a ν =>
    have hmax := le_head_of_isChain a ν (isChain_le_of_gap hc)
    have ha : n ≤ 2 * a := hb.trans (by have := hmax b hbN; omega)
    have hbig := head_big ν a hc h2
    have hcν : ν.IsChain (fun a b => b + 2 ≤ a) := hc.tail
    have h2ν : ∀ x ∈ ν, 2 ≤ x := fun x hx => h2 x (List.mem_cons_of_mem _ hx)
    refine ⟨?_, ?_, ⟨a, List.mem_cons_self, ha⟩, ?_⟩
    · rw [G, List.isChain_cons]
      refine ⟨?_, isChain_map_add _ _ (isChain_unstair ν hcν h2ν)⟩
      intro y hy
      cases ν with
      | nil => simp [tailG, unstair] at hy
      | cons w ws =>
        simp only [tailG, unstair, List.map_cons, List.head?_cons, Option.mem_some_iff,
          List.length_cons] at hy
        have hw : w + 2 ≤ a := (List.isChain_cons_cons.1 hc).1
        have hwb := head_big ws w hcν h2ν
        omega
    · rw [G, List.sum_cons, sum_tailG ν hcν h2ν, ← hs, List.sum_cons]
    · intro x hx
      have hlen : (G (a :: ν)).length = ν.length + 1 := by
        simp [G, tailG, length_unstair]
      rw [hlen]
      rw [G, List.mem_cons] at hx
      rcases hx with rfl | hx
      · omega
      · obtain ⟨u, -, rfl⟩ := List.mem_map.1 hx
        omega

/-- `G ∘ F` is the identity on A387737 lists. -/
theorem G_F (n : ℕ) (L : List ℕ) (hq : Q1 n L) : G (F L) = L := by
  cases L with
  | nil => rfl
  | cons a μ =>
    have hμ : ∀ x ∈ μ, μ.length + 1 ≤ x := fun x hx => by
      simpa using hq.2 x (List.mem_cons_of_mem _ hx)
    rw [F, G, tailG_tailF μ hμ]

/-- `F ∘ G` is the identity on A387736 lists. -/
theorem F_G (n : ℕ) (N : List ℕ) (hq : Q2 n N) : F (G N) = N := by
  obtain ⟨-, hc, h2⟩ := hq
  cases N with
  | nil => rfl
  | cons a ν =>
    rw [G, F, tailF_tailG ν hc.tail (fun x hx => h2 x (List.mem_cons_of_mem _ hx))]

/-! ## Partition layer: sorting parts -/

/-- Membership in the sorted part list is membership in the parts. -/
theorem mem_decParts {n : ℕ} (p : Nat.Partition n) (a : ℕ) : a ∈ decParts p ↔ a ∈ p.parts :=
  Multiset.mem_sort _

/-- The sorted part list has as many entries as there are parts. -/
theorem length_decParts {n : ℕ} (p : Nat.Partition n) :
    (decParts p).length = Multiset.card p.parts :=
  Multiset.length_sort _

/-- The sorted part list is nonincreasing. -/
theorem isChain_decParts {n : ℕ} (p : Nat.Partition n) :
    (decParts p).IsChain (fun a b => b ≤ a) :=
  List.isChain_iff_pairwise.2 (Multiset.pairwise_sort _ _)

/-- The sorted part list of a partition of `n` sums to `n`. -/
theorem sum_decParts {n : ℕ} (p : Nat.Partition n) : (decParts p).sum = n := by
  have h := p.parts_sum
  rw [← Multiset.sort_eq p.parts (· ≥ ·), Multiset.sum_coe] at h
  exact h

/-- Rebuilding a partition from its sorted part list returns it. -/
theorem ofList_decParts {n : ℕ} (p : Nat.Partition n) (hpos : ∀ x ∈ decParts p, 0 < x)
    (hs : (decParts p).sum = n) : ofList (decParts p) hpos hs = p := by
  ext1
  exact Multiset.sort_eq _ _

/-- The A387737 condition in terms of the sorted part list. -/
theorem isA387737_iff {n : ℕ} (p : Nat.Partition n) : IsA387737 p ↔ Q1 n (decParts p) := by
  simp only [IsA387737, HasLargePart, Q1, mem_decParts, length_decParts]

/-- The A387736 condition in terms of the sorted part list. -/
theorem isA387736_iff {n : ℕ} (p : Nat.Partition n) : IsA387736 p ↔ Q2 n (decParts p) := by
  simp only [IsA387736, HasLargePart, Q2, mem_decParts]


/-! ## The main theorem -/

/-- Entries of an A387737 list are positive. -/
theorem pos_of_Q1 {n : ℕ} {L : List ℕ} (hq : Q1 n L) : ∀ x ∈ L, 0 < x := fun x hx =>
  lt_of_lt_of_le (List.length_pos_of_mem hx) (hq.2 x hx)

/-- Entries of an A387736 list are positive. -/
theorem pos_of_Q2 {n : ℕ} {L : List ℕ} (hq : Q2 n L) : ∀ x ∈ L, 0 < x := fun x hx =>
  lt_of_lt_of_le (by norm_num) (hq.2.2 x hx)

/-- Forward direction with nonincreasingness and positivity of `F L` packaged. -/
theorem F_spec' (n : ℕ) (hn : 4 ≤ n) (L : List ℕ) (hd : L.IsChain (fun a b => b ≤ a))
    (hs : L.sum = n) (hq : Q1 n L) :
    (F L).IsChain (fun a b => b ≤ a) ∧ (F L).sum = n ∧ (∀ x ∈ F L, 0 < x) ∧
      (F L = eL n ∨ Q2 n (F L)) := by
  obtain ⟨hsum, h⟩ := F_spec n hn L hd hs hq
  refine ⟨?_, hsum, ?_, h⟩
  · rcases h with h | h
    · rw [h]; exact (eL_spec n hn).1
    · exact isChain_le_of_gap h.2.1
  · rcases h with h | h
    · rw [h]; exact pos_of_Q1 (eL_spec n hn).2.2
    · exact pos_of_Q2 h

/-- Backward direction, including the exceptional list. -/
theorem G_spec' (n : ℕ) (hn : 4 ≤ n) (N : List ℕ) (hs : N.sum = n) (hq : N = eL n ∨ Q2 n N) :
    (G N).IsChain (fun a b => b ≤ a) ∧ (G N).sum = n ∧ Q1 n (G N) := by
  rcases hq with rfl | hq
  · rw [G_eL n hn]; exact eL_spec n hn
  · exact G_spec n hn N hs hq

/-- `F ∘ G` is the identity on A387736 lists and on the exceptional list. -/
theorem F_G' (n : ℕ) (hn : 4 ≤ n) (N : List ℕ) (hq : N = eL n ∨ Q2 n N) : F (G N) = N := by
  rcases hq with rfl | hq
  · rw [G_eL n hn, F_eL n hn]
  · exact F_G n N hq

/-- The parts of `ofList L` are `L`. -/
theorem parts_ofList {n : ℕ} (L : List ℕ) (hpos : ∀ x ∈ L, 0 < x) (hs : L.sum = n) :
    (ofList L hpos hs).parts = ↑L := rfl

/-- **A387737 conjecture (Sean A. Irvine, Sep 2025), proved.**

Verbatim (A387737, FORMULA): "Conjecture: a(n) = A387736(n) + 1, n>=4."

For every `n ≥ 4`, the number of partitions of `n` with largest part `≥ n/2` and
smallest part `≥` the number of parts equals one plus the number of partitions
of `n` with largest part `≥ n/2`, adjacent parts differing by at least `2`, and
smallest part `≥ 2`.  The extra partition is `(⌈n/2⌉, ⌊n/2⌋)`; the guard
`4 ≤ n` is needed, because the differences at `n = 1, 2, 3` are `1, 0, 0`. -/
theorem a387737_eq_a387736_add_one (n : ℕ) (hn : 4 ≤ n) : a387737 n = a387736 n + 1 := by
  obtain ⟨heD, heS, heQ⟩ := eL_spec n hn
  let e : Nat.Partition n := ofList (eL n) (pos_of_Q1 heQ) heS
  have hde : decParts e = eL n := decParts_ofList _ _ _ heD
  have he : e ∉ ({p : Nat.Partition n | IsA387736 p} : Finset (Nat.Partition n)) := by
    rw [mem_filter, isA387736_iff, hde]
    exact fun h => not_Q2_eL n h.2
  rw [a387736, ← card_insert_of_notMem he, a387737]
  have hS : ∀ p ∈ ({p : Nat.Partition n | IsA387737 p} : Finset (Nat.Partition n)),
      Q1 n (decParts p) := fun p hp => (isA387737_iff p).1 (mem_filter.1 hp).2
  have hT : ∀ q ∈ insert e ({p : Nat.Partition n | IsA387736 p} : Finset (Nat.Partition n)),
      decParts q = eL n ∨ Q2 n (decParts q) := by
    intro q hq
    rcases mem_insert.1 hq with rfl | hq
    · exact Or.inl hde
    · exact Or.inr ((isA387736_iff q).1 (mem_filter.1 hq).2)
  refine card_bij'
    (fun p hp => ofList (F (decParts p))
      (F_spec' n hn _ (isChain_decParts p) (sum_decParts p) (hS p hp)).2.2.1
      (F_spec' n hn _ (isChain_decParts p) (sum_decParts p) (hS p hp)).2.1)
    (fun q hq => ofList (G (decParts q))
      (pos_of_Q1 (G_spec' n hn _ (sum_decParts q) (hT q hq)).2.2)
      (G_spec' n hn _ (sum_decParts q) (hT q hq)).2.1)
    ?_ ?_ ?_ ?_
  · intro p hp
    obtain ⟨hd, hsum, hpos, hor⟩ := F_spec' n hn _ (isChain_decParts p) (sum_decParts p) (hS p hp)
    rcases hor with h | h
    · apply mem_insert.2
      left
      ext1
      rw [parts_ofList, parts_ofList, h]
    · apply mem_insert_of_mem
      rw [mem_filter, isA387736_iff, decParts_ofList _ _ _ hd]
      exact ⟨mem_univ _, h⟩
  · intro q hq
    obtain ⟨hd, hsum, hQ⟩ := G_spec' n hn _ (sum_decParts q) (hT q hq)
    rw [mem_filter, isA387737_iff, decParts_ofList _ _ _ hd]
    exact ⟨mem_univ _, hQ⟩
  · intro p hp
    obtain ⟨hd, hsum, hpos, hor⟩ := F_spec' n hn _ (isChain_decParts p) (sum_decParts p) (hS p hp)
    ext1
    rw [parts_ofList, decParts_ofList _ _ _ hd, G_F n _ (hS p hp), decParts, Multiset.sort_eq]
  · intro q hq
    obtain ⟨hd, hsum, hQ⟩ := G_spec' n hn _ (sum_decParts q) (hT q hq)
    ext1
    rw [parts_ofList, decParts_ofList _ _ _ hd, F_G' n hn _ (hT q hq), decParts, Multiset.sort_eq]

end Candidates.A387737CountsPartitionsLargest
